;;; coq-eglot.el --- Coq backend using a language server through Eglot  -*- lexical-binding:t -*-

;; This file is part of Proof General.

;; Portions © Copyright 2026  Pierre Courtieu

;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;;
;; Experimental backend for `coq-mode', using a language server
;; (coq-lsp) through Eglot instead of running Coq in a shell.  It is
;; selected by setting `coq-backend' to `eglot' before `coq-mode' is
;; loaded.  Requires Emacs 29 or later.
;;
;; Files in this directory may require files from coq/ (coq-mode,
;; coq-syntax...), but files from coq/ never require files from here,
;; except coq-mode.el which loads this file when the backend is
;; selected.
;;
;; Like in Proof General, a proof position, distinct from the point,
;; tells up to where the script is processed.  It is displayed like
;; the locked region of Proof General, but the text before it can be
;; edited: the proof position then moves back before the edited
;; sentence.
;;
;; The server checks the document only up to the requested positions.
;; Moving forward asks it asynchronously to check up to the target,
;; without computing goals.  Meanwhile the part to check is displayed
;; like the queue region of Proof General, and the proof position
;; follows the progress of the server, sentence by sentence.  The
;; first error found stops the proof position before its sentence.
;; Goals are asked only for the final proof position.
;;
;; Sentences are delimited by the server, not by regexps.  The answers
;; of the server are kept with the processed sentences: moving back to
;; a sentence whose goals were displayed does not ask the server.

;;; Code:

(require 'coq-mode)
(require 'coq-syntax)                   ; also loads the faces of PG
(require 'coq-indent)
(require 'color)
(require 'coq-eglot-lsp)

(defvar coq-eglot-mode)                 ; defined below

;;; Options

(defcustom coq-eglot-error-highlight-duration 10
  "Seconds during which the sentence that failed stays highlighted.
If nil, until the next command or edition before the proof position."
  :type '(choice (number :tag "Seconds")
                 (const :tag "Until the next command" nil))
  :group 'coq-eglot)

(defcustom coq-eglot-ignored-capabilities '(:completionProvider)
  "Capabilities of the server that Eglot ignores in Coq buffers.
The server checks the document only up to the requested positions.
Some requests sent by Eglot on its own force it to check up to point,
which freezes Emacs meanwhile: completion is synchronous and asks the
server to check everything before point.  See
`eglot-ignored-server-capabilities' for the possible values.  Takes
effect when the server starts managing the buffer."
  :type '(repeat symbol)
  :group 'coq-eglot)

(defcustom coq-eglot-use-flymake nil
  "If non-nil, Eglot displays the diagnostics of the server with Flymake.
Errors are then underlined until they are fixed.  Like Proof General,
only the error of the last command is highlighted by default.  Takes
effect when the server starts managing the buffer."
  :type 'boolean
  :group 'coq-eglot)

(defface coq-eglot-goals-separator '((t :inherit shadow))
  "Face of the line between the hypotheses and the conclusion.
See `coq-eglot-split-goals'.  The default inherits from `shadow', which
themes make visible on their background."
  :group 'coq-eglot)

(defcustom coq-eglot-resize-windows-function
  #'coq-eglot-resize-windows-by-priority
  "Function adjusting the heights of the goals and response windows.
Called without argument when their content changes.  If nil, the
heights are the ones Emacs chooses."
  :type '(choice (const :tag "Do not resize" nil)
                 (function-item coq-eglot-resize-windows-by-priority)
                 function)
  :group 'coq-eglot)

(defcustom coq-eglot-window-priorities '(conclusion goals response)
  "Order in which the windows get the height they need.
Used by `coq-eglot-resize-windows-by-priority'.  The goals window holds
the whole goals, or only the hypotheses if `coq-eglot-split-goals'."
  :type '(repeat (choice (const conclusion) (const goals) (const response)))
  :group 'coq-eglot)

(defcustom coq-eglot-split-goals nil
  "If non-nil, display the conclusion apart from the hypotheses.
The hypotheses of the first goal stay in the goals buffer, its
conclusion and the other goals go to the conclusion buffer, in a
window of its own: both scroll independently.  See also
`coq-eglot-toggle-split-goals'."
  :type 'boolean
  :group 'coq-eglot)

;;; Proof position

(defvar-local coq-eglot--ends nil
  "The processed sentences, the last one first.
Each element is (MARKER . ANSWER): MARKER is at the end of a sentence,
ANSWER is the answer of the server with the goals after it, or nil if
they were not asked.  The text before MARKER did not change since, so
ANSWER is still valid.  Not every processed sentence has an element.
The proof position is the first marker, or the beginning of the
buffer.")

(defvar-local coq-eglot--locked-overlay nil
  "Overlay displaying the processed part of the script.")

(defvar-local coq-eglot--queue-overlay nil
  "Overlay displaying the part of the script being checked.")

(defvar-local coq-eglot--running nil
  "The check running, or nil.
A plist with :id, the id of the request, and :target, a marker at the
end of the part to check.")

(defun coq-eglot-position ()
  "Return the proof position of the current buffer."
  (if coq-eglot--ends
      (marker-position (caar coq-eglot--ends))
    (point-min)))

(defface coq-eglot-inactive-locked-face '((t :extend t))
  "Face of the processed part of the script buffers that are not active.
Only the active script buffer displays its goals and messages, see
`coq-eglot--active-buffer'.  If this face has no background, the
background is the one of `proof-locked-face', grayed: see
`coq-eglot-inactive-saturation'."
  :group 'coq-eglot)

(defcustom coq-eglot-inactive-saturation 0.5
  "Saturation of the processed part of inactive script buffers.
A factor between 0 (gray) and 1 (same color), applied to the background
of `proof-locked-face' when `coq-eglot-inactive-locked-face' has no
background."
  :type 'number
  :group 'coq-eglot)

(defun coq-eglot--desaturate-rgb (rgb factor)
  "Return color RGB, a list of 3 numbers in [0,1], with saturation times FACTOR.
The result is a hexadecimal color string."
  (pcase-let ((`(,h ,s ,l) (apply #'color-rgb-to-hsl rgb)))
    (apply #'color-rgb-to-hex
           (append (color-hsl-to-rgb h (* s factor) l) '(2)))))

(defun coq-eglot--inactive-locked-face ()
  "Face of the processed part of an inactive script buffer.
See `coq-eglot-inactive-locked-face'."
  (let ((locked (face-background 'proof-locked-face nil t)))
    (if (or (face-background 'coq-eglot-inactive-locked-face nil t)
            (not (stringp locked))
            (not (color-defined-p locked)))
        'coq-eglot-inactive-locked-face
      (list (list :background (coq-eglot--desaturate-rgb
                               (color-name-to-rgb locked)
                               coq-eglot-inactive-saturation))
            'coq-eglot-inactive-locked-face))))

(defvar coq-eglot--active-buffer nil
  "The script buffer whose goals and messages are displayed.
It is the last one where a command of the backend ran, or where the
processed part was edited.  The processed part of the other script
buffers is grayed: they go on checking, but display nothing.  Any
command in one of them makes it active again.")

(defun coq-eglot--active-p ()
  "Non-nil if the current buffer is the active script buffer."
  (eq (current-buffer) coq-eglot--active-buffer))

(defun coq-eglot--activate ()
  "Make the current buffer the active script buffer.
Gray the processed part of the previous one, display the goals of the
current one."
  (unless (coq-eglot--active-p)
    (let ((previous coq-eglot--active-buffer))
      (setq coq-eglot--active-buffer (current-buffer))
      (when (buffer-live-p previous)
        (with-current-buffer previous (coq-eglot--update-overlays)))
      (coq-eglot--update-overlays)
      (coq-eglot--goals-at-position-async))))

(defun coq-eglot--forget-active ()
  "Forget the current buffer if it is the active script buffer."
  (when (coq-eglot--active-p)
    (setq coq-eglot--active-buffer nil)))

(defun coq-eglot--update-overlays ()
  "Update the overlays of the processed part and of the checked part."
  (unless (overlayp coq-eglot--locked-overlay)
    (setq coq-eglot--locked-overlay (make-overlay (point-min) (point-min))))
  (overlay-put coq-eglot--locked-overlay 'face
               (if (or (coq-eglot--active-p) (null coq-eglot--active-buffer))
                   'proof-locked-face
                 (coq-eglot--inactive-locked-face)))
  (move-overlay coq-eglot--locked-overlay (point-min) (coq-eglot-position))
  (if (not coq-eglot--running)
      (when (overlayp coq-eglot--queue-overlay)
        (delete-overlay coq-eglot--queue-overlay))
    (unless (overlayp coq-eglot--queue-overlay)
      (setq coq-eglot--queue-overlay (make-overlay (point-min) (point-min)))
      (overlay-put coq-eglot--queue-overlay 'face 'proof-queue-face))
    (move-overlay coq-eglot--queue-overlay (coq-eglot-position)
                  (max (coq-eglot-position)
                       (plist-get coq-eglot--running :target)))))

(defun coq-eglot--pop-ends (pos)
  "Forget the processed sentences ending after POS."
  (while (and coq-eglot--ends (> (caar coq-eglot--ends) pos))
    (set-marker (car (pop coq-eglot--ends)) nil)))

(defun coq-eglot--set-position (end answer)
  "Move the proof position to END, with the ANSWER of the server for it.
END is the end of a sentence, or nil for the beginning of the buffer.
ANSWER may be nil."
  (coq-eglot--pop-ends (or end (point-min)))
  (when end
    (if (and coq-eglot--ends (= (caar coq-eglot--ends) end))
        (when answer (setcdr (car coq-eglot--ends) answer))
      (push (cons (copy-marker end) answer) coq-eglot--ends)))
  (coq-eglot--update-overlays))

(defun coq-eglot--skip-backward (pos)
  "Return the position before the blanks and comments preceding POS."
  (save-excursion (goto-char pos) (forward-comment (- (point))) (point)))

(defun coq-eglot--skip-forward (pos)
  "Return the position after the blanks and comments following POS."
  (save-excursion (goto-char pos) (forward-comment (buffer-size)) (point)))

(defun coq-eglot--sentence-before (pos)
  "Return (END . ANSWER) for the last processed sentence ending before POS.
A sentence ending exactly at POS counts.  END is the end of the
sentence, ANSWER the answer of the server with the goals after it.
Return nil if there is no such sentence.  The kept answers are used if
possible, otherwise the server is asked for sentences it checked
already."
  (let ((end (coq-eglot--skip-backward pos)))
    (if (<= end (point-min))
        nil
      (let ((kept (assoc end coq-eglot--ends #'=)))
        (if (cdr kept)
            (cons end (cdr kept))
          ;; the sentence containing the last character before POS
          (let* ((answer (coq-eglot-lsp-goals (1- end)))
                 (range (plist-get answer :range))
                 (bounds (and range (coq-eglot-lsp-range range))))
            (cond
             ((null bounds) nil)
             ((<= (cdr bounds) pos) (cons (cdr bounds) answer))
             ;; it does not end before POS: take the one before it
             (t (coq-eglot--sentence-before (car bounds))))))))))

;;; Errors

(defvar-local coq-eglot--error-overlays nil
  "Overlays on the sentence that failed and on the error location.")

(defvar-local coq-eglot--error-timer nil
  "Timer removing the highlighting of the sentence that failed.")

(defun coq-eglot--clear-error ()
  "Remove the highlighting of the sentence that failed."
  (when (timerp coq-eglot--error-timer)
    (cancel-timer coq-eglot--error-timer)
    (setq coq-eglot--error-timer nil))
  (mapc #'delete-overlay coq-eglot--error-overlays)
  (setq coq-eglot--error-overlays nil))

(defun coq-eglot--clear-error-in (buffer)
  "Remove the highlighting of the sentence that failed in BUFFER."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (setq coq-eglot--error-timer nil)
      (coq-eglot--clear-error))))

(defun coq-eglot--error-overlay (start end face priority)
  "Add an error overlay from START to END with FACE and PRIORITY."
  (let ((ov (make-overlay start end)))
    (overlay-put ov 'face face)
    (overlay-put ov 'priority priority)
    (push ov coq-eglot--error-overlays)))

(defun coq-eglot--highlight-error (start end)
  "Highlight the sentence between START and END, which failed.
Like Proof General: the sentence with `proof-boring-face', the location
of the error, if known, with `proof-warning-face'.  Move point to the
error."
  (coq-eglot--clear-error)
  (coq-eglot--error-overlay start end 'proof-boring-face 0)
  (let ((range (coq-eglot-lsp-error-range start end)))
    (when range
      (coq-eglot--error-overlay (car range) (cdr range) 'proof-warning-face 1))
    (goto-char (if range (car range) start)))
  (when coq-eglot-error-highlight-duration
    (setq coq-eglot--error-timer
          (run-at-time coq-eglot-error-highlight-duration nil
                       #'coq-eglot--clear-error-in (current-buffer)))))

;;; Display

(defvar coq-eglot-goals-buffer-name "*goals*")
(defvar coq-eglot-conclusion-buffer-name "*conclusion*"
  "Buffer of the conclusion, see `coq-eglot-split-goals'.")
(defvar coq-eglot-response-buffer-name "*response*")

(define-derived-mode coq-eglot-goals-mode special-mode "Coq Goals"
  "Major mode for the goals of the Eglot backend of Coq."
  (setq-local font-lock-defaults '(coq-goals-font-lock-keywords)))

(define-derived-mode coq-eglot-response-mode special-mode "Coq Response"
  "Major mode for the messages of the Eglot backend of Coq."
  (setq-local font-lock-defaults '(coq-response-font-lock-keywords)))

(defun coq-eglot--display-buffer (name mode slot)
  "Return buffer NAME in MODE, displayed in the right side window SLOT."
  (let ((buffer (get-buffer-create name)))
    (with-current-buffer buffer
      (unless (eq major-mode mode) (funcall mode)))
    (display-buffer buffer
                    `((display-buffer-reuse-window
                       display-buffer-in-side-window)
                      (side . right) (slot . ,slot) (window-width . 0.5)))
    buffer))

(defun coq-eglot--set-buffer-text (name mode slot text)
  "Replace the content of buffer NAME (in MODE, window SLOT) by TEXT.
Then adjust the heights of the windows, see
`coq-eglot-resize-windows-function'.  Do nothing if called from a script
buffer that is not active: only the active one displays its state."
  (when (or (not coq-eglot-mode) (coq-eglot--active-p))
    (coq-eglot--set-buffer-text-1 name mode slot text)))

(defun coq-eglot--set-buffer-text-1 (name mode slot text)
  "Replace the content of buffer NAME (in MODE, window SLOT) by TEXT."
  (with-current-buffer (coq-eglot--display-buffer name mode slot)
    (let ((inhibit-read-only t))
      (erase-buffer)
      (insert text)
      (goto-char (point-min))))
  (when coq-eglot-resize-windows-function
    (funcall coq-eglot-resize-windows-function)))

(defun coq-eglot--allocate-heights (total needs minimum)
  "Share TOTAL lines between windows needing NEEDS lines.
NEEDS lists the heights the windows need, by priority.  Each window
gets at least MINIMUM lines, then by priority what it needs if there is
enough left.  The last one gets what remains.  Return the list of
heights in the same order, or nil if TOTAL is too small."
  (let ((rest (- total (* minimum (length needs)))))
    (when (and needs (>= rest 0))
      (let ((heights (mapcar (lambda (need)
                               (let ((extra (min rest (max 0 (- need minimum)))))
                                 (setq rest (- rest extra))
                                 (+ minimum extra)))
                             needs)))
        (setcar (last heights) (+ (car (last heights)) rest))
        heights))))

(defun coq-eglot--window-need (window)
  "Height WINDOW needs to display its whole buffer, mode line included."
  (+ (- (window-total-height window) (window-body-height window))
     (with-current-buffer (window-buffer window)
       (count-screen-lines (point-min) (point-max) nil window))))

(defun coq-eglot-resize-windows-by-priority ()
  "Give the windows the height they need, by priority.
The goals, conclusion and response windows displayed one above the
other share their height: each one gets the height it needs in the
order of `coq-eglot-window-priorities', the last one gets what remains."
  (let* ((names `((goals . ,coq-eglot-goals-buffer-name)
                  (conclusion . ,coq-eglot-conclusion-buffer-name)
                  (response . ,coq-eglot-response-buffer-name)))
         (windows (delq nil (mapcar (lambda (role)
                                      (get-buffer-window
                                       (cdr (assq role names))))
                                    coq-eglot-window-priorities)))
         (parent (window-parent (car windows))))
    (when (and (cdr windows)
               (cl-every (lambda (window) (eq (window-parent window) parent))
                         windows)
               (window-combined-p (car windows)))
      (let ((heights (coq-eglot--allocate-heights
                      (apply #'+ (mapcar #'window-total-height windows))
                      (mapcar #'coq-eglot--window-need windows)
                      window-min-height)))
        (when heights
          ;; from top to bottom, the last one takes what remains
          (let ((sorted (sort (cl-mapcar #'cons windows heights)
                              (lambda (a b) (< (window-top-line (car a))
                                               (window-top-line (car b)))))))
            (dolist (window-height (butlast sorted))
              (ignore-errors
                (window-resize (car window-height)
                               (- (cdr window-height)
                                  (window-total-height (car window-height))))))))))))

(defun coq-eglot--format-hyp (hyp)
  "Format hypothesis HYP of a goal."
  (let ((names (mapconcat #'identity (plist-get hyp :names) ", "))
        (def (plist-get hyp :def)))
    (concat "  " names
            (if def (concat " := " def) "")
            " : " (plist-get hyp :ty))))

(defun coq-eglot--format-hyps (goal)
  "Format the hypotheses of GOAL, one per line."
  (mapconcat (lambda (hyp) (concat (coq-eglot--format-hyp hyp) "\n"))
             (plist-get goal :hyps) ""))

(defun coq-eglot--format-conclusion (goal &optional no-separator)
  "Format the conclusion of GOAL, below the separator unless NO-SEPARATOR."
  (concat (if no-separator "" "  ============================\n")
          "  " (plist-get goal :ty) "\n"))

(defun coq-eglot--unfocused-p (goals)
  "Non-nil if GOALS has unfocused goals."
  (seq-some (lambda (level)
              (seq-some (lambda (side) (> (length side) 0)) level))
            (plist-get goals :stack)))

(defun coq-eglot--format-goals-parts (goals &optional no-separator)
  "Format GOALS, as returned by the server, like Coq does.
Return (HYPOTHESES . REST): the number of goals and the hypotheses of
the first one, then its conclusion and the other goals.  Both are empty
if GOALS is nil (outside of proofs).  Without the separator line before
the conclusion if NO-SEPARATOR."
  (if (null goals)
      (cons "" "")
    (let* ((focused (plist-get goals :goals))
           (n (length focused)))
      (cond
       ((> n 0)
        (cons
         (concat (format "%d goal%s\n\n" n (if (= n 1) "" "s"))
                 (coq-eglot--format-hyps (aref focused 0)))
         (concat
          (coq-eglot--format-conclusion (aref focused 0) no-separator)
          (mapconcat #'identity
                     (cl-loop for i from 1 below n
                              collect (format "\ngoal %d is:\n %s\n" (1+ i)
                                              (plist-get (aref focused i) :ty)))
                     ""))))
       ((coq-eglot--unfocused-p goals)
        (cons "" "This subproof is complete, but there are some unfocused goals.\n"))
       ((> (length (plist-get goals :given_up)) 0)
        (cons "" "No more goals, but there are some goals you gave up.\n"))
       ((> (length (plist-get goals :shelf)) 0)
        (cons "" "All the remaining goals are on the shelf.\n"))
       (t (cons "" "No more goals.\n"))))))

(defun coq-eglot--format-goals (goals)
  "Format GOALS, as returned by the server, like Coq does.
Return the empty string if GOALS is nil (outside of proofs)."
  (let ((parts (coq-eglot--format-goals-parts goals)))
    (concat (car parts) (cdr parts))))

(defun coq-eglot--format-messages (messages)
  "Format MESSAGES of a sentence, as returned by the server."
  (mapconcat (lambda (m) (if (stringp m) m (plist-get m :text)))
             messages "\n"))

(defvar coq-eglot--displayed-goals nil
  "Goals of the last answer displayed, to display them again.")

(defun coq-eglot--show-goals (answer)
  "Display the goals of ANSWER of the server.
See `coq-eglot-split-goals'."
  (let ((goals (plist-get answer :goals)))
    (setq coq-eglot--displayed-goals goals)
    (if (not coq-eglot-split-goals)
        (progn
          (coq-eglot--set-buffer-text coq-eglot-goals-buffer-name
                                      #'coq-eglot-goals-mode 0
                                      (coq-eglot--format-goals goals))
          (coq-eglot--set-mode-line coq-eglot-goals-buffer-name t))
      ;; the windows separate the hypotheses from the conclusion
      (let ((parts (coq-eglot--format-goals-parts goals t)))
        (coq-eglot--set-buffer-text coq-eglot-goals-buffer-name
                                    #'coq-eglot-goals-mode 0 (car parts))
        ;; the conclusion comes right below the hypotheses
        (coq-eglot--set-mode-line coq-eglot-goals-buffer-name nil)
        (coq-eglot--set-buffer-text coq-eglot-conclusion-buffer-name
                                    #'coq-eglot-goals-mode 1 (cdr parts))
        (coq-eglot--set-separator coq-eglot-conclusion-buffer-name)))))

(defun coq-eglot--set-separator (name)
  "Draw a line at the top of the windows of buffer NAME.
It stays there when scrolling.  Its color comes from the face
`coq-eglot-goals-separator', on the background of the buffer."
  (with-current-buffer name
    (unless header-line-format
      ;; not the background of the header line of the theme
      (face-remap-add-relative 'header-line 'default)
      ;; truncated to the width of the window
      (setq header-line-format
            (propertize (make-string 512 ?─) 'face 'coq-eglot-goals-separator))
      (when coq-eglot-resize-windows-function
        (funcall coq-eglot-resize-windows-function)))))

(defun coq-eglot--set-mode-line (name visible)
  "Show the mode line of buffer NAME if VISIBLE, hide it otherwise."
  (with-current-buffer name
    (if visible
        (kill-local-variable 'mode-line-format)
      (setq mode-line-format nil))))

(defun coq-eglot-toggle-split-goals ()
  "Toggle the display of the conclusion apart from the hypotheses.
See `coq-eglot-split-goals'."
  (interactive)
  (setq coq-eglot-split-goals (not coq-eglot-split-goals))
  (unless coq-eglot-split-goals
    (let ((buffer (get-buffer coq-eglot-conclusion-buffer-name)))
      (when buffer
        (mapc #'delete-window (get-buffer-window-list buffer nil t))
        (kill-buffer buffer))))
  (coq-eglot--show-goals (list :goals coq-eglot--displayed-goals))
  (message "Coq: conclusion %s" (if coq-eglot-split-goals "apart" "with the hypotheses")))

(defun coq-eglot--show-response (text)
  "Display TEXT in the response buffer."
  (coq-eglot--set-buffer-text coq-eglot-response-buffer-name
                              #'coq-eglot-response-mode 2 text))

(defun coq-eglot--show-answer (answer)
  "Display the goals and the messages of ANSWER of the server."
  (coq-eglot--show-goals answer)
  (coq-eglot--show-response
   (coq-eglot--format-messages (plist-get answer :messages))))

(defun coq-eglot--show-error (text)
  "Display error TEXT in the response buffer."
  ;; not face: font-lock would remove it
  (coq-eglot--show-response (propertize text 'font-lock-face 'error)))

(defun coq-eglot--goals-at-position (&optional ask)
  "Display the goals and messages at the proof position.
Use the answer kept for the last processed sentence if any, ask the
server otherwise, or if ASK is non-nil."
  (coq-eglot--clear-error)
  (if (null coq-eglot--ends)
      (progn (coq-eglot--show-goals nil)
             (coq-eglot--show-response ""))
    (when (or ask (null (cdar coq-eglot--ends)))
      (setcdr (car coq-eglot--ends)
              (coq-eglot-lsp-goals (1- (coq-eglot-position)))))
    (coq-eglot--show-answer (cdar coq-eglot--ends))))

(defun coq-eglot--goals-at-position-async ()
  "Display the goals and messages at the proof position, without waiting.
Use the answer kept for the last processed sentence if any.  Otherwise
ask the server asynchronously, and display the answer when it comes if
the proof position did not move meanwhile.  Used after editions: the
server may still be finishing an interrupted sentence."
  (coq-eglot--clear-error)
  (cond
   ((null coq-eglot--ends)
    (coq-eglot--show-goals nil)
    (coq-eglot--show-response ""))
   ((cdar coq-eglot--ends)
    (coq-eglot--show-answer (cdar coq-eglot--ends)))
   (t
    (let ((last (car coq-eglot--ends)))
      (coq-eglot-lsp-goals-async
       (1- (car last))
       (lambda (answer)
         (when (eq (car coq-eglot--ends) last)
           (setcdr last answer)
           (coq-eglot--show-answer answer)))
       #'ignore)))))

;;; Moving forward

(defun coq-eglot--check-busy ()
  "Signal an error if a check is running."
  (when coq-eglot--running
    (user-error "Coq is busy, use \\[coq-eglot-interrupt] to interrupt")))

(defun coq-eglot--start (target)
  "Mark the part from the proof position to TARGET as being checked."
  (setq coq-eglot--running (list :target (copy-marker target)))
  (coq-eglot--clear-error)
  (coq-eglot--update-overlays))

(defun coq-eglot--send (request-fn pos on-success)
  "Send the request of the running check with REQUEST-FN at POS.
ON-SUCCESS is called with the answer.  The answer is ignored if the
check was interrupted meanwhile: an answer or an error may still come
for a cancelled request."
  (let ((running coq-eglot--running))
    (plist-put running :id
               (funcall request-fn pos
                        (lambda (answer)
                          (when (eq coq-eglot--running running)
                            (funcall on-success answer)))
                        (lambda (err)
                          (when (eq coq-eglot--running running)
                            (coq-eglot--failed-request err)))))))

(defun coq-eglot--stop ()
  "Mark the running check as finished."
  (when coq-eglot--running
    (set-marker (plist-get coq-eglot--running :target) nil)
    (setq coq-eglot--running nil))
  (coq-eglot--update-overlays))

(defun coq-eglot--fail (start end text answer)
  "The sentence between START and END failed with error TEXT.
Move the proof position before it and display the error, with the
goals before the sentence.  ANSWER is the answer of the server for the
sentence before, if known."
  (let ((before (if answer (cons (coq-eglot-position) answer)
                  (coq-eglot--sentence-before start))))
    (coq-eglot--set-position (car before) (cdr before))
    (coq-eglot--goals-at-position)
    (coq-eglot--show-error text)
    (coq-eglot--highlight-error start end)))

(defun coq-eglot--failed-request (err)
  "Handle the failure ERR of a request: stop the running check."
  (coq-eglot--stop)
  (message "Coq request failed: %s" (or (plist-get err :message) err)))

(defun coq-eglot--progress (pos)
  "The server checked the sentences up to POS: move the proof position.
Do not go past the target, nor past an error."
  (when (and coq-eglot--running
             (> pos (coq-eglot-position))
             (<= pos (plist-get coq-eglot--running :target))
             (not (coq-eglot-lsp-error-range (coq-eglot-position) pos)))
    (coq-eglot--set-position pos nil)))

(defun coq-eglot--next-sentence-start ()
  "Return the start of the first sentence after the proof position, or nil."
  (let ((start (coq-eglot--skip-forward (coq-eglot-position))))
    (and (< start (point-max)) start)))

(defun coq-eglot--guess-end (start)
  "Return the end of the sentence at START, as guessed locally.
Only used to display the part being checked."
  (save-excursion
    (goto-char start)
    (if (eq (coq-script-parse-cmdend-forward) 'cmd) (point)
      (line-end-position))))

(defun coq-eglot--next ()
  "Process the sentence after the proof position, asynchronously."
  (let ((start (coq-eglot--next-sentence-start)))
    (when start
      (coq-eglot--start (coq-eglot--guess-end start))
      (coq-eglot--send #'coq-eglot-lsp-goals-async start
                       #'coq-eglot--next-done))))

(defun coq-eglot--next-done (answer)
  "Handle ANSWER of the server for the sentence after the proof position."
  (let* ((range (plist-get answer :range))
         (bounds (and range (coq-eglot-lsp-range range))))
    (coq-eglot--stop)
    (cond
     ((null bounds) nil)
     ((plist-get answer :error)
      (coq-eglot--fail (car bounds) (cdr bounds) (plist-get answer :error)
                       nil))
     (t
      (coq-eglot--set-position (cdr bounds) answer)
      (coq-eglot--show-answer answer)))))

(defun coq-eglot--advance (target)
  "Process the sentences up to the one containing the character before TARGET.
Asynchronously: the server is asked to check up to it, without goals."
  (let ((last (1- (coq-eglot--skip-backward target)))
        (start (coq-eglot--next-sentence-start)))
    ;; nothing to do if no sentence starts before TARGET
    (when (and start (< start target))
      (coq-eglot--start (max target (coq-eglot--guess-end last)))
      (coq-eglot--send #'coq-eglot-lsp-check-async last
                       (lambda (_answer)
                         (coq-eglot--advance-done start last))))))

(defun coq-eglot--advance-done (start last)
  "The server checked from START up to the sentence containing LAST.
Stop at the first error, or ask the goals after the last sentence."
  (coq-eglot--stop)
  (let ((error (coq-eglot-lsp-error-range start (1+ last))))
    (if error
        ;; the sentence that failed and its error message
        (let* ((answer (coq-eglot-lsp-goals (car error)))
               (range (plist-get answer :range))
               (bounds (if range (coq-eglot-lsp-range range) error)))
          (coq-eglot--fail (car bounds) (cdr bounds)
                           (or (plist-get answer :error) "Error.") nil))
      (let* ((answer (coq-eglot-lsp-goals last))
             (range (plist-get answer :range)))
        (when range
          (coq-eglot--set-position (cdr (coq-eglot-lsp-range range)) answer)
          (coq-eglot--show-answer answer))))))

;;; Moving back

(defun coq-eglot--retract (pos)
  "Move the proof position back to the last sentence ending before POS.
A sentence ending exactly at POS stays processed.  Display the goals."
  (coq-eglot--pop-ends pos)
  (let ((before (coq-eglot--sentence-before pos)))
    (coq-eglot--set-position (car before) (cdr before)))
  (coq-eglot--goals-at-position))

;;; Commands

(defun coq-eglot-assert-next-command ()
  "Process the next sentence."
  (interactive)
  (coq-eglot--activate)
  (coq-eglot--check-busy)
  (coq-eglot--next))

(defun coq-eglot-undo-last-command ()
  "Move the proof position back one sentence."
  (interactive)
  (coq-eglot--activate)
  (coq-eglot--check-busy)
  (when coq-eglot--ends
    (let* ((range (plist-get (cdar coq-eglot--ends) :range))
           (start (if range (car (coq-eglot-lsp-range range))
                    (1- (coq-eglot-position)))))
      (coq-eglot--retract start))))

(defun coq-eglot-goto-point ()
  "Move the proof position to the sentence at point.
Process the sentences up to the one containing point, or move back to
the end of the last sentence before point."
  (interactive)
  (coq-eglot--activate)
  (coq-eglot--check-busy)
  (if (< (point) (coq-eglot-position))
      (coq-eglot--retract (point))
    (coq-eglot--advance (point))))

(defun coq-eglot-process-buffer ()
  "Process the whole buffer."
  (interactive)
  (coq-eglot--activate)
  (coq-eglot--check-busy)
  (coq-eglot--advance (point-max)))

(defun coq-eglot-retract-buffer ()
  "Move the proof position to the beginning of the buffer."
  (interactive)
  (coq-eglot--activate)
  (coq-eglot--check-busy)
  (coq-eglot--set-position nil nil)
  (coq-eglot--goals-at-position))

(defun coq-eglot--cancel ()
  "Cancel the running check and all pending requests, display nothing."
  (coq-eglot--stop)
  (coq-eglot-lsp-cancel-all))

(defvar-local coq-eglot--interrupting nil
  "Non-nil while the server did not answer since an interruption.
It may still be finishing a computation that cannot be interrupted.")

(defun coq-eglot--wait-interruption ()
  "Note that an interruption was sent, clear it when the server answers.
Send a cheap request: its answer, coming after the interruption, tells
that the server is ready again."
  (setq coq-eglot--interrupting t)
  (coq-eglot-lsp-ping (lambda (_) (setq coq-eglot--interrupting nil))))

(defun coq-eglot-interrupt ()
  "Interrupt the running check, without waiting.
The proof position stays where the server was.  If the server does not
answer since the last interruption, because it is finishing a
computation that cannot be interrupted, restart it: see
`coq-eglot-restart-server'."
  (interactive)
  (coq-eglot--activate)
  (cond
   (coq-eglot--running
    (coq-eglot--cancel)
    (coq-eglot--wait-interruption)
    (coq-eglot--goals-at-position-async)
    (message "Coq: interrupted (%s again to restart the server if it stays busy)"
             (substitute-command-keys "\\[coq-eglot-interrupt]")))
   (coq-eglot--interrupting (coq-eglot-restart-server))
   (t (message "Coq: nothing to interrupt"))))

(defun coq-eglot-restart-server ()
  "Restart the server, even if it is busy.
The proof position and the kept goals stay: the text did not change.
The new server checks again the processed part when needed."
  (interactive)
  (coq-eglot--activate)
  (coq-eglot--cancel)
  (setq coq-eglot--interrupting nil)
  (coq-eglot-lsp-restart)
  (coq-eglot--goals-at-position-async)
  (message "Coq: server restarted"))

(defun coq-eglot-exit ()
  "Stop the server, like `proof-shell-exit' in Proof General.
The proof position goes back to the beginning in all the buffers the
server managed.  The next command starts a new server."
  (interactive)
  (coq-eglot--activate)
  (coq-eglot--cancel)
  (dolist (buffer (or (coq-eglot-lsp-shutdown) (list (current-buffer))))
    (when (buffer-live-p buffer)
      (with-current-buffer buffer
        (when coq-eglot-mode
          (setq coq-eglot--interrupting nil)
          (coq-eglot--set-position nil nil)
          (coq-eglot--clear-error)))))
  (coq-eglot--show-goals nil)
  (coq-eglot--show-response "")
  (message "Coq: server stopped"))

(defun coq-eglot-show-goals ()
  "Ask the server the goals at the proof position and display them."
  (interactive)
  (coq-eglot--activate)
  (coq-eglot--check-busy)
  (coq-eglot--goals-at-position t))

(defun coq-eglot-goto-end-of-locked ()
  "Move point to the proof position."
  (interactive)
  (goto-char (coq-eglot-position)))

;;; Edition before the proof position

(defvar-local coq-eglot--edited nil
  "Start of the first edition before the proof position, or nil.
The proof position is moved back at the end of the current command.")

(defvar-local coq-eglot--interrupted nil
  "Non-nil if an edition interrupted the running check.
The goals are displayed at the end of the current command.")

(defun coq-eglot--after-change (beg _end _len)
  "Move the proof position before the sentence edited at BEG.
Typing right at the proof position does not move it.  Editing the
processed part, or the part being checked, interrupts the server: all
pending requests are cancelled, and the edition is sent to the server
at the end of the command (not here, see `coq-eglot-lsp-send-changes')."
  (when (< beg (if coq-eglot--running
                   (plist-get coq-eglot--running :target)
                 (coq-eglot-position)))
    (coq-eglot--cancel)
    (setq coq-eglot--interrupted t))
  (when (< beg (coq-eglot-position))
    ;; a sentence ending at BEG is edited too
    (coq-eglot--pop-ends (1- beg))
    (coq-eglot--update-overlays)
    (coq-eglot--clear-error)
    (setq coq-eglot--edited (min beg (or coq-eglot--edited beg)))))

(defun coq-eglot--sentence-before-async (pos on-found)
  "Like `coq-eglot--sentence-before' for POS, but without waiting.
Call ON-FOUND with (END . ANSWER) when found.  Do nothing if there is
no such sentence or a request fails."
  (let* ((end (coq-eglot--skip-backward pos))
         (kept (and (> end (point-min)) (assoc end coq-eglot--ends #'=))))
    (cond
     ((<= end (point-min)) nil)
     ((cdr kept) (funcall on-found (cons end (cdr kept))))
     (t
      (coq-eglot-lsp-goals-async
       (1- end)
       (lambda (answer)
         (let* ((range (plist-get answer :range))
                (bounds (and range (coq-eglot-lsp-range range))))
           (cond
            ((null bounds) nil)
            ((<= (cdr bounds) pos)
             (funcall on-found (cons (cdr bounds) answer)))
            (t (coq-eglot--sentence-before-async (car bounds) on-found)))))
       #'ignore)))))

(defun coq-eglot--post-command ()
  "Display the goals after an edition moved back or interrupted.
Never wait for the server here: it may still be finishing an
interrupted sentence.  The proof position is first the end of the last
known sentence before the edition (see `coq-eglot--after-change').  The
server is then asked asynchronously for the last sentence before the
edition, the proof position moves there if the buffer did not change
meanwhile."
  (when (or coq-eglot--edited coq-eglot--interrupted)
    (coq-eglot--activate)
    (let ((beg coq-eglot--edited)
          (tick (buffer-chars-modified-tick)))
      (setq coq-eglot--edited nil coq-eglot--interrupted nil)
      ;; the server must work on the new text right now
      (coq-eglot-lsp-send-changes)
      (coq-eglot--wait-interruption)
      (coq-eglot--goals-at-position-async)
      (when beg
        (coq-eglot--sentence-before-async
         (1- beg)
         (lambda (found)
           (when (and (= tick (buffer-chars-modified-tick))
                      (not coq-eglot--running)
                      (> (car found) (coq-eglot-position)))
             (coq-eglot--set-position (car found) (cdr found))
             (coq-eglot--show-answer (cdr found)))))))))

;;; Queries

(defvar coq-eglot--query-history nil
  "History of the arguments of queries.")

(defcustom coq-eglot-query-flags
  '(("All" . "Set Printing All")
    ("Implicit" . "Set Printing Implicit")
    ("Coercions" . "Set Printing Coercions")
    ("Parentheses" . "Set Printing Parentheses")
    ("No Notations" . "Unset Printing Notations")
    ("Universes" . "Set Printing Universes"))
  "Printing flags that a query can use, by name.
With \\[universal-argument] \\[universal-argument], query commands ask
which ones to use.  Each value is a Coq command run just before the
query, for this query only."
  :type '(alist :key-type (string :tag "Name")
                :value-type (string :tag "Coq command"))
  :group 'coq-eglot)

(defun coq-eglot--query-flags (arg)
  "Return the flag commands for a query with prefix argument ARG.
None without prefix, Set Printing All with \\[universal-argument],
otherwise ask among `coq-eglot-query-flags'."
  (cond
   ((null arg) nil)
   ((equal arg '(4)) (list "Set Printing All"))
   (t (mapcar (lambda (name) (cdr (assoc name coq-eglot-query-flags)))
              (completing-read-multiple "Printing flags: "
                                        coq-eglot-query-flags nil t)))))

(defun coq-eglot--query-prompt (prompt flags)
  "PROMPT for a query, mentioning FLAGS if any."
  (if flags (format "%s [%s]" prompt (string-join flags ", ")) prompt))

(defun coq-eglot--id-at-point ()
  "Return the qualified identifier at point, or nil."
  (save-excursion
    (skip-chars-backward "[:alnum:]_'.")
    (skip-chars-forward ".")
    (when (looking-at "[[:alpha:]_][[:alnum:]_'.]*")
      (string-trim-right (match-string-no-properties 0) "\\.+"))))

(defun coq-eglot--read-query-argument (prompt)
  "Read the argument of a query with PROMPT.
The default is the region if active, or the identifier at point."
  (let ((guess (if (use-region-p)
                   (buffer-substring-no-properties (region-beginning)
                                                   (region-end))
                 (coq-eglot--id-at-point))))
    (read-string (format-prompt prompt guess) nil
                 'coq-eglot--query-history guess)))

(defun coq-eglot-query (command &optional flags)
  "Run Coq COMMAND at the proof position and display its messages.
COMMAND does not change the document, nor the proof position.  The
final dot may be omitted.  FLAGS are Coq commands run just before,
like \"Set Printing All\", for this query only.  Interactively, they
come from the prefix argument, see `coq-eglot--query-flags'."
  (interactive
   (let ((flags (coq-eglot--query-flags current-prefix-arg)))
     (list (read-string (format-prompt (coq-eglot--query-prompt
                                        "Coq command" flags)
                                       nil)
                        nil 'coq-eglot--query-history)
           flags)))
  (coq-eglot--activate)
  (when (<= (coq-eglot-position) (point-min))
    (user-error "Coq: process at least one sentence before a query"))
  (unless (string-match-p "\\.[ \t\n]*\\'" command)
    (setq command (concat command ".")))
  ;; the server runs all the sentences on a copy of the state
  (setq command (concat (mapconcat (lambda (flag) (concat flag ". ")) flags "")
                        command))
  ;; in the last processed sentence: the state after it
  (coq-eglot-lsp-query-async
   (1- (coq-eglot-position)) command
   (lambda (messages)
     (coq-eglot--show-response (mapconcat #'identity messages "\n"))
     (unless messages (message "Coq: no output")))
   (lambda (err)
     (coq-eglot--show-error (or (plist-get err :message) (format "%S" err))))))

(defmacro coq-eglot--define-query (name command prompt)
  "Define query NAME running Coq COMMAND on an argument read with PROMPT."
  `(defun ,name (arg &optional flags)
     ,(format "Run %s ARG at the proof position.
With \\[universal-argument], with Printing All.  With \\[universal-argument] \
\\[universal-argument], ask
which printing flags to use, see `coq-eglot-query-flags'.  FLAGS are
the commands setting them." command)
     (interactive
      (let ((flags (coq-eglot--query-flags current-prefix-arg)))
        (list (coq-eglot--read-query-argument
               (coq-eglot--query-prompt ,prompt flags))
              flags)))
     (coq-eglot-query (concat ,command " " arg) flags)))

(defun coq-eglot--call-with-prefix (command arg)
  "Call COMMAND interactively with prefix argument ARG, for menus."
  (let ((current-prefix-arg arg))
    (call-interactively command)))

(coq-eglot--define-query coq-eglot-About "About" "About")
(coq-eglot--define-query coq-eglot-Check "Check" "Check")
(coq-eglot--define-query coq-eglot-Search "Search"
                         "Search (ex: \"eq_\" eq -bool)")

;;; Hover

(defun coq-eglot--hover-eldoc-function (callback &rest args)
  "Like `eglot-hover-eldoc-function' with CALLBACK and ARGS.
But only in the processed part: elsewhere the server has nothing to
say, and a pending hover would make it check up to point."
  (when (< (point) (coq-eglot-position))
    (apply #'eglot-hover-eldoc-function callback args)))

(defun coq-eglot--setup-eldoc ()
  "Replace the hover function of Eglot by `coq-eglot--hover-eldoc-function'.
Run when Eglot starts or stops managing the buffer."
  (when (bound-and-true-p eglot--managed-mode)
    (setq-local eldoc-documentation-functions
                (cl-substitute #'coq-eglot--hover-eldoc-function
                               #'eglot-hover-eldoc-function
                               eldoc-documentation-functions))))

;;; Mode

(defvar-keymap coq-eglot-mode-map
  :doc "Keymap of the Eglot backend of Coq, same keys as Proof General."
  "C-c C-n" #'coq-eglot-assert-next-command
  "C-c C-u" #'coq-eglot-undo-last-command
  "C-c RET" #'coq-eglot-goto-point
  "C-c C-<return>" #'coq-eglot-goto-point
  "C-c C-b" #'coq-eglot-process-buffer
  "C-c C-r" #'coq-eglot-retract-buffer
  "C-c C-c" #'coq-eglot-interrupt
  "C-c C-x" #'coq-eglot-exit
  "C-c C-p" #'coq-eglot-show-goals
  "C-c C-." #'coq-eglot-goto-end-of-locked
  "C-c C-a C-a" #'coq-eglot-Search
  "C-c C-a C-b" #'coq-eglot-About
  "C-c C-a C-c" #'coq-eglot-Check
  "C-c C-v" #'coq-eglot-query)

(easy-menu-define coq-eglot-menu coq-eglot-mode-map
  "Menu of the Eglot backend of Coq."
  '("Coq"
    ["Next Step" coq-eglot-assert-next-command]
    ["Undo Step" coq-eglot-undo-last-command]
    ["Goto Point" coq-eglot-goto-point]
    ["Process Buffer" coq-eglot-process-buffer]
    ["Retract Buffer" coq-eglot-retract-buffer]
    ["Goto End of Locked" coq-eglot-goto-end-of-locked]
    "---"
    ["Show Goals" coq-eglot-show-goals]
    ["Conclusion Apart" coq-eglot-toggle-split-goals
     :style toggle :selected coq-eglot-split-goals]
    ("Queries"
     ["About..." coq-eglot-About]
     ["Check..." coq-eglot-Check]
     ["Search..." coq-eglot-Search]
     ["Other Command..." coq-eglot-query]
     "---"
     ["About with Printing All..."
      (coq-eglot--call-with-prefix #'coq-eglot-About '(4))
      :keys "C-u C-c C-a C-b"]
     ["Check with Printing All..."
      (coq-eglot--call-with-prefix #'coq-eglot-Check '(4))
      :keys "C-u C-c C-a C-c"]
     ("With Printing Flags"
      ["About..." (coq-eglot--call-with-prefix #'coq-eglot-About '(16))]
      ["Check..." (coq-eglot--call-with-prefix #'coq-eglot-Check '(16))]
      ["Search..." (coq-eglot--call-with-prefix #'coq-eglot-Search '(16))]
      ["Other Command..."
       (coq-eglot--call-with-prefix #'coq-eglot-query '(16))]))
    "---"
    ["Interrupt" coq-eglot-interrupt]
    ["Restart Server" coq-eglot-restart-server]
    ["Exit Server" coq-eglot-exit]))

(define-minor-mode coq-eglot-mode
  "Interaction with Coq through a language server, like Proof General.

\\{coq-eglot-mode-map}"
  :lighter " Coq-LSP"
  (if coq-eglot-mode
      (progn
        (unless coq-eglot-use-flymake
          (setq-local eglot-stay-out-of (cons 'flymake eglot-stay-out-of)))
        (setq-local eglot-ignored-server-capabilities
                    (append coq-eglot-ignored-capabilities
                            eglot-ignored-server-capabilities))
        (setq coq-eglot-lsp-progress-function #'coq-eglot--progress)
        (add-hook 'eglot-managed-mode-hook #'coq-eglot--setup-eldoc nil t)
        (add-hook 'after-change-functions #'coq-eglot--after-change nil t)
        (add-hook 'post-command-hook #'coq-eglot--post-command nil t)
        (add-hook 'kill-buffer-hook #'coq-eglot--forget-active nil t)
        (coq-eglot--update-overlays))
    (setq coq-eglot-lsp-progress-function nil)
    (remove-hook 'eglot-managed-mode-hook #'coq-eglot--setup-eldoc t)
    (remove-hook 'after-change-functions #'coq-eglot--after-change t)
    (remove-hook 'post-command-hook #'coq-eglot--post-command t)
    (remove-hook 'kill-buffer-hook #'coq-eglot--forget-active t)
    (coq-eglot--forget-active)
    (coq-eglot--cancel)
    (coq-eglot--set-position nil nil)
    (coq-eglot--clear-error)))

(defun coq-eglot-setup ()
  "Set up the current `coq-mode' buffer for the Eglot backend."
  (coq-eglot-mode 1)
  (eglot-ensure))

(provide 'coq-eglot)

;;; coq-eglot.el ends here
