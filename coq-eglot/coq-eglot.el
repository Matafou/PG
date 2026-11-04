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
;; Like in Proof General with `coq-compile-before-require', the
;; libraries required by the part to check are compiled before, see
;; coq-eglot-compile.el.
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
(require 'coq-eglot-compile)
(require 'pg-double-hit)
(require 'coq-goals)                    ; folding, number of goals
(require 'coq-hyps)                     ; folding and highlighting of hypotheses
(require 'pg-goals-indicators)          ; goals out of view

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
      (coq-eglot-compile-check-outdated)
      (coq-eglot--update-overlays)
      (coq-eglot--goals-at-position-async))))

(defun coq-eglot--script-buffer ()
  "Return the script buffer a command of the backend acts on.
The current buffer in a script buffer, the active script buffer in the
goals and response buffers, like in Proof General."
  (cond
   (coq-eglot-mode (current-buffer))
   ((and (derived-mode-p 'coq-eglot-output-mode)
         (buffer-live-p coq-eglot--active-buffer))
    coq-eglot--active-buffer)
   (t (user-error "Coq: no script buffer"))))

(defmacro coq-eglot--with-script (&rest body)
  "Run BODY in the script buffer of the command, made active.
See `coq-eglot--script-buffer'."
  (declare (indent 0) (debug t))
  `(with-current-buffer (coq-eglot--script-buffer)
     (coq-eglot--activate)
     ,@body))

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
  (coq-eglot-compile-show-outdated (coq-eglot-position))
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

(define-derived-mode coq-eglot-output-mode nil "Coq Output"
  "Parent mode of the goals and response buffers of the Eglot backend.
Read-only, with the keys of the script buffer, but not those of
`special-mode': like in Proof General, \"q\" does not close the
window.  Queries run on the active script buffer."
  :syntax-table coq-mode-syntax-table   ; for `coq-id-at-point'
  (setq buffer-read-only t)
  (setq coq-query-function #'coq-eglot-run-query)
  (setq coq-query-result-function #'coq-eglot-query-result))

(define-derived-mode coq-eglot-goals-mode coq-eglot-output-mode "Coq Goals"
  "Major mode for the goals of the Eglot backend of Coq."
  (setq-local font-lock-defaults '(coq-goals-font-lock-keywords))
  ;; like in Proof General, see coq-goals.el and pg-goals-indicators.el
  (proof-goals-indicators-setup)
  (setq coq-goals-count-function #'coq-eglot--goals-count)
  (setq mode-line-process '(:eval (coq-goals-mode-line)))
  ;; the goals are printed at the width of their windows
  (add-hook 'window-size-change-functions
            #'coq-eglot--schedule-width-refresh nil t))

(define-derived-mode coq-eglot-response-mode coq-eglot-output-mode "Coq Response"
  "Major mode for the messages of the Eglot backend of Coq."
  (setq-local font-lock-defaults '(coq-response-font-lock-keywords)))

(defun coq-eglot--output-buffer (name mode)
  "Return buffer NAME, in MODE."
  (let ((buffer (get-buffer-create name)))
    (with-current-buffer buffer
      (unless (eq major-mode mode) (funcall mode)))
    buffer))

(defun coq-eglot--output-window-p (window)
  "Non-nil if WINDOW displays the goals, the conclusion or the messages."
  (member (buffer-name (window-buffer window))
          (list coq-eglot-goals-buffer-name coq-eglot-conclusion-buffer-name
                coq-eglot-response-buffer-name)))

(defun coq-eglot--three-windows-p ()
  "Non-nil if the goals and the messages have windows of their own.
Like in Proof General: if `proof-three-window-enable' is non-nil and the
frame is high enough."
  (and proof-three-window-enable
       (> (frame-height) (* 4 window-min-height))))

(defun coq-eglot--main-window ()
  "The window of the script, next to which the output windows go."
  (or (and coq-eglot--active-buffer
           (get-buffer-window coq-eglot--active-buffer))
      (seq-find (lambda (window) (not (coq-eglot--output-window-p window)))
                (window-list nil 'no-minibuffer))
      (selected-window)))

(defun coq-eglot--show-in (window buffer)
  "Display BUFFER in WINDOW, a window of its own in three windows mode."
  (set-window-buffer window buffer)
  (set-window-dedicated-p window (coq-eglot--three-windows-p))
  window)

(defun coq-eglot--display-three ()
  "Display the goals and the messages in windows of their own.
The windows missing are created like in Proof General, see
`proof-three-window-mode-policy': below the script (vertical), on its
right (hybrid) or in three columns (horizontal).  With the conclusion
apart, its window is below the goals window."
  (let* ((policy (proof-guess-3win-display-policy
                  proof-three-window-mode-policy))
         (columns (eq policy 'horizontal))
         (goals (coq-eglot--output-buffer coq-eglot-goals-buffer-name
                                          #'coq-eglot-goals-mode))
         (conclusion (and coq-eglot-split-goals
                          (coq-eglot--output-buffer
                           coq-eglot-conclusion-buffer-name
                           #'coq-eglot-goals-mode)))
         (response (coq-eglot--output-buffer coq-eglot-response-buffer-name
                                             #'coq-eglot-response-mode))
         (goals-window (get-buffer-window goals))
         (response-window (get-buffer-window response)))
    (unless goals-window
      (setq goals-window
            (coq-eglot--show-in
             (if response-window
                 ;; the goals come before the messages
                 (split-window response-window nil (if columns 'left 'above))
               (let ((main (coq-eglot--main-window)))
                 (pcase policy
                   ('vertical (split-window main nil 'below))
                   ;; a third of the width for each column
                   ('horizontal (split-window main (/ (window-total-width main) 3)
                                              'right))
                   (_ (split-window main nil 'right)))))
             goals)))
    ;; in columns, the messages before the conclusion: full height
    (when (and columns (not response-window))
      (setq response-window
            (coq-eglot--show-in (split-window goals-window nil 'right)
                                response)))
    (when (and conclusion (not (get-buffer-window conclusion)))
      ;; always below the goals, room taken from the neighbours if needed
      (let ((missing (- (* 2 window-min-height)
                        (window-total-height goals-window))))
        (when (> missing 0)
          (window-resize goals-window (window-resizable goals-window missing))))
      (coq-eglot--show-in (split-window goals-window nil 'below) conclusion))
    (unless response-window
      (coq-eglot--show-in
       (split-window (or (and conclusion (get-buffer-window conclusion))
                         goals-window)
                     nil 'below)
       response))))

(defun coq-eglot--display-two (buffer)
  "Display BUFFER in the window of the goals or the messages.
Like in Proof General when `proof-three-window-enable' is nil: they
share one window.  With the conclusion apart, its window is below the
goals window."
  (let ((shared (seq-find (lambda (window)
                            (and (coq-eglot--output-window-p window)
                                 (not (equal (buffer-name (window-buffer window))
                                             coq-eglot-conclusion-buffer-name))))
                          (window-list nil 'no-minibuffer)))
        (goals-window (get-buffer-window coq-eglot-goals-buffer-name)))
    (cond
     ((and (equal (buffer-name buffer) coq-eglot-conclusion-buffer-name)
           goals-window)
      (coq-eglot--show-in (split-window goals-window nil 'below) buffer))
     (shared (coq-eglot--show-in shared buffer))
     (t (coq-eglot--show-in
         (split-window (coq-eglot--main-window) nil
                       (if (eq (proof-guess-3win-display-policy 'smart)
                               'vertical)
                           'below 'right))
         buffer)))))

(defun coq-eglot--display-buffer (name mode)
  "Return buffer NAME in MODE, displayed like in Proof General.
See `proof-three-window-enable' and `proof-three-window-mode-policy'.
If the windows cannot be split, let `display-buffer' choose."
  (let ((buffer (coq-eglot--output-buffer name mode)))
    (unless (get-buffer-window buffer)
      (condition-case nil
          (if (coq-eglot--three-windows-p)
              (coq-eglot--display-three)
            (coq-eglot--display-two buffer))
        (error (display-buffer buffer))))
    buffer))

(defun coq-eglot-layout-windows ()
  "Display the goals and response windows again, like in Proof General.
They come back if closed, with their default sizes, see
`proof-three-window-enable' and `proof-three-window-mode-policy'."
  (interactive)
  (let ((selected (current-buffer)))
    (coq-eglot--with-script
      ;; displayed again from scratch: default sizes
      (dolist (window (window-list nil 'no-minibuffer))
        (when (and (coq-eglot--output-window-p window)
                   (not (frame-root-window-p window)))
          (delete-window window)))
      (coq-eglot--display-buffer coq-eglot-goals-buffer-name
                                 #'coq-eglot-goals-mode)
      (when (coq-eglot--three-windows-p)
        (coq-eglot--display-buffer coq-eglot-response-buffer-name
                                   #'coq-eglot-response-mode))
      (when coq-eglot-split-goals
        (coq-eglot--display-buffer coq-eglot-conclusion-buffer-name
                                   #'coq-eglot-goals-mode))
      (coq-eglot--resize-windows)
      (coq-eglot--scroll-goals))
    (let ((window (get-buffer-window selected)))
      (when window (select-window window)))))

(defun coq-eglot-set-layout-option (option value)
  "Set OPTION to VALUE, like customize does, and lay out the windows again.
For the menu: OPTION is `proof-three-window-enable' or
`proof-three-window-mode-policy', see `coq-eglot-layout-windows'."
  (customize-set-variable option value)
  (coq-eglot-layout-windows))

(defun coq-eglot--set-buffer-text (name mode text)
  "Replace the content of buffer NAME (in MODE) by TEXT, and display it.
Then adjust the heights of the windows, see
`coq-optimise-resp-windows-enable'.  Do nothing if called from a script
buffer that is not active: only the active one displays its state."
  (when (or (not coq-eglot-mode) (coq-eglot--active-p))
    (coq-eglot--set-buffer-text-1 name mode text)))

(defun coq-eglot--set-buffer-text-1 (name mode text)
  "Replace the content of buffer NAME (in MODE) by TEXT, and display it.
When the goals and the messages share a window (see
`proof-three-window-enable'), no messages do not hide the goals."
  (with-current-buffer
      (if (or (coq-eglot--three-windows-p)
              (not (equal name coq-eglot-response-buffer-name))
              (not (string-empty-p text)))
          (coq-eglot--display-buffer name mode)
        (coq-eglot--output-buffer name mode))
    (let ((inhibit-read-only t))
      (erase-buffer)
      (insert text)
      (goto-char (point-min)))
    ;; before resizing: folded, the other goals take one line
    (when (derived-mode-p 'coq-eglot-goals-mode)
      (coq-goals-fold-other-goals)))
  (coq-eglot--resize-windows))

(defun coq-eglot--allocate-heights (total needs minimum)
  "Share TOTAL lines between windows needing NEEDS lines.
NEEDS lists the heights the windows need, by priority.  Each window
gets at least MINIMUM lines, then by priority what it needs if there is
enough left.  The first one gets what remains.  Return the list of
heights in the same order, or nil if TOTAL is too small."
  (let ((rest (- total (* minimum (length needs)))))
    (when (and needs (>= rest 0))
      (let ((heights (mapcar (lambda (need)
                               (let ((extra (min rest (max 0 (- need minimum)))))
                                 (setq rest (- rest extra))
                                 (+ minimum extra)))
                             needs)))
        (setcar heights (+ (car heights) rest))
        heights))))

(defun coq-eglot--window-need (window)
  "Height WINDOW needs to display its whole buffer, mode line included."
  (+ (- (window-total-height window) (window-body-height window))
     (with-current-buffer (window-buffer window)
       (count-screen-lines (point-min) (point-max) nil window))))

(defun coq-eglot--resize-windows ()
  "Adjust the heights of the windows if `coq-optimise-resp-windows-enable'."
  (when coq-optimise-resp-windows-enable
    (coq-eglot-resize-windows-by-priority)))

(defun coq-eglot-resize-windows-by-priority ()
  "Give the windows the height they need, by priority.
The goals, conclusion and response windows displayed one above the
other share their height: each one gets the height it needs, the
conclusion first, then the goals, then the response.  The first one
gets what remains: the conclusion if `coq-eglot-split-goals', the
hypotheses never get more than they need; the goals otherwise.  In
three columns (see `proof-three-window-mode-policy'), only the windows
of the same column.  The script window keeps its height."
  (let* ((names `((goals . ,coq-eglot-goals-buffer-name)
                  (conclusion . ,coq-eglot-conclusion-buffer-name)
                  (response . ,coq-eglot-response-buffer-name)))
         (windows (delq nil (mapcar (lambda (role)
                                      (get-buffer-window
                                       (cdr (assq role names))))
                                    '(conclusion goals response)))))
    (pcase-dolist (`(,_parent . ,column) (seq-group-by #'window-parent windows))
      (when (and (cdr column) (window-combined-p (car column)))
        (coq-eglot--resize-column column)))))

(defun coq-eglot--resize-column (windows)
  "Give WINDOWS, one above the other, the height they need, by priority.
See `coq-eglot-resize-windows-by-priority'."
  (let ((heights (coq-eglot--allocate-heights
                  (apply #'+ (mapcar #'window-total-height windows))
                  (mapcar #'coq-eglot--window-need windows)
                  window-min-height)))
    (when heights
      ;; from top to bottom, the last one takes what remains: only the
      ;; edges between them move
      (let ((sorted (sort (cl-mapcar #'cons windows heights)
                          (lambda (a b) (< (window-top-line (car a))
                                           (window-top-line (car b)))))))
        (dolist (window-height (butlast sorted))
          (ignore-errors
            (adjust-window-trailing-edge
             (car window-height)
             (- (cdr window-height)
                (window-total-height (car window-height))))))))))

;;; Printing width

;; The server prints the goals and the answers of the queries.  The goals
;; requests and the queries run Set Printing Width first: the server runs
;; it on a copy of the state, nothing is checked again.  See
;; `coq-auto-adapt-printing-width'.

(defvar coq-eglot--displayed-goals nil
  "Goals of the last answer displayed, to display them again.")

(defvar coq-eglot--displayed-width nil
  "Printing width of the goals displayed, or nil for Coq's default.
See `coq-eglot--goals-printing-width'.")

(defconst coq-eglot--hyp-indentation 4
  "Indentation of the type of a hypothesis below its names.
The widest indentation of the goals: they are printed this much
narrower than their window.")

(defconst coq-eglot--printing-width-margin 3
  "Columns left free at the end of the lines printed by Coq.
Coq breaks a line before an infix operator but prints the operator on
it: the line may be up to its length wider than the printing width.  3
is enough for the usual operators, like /\\ or <->.")

(defun coq-eglot--windows-width (&rest names)
  "Number of characters of the narrowest window of the buffers NAMES, or nil."
  (let ((widths (mapcan (lambda (name)
                          (let ((buffer (get-buffer name)))
                            (and buffer
                                 (mapcar #'window-max-chars-per-line
                                         (get-buffer-window-list buffer nil t)))))
                        names)))
    (and widths (apply #'min widths))))

(defun coq-eglot--printing-width (window-width indentation)
  "Printing width for text indented by INDENTATION in WINDOW-WIDTH, or nil.
Nil if WINDOW-WIDTH is nil or `coq-auto-adapt-printing-width' is nil.
See `coq-eglot--printing-width-margin'."
  (when (and coq-auto-adapt-printing-width window-width)
    (max 20 (- window-width indentation coq-eglot--printing-width-margin))))

(defvar coq-eglot--asked-width nil
  "Printing width asked by `coq-eglot-ask-printing-width', or nil.
As (WIDTH . GOALS-WINDOWS-WIDTH): it holds while the goals windows keep
this width.")

(defun coq-eglot--goals-windows-width ()
  "Number of characters of the narrowest goals window, or nil."
  (apply #'coq-eglot--windows-width coq-eglot-goals-buffer-name
         (and coq-eglot-split-goals (list coq-eglot-conclusion-buffer-name))))

(defun coq-eglot--asked-width ()
  "Printing width asked by the user, or nil if the windows changed since."
  (and coq-eglot--asked-width
       (eql (cdr coq-eglot--asked-width) (coq-eglot--goals-windows-width))
       (car coq-eglot--asked-width)))

(defun coq-eglot--goals-printing-width ()
  "Printing width of the goals, from the width of their windows, or nil.
Nil if they are not displayed: the windows will be created at their
display, the goals are printed again then.  The width asked by
`coq-eglot-ask-printing-width' instead, if any.  This is
`coq-eglot-lsp-printing-width-function'."
  (or (coq-eglot--asked-width)
      (coq-eglot--printing-width (coq-eglot--goals-windows-width)
                                 coq-eglot--hyp-indentation)))

(setq coq-eglot-lsp-printing-width-function #'coq-eglot--goals-printing-width)

(defun coq-eglot--query-printing-width ()
  "Printing width of the answers of the queries, or nil.
From the width of the response window, or of the goals window if the
response is not displayed.  The width asked by
`coq-eglot-ask-printing-width' instead, if any."
  (or (coq-eglot--asked-width)
      (coq-eglot--printing-width
       (or (coq-eglot--windows-width coq-eglot-response-buffer-name)
           (coq-eglot--windows-width coq-eglot-goals-buffer-name))
       0)))

(defun coq-eglot-ask-printing-width (width)
  "Print the goals and the answers of the queries WIDTH columns wide.
Until the goals windows change width, then the printing width follows
them again if `coq-auto-adapt-printing-width'."
  (interactive
   (list (read-number "Printing width: "
                      (or coq-eglot--displayed-width
                          (coq-eglot--goals-printing-width)
                          78))))
  (setq coq-eglot--asked-width (cons width (coq-eglot--goals-windows-width)))
  (coq-eglot--refresh-width))

(defvar coq-eglot--width-timer nil
  "Timer of `coq-eglot--refresh-width'.")

(defun coq-eglot--schedule-width-refresh (&rest _)
  "Print the goals again soon if the width of their windows changed.
In `window-size-change-functions' of the goals buffers, and after each
display of the goals.  A timer, not to change the buffers during the
redisplay, and to wait for the end of a resizing."
  (when (timerp coq-eglot--width-timer)
    (cancel-timer coq-eglot--width-timer))
  (setq coq-eglot--width-timer
        (run-at-time 0.1 nil #'coq-eglot--refresh-width)))

(defun coq-eglot--refresh-width ()
  "Print the goals again if the width of their windows changed.
Not during a check: the goals of each sentence are asked when it is
checked, at the current width."
  (setq coq-eglot--width-timer nil)
  (let ((script coq-eglot--active-buffer)
        (width (coq-eglot--goals-printing-width)))
    (when (and coq-eglot--displayed-goals
               width (not (eql width coq-eglot--displayed-width))
               (buffer-live-p script))
      (with-current-buffer script
        (let ((last (car coq-eglot--ends)))
          (when (and last (not coq-eglot--running))
            (coq-eglot-lsp-goals-async
             (1- (car last))
             (lambda (answer)
               (when (and (eq (car coq-eglot--ends) last)
                          (coq-eglot--active-p))
                 (setcdr last answer)
                 (coq-eglot--show-goals answer)))
             #'ignore)))))))

(defun coq-eglot--trim-lines (text)
  "TEXT without blanks at the end of its lines.
Coq leaves a space before some line breaks: in a line as wide as the
window, it would wrap."
  (replace-regexp-in-string "[ \t]+$" "" text))

(defun coq-eglot--indent (text indentation)
  "TEXT with INDENTATION, a string, at the beginning of its lines but the first.
Without blanks at the end of its lines, see `coq-eglot--trim-lines'."
  (string-replace "\n" (concat "\n" indentation)
                  (coq-eglot--trim-lines text)))

(defun coq-eglot--fill-names (names width)
  "Join NAMES with commas, in lines of at most WIDTH characters.
The lines after the first one are indented by 2, like Coq does.  Room
is left for the comma or the colon after them."
  (let ((lines nil) (line nil))
    (dolist (name names)
      (let ((candidate (if line (concat line ", " name) name)))
        (if (or (null line) (<= (+ 2 (length candidate)) width))
            (setq line candidate)
          (push (concat line ",") lines)
          (setq line name))))
    (mapconcat #'identity (nreverse (cons line lines)) "\n  ")))

(defun coq-eglot--format-hyp (hyp)
  "Format hypothesis HYP of a goal.
Like Coq does: if it does not fit on one line, its names are on several
lines, and its type goes below them, indented.  The text has the
property `coq-hyp', the list of its names, and the part after the
names the property `coq-hyp-body', to highlight and fold it, see
`coq-hyps-decorate'."
  (let* ((names (append (plist-get hyp :names) nil))
         ;; the lines must fit in the window, or in Coq's default width
         (width (if coq-eglot--displayed-width
                    (+ coq-eglot--displayed-width
                       coq-eglot--hyp-indentation
                       coq-eglot--printing-width-margin)
                  78))
         (names-text (coq-eglot--fill-names names (- width 2)))
         (last-line (car (last (split-string names-text "\n"))))
         (def (and (plist-get hyp :def)
                   (coq-eglot--trim-lines (plist-get hyp :def))))
         (ty (coq-eglot--trim-lines (plist-get hyp :ty)))
         (one-line (concat (if def (concat " := " def) "") " : " ty))
         (body
          ;; the server printed TY alone, without the names
          (if (and (not (string-search "\n" one-line))
                   (<= (+ 2 (length last-line) (length one-line)) width))
              one-line
            (concat (if def
                        (concat " :=\n    " (coq-eglot--indent def "    ")
                                "\n    : " (coq-eglot--indent ty "      "))
                      (concat " :\n    " (coq-eglot--indent ty "    ")))))))
    (propertize
     (concat "  " names-text (propertize body 'coq-hyp-body t))
     'coq-hyp names)))

(defun coq-eglot--format-hyps (goal)
  "Format the hypotheses of GOAL, one per line."
  (mapconcat (lambda (hyp) (concat (coq-eglot--format-hyp hyp) "\n"))
             (plist-get goal :hyps) ""))

(defun coq-eglot--format-conclusion (goal &optional no-separator)
  "Format the conclusion of GOAL, below the separator unless NO-SEPARATOR."
  (concat (if no-separator "" "  ============================\n")
          "  " (coq-eglot--indent (plist-get goal :ty) "  ") "\n"))

(defun coq-eglot--unfocused-p (goals)
  "Non-nil if GOALS has unfocused goals."
  (seq-some (lambda (level)
              (seq-some (lambda (side) (> (length side) 0)) level))
            (plist-get goals :stack)))

(defun coq-eglot--unfocused-count (goals)
  "Number of unfocused goals of GOALS."
  (seq-reduce (lambda (count level)
                (seq-reduce (lambda (count side) (+ count (length side)))
                            level count))
              (plist-get goals :stack) 0))

(defun coq-eglot--unfocused-goals (goals)
  "The unfocused goals of GOALS, the innermost level first."
  (seq-mapcat (lambda (level) (seq-mapcat #'identity level 'list))
              (plist-get goals :stack) 'list))

(defun coq-eglot--goals-count ()
  "Numbers of the goals displayed, as (FOCUSED . UNFOCUSED), or nil.
Nil outside of proofs.  This is `coq-goals-count-function' for the
Eglot backend: the server gives the unfocused goals, whatever Set
Printing Unfocused."
  (when coq-eglot--displayed-goals
    (cons (length (plist-get coq-eglot--displayed-goals :goals))
          (coq-eglot--unfocused-count coq-eglot--displayed-goals))))

(defun coq-eglot--format-goal-list (goals first)
  "Format GOALS, numbered from FIRST, like Coq does for the other goals."
  (let ((i (1- first)))
    (mapconcat (lambda (goal)
                 (setq i (1+ i))
                 (format "\ngoal %d is:\n %s\n" i
                         (coq-eglot--indent (plist-get goal :ty) " ")))
               goals "")))

(defun coq-eglot--format-other-goals (goals)
  "Format the goals of GOALS after the first one.
Like Coq with Set Printing Unfocused: the unfocused goals come after a
line \"*** Unfocused goals:\".  coq-goals.el folds them, see
`coq-fold-other-goals'."
  (let ((others (cdr (append (plist-get goals :goals) nil)))
        (unfocused (coq-eglot--unfocused-goals goals)))
    (concat (coq-eglot--format-goal-list others 2)
            (when unfocused
              (concat "\n*** Unfocused goals:\n"
                      (coq-eglot--format-goal-list unfocused
                                                   (+ 2 (length others))))))))

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
          (coq-eglot--format-other-goals goals))))
       ((coq-eglot--unfocused-p goals)
        (let ((unfocused (coq-eglot--unfocused-goals goals)))
          (cons ""
                (concat "This subproof is complete, but there are some unfocused goals.\n"
                        (format "\n%d goal%s\n" (length unfocused)
                                (if (cdr unfocused) "s" ""))
                        (coq-eglot--format-goal-list unfocused 1)))))
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

(defun coq-eglot--show-goals (answer)
  "Display the goals of ANSWER of the server.
See `coq-eglot-split-goals'."
  (let* ((goals (plist-get answer :goals))
         (new (not (equal goals coq-eglot--displayed-goals))))
    (setq coq-eglot--displayed-goals goals)
    (setq coq-eglot--displayed-width (plist-get answer :printing-width))
    (if (not coq-eglot-split-goals)
        (progn
          (coq-eglot--set-buffer-text coq-eglot-goals-buffer-name
                                      #'coq-eglot-goals-mode
                                      (coq-eglot--format-goals goals))
          (coq-eglot--set-mode-line coq-eglot-goals-buffer-name t))
      ;; the windows separate the hypotheses from the conclusion
      (let ((parts (coq-eglot--format-goals-parts goals t)))
        (coq-eglot--set-buffer-text coq-eglot-goals-buffer-name
                                    #'coq-eglot-goals-mode (car parts))
        ;; the conclusion comes right below the hypotheses
        (coq-eglot--set-mode-line coq-eglot-goals-buffer-name nil)
        (coq-eglot--set-buffer-text coq-eglot-conclusion-buffer-name
                                    #'coq-eglot-goals-mode (cdr parts))
        (coq-eglot--set-separator coq-eglot-conclusion-buffer-name)))
    (coq-hyps-decorate new)
    (coq-eglot--scroll-goals)
    ;; the windows may have been created or resized meanwhile
    (coq-eglot--schedule-width-refresh)))

(defun coq-eglot--goals-buffer ()
  "The goals buffer holding the goals after the first one, or nil.
The conclusion buffer if `coq-eglot-split-goals'.  This is
`coq-goals-buffer-function' for the Eglot backend."
  (get-buffer (if coq-eglot-split-goals coq-eglot-conclusion-buffer-name
                coq-eglot-goals-buffer-name)))

(setq coq-goals-buffer-function #'coq-eglot--goals-buffer)
(setq coq-response-buffer-function
      (lambda () (get-buffer coq-eglot-response-buffer-name)))

(defun coq-eglot--hyps-window-start (window)
  "Start of WINDOW showing the last hypotheses at its bottom.
For the goals buffer when the conclusion is apart."
  (with-current-buffer (window-buffer window)
    (save-excursion
      (goto-char (point-max))
      (skip-chars-backward " \t\n")
      (vertical-motion (- 1 (window-body-height window)) window)
      (point))))

(defun coq-eglot--scroll-goals ()
  "Show the first goal in the goals windows.
Like in Proof General, see `coq-goals-show-first-goal'.  With the
conclusion apart, the goals window shows the last hypotheses, the
conclusion window starts at the top."
  (let ((goals (get-buffer coq-eglot-goals-buffer-name))
        (conclusion (get-buffer coq-eglot-conclusion-buffer-name)))
    (when goals
      (if (not coq-eglot-split-goals)
          (coq-goals-show-first-goal goals)
        (dolist (window (get-buffer-window-list goals nil t))
          ;; forced: the redisplay moves point into the window
          (set-window-start window (coq-eglot--hyps-window-start window)))))
    (when (and conclusion coq-eglot-split-goals)
      (dolist (window (get-buffer-window-list conclusion nil t))
        (set-window-start window 1)))))

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
      (coq-eglot--resize-windows))))

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
  (coq-eglot--show-goals (list :goals coq-eglot--displayed-goals
                               :printing-width coq-eglot--displayed-width))
  (message "Coq: conclusion %s" (if coq-eglot-split-goals "apart" "with the hypotheses")))

(defun coq-eglot--show-response (text)
  "Display TEXT in the response buffer."
  (coq-eglot--set-buffer-text coq-eglot-response-buffer-name
                              #'coq-eglot-response-mode text))

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
  "Mark the running check as finished.
Return the position the user asked to go to meanwhile, if any, see
`coq-eglot--queue'."
  (let ((then nil))
    (when coq-eglot--running
      (set-marker (plist-get coq-eglot--running :target) nil)
      (let ((marker (plist-get coq-eglot--running :then)))
        (when marker
          (setq then (marker-position marker))
          (set-marker marker nil)))
      (setq coq-eglot--running nil))
    (coq-eglot--update-overlays)
    then))

(defun coq-eglot--queue (target)
  "Extend the running check up to the sentence before TARGET.
Like the queue of Proof General: the part being checked grows at once,
the check of the rest starts when the running one is finished, unless
it fails.  The running request is not replaced: cancelling it could
interrupt Coq.  Signal an error if TARGET is not after the part being
checked: moving back while checking is not possible."
  (let ((end (plist-get coq-eglot--running :target)))
    (when (<= target end)
      (coq-eglot--check-busy))
    (set-marker end (max target
                         (coq-eglot--guess-end
                          (1- (coq-eglot--skip-backward target)))))
    (let ((then (plist-get coq-eglot--running :then)))
      (if then
          (set-marker then target)
        (plist-put coq-eglot--running :then (copy-marker target))))
    (coq-eglot--update-overlays)))

(defun coq-eglot--continue (then)
  "Process up to THEN, the position asked during the last check, if any."
  (when then
    (coq-eglot--advance then)))

(defun coq-eglot--fail (start end text answer)
  "The sentence between START and END failed with error TEXT.
Move the proof position before it and display the error, with the
goals before the sentence.  ANSWER is the answer of the server for the
sentence before, if known."
  (coq-eglot--trace-error start end text)
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

(defun coq-eglot--compile-then (start end continue)
  "Compile the libraries required between START and END, then CONTINUE.
CONTINUE is called with nil, or with the start of the first Require
sentence whose compilation failed.  It is called right away if there
is nothing to compile, never if the running check is cancelled
meanwhile.  See `coq-eglot-compile-requires'."
  (let ((running coq-eglot--running))
    (unless (coq-eglot-compile-requires
             start end
             (lambda (failed)
               (when (eq coq-eglot--running running)
                 (funcall continue failed))))
      (funcall continue nil))))

(defun coq-eglot--compilation-failed (start)
  "Report that the compilation for the Require sentence at START failed."
  (coq-eglot--show-error
   (format "Compilation of the required libraries failed, see buffer %s."
           coq--compile-response-buffer))
  (coq-eglot--highlight-error start (coq-eglot--guess-end start)))

(defun coq-eglot--next ()
  "Process the sentence after the proof position, asynchronously.
Compile first the libraries it requires, if any."
  (let ((start (coq-eglot--next-sentence-start)))
    (when start
      (coq-eglot--start (coq-eglot--guess-end start))
      (coq-eglot--compile-then
       start (1+ start)
       (lambda (failed)
         (if (not failed)
             ;; inside the sentence: at the start of the buffer, the
             ;; server finds no sentence
             (coq-eglot--send #'coq-eglot-lsp-goals-async (1+ start)
                              #'coq-eglot--next-done)
           (coq-eglot--stop)
           (coq-eglot--compilation-failed failed)))))))

(defun coq-eglot--next-done (answer)
  "Handle ANSWER of the server for the sentence after the proof position."
  (let* ((range (plist-get answer :range))
         (bounds (and range (coq-eglot-lsp-range range)))
         (then (coq-eglot--stop)))
    (cond
     ((null bounds) nil)
     ((plist-get answer :error)
      (coq-eglot--fail (car bounds) (cdr bounds) (plist-get answer :error)
                       nil))
     (t
      (coq-eglot--trace-check (car bounds) (cdr bounds) answer)
      (coq-eglot--set-position (cdr bounds) answer)
      (coq-eglot--show-answer answer)
      (coq-eglot--continue then)))))

(defun coq-eglot--advance (target)
  "Process the sentences up to the one containing the character before TARGET.
Asynchronously: the libraries required there are compiled, then the
server is asked to check up to it, without goals.  If a compilation
fails, the server checks up to the Require sentence."
  (let ((last (1- (coq-eglot--skip-backward target)))
        (start (coq-eglot--next-sentence-start)))
    ;; nothing to do if no sentence starts before TARGET
    (when (and start (< start target))
      (coq-eglot--start (max target (coq-eglot--guess-end last)))
      (coq-eglot--compile-then
       start target
       (lambda (failed)
         (coq-eglot--check start
                           (if failed (1- (coq-eglot--skip-backward failed))
                             last)
                           failed))))))

(defun coq-eglot--check (start last failed)
  "Ask the server to check from START up to the sentence containing LAST.
FAILED is the start of a Require sentence after LAST whose compilation
failed, or nil.  It is reported after the check."
  (if (< last start)
      (progn
        (coq-eglot--stop)
        (coq-eglot--compilation-failed failed))
    (coq-eglot--send #'coq-eglot-lsp-check-async last
                     (lambda (_answer)
                       (coq-eglot--advance-done start last failed)))))

(defun coq-eglot--advance-done (start last &optional failed)
  "The server checked from START up to the sentence containing LAST.
Stop at the first error, or ask the goals after the last sentence.
FAILED is the start of a Require sentence after LAST whose compilation
failed, reported if there was no error before."
  (let ((then (coq-eglot--stop))
        (error (coq-eglot-lsp-error-range start (1+ last))))
    (if error
        ;; the sentence that failed and its error message
        (let* ((answer (coq-eglot-lsp-goals (car error)))
               (range (plist-get answer :range))
               (bounds (if range (coq-eglot-lsp-range range) error)))
          (when (< start (car bounds))
            (coq-eglot--trace-check start (car bounds) nil))
          (coq-eglot--fail (car bounds) (cdr bounds)
                           (or (plist-get answer :error) "Error.") nil))
      (let* ((answer (coq-eglot-lsp-goals last))
             (range (plist-get answer :range)))
        (when range
          (coq-eglot--trace-check start (cdr (coq-eglot-lsp-range range))
                                  answer)
          (coq-eglot--set-position (cdr (coq-eglot-lsp-range range)) answer)
          (coq-eglot--show-answer answer))
        (if failed
            (coq-eglot--compilation-failed failed)
          (coq-eglot--continue then))))))

;;; Trace

;; A transcript of what is sent to the server and what it answers, like
;; a coqtop session: the sentences checked, then their messages and the
;; number of goals, in comments.  The server checks several sentences in
;; one request: their messages are not traced, only those of the last
;; one.

(defcustom coq-eglot-trace nil
  "If non-nil, write a transcript of the session in buffer *coq-trace*.
The sentences checked and the queries, followed by their messages and
the number of goals, in comments: the transcript is a Coq file, see
`coq-eglot-show-trace'."
  :type 'boolean
  :group 'coq-eglot)

(defcustom coq-eglot-trace-max-size 200000
  "Maximal number of characters of the trace, the oldest are removed.
See `coq-eglot-trace'."
  :type 'integer
  :group 'coq-eglot)

(defvar coq-eglot-trace-buffer-name "*coq-trace*")

(defvar coq-eglot--trace-file nil
  "Script buffer of the last entry of the trace.")

(define-derived-mode coq-eglot-trace-mode coq-eglot-output-mode "Coq Trace"
  "Major mode of the trace of the Eglot backend of Coq.
See `coq-eglot-trace'."
  (setq-local font-lock-defaults '(coq-font-lock-keywords-1)))

(defun coq-eglot--trace-comment (text)
  "TEXT as a Coq comment, or the empty string if TEXT is empty."
  (let ((text (string-trim (or text ""))))
    (if (string-empty-p text) ""
      ;; no end of comment inside
      (concat "(* " (string-replace "*)" "* )" text) " *)\n"))))

(defun coq-eglot--trace (text)
  "Append TEXT to the trace, if `coq-eglot-trace'.
Called from the script buffer."
  (when coq-eglot-trace
    (let ((script (current-buffer)))
      (with-current-buffer (coq-eglot--output-buffer coq-eglot-trace-buffer-name
                                                     #'coq-eglot-trace-mode)
        (let ((inhibit-read-only t)
              (windows (seq-filter (lambda (w) (= (window-point w) (point-max)))
                                   (get-buffer-window-list nil nil t))))
          (save-excursion
            (goto-char (point-max))
            (unless (eq coq-eglot--trace-file script)
              (setq coq-eglot--trace-file script)
              (insert (coq-eglot--trace-comment
                       (format "File %s" (buffer-name script)))))
            (insert text)
            (when (> (buffer-size) coq-eglot-trace-max-size)
              (goto-char (- (point-max) coq-eglot-trace-max-size))
              (forward-line 1)
              (delete-region (point-min) (point))))
          ;; the windows showing the end follow it
          (dolist (window windows)
            (set-window-point window (point-max))))))))

(defun coq-eglot--trace-goals (answer)
  "The number of goals of ANSWER of the server, as a comment."
  (let ((goals (plist-get answer :goals)))
    (if (null goals) ""
      (let ((n (length (plist-get goals :goals)))
            (unfocused (coq-eglot--unfocused-count goals)))
        (coq-eglot--trace-comment
         (concat (if (= n 0) "No more goals" (format "%d goal%s" n (if (= n 1) "" "s")))
                 (if (> unfocused 0) (format ", %d unfocused" unfocused) "")))))))

(defun coq-eglot--trace-check (start end answer)
  "Trace the sentences from START to END, ANSWER for the last one.
ANSWER may be nil."
  (when coq-eglot-trace
    (coq-eglot--trace
     (concat (string-trim (buffer-substring-no-properties start end)) "\n"
             (and answer
                  (concat (coq-eglot--trace-comment
                           (coq-eglot--format-messages
                            (plist-get answer :messages)))
                          (coq-eglot--trace-goals answer)))))))

(defun coq-eglot--trace-error (start end text)
  "Trace the sentence from START to END, that failed with error TEXT."
  (when coq-eglot-trace
    (coq-eglot--trace
     (concat (coq-eglot--trace-comment
              (concat "Failed: " (buffer-substring-no-properties start end)))
             (coq-eglot--trace-comment text)))))

(defun coq-eglot--trace-retract (pos)
  "Trace a move of the proof position back to POS."
  (when coq-eglot-trace
    (coq-eglot--trace
     (coq-eglot--trace-comment
      (format "Back to line %d" (line-number-at-pos pos))))))

(defun coq-eglot--trace-query (command flags messages)
  "Trace the query COMMAND run after FLAGS, and its MESSAGES."
  (when coq-eglot-trace
    (coq-eglot--trace
     (concat (coq-eglot--trace-comment
              (and flags (concat "Query, with " (string-join flags ", "))))
             command "\n"
             (coq-eglot--trace-comment (string-join messages "\n"))))))

(defun coq-eglot-show-trace ()
  "Display the trace of the session, see `coq-eglot-trace'."
  (interactive)
  (unless coq-eglot-trace
    (message "Coq: the trace is off, see `coq-eglot-trace'"))
  (display-buffer (coq-eglot--output-buffer coq-eglot-trace-buffer-name
                                            #'coq-eglot-trace-mode)))

(defun coq-eglot-toggle-trace ()
  "Turn the trace on or off, see `coq-eglot-trace'."
  (interactive)
  (setq coq-eglot-trace (not coq-eglot-trace))
  (message "Coq: trace %s" (if coq-eglot-trace "on" "off")))

;;; Moving back

(defun coq-eglot--retract (pos)
  "Move the proof position back to the last sentence ending before POS.
A sentence ending exactly at POS stays processed.  Display the goals."
  (coq-eglot--pop-ends pos)
  (coq-eglot--trace-retract pos)
  (let ((before (coq-eglot--sentence-before pos)))
    (coq-eglot--set-position (car before) (cdr before)))
  (coq-eglot--goals-at-position))

;;; Commands

(defun coq-eglot-assert-next-command ()
  "Process the next sentence.
During a check, the sentence after the part being checked, see
`coq-eglot--queue'."
  (interactive)
  (coq-eglot--with-script
    (if (not coq-eglot--running)
        (coq-eglot--next)
      ;; the sentence after the part being checked
      (let ((start (coq-eglot--skip-forward
                    (plist-get coq-eglot--running :target))))
        (when (< start (point-max))
          (coq-eglot--queue (coq-eglot--guess-end start)))))))

(defun coq-eglot-undo-last-command ()
  "Move the proof position back one sentence."
  (interactive)
  (coq-eglot--with-script
    (coq-eglot--check-busy)
    (when coq-eglot--ends
      (let* ((range (plist-get (cdar coq-eglot--ends) :range))
             (start (if range (car (coq-eglot-lsp-range range))
                      (1- (coq-eglot-position)))))
        (coq-eglot--retract start)))))

(defun coq-eglot-goto-point ()
  "Move the proof position to the sentence at point.
Process the sentences up to the one containing point, or move back to
the end of the last sentence before point.  During a check, only
forward, after the part being checked, see `coq-eglot--queue'."
  (interactive)
  (coq-eglot--with-script
    (cond
     (coq-eglot--running (coq-eglot--queue (point)))
     ((< (point) (coq-eglot-position)) (coq-eglot--retract (point)))
     (t (coq-eglot--advance (point))))))

(defun coq-eglot-process-buffer ()
  "Process the whole buffer, also during a check, see `coq-eglot--queue'."
  (interactive)
  (coq-eglot--with-script
    (if coq-eglot--running
        (coq-eglot--queue (point-max))
      (coq-eglot--advance (point-max)))))

(defun coq-eglot-retract-buffer ()
  "Move the proof position to the beginning of the buffer."
  (interactive)
  (coq-eglot--with-script
    (coq-eglot--check-busy)
    (coq-eglot--set-position nil nil)
    (coq-eglot--goals-at-position)))

(defun coq-eglot--cancel ()
  "Cancel the running check and all pending requests, display nothing.
Kill the compilation of the required libraries, if running."
  (coq-eglot-compile-cancel)
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
  (coq-eglot--with-script
    (cond
     (coq-eglot--running
      (coq-eglot--cancel)
      (coq-eglot--wait-interruption)
      (coq-eglot--goals-at-position-async)
      (message "Coq: interrupted (%s again to restart the server if it stays busy)"
               (substitute-command-keys "\\[coq-eglot-interrupt]")))
     (coq-eglot--interrupting (coq-eglot-restart-server))
     (t (message "Coq: nothing to interrupt")))))

(defun coq-eglot-restart-server ()
  "Restart the server, even if it is busy.
The proof position and the kept goals stay: the text did not change.
The new server checks again the processed part when needed."
  (interactive)
  (coq-eglot--with-script
    (coq-eglot--cancel)
    (setq coq-eglot--interrupting nil)
    (coq-eglot-lsp-restart)
    (coq-eglot--goals-at-position-async)
    (message "Coq: server restarted")))

(defun coq-eglot-exit ()
  "Stop the server, like `proof-shell-exit' in Proof General.
The proof position goes back to the beginning in all the buffers the
server managed.  The next command starts a new server."
  (interactive)
  (coq-eglot--with-script
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
    (message "Coq: server stopped")))

(defun coq-eglot-show-goals ()
  "Ask the server the goals at the proof position and display them."
  (interactive)
  (coq-eglot--with-script
    (coq-eglot--check-busy)
    (coq-eglot--goals-at-position t)))

(defun coq-eglot-goto-end-of-locked ()
  "Move point to the proof position.
In the goals and response buffers, go to the script buffer first."
  (interactive)
  (let ((buffer (coq-eglot--script-buffer)))
    (unless (eq buffer (current-buffer))
      (pop-to-buffer buffer))
    (goto-char (coq-eglot-position))))

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

;; The query commands are common to all backends, see coq-queries.el.

(defvar coq-eglot--query-history nil
  "History of the queries of `coq-eglot-query'.")

(defun coq-eglot-run-query (command &optional flags then)
  "Run Coq COMMAND at the proof position and display its messages.
COMMAND does not change the document, nor the proof position.  The
final dot may be omitted.  FLAGS are Coq commands run just before,
like \"Set Printing All\", for this query only.  THEN is nil or a
function called without argument once the messages are displayed.
This is `coq-query-function' for the Eglot backend."
  (coq-eglot--with-script
    (coq-eglot--query
     command flags
     (lambda (_messages)
       (when then (funcall then))))))

(defun coq-eglot-query-result (command)
  "Run Coq COMMAND at the proof position and return its answer.
Wait for it, display nothing.  Return nil if Coq answers an error, or
outside of the processed part.  This is `coq-query-result-function'
for the Eglot backend, used by the insertions built from a query, like
`coq-insert-intros'."
  (coq-eglot--with-script
    (when (> (coq-eglot-position) (point-min))
      (condition-case nil
          (string-join (coq-eglot-lsp-query
                        (1- (coq-eglot-position))
                        (if (string-match-p "\\.[ \t\n]*\\'" command)
                            command
                          (concat command ".")))
                       "\n")
        (jsonrpc-error nil)))))

(defun coq-eglot-query (command &optional flags)
  "Run Coq COMMAND at the proof position, read in the minibuffer.
With \\[universal-argument], with Printing All.  FLAGS are the commands
setting printing flags, see `coq-eglot-run-query'."
  (interactive
   (let ((flags (and current-prefix-arg '("Set Printing All"))))
     (list (read-string (format-prompt (if flags "Coq command [Printing All]"
                                         "Coq command")
                                       nil)
                        nil 'coq-eglot--query-history)
           flags)))
  (coq-eglot-run-query command flags))

(defun coq-eglot--query (command flags then)
  "Run Coq COMMAND after FLAGS, then THEN, see `coq-eglot-run-query'.
THEN is called with the messages."
  (when (<= (coq-eglot-position) (point-min))
    (user-error "Coq: process at least one sentence before a query"))
  (unless (string-match-p "\\.[ \t\n]*\\'" command)
    (setq command (concat command ".")))
  (let ((script (current-buffer))
        ;; the server runs all the sentences on a copy of the state
        (sentences (concat (let ((width (coq-eglot--query-printing-width)))
                             (if width (format "Set Printing Width %d. " width) ""))
                           (mapconcat (lambda (flag) (concat flag ". ")) flags "")
                           command)))
    ;; in the last processed sentence: the state after it
    (coq-eglot-lsp-query-async
     (1- (coq-eglot-position)) sentences
     (lambda (messages)
       (with-current-buffer script
         (coq-eglot--trace-query command flags messages))
       (coq-eglot--show-response
        (coq-eglot--trim-lines (mapconcat #'identity messages "\n")))
       (unless messages (message "Coq: no output"))
       (when then (funcall then messages)))
     (lambda (err)
       (coq-eglot--show-error (or (plist-get err :message) (format "%S" err)))))))

;;; Double hit

(defun coq-eglot-terminator-insert (&optional count)
  "Insert the key typed, COUNT times, or process up to it on a double hit.
On a double hit, \".\" replaces the key.  See `proof-double-hit-enable'.
This is `coq-terminator-insert-function' for the Eglot backend, the key
is bound to `coq-terminator-insert'."
  (proof-double-hit-insert #'coq-eglot-goto-point count "."))

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
  "C-c C-l" #'coq-eglot-layout-windows
  "C-c C-." #'coq-eglot-goto-end-of-locked
  "C-c C-v" #'coq-eglot-query
  "C-c C-a C-w" #'coq-eglot-ask-printing-width)

;; like in Proof General, in the goals buffer only
(coq-hyps-define-keys coq-eglot-goals-mode-map)

(defvar coq-eglot--menu-spec
  `("Coq"
    ["Next Step" coq-eglot-assert-next-command]
    ["Undo Step" coq-eglot-undo-last-command]
    ["Goto Point" coq-eglot-goto-point]
    ["Process Buffer" coq-eglot-process-buffer]
    ["Retract Buffer" coq-eglot-retract-buffer]
    ["Goto End of Locked" coq-eglot-goto-end-of-locked]
    "---"
    ["Show Goals" coq-eglot-show-goals]
    ["Show Trace" coq-eglot-show-trace]
    ["Set Printing Width..." coq-eglot-ask-printing-width]
    ("Windows"
     ["Layout Windows" coq-eglot-layout-windows]
     ["Three Windows"
      (coq-eglot-set-layout-option 'proof-three-window-enable
                                   (not proof-three-window-enable))
      :style toggle :selected proof-three-window-enable
      :help "Goals and messages in windows of their own"]
     ["Conclusion Apart" coq-eglot-toggle-split-goals
      :style toggle :selected coq-eglot-split-goals
      :help "The conclusion in a window of its own, below the hypotheses"]
     ("3 Windows mode layout"
      ["smart"
       (coq-eglot-set-layout-option 'proof-three-window-mode-policy 'smart)
       :style radio :selected (eq proof-three-window-mode-policy 'smart)
       :active proof-three-window-enable
       :help "Adapt to frame width (C-c C-l to refresh)"]
      ["hybrid"
       (coq-eglot-set-layout-option 'proof-three-window-mode-policy 'hybrid)
       :style radio :selected (eq proof-three-window-mode-policy 'hybrid)
       :active proof-three-window-enable
       :help "Two column mode"]
      ["horizontal"
       (coq-eglot-set-layout-option 'proof-three-window-mode-policy
                                    'horizontal)
       :style radio :selected (eq proof-three-window-mode-policy 'horizontal)
       :active proof-three-window-enable
       :help "Three column mode"]
      ["vertical"
       (coq-eglot-set-layout-option 'proof-three-window-mode-policy 'vertical)
       :style radio :selected (eq proof-three-window-mode-policy 'vertical)
       :active proof-three-window-enable
       :help "One column mode"]))
    ["Fold Other Goals" coq-toggle-other-goals
     :style toggle :selected coq-fold-other-goals]
    ["Compile Before Require" coq-compile-before-require-toggle
     :style toggle :selected coq-compile-before-require]
    ["Double Hit Electric Terminator" proof-double-hit-toggle
     :style toggle :selected proof-double-hit-enable]
    ["Trace" coq-eglot-toggle-trace
     :style toggle :selected coq-eglot-trace
     :help "Transcript of the session in buffer *coq-trace*"]
    ,coq-hyps-menu
    ("Queries"
     ["About..." coq-About]
     ["Check..." coq-Check]
     ["Print..." coq-Print]
     ["Search..." coq-Search]
     ["SearchPattern..." coq-SearchIsos]
     ["Locate..." coq-LocateConstant]
     ["Locate Notation..." coq-LocateNotation]
     ["Print Hint" coq-PrintHint]
     ["Query..." coq-query]
     ["Other Command..." coq-eglot-query]
     "---"
     ["About with Printing All..." coq-About-with-all]
     ["Check with Printing All..." coq-Check-show-all]
     ["Print with Printing All..." coq-Print-with-all])
    ,(append coq-insert-menu
             '(["Named Goal Selectors" coq-insert-named-goal-selectors]))
    "---"
    ["Interrupt" coq-eglot-interrupt]
    ["Restart Server" coq-eglot-restart-server]
    ["Exit Server" coq-eglot-exit])
  "Menu of the Eglot backend of Coq, see `easy-menu-define'.")

(easy-menu-define coq-eglot-menu coq-eglot-mode-map
  "Menu of the Eglot backend of Coq."
  coq-eglot--menu-spec)

;; the same keys in the goals and response buffers, like Proof General
(set-keymap-parent coq-eglot-output-mode-map
                   (make-composed-keymap coq-eglot-mode-map coq-mode-map))

;; The queries at mouse click, see `coq-remap-mouse-1'.
(coq-mouse-query-add-keymap coq-eglot-output-mode-map)

(defun coq-eglot--lighter ()
  "Mode line indicator of `coq-eglot-mode'.
Warn if processed Require sentences load outdated libraries."
  (if coq-eglot-compile--outdated-p
      (propertize " Coq-LSP!" 'face 'warning
                  'help-echo "Some required libraries changed since loaded")
    " Coq-LSP"))

(define-minor-mode coq-eglot-mode
  "Interaction with Coq through a language server, like Proof General.

\\{coq-eglot-mode-map}"
  :lighter (:eval (coq-eglot--lighter))
  (if coq-eglot-mode
      (progn
        (unless coq-eglot-use-flymake
          (setq-local eglot-stay-out-of (cons 'flymake eglot-stay-out-of)))
        (setq-local eglot-ignored-server-capabilities
                    (append coq-eglot-ignored-capabilities
                            eglot-ignored-server-capabilities))
        (setq coq-eglot-lsp-progress-function #'coq-eglot--progress)
        (setq coq-terminator-insert-function #'coq-eglot-terminator-insert)
        (setq coq-query-function #'coq-eglot-run-query)
        (setq coq-query-result-function #'coq-eglot-query-result)
        (add-hook 'project-find-functions #'coq-eglot-lsp-project nil t)
        (add-hook 'eglot-managed-mode-hook #'coq-eglot--setup-eldoc nil t)
        (add-hook 'after-change-functions #'coq-eglot--after-change nil t)
        (add-hook 'post-command-hook #'coq-eglot--post-command nil t)
        (add-hook 'kill-buffer-hook #'coq-eglot--forget-active nil t)
        (coq-eglot--update-overlays))
    (setq coq-eglot-lsp-progress-function nil)
    (kill-local-variable 'coq-terminator-insert-function)
    (kill-local-variable 'coq-query-function)
    (kill-local-variable 'coq-query-result-function)
    (remove-hook 'project-find-functions #'coq-eglot-lsp-project t)
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
