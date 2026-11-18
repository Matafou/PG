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
(require 'button)
(require 'cl-lib)
(require 'coq-eglot-lsp)
(require 'coq-eglot-session)
(require 'coq-eglot-compile)
(require 'pg-terminator)                ; the double hit
(require 'coq-goals)                    ; folding, number of goals, hypotheses
(require 'coq-eglot-goals)              ; the other goals, detailed
(require 'coq-eglot-ui)                 ; faces, mode line, menu
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

(defcustom coq-eglot-split-goals nil
  "If non-nil, display the conclusion apart from the hypotheses.
The hypotheses of the first goal stay in the goals buffer, its
conclusion and the other goals go to the conclusion buffer, in a
window of its own: both scroll independently.  See also
`coq-eglot-toggle-split-goals'."
  :type 'boolean
  :group 'coq-eglot)

;;; Proof position

(defvar-local coq-eglot--locked-overlay nil
  "Overlay displaying the processed part of the script.")

(defvar-local coq-eglot--queue-overlay nil
  "Overlay displaying the part of the script being checked.")

(defun coq-eglot-position ()
  "Return the proof position of the current buffer.
See `coq-eglot-session-position'."
  (coq-eglot-session-position))

(cl-defstruct (coq-eglot--output
               (:constructor coq-eglot--make-output (&optional suffix))
               (:copier nil))
  "Where script buffers display their goals and messages, and its state.
The goals, conclusion and response buffers, named after
`coq-eglot-goals-buffer-name', `coq-eglot-conclusion-buffer-name' and
`coq-eglot-response-buffer-name' followed by SUFFIX, and what they
display.  Only the active script buffer of an output displays there,
see `coq-eglot--active-p'.  All script buffers share the default
output, `coq-eglot--default-output'."
  (suffix "" :documentation "Suffix of the names of the buffers.")
  (active nil :documentation "The script buffer whose goals and messages
are displayed.  It is the last one where a command of the backend ran,
or where the processed part was edited.  The processed part of the
other script buffers of the output is grayed: they go on checking, but
display nothing.  Any command in one of them makes it active again.")
  (goals nil :documentation "Goals of the last answer displayed, to
display them again.")
  (width nil :documentation "Printing width of the goals displayed, or
nil for Coq's default.  See `coq-eglot--goals-printing-width'.")
  (flags nil :documentation "Printing flags of the goals displayed, see
`coq-eglot--printing-flags'.")
  (asked-width nil :documentation "Printing width asked by
`coq-eglot-ask-printing-width', or nil.  As (WIDTH .
GOALS-WINDOWS-WIDTH): it holds while the goals windows keep this
width.")
  (width-timer nil :documentation "Timer of `coq-eglot--refresh-width'."))

(defvar coq-eglot--default-output (coq-eglot--make-output)
  "The output of the script buffers, see `coq-eglot--output'.")

(defvar-local coq-eglot--buffer-output nil
  "Output of the current script, goals or response buffer, or nil.
Nil for `coq-eglot--default-output'.")
(put 'coq-eglot--buffer-output 'permanent-local t)

(defvar coq-eglot--bound-output nil
  "Output bound by `coq-eglot--with-output', or nil.")

(defun coq-eglot--output ()
  "The output of the current buffer.
The one bound by `coq-eglot--with-output' if any, otherwise the one of
the current script, goals or response buffer, see
`coq-eglot--buffer-output'."
  (or coq-eglot--bound-output coq-eglot--buffer-output
      coq-eglot--default-output))

(defmacro coq-eglot--with-output (output &rest body)
  "Run BODY with OUTPUT as the output of all buffers.
For timers and callbacks, which may run in any buffer."
  (declare (indent 1) (debug t))
  `(let ((coq-eglot--bound-output ,output))
     ,@body))

(defun coq-eglot--output-name (base)
  "Name of the buffer BASE of the current output, see `coq-eglot--output'."
  (concat base (coq-eglot--output-suffix (coq-eglot--output))))

(defvar coq-eglot-goals-buffer-name "*goals*")
(defvar coq-eglot-conclusion-buffer-name "*conclusion*"
  "Buffer of the conclusion, see `coq-eglot-split-goals'.")
(defvar coq-eglot-response-buffer-name "*response*")

(defun coq-eglot--goals-name ()
  "Name of the goals buffer of the current output."
  (coq-eglot--output-name coq-eglot-goals-buffer-name))

(defun coq-eglot--conclusion-name ()
  "Name of the conclusion buffer of the current output."
  (coq-eglot--output-name coq-eglot-conclusion-buffer-name))

(defun coq-eglot--response-name ()
  "Name of the response buffer of the current output."
  (coq-eglot--output-name coq-eglot-response-buffer-name))

(defun coq-eglot--active-buffer ()
  "The active script buffer of the current output, or nil."
  (coq-eglot--output-active (coq-eglot--output)))

(defun coq-eglot--active-p ()
  "Non-nil if the current buffer is the active script buffer of its output."
  (eq (current-buffer) (coq-eglot--active-buffer)))

(defvar-local coq-eglot--twin nil
  "The twin of the current script buffer, or nil.
See `coq-eglot-twin-pair'.")
(put 'coq-eglot--twin 'permanent-local t)

(defvar-local coq-eglot--twin-label nil
  "Label of the server of a twin in the mode line, like an opam switch.
See `coq-eglot-twin-pair'.")

(defun coq-eglot--twin-layout-p ()
  "Non-nil if the active script buffer of the current output has a twin.
Then its goals and messages have windows of their own below it, see
`coq-eglot-twin-layout'."
  (let ((active (coq-eglot--active-buffer)))
    (and (buffer-live-p active)
         (buffer-live-p (buffer-local-value 'coq-eglot--twin active)))))

(defun coq-eglot--activate ()
  "Make the current buffer the active script buffer.
Gray the processed part of the previous one, display the goals of the
current one."
  (unless (coq-eglot--active-p)
    (let ((previous (coq-eglot--active-buffer)))
      (setf (coq-eglot--output-active (coq-eglot--output)) (current-buffer))
      (when (buffer-live-p previous)
        (with-current-buffer previous (coq-eglot--update-overlays)))
      (coq-eglot-compile-check-outdated)
      (coq-eglot--update-overlays)
      (coq-eglot--goals-at-position-async))))

(defun coq-eglot-script-buffer ()
  "Return the script buffer a command of the backend acts on.
The current buffer in a script buffer, the active script buffer in the
goals and response buffers, like in Proof General."
  (cond
   (coq-eglot-mode (current-buffer))
   ((and (derived-mode-p 'coq-eglot-output-mode)
         (buffer-live-p (coq-eglot--active-buffer)))
    (coq-eglot--active-buffer))
   (t (user-error "Coq: no script buffer"))))

(defmacro coq-eglot--with-script (&rest body)
  "Run BODY in the script buffer of the command, made active.
See `coq-eglot-script-buffer'."
  (declare (indent 0) (debug t))
  `(with-current-buffer (coq-eglot-script-buffer)
     (setq coq-eglot--command-buffer (current-buffer))
     (coq-eglot--activate)
     ,@body))

(defun coq-eglot--forget-active ()
  "Forget the current buffer if it is the active script buffer."
  (when (coq-eglot--active-p)
    (setf (coq-eglot--output-active (coq-eglot--output)) nil)))

(defvar coq-eglot-position-hook nil
  "Hook run in a script buffer when its proof position moved.
Or the part being checked, or the face of the processed part: when
what the overlays display changed, see `coq-eglot--update-overlays'.
Not when nothing changed: no cascade of updates between buffers that
follow each other, like twins.")

(defvar-local coq-eglot--displayed nil
  "What the overlays displayed when `coq-eglot-position-hook' last ran.
A list: the proof position, the end of the part being checked or nil,
the face of the processed part.")

(defvar coq-eglot--command-buffer nil
  "Script buffer of the last command of the backend, or of the last edition.
By the user, not by a program, nor the cursor moves: the buffer where
the user works, see
`coq-eglot--with-script' and `coq-eglot--after-change'.")

(defun coq-eglot--on-kill ()
  "Forget the current script buffer, being killed.
Stop its check and its compilation, it is no longer the active one, nor
the one where the user works."
  (coq-eglot-compile-cancel)
  (coq-eglot--stop)
  (when (eq coq-eglot--command-buffer (current-buffer))
    (setq coq-eglot--command-buffer nil))
  (coq-eglot--forget-active))

(defun coq-eglot--update-overlays ()
  "Update the overlays of the processed part and of the checked part.
Computed from the session, the proof position and the target: calling
it again changes nothing.  Run `coq-eglot-position-hook' if what they
display changed."
  (unless (overlayp coq-eglot--locked-overlay)
    (setq coq-eglot--locked-overlay (make-overlay (point-min) (point-min))))
  (overlay-put coq-eglot--locked-overlay 'face
               (if (or (coq-eglot--active-p) (null (coq-eglot--active-buffer)))
                   'proof-locked-face
                 (coq-eglot--inactive-locked-face)))
  (move-overlay coq-eglot--locked-overlay (point-min) (coq-eglot-position))
  (coq-eglot-compile-show-outdated (coq-eglot-position))
  (if (not (coq-eglot-checking-p))
      (when (overlayp coq-eglot--queue-overlay)
        (delete-overlay coq-eglot--queue-overlay))
    (unless (overlayp coq-eglot--queue-overlay)
      (setq coq-eglot--queue-overlay (make-overlay (point-min) (point-min)))
      (overlay-put coq-eglot--queue-overlay 'face 'proof-queue-face))
    (move-overlay coq-eglot--queue-overlay (coq-eglot-position)
                  (max (coq-eglot-position)
                       (coq-eglot-check-target))))
  (let ((displayed (list (coq-eglot-position)
                         (and (coq-eglot-checking-p) (coq-eglot-check-target))
                         (overlay-get coq-eglot--locked-overlay 'face))))
    (unless (equal displayed coq-eglot--displayed)
      (setq coq-eglot--displayed displayed)
      (run-hooks 'coq-eglot-position-hook))))

(defun coq-eglot--set-position (end answer)
  "Move the proof position to END, with the ANSWER of the server for it.
END is the end of a sentence, or nil for the beginning of the buffer.
ANSWER may be nil."
  (coq-eglot-session-forget-sentences (or end (point-min)))
  (when end
    (if (= (coq-eglot-position) end)
        (when answer
          (coq-eglot-session-set-sentence-answer
           (coq-eglot-session-last-sentence) answer))
      (coq-eglot-session-add-sentence end answer)))
  (coq-eglot--update-overlays))

(defun coq-eglot--skip-backward (pos)
  "Return the position before the blanks and comments preceding POS."
  (save-excursion (goto-char pos) (forward-comment (- (point))) (point)))

(defun coq-eglot--skip-forward (pos)
  "Return the position after the blanks and comments following POS."
  (save-excursion (goto-char pos) (forward-comment (buffer-size)) (point)))

(defvar-local coq-eglot--intent 0
  "Counter of the commands that move the proof position.
An answer asked for one of them is not used after another one, see
`coq-eglot--move-back'.")

(defun coq-eglot--new-intent ()
  "Note that the user asked to move the proof position, return the intent."
  ;; A presentation enrichment of the previously displayed goals is now
  ;; obsolete.  It is not session work, but it should not delay the new
  ;; semantic request in coq-lsp's queue.
  (coq-eglot--cancel-hyp-sorts)
  (cl-incf coq-eglot--intent))

(defun coq-eglot--answer-valid-p (answer)
  "Non-nil if ANSWER, a `coq-eglot-lsp-answer', is still valid.
The text did not change up to the end of its sentence since the
version it is about, see `coq-eglot-session-valid-p'."
  (let ((context (coq-eglot-lsp-answer-context answer))
        (sentence (coq-eglot-lsp-answer-sentence answer)))
    (coq-eglot-session-valid-p
     (or (coq-eglot-lsp-answer-version answer)
         (and context (coq-eglot-lsp-context-version context)))
     (cond (sentence (cdr sentence))
           (context (coq-eglot-lsp-context-position context))
           (t (point-max))))))

(defun coq-eglot--ask-goals (pos callback)
  "Ask the goals after the sentence at POS, without waiting.
CALLBACK is called with the answer when it comes, if still valid, see
`coq-eglot--answer-valid-p'; not if the request fails.  Asking again
what is asked waits for the same answer, see `coq-eglot-session-ask'."
  (coq-eglot-session-ask
   ;; what the answer depends on: no answer for an older text, or for
   ;; other printing options, see `coq-eglot-session-ask'
   (append (list 'goals pos (coq-eglot-session-clock))
           (coq-eglot-lsp-goals-options))
   (lambda (answer)
     (when (and answer (coq-eglot--answer-valid-p answer))
       (funcall callback answer)))
   (lambda (done)
     (coq-eglot-lsp-goals-async pos done (lambda (_failure) (funcall done nil))))))

(defun coq-eglot--sentence-before (pos on-found)
  "Find the last processed sentence ending before POS, without waiting.
A sentence ending exactly at POS counts.  Call ON-FOUND with (END .
ANSWER), END the end of the sentence, ANSWER the answer of the server
with the goals after it.  The kept answers are used if possible,
otherwise the server is asked for sentences it checked already.  Do
nothing if there is no such sentence or a request fails."
  (let* ((end (coq-eglot--skip-backward pos))
         (kept (and (> end (point-min))
                    (coq-eglot-session-sentence-ending-at end)))
         (answer (and kept (coq-eglot-session-sentence-answer kept))))
    (cond
     ((<= end (point-min)) nil)
     (answer (funcall on-found (cons end answer)))
     (t
      ;; the sentence containing the last character before POS
      (coq-eglot--ask-goals
       (1- end)
       (lambda (answer)
         (let ((bounds (coq-eglot-lsp-answer-sentence answer)))
           (cond
            ((null bounds) nil)
            ((<= (cdr bounds) pos)
             (funcall on-found (cons (cdr bounds) answer)))
            ;; it does not end before POS: take the one before it
            (t (coq-eglot--sentence-before (car bounds) on-found))))))))))

(defun coq-eglot--move-back (pos &optional goals-only)
  "Move the proof position back to the last sentence ending at POS or before.
Without waiting.  Usually the server told the bounds of all the
sentences it checked (see `coq-eglot-sentences-previous-end'): the
proof position moves there at once.  Otherwise first to the last
processed sentence known, at once, then to the one the server finds, if
the user did not ask anything else meanwhile and the answer is still
valid.  Display the goals and messages, or only the goals if
GOALS-ONLY: the response buffer keeps an error."
  (let ((intent (coq-eglot--new-intent))
        (known (coq-eglot-sentences-previous-end pos)))
    (coq-eglot-session-forget-sentences pos)
    (when (and known (> known (coq-eglot-position)))
      ;; before the old proof position: checked
      (coq-eglot--set-position known nil))
    (coq-eglot--update-overlays)
    (coq-eglot--goals-at-position nil goals-only)
    (unless known
      (coq-eglot--sentence-before
       pos
       (lambda (found)
         (when (and (= intent coq-eglot--intent)
                    (not (coq-eglot-checking-p))
                    (> (car found) (coq-eglot-position)))
           (coq-eglot--set-position (car found) (cdr found))
           (coq-eglot--show-answer (cdr found) goals-only)))))))

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

(defvar coq-eglot-error-hook nil
  "Hook run in a script buffer when it highlights an error.
Point is at the error, see `coq-eglot--highlight-error'.")

(defun coq-eglot--highlight-error (start end)
  "Highlight the sentence between START and END, which failed.
Like Proof General: the sentence with `proof-boring-face', the location
of the error, if known, with `proof-warning-face'.  Move point to the
error.  Run `coq-eglot-error-hook'."
  (coq-eglot--clear-error)
  (coq-eglot--error-overlay start end 'proof-boring-face 0)
  (let ((range (coq-eglot-session-error-range start end)))
    (when range
      (coq-eglot--error-overlay (car range) (cdr range) 'proof-warning-face 1))
    (goto-char (if range (car range) start)))
  (when coq-eglot-error-highlight-duration
    (setq coq-eglot--error-timer
          (run-at-time coq-eglot-error-highlight-duration nil
                       #'coq-eglot--clear-error-in (current-buffer))))
  (run-hooks 'coq-eglot-error-hook))

;;; Display

(define-derived-mode coq-eglot-output-mode nil "Coq Output"
  "Parent mode of the goals and response buffers of the Eglot backend.
Read-only, with the keys of the backend, and the keys of the queries
and of the display common to all backends, see
`coq-eglot--set-output-keys', but not those of `special-mode': like in
Proof General, \"q\" does not close the window.  Queries run on the
active script buffer."
  :syntax-table coq-mode-syntax-table   ; for `coq-id-at-point'
  (setq buffer-read-only t)
  (coq-eglot--set-output-keys)
  (setq coq-query-function #'coq-eglot-run-query)
  (setq coq-query-result-function #'coq-eglot-query-result)
  (setq coq-ask-printing-width-function #'coq-eglot-ask-printing-width)
  (setq coq-set-flag-function #'coq-eglot-set-flag)
  (setq coq-set-search-blacklist-function #'coq-eglot-set-search-blacklist))

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
  "Return buffer NAME, in MODE, of the current output."
  (let ((output (coq-eglot--output))
        (buffer (get-buffer-create name)))
    (with-current-buffer buffer
      (unless (eq major-mode mode) (funcall mode))
      (setq coq-eglot--buffer-output
            (unless (eq output coq-eglot--default-output) output)))
    buffer))

(defvar coq-eglot-trace-buffer-name)

(defun coq-eglot--output-window-p (window)
  "Non-nil if WINDOW displays the goals, the conclusion or the messages."
  (member (buffer-name (window-buffer window))
          (list (coq-eglot--goals-name) (coq-eglot--conclusion-name)
                (coq-eglot--response-name))))

(defun coq-eglot--three-windows-p ()
  "Non-nil if the goals and the messages have windows of their own.
Like in Proof General: if `proof-three-window-enable' is non-nil and the
frame is high enough.  Always for twins, see `coq-eglot--twin-layout-p'."
  (and (or proof-three-window-enable (coq-eglot--twin-layout-p))
       (> (frame-height) (* 4 window-min-height))))

(defun coq-eglot--multiple-frames-p ()
  "Non-nil if the goals and the messages have frames of their own.
See `proof-multiple-frames-enable'.  Never for twins: they are side by
side in one frame, see `coq-eglot-twin-layout'."
  (and proof-multiple-frames-enable (not (coq-eglot--twin-layout-p))))

(defun coq-eglot--main-window ()
  "The window of the script, next to which the output windows go."
  (or (and (coq-eglot--active-buffer)
           (get-buffer-window (coq-eglot--active-buffer)))
      (seq-find (lambda (window) (not (coq-eglot--output-window-p window)))
                (window-list nil 'no-minibuffer))
      (selected-window)))

(defun coq-eglot--show-in (window buffer)
  "Display BUFFER in WINDOW, a window of its own in three windows mode."
  (set-window-dedicated-p window nil)
  (set-window-buffer window buffer)
  (set-window-dedicated-p window (coq-eglot--three-windows-p))
  window)

(defun coq-eglot--display-three ()
  "Display the goals and the messages in windows of their own.
The windows missing are created like in Proof General, see
`proof-three-window-mode-policy': below the script (vertical), on its
right (hybrid) or in three columns (horizontal).  With the conclusion
apart, its window is below the goals window."
  (let* ((policy (if (coq-eglot--twin-layout-p)
                     ;; below each twin
                     'vertical
                   (proof-guess-3win-display-policy
                    proof-three-window-mode-policy)))
         (columns (eq policy 'horizontal))
         (goals (coq-eglot--output-buffer (coq-eglot--goals-name)
                                          #'coq-eglot-goals-mode))
         (conclusion (and coq-eglot-split-goals
                          (coq-eglot--output-buffer
                           (coq-eglot--conclusion-name)
                           #'coq-eglot-goals-mode)))
         (response (coq-eglot--output-buffer (coq-eglot--response-name)
                                             #'coq-eglot-response-mode))
         (goals-window (get-buffer-window goals))
         (response-window (or (get-buffer-window response)
                              (coq-eglot--reuse-rotated-window response))))
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
  (let ((shared (or (seq-find (lambda (window)
                                (and (coq-eglot--output-window-p window)
                                     (not (equal (buffer-name
                                                  (window-buffer window))
                                                 (coq-eglot--conclusion-name)))))
                              (window-list nil 'no-minibuffer))
                    (coq-eglot--reuse-rotated-window nil)))
        (goals-window (get-buffer-window (coq-eglot--goals-name))))
    (cond
     ((and (equal (buffer-name buffer) (coq-eglot--conclusion-name))
           goals-window)
      (coq-eglot--show-in (split-window goals-window nil 'below) buffer))
     (shared (coq-eglot--show-in shared buffer))
     (t (coq-eglot--show-in
         (split-window (coq-eglot--main-window) nil
                       (if (eq (proof-guess-3win-display-policy 'smart)
                               'vertical)
                           'below 'right))
         buffer)))))

(defconst coq-eglot--frame-parameters
  '((minibuffer . nil)
    (unsplittable . t)
    (menu-bar-lines . 0)
    (tool-bar-lines . 0)
    (coq-eglot . t))
  "Parameters of the frames of the goals, conclusion and messages.
Like `proof-multiframe-parameters' in Proof General.  The parameter
`coq-eglot' marks these frames.  See `proof-multiple-frames-enable'.")

(defun coq-eglot--frames ()
  "The frames of the goals, conclusion and messages buffers."
  (seq-filter (lambda (frame) (frame-parameter frame 'coq-eglot))
              (frame-list)))

(defun coq-eglot--display-in-frame (buffer)
  "Display BUFFER in a frame of its own, see `proof-multiple-frames-enable'."
  (let ((window (display-buffer
                 buffer
                 `((display-buffer-reuse-window display-buffer-pop-up-frame)
                   (reusable-frames . t)
                   (pop-up-frame-parameters . ,coq-eglot--frame-parameters)))))
    (when window
      (set-window-dedicated-p window t))
    window))

(defun coq-eglot--display-buffer (name mode)
  "Return buffer NAME in MODE, displayed like in Proof General.
See `proof-three-window-enable', `proof-three-window-mode-policy' and
`proof-multiple-frames-enable'.  If the windows cannot be split, let
`display-buffer' choose."
  (let ((buffer (coq-eglot--output-buffer name mode)))
    (cond
     ((coq-eglot--multiple-frames-p)
      (unless (get-buffer-window buffer t)
        (coq-eglot--display-in-frame buffer)))
     ((not (get-buffer-window buffer))
      (condition-case nil
          (if (coq-eglot--three-windows-p)
              (coq-eglot--display-three)
            (coq-eglot--display-two buffer))
        (error (display-buffer buffer)))))
    buffer))

(defun coq-eglot-layout-windows ()
  "Display the goals and response windows again, like in Proof General.
They come back if closed, with their default sizes, see
`proof-three-window-enable' and `proof-three-window-mode-policy'.  With
`proof-multiple-frames-enable', in frames of their own; without, these
frames are deleted."
  (interactive)
  (let ((selected (current-buffer)))
    (coq-eglot--with-script
      ;; displayed again from scratch: default sizes
      (dolist (window (window-list nil 'no-minibuffer))
        (when (and (coq-eglot--output-window-p window)
                   (not (frame-root-window-p window)))
          (delete-window window)))
      (unless (coq-eglot--multiple-frames-p)
        (mapc #'delete-frame (coq-eglot--frames)))
      (coq-eglot--display-buffer (coq-eglot--goals-name)
                                 #'coq-eglot-goals-mode)
      (when (or (coq-eglot--multiple-frames-p) (coq-eglot--three-windows-p))
        (coq-eglot--display-buffer (coq-eglot--response-name)
                                   #'coq-eglot-response-mode))
      (when coq-eglot-split-goals
        (coq-eglot--display-buffer (coq-eglot--conclusion-name)
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

(defun coq-eglot--reuse-rotated-window (buffer)
  "A window where \\[coq-eglot-display-some-buffers] displayed the trace.
Display BUFFER in it if non-nil.  Return nil if there is none."
  (let* ((trace (get-buffer coq-eglot-trace-buffer-name))
         (window (and trace
                      (seq-find (lambda (window)
                                  (window-parameter window 'coq-eglot-rotated))
                                (get-buffer-window-list trace nil)))))
    (when window
      (set-window-parameter window 'coq-eglot-rotated nil)
      (when buffer (coq-eglot--show-in window buffer))
      window)))

(defvar coq-eglot--rotation 0
  "Number of repetitions of `coq-eglot-display-some-buffers'.")

(defun coq-eglot-display-some-buffers ()
  "Display the messages, the trace or the goals, rotating.
Like in Proof General: repeated, it displays each of them in turn,
without changing the layout of the windows.  In three windows mode
\(see `proof-three-window-enable'), the goals keep their window, the
trace is displayed in the window of the messages, until the next
messages."
  (interactive)
  (setq coq-eglot--rotation
        (if (eq last-command 'coq-eglot-display-some-buffers)
            (1+ coq-eglot--rotation)
          0))
  (let* ((names (list (coq-eglot--response-name) coq-eglot-trace-buffer-name
                      (coq-eglot--goals-name)))
         (buffers (delq nil (mapcar #'get-buffer names)))
         (buffer (and buffers
                      (nth (mod coq-eglot--rotation (length buffers)) buffers)))
         (three (coq-eglot--three-windows-p))
         (shared (if (and three (equal (buffer-name buffer)
                                       (coq-eglot--goals-name)))
                     (list (coq-eglot--goals-name))
                   (seq-remove (lambda (name)
                                 (and three
                                      (equal name (coq-eglot--goals-name))))
                               names))))
    (when buffer
      (let ((window (seq-find (lambda (window)
                                (member (buffer-name (window-buffer window))
                                        shared))
                              ;; also in their frames, see
                              ;; `proof-multiple-frames-enable'
                              (window-list-1 nil 'no-minibuffer
                                             (and (coq-eglot--multiple-frames-p)
                                                  t)))))
        (if (not window)
            (display-buffer buffer)
          (coq-eglot--show-in window buffer)
          (set-window-parameter window 'coq-eglot-rotated
                                (equal (buffer-name buffer)
                                       coq-eglot-trace-buffer-name))))
      (message "Coq: %s" (buffer-name buffer)))))

(defun coq-eglot--layout-on-visit ()
  "Display the goals and messages windows if wanted, when visiting a file.
See `proof-layout-windows-on-visit-file'.  Later: the buffer of the file
is not displayed yet."
  (when proof-layout-windows-on-visit-file
    (let ((buffer (current-buffer)))
      (run-at-time 0 nil
                   (lambda ()
                     (when (and (buffer-live-p buffer)
                                (eq (window-buffer (selected-window)) buffer)
                                (with-current-buffer buffer
                                  (or (not (coq-eglot--active-buffer))
                                      (coq-eglot--active-p))))
                       (with-current-buffer buffer
                         (coq-eglot-layout-windows))))))))

(defun coq-eglot--displays-p ()
  "Non-nil if the current buffer displays its state in its output.
A script buffer that is active, or a goals or response buffer: only
the active script buffer displays its state."
  (or (not coq-eglot-mode) (coq-eglot--active-p)))

(defun coq-eglot--set-buffer-text (name mode text)
  "Replace the content of buffer NAME (in MODE) by TEXT, and display it.
Then adjust the heights of the windows, see
`coq-optimise-resp-windows-enable'.  Do nothing if called from a script
buffer that is not active, see `coq-eglot--displays-p'."
  (when (coq-eglot--displays-p)
    (coq-eglot--set-buffer-text-1 name mode text)))

(defun coq-eglot--set-buffer-text-1 (name mode text)
  "Replace the content of buffer NAME (in MODE) by TEXT, and display it.
When the goals and the messages share a window (see
`proof-three-window-enable'), no messages do not hide the goals.  Like
in Proof General, the buffer is displayed only if
`proof-auto-raise-buffers', and its windows are deleted when it becomes
empty if `proof-delete-empty-windows'."
  (let* ((empty (string-empty-p text))
         (delete-empty (and proof-delete-empty-windows
                            (not (coq-eglot--multiple-frames-p))))
         (delete (and empty delete-empty))
         (display (and proof-auto-raise-buffers
                       (not delete)
                       (or (coq-eglot--multiple-frames-p)
                           (coq-eglot--three-windows-p)
                           (not (equal name (coq-eglot--response-name)))
                           (not empty)))))
    (with-current-buffer (if display
                             (coq-eglot--display-buffer name mode)
                           (coq-eglot--output-buffer name mode))
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert text)
        (goto-char (point-min)))
      ;; before resizing: folded, the other goals take one line
      (when (derived-mode-p 'coq-eglot-goals-mode)
        (coq-eglot-goals-decorate)
        (coq-goals-fold-other-goals)))
    (when delete-empty
      ;; also the windows that the layout created for empty buffers
      (dolist (other (list (coq-eglot--goals-name)
                           (coq-eglot--conclusion-name)
                           (coq-eglot--response-name)))
        (let ((buffer (get-buffer other)))
          (when (and buffer (zerop (buffer-size buffer)))
            (coq-eglot--delete-windows other)))))
    ;; without auto raise, the windows are not managed
    (when proof-auto-raise-buffers
      (coq-eglot--resize-windows))))

(defun coq-eglot--delete-windows (name)
  "Delete the windows of buffer NAME in the selected frame.
Not the only window of the frame.  See `proof-delete-empty-windows'."
  (dolist (window (get-buffer-window-list name nil))
    (unless (frame-root-window-p window)
      (delete-window window))))

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
  "Height WINDOW needs to display its buffer, mode line included.
The goals after the first one count for one line, the first of them or
their summary when folded: they are displayed only if the other windows
leave room."
  (+ (- (window-total-height window) (window-body-height window))
     (with-current-buffer (window-buffer window)
       (let ((others (and (derived-mode-p 'coq-eglot-goals-mode)
                          (coq-goals--other-goals-start))))
         (if others
             (1+ (count-screen-lines (point-min) others nil window))
           (count-screen-lines (point-min) (point-max) nil window))))))

(defun coq-eglot--resize-windows ()
  "Adjust the heights of the windows.
See `coq-optimise-resp-windows-enable' and `proof-shrink-windows-tofit'.
Not with `proof-multiple-frames-enable'."
  (when (and (or coq-optimise-resp-windows-enable proof-shrink-windows-tofit)
             (not (coq-eglot--multiple-frames-p)))
    (coq-eglot-resize-windows-by-priority)))

(defun coq-eglot-resize-windows-by-priority ()
  "Give the windows the height they need, by priority.
The goals, conclusion and response windows displayed one above the
other share their height: each one gets the height it needs, the
conclusion first, then the goals, then the response.  The first one
gets what remains: the conclusion if `coq-eglot-split-goals', the
hypotheses never get more than they need; the goals otherwise.  In
three columns (see `proof-three-window-mode-policy'), only the windows
of the same column.  The script window keeps its height, unless
`proof-shrink-windows-tofit': then the windows below it get only the
height they need, at most half of the frame (two thirds without
`proof-three-window-enable'), like in Proof General, and the script
window the rest.  Without `coq-optimise-resp-windows-enable', only the
windows below the script are resized."
  (let* ((names `((goals . ,(coq-eglot--goals-name))
                  (conclusion . ,(coq-eglot--conclusion-name))
                  (response . ,(coq-eglot--response-name))))
         (windows (delq nil (mapcar (lambda (role)
                                      (get-buffer-window
                                       (cdr (assq role names))))
                                    '(conclusion goals response))))
         (script (coq-eglot--main-window)))
    (pcase-dolist (`(,parent . ,column) (seq-group-by #'window-parent windows))
      (let ((shrink (and proof-shrink-windows-tofit
                         parent
                         (eq (window-parent script) parent))))
        (when (and (or shrink coq-optimise-resp-windows-enable)
                   (or shrink (cdr column))
                   (window-combined-p (car column)))
          (coq-eglot--resize-column (if shrink (cons script column) column)
                                    shrink))))))

(defun coq-eglot--resize-column (windows &optional script)
  "Give WINDOWS, one above the other, the height they need, by priority.
If SCRIPT is non-nil, the first window is the script window: it gets
what remains, the others at most half of the frame (two thirds in two
windows mode).  See `coq-eglot-resize-windows-by-priority'."
  (let* ((max-need (floor (frame-height)
                          (if (coq-eglot--three-windows-p) 2 1.5)))
         (needs (mapcar (lambda (window)
                          (let ((need (coq-eglot--window-need window)))
                            (if script (min max-need need) need)))
                        windows))
         (heights (coq-eglot--allocate-heights
                   (apply #'+ (mapcar #'window-total-height windows))
                   (if script (cons 0 (cdr needs)) needs)
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

(defun coq-eglot--displayed-width ()
  "Printing width of the goals displayed by the current output, or nil.
See `coq-eglot--output'."
  (coq-eglot--output-width (coq-eglot--output)))

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

(defun coq-eglot--goals-windows-width ()
  "Number of characters of the narrowest goals window, or nil."
  (apply #'coq-eglot--windows-width (coq-eglot--goals-name)
         (and coq-eglot-split-goals (list (coq-eglot--conclusion-name)))))

(defun coq-eglot--asked-width ()
  "Printing width asked by the user, or nil if the windows changed since."
  (let ((asked (coq-eglot--output-asked-width (coq-eglot--output))))
    (and asked
         (eql (cdr asked) (coq-eglot--goals-windows-width))
         (car asked))))

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
       (or (coq-eglot--windows-width (coq-eglot--response-name))
           (coq-eglot--windows-width (coq-eglot--goals-name)))
       0)))

(defun coq-eglot-ask-printing-width (width)
  "Print the goals and the answers of the queries WIDTH columns wide.
Until the goals windows change width, then the printing width follows
them again if `coq-auto-adapt-printing-width'."
  (interactive
   (list (read-number "Printing width: "
                      (or (coq-eglot--displayed-width)
                          (coq-eglot--goals-printing-width)
                          78))))
  (setf (coq-eglot--output-asked-width (coq-eglot--output))
        (cons width (coq-eglot--goals-windows-width)))
  (coq-eglot--refresh-width))

(defvar coq-eglot--printing-flags nil
  "Commands setting the printing flags of the goals and queries.
Without their final dot, in the order they were run, at most one per
flag.  See `coq-eglot-set-flag'.")

(defun coq-eglot--flag-name (command)
  "Name of the flag set or unset by COMMAND, like \"Printing All\"."
  (replace-regexp-in-string "\\`\\(?:Set\\|Unset\\)[ \t]+" ""
                            (string-trim command)))

(defun coq-eglot-set-flag (command)
  "Run COMMAND, setting a printing flag, for the next goals and queries.
COMMAND is like \"Set Printing Parentheses\", without final dot.  The
server runs it before each goals request and each query, on a copy of
the state: nothing is checked again, the goals are printed again now.
The flags are forgotten when the server stops.  This is
`coq-set-flag-function' for the Eglot backend."
  (let ((name (coq-eglot--flag-name command)))
    (setq coq-eglot--printing-flags
          (append (cl-remove name coq-eglot--printing-flags
                             :key #'coq-eglot--flag-name :test #'equal)
                  (list (string-trim command)))))
  (if (string-match-p "Printing Unfocused\\'" command)
      (coq-eglot--warn-no-effect
       command "the goals show the unfocused goals, folded by \
`coq-fold-other-goals'")
    (message "Coq: %s" command))
  (coq-eglot--refresh-width))

(defun coq-eglot--goals-printing-flags ()
  "Printing flags of the goals.
This is `coq-eglot-lsp-printing-flags-function'."
  coq-eglot--printing-flags)

(setq coq-eglot-lsp-printing-flags-function #'coq-eglot--goals-printing-flags)

(defun coq-eglot-set-search-blacklist (_old new)
  "Check the search blacklist NEW, used by the next queries.
NEW is in the syntax of Add Search Blacklist.  The server keeps no
state between two queries: each query starts by replacing the strings
of `coq-search-blacklist-string' by those of
`coq-search-blacklist-current-string', see
`coq-eglot--search-blacklist-commands'.  This is
`coq-set-search-blacklist-function' for the Eglot backend."
  (unless (string-match-p "\\`\\(?:[ \t\n]*\"[^\"]*\"\\)*[ \t\n]*\\'" new)
    (user-error "Coq: the search blacklist is a list of strings in \
double quotes, like \"Private_\" \"_subproof\""))
  (message "Coq: search blacklist %s" new))

(defun coq-eglot--search-blacklist-commands ()
  "Commands setting the search blacklist at the start of a query.
Without their final dot.  Like Proof General, which adds
`coq-search-blacklist-string' to the blacklist of Coq when it starts,
then replaces the old blacklist by the new one at each change."
  (append (unless (string-blank-p coq-search-blacklist-string)
            (list (format "Remove Search Blacklist %s"
                          coq-search-blacklist-string)))
          (unless (string-blank-p coq-search-blacklist-current-string)
            (list (format "Add Search Blacklist %s"
                          coq-search-blacklist-current-string)))))

(defun coq-eglot--schedule-width-refresh (&rest _)
  "Print the goals again soon if the width of their windows changed.
In `window-size-change-functions' of the goals buffers, and after each
display of the goals.  A timer, not to change the buffers during the
redisplay, and to wait for the end of a resizing.  For the current
output, see `coq-eglot--output'."
  (let ((output (coq-eglot--output)))
    (coq-eglot--cancel-width-refresh output)
    (setf (coq-eglot--output-width-timer output)
          (run-at-time 0.1 nil #'coq-eglot--refresh-width output))))

(defun coq-eglot--cancel-width-refresh (&optional output)
  "Cancel the automatic goals-width refresh of OUTPUT.
OUTPUT is the current one by default."
  (let* ((output (or output (coq-eglot--output)))
         (timer (coq-eglot--output-width-timer output)))
    (when (timerp timer)
      (cancel-timer timer))
    (setf (coq-eglot--output-width-timer output) nil)))

(defun coq-eglot--refresh-width (&optional output)
  "Print the goals again if their width or printing flags changed.
The width of their windows, or the flags of `coq-eglot-set-flag'.  Not
during a check: the goals of each sentence are asked when it is checked,
at the current width.  For OUTPUT, the current one by default."
  (coq-eglot--with-output (or output (coq-eglot--output))
    (coq-eglot--refresh-width-1)))

(defun coq-eglot--refresh-width-1 ()
  "Like `coq-eglot--refresh-width' for the current output."
  (setf (coq-eglot--output-width-timer (coq-eglot--output)) nil)
  (let* ((output (coq-eglot--output))
         (script (coq-eglot--active-buffer))
         (width (coq-eglot--goals-printing-width)))
    (when (and (coq-eglot--output-goals output)
               (or (and width
                        (not (eql width (coq-eglot--output-width output))))
                   (not (equal coq-eglot--printing-flags
                               (coq-eglot--output-flags output))))
               (buffer-live-p script))
      (with-current-buffer script
        (let ((last (coq-eglot-session-last-sentence)))
          (when (and last (not (coq-eglot-checking-p)))
            (coq-eglot-lsp-goals-async
             (1- (overlay-end last))
             (lambda (answer)
               (when (and (eq (coq-eglot-session-last-sentence) last)
                          (coq-eglot--active-p))
                 (coq-eglot-session-set-sentence-answer last answer)
                 (coq-eglot--show-answer answer t)))
             #'ignore)))))))

(defun coq-eglot--hyps-width ()
  "Width of the lines of the hypotheses.
They must fit in the window, or in Coq's default width."
  (if (coq-eglot--displayed-width)
      (+ (coq-eglot--displayed-width)
         coq-eglot--hyp-indentation
         coq-eglot--printing-width-margin)
    78))

(defcustom coq-eglot-compact-contexts t
  "Non-nil: in the goals, the hypotheses whose type is in Type share lines.
See `coq-eglot--simple-hyp-p'.  Displaying a goal then costs a separate,
bounded request for the sorts of the hypotheses that may share a line.
Intermediate goals that are not displayed never cause this request."
  :type 'boolean
  :safe #'booleanp
  :group 'coq-eglot)

(defun coq-eglot--compact-contexts-p ()
  "Non-nil if the hypotheses of the goals share their lines."
  ;; One hypothesis per line makes the output comparison of twins stable.
  ;; It also makes the auxiliary sorts request unnecessary there.
  (and coq-eglot-compact-contexts
       (not (buffer-live-p coq-eglot--twin))
       (not (coq-eglot--twin-layout-p))))

(defun coq-eglot-toggle-compact-contexts ()
  "Toggle compact presentation of hypotheses in the goals buffer."
  (interactive)
  (setq coq-eglot-compact-contexts (not coq-eglot-compact-contexts))
  (coq-eglot--with-script
    ;; Reuse the answer kept with the current sentence.  Enabling may ask
    ;; only for its presentation sorts; disabling needs no server request.
    (coq-eglot--goals-at-position nil t))
  (message "Coq: compact contexts %s"
           (if coq-eglot-compact-contexts "enabled" "disabled")))

(defun coq-eglot--hyp-sort-names (answer)
  "Names of the hypotheses of ANSWER whose sorts may affect formatting."
  (let ((goal (coq-eglot--first-goal
               (coq-eglot-lsp-answer-goals answer))))
    (when goal
      (seq-mapcat
       (lambda (hyp)
         (and (not (plist-get hyp :def))
              (not (string-search "\n" (coq-eglot--format-hyp hyp)))
              (append (plist-get hyp :names) nil)))
       (append (plist-get goal :hyps) nil)))))

(setq coq-eglot-lsp-hyp-sort-names-function #'coq-eglot--hyp-sort-names)

(defun coq-eglot--late-hyp-sorts-useful-p (goals)
  "Non-nil if the late hypothesis sorts of GOALS would compact its context."
  (let* ((goal (coq-eglot--first-goal goals))
         (sorts (and goal (plist-get goal :hyp-sorts-late))))
    (and sorts
         (coq-eglot--compact-contexts-p)
         (let ((enriched (copy-sequence goal)))
           (plist-put enriched :hyp-sorts sorts)
           (not (equal (coq-eglot--format-hyps goal)
                       (coq-eglot--format-hyps enriched)))))))

(defun coq-eglot-compact-late-context ()
  "Compact the displayed context with hypothesis sorts received late."
  (interactive)
  (coq-eglot--with-script
    (let* ((output (coq-eglot--output))
           (goals (coq-eglot--output-goals output))
           (goal (coq-eglot--first-goal goals))
           (sorts (and goal (plist-get goal :hyp-sorts-late))))
      (unless (and sorts (coq-eglot--compact-contexts-p))
        (user-error "Coq: no late context compaction is available"))
      (plist-put goal :hyp-sorts sorts)
      (plist-put goal :hyp-sorts-late nil)
      (coq-eglot--show-goals-1
       (coq-eglot-lsp-make-answer
        :goals goals
        :printing-width (coq-eglot--output-width output)
        :printing-flags (coq-eglot--output-flags output))))))

(defun coq-eglot--offer-late-context-compaction ()
  "Add an explicit compaction action when late sorts would change the goals."
  (let* ((output (coq-eglot--output))
         (goals (coq-eglot--output-goals output))
         (buffer (and (coq-eglot--late-hyp-sorts-useful-p goals)
                      (get-buffer (coq-eglot--goals-name)))))
    (when (buffer-live-p buffer)
      (with-current-buffer buffer
        (save-excursion
          (goto-char (point-min))
          (unless (text-property-search-forward
                   'coq-eglot-late-context-compaction t t)
            (let ((inhibit-read-only t))
              ;; Keep the action visible near the goal count.  At the end
              ;; of a long context it could be outside the goals window.
              (goto-char (point-min))
              (if (search-forward "\n\n" nil t)
                  (goto-char (match-end 0))
                (goto-char (point-max))
                (unless (bolp) (insert "\n")))
              (insert-text-button
               "Compact context"
               'coq-eglot-late-context-compaction t
               'follow-link t
               'help-echo "Use the hypothesis sorts that arrived after the goal"
               'action (lambda (_button)
                         (coq-eglot-compact-late-context)))
              (insert "\n\n"))))))))

(defun coq-eglot--goals-count ()
  "Numbers of the goals displayed, as (FOCUSED . UNFOCUSED), or nil.
Nil outside of proofs.  This is `coq-goals-count-function' for the
Eglot backend: the server gives the unfocused goals, whatever Set
Printing Unfocused."
  (let ((goals (coq-eglot--output-goals (coq-eglot--output))))
    (when goals
      (cons (length (plist-get goals :goals))
            (coq-eglot--unfocused-count goals)))))

(defun coq-eglot-toggle-detailed-goals ()
  "Show or hide the hypotheses and levels of the other goals.
See `coq-eglot-detailed-goals'.  Without asking the server again."
  (interactive)
  (setq coq-eglot-detailed-goals (not coq-eglot-detailed-goals))
  (coq-eglot--with-script
    (let ((output (coq-eglot--output)))
      (coq-eglot--show-goals-1
       (coq-eglot-lsp-make-answer
        :goals (coq-eglot--output-goals output)
        :printing-width (coq-eglot--output-width output)
        :printing-flags (coq-eglot--output-flags output)))))
  (message "Coq: other goals %s"
           (if coq-eglot-detailed-goals "detailed" "like Coq")))

(defun coq-eglot--format-messages (messages)
  "Format MESSAGES of a sentence, a list of `coq-eglot-lsp-message'."
  (mapconcat #'coq-eglot-lsp-message-text messages "\n"))

(defvar coq-eglot-output-hook nil
  "Hook run in a script buffer when it displayed its goals or messages.
See `coq-eglot--show-goals' and `coq-eglot--show-response'.")

(defun coq-eglot--show-goals (answer)
  "Display the goals of ANSWER of the server.
See `coq-eglot-split-goals'.  Run `coq-eglot-output-hook'.  Do nothing
in a script buffer that is not active, see `coq-eglot--displays-p': the
output keeps the state of the buffer it displays."
  (when (coq-eglot--displays-p)
    (coq-eglot--show-goals-1 answer)))

(defun coq-eglot--show-goals-1 (answer)
  "Display the goals of ANSWER of the server, see `coq-eglot--show-goals'."
  (let* ((output (coq-eglot--output))
         (goals (and answer (coq-eglot-lsp-answer-goals answer)))
         (new (not (equal goals (coq-eglot--output-goals output)))))
    (setf (coq-eglot--output-goals output) goals)
    (setf (coq-eglot--output-width output)
          (and answer (coq-eglot-lsp-answer-printing-width answer)))
    (setf (coq-eglot--output-flags output)
          (and answer (coq-eglot-lsp-answer-printing-flags answer)))
    (if (not coq-eglot-split-goals)
        (progn
          (coq-eglot--set-buffer-text (coq-eglot--goals-name)
                                      #'coq-eglot-goals-mode
                                      (coq-eglot--format-goals goals))
          (coq-eglot--set-mode-line (coq-eglot--goals-name) t))
      ;; the windows separate the hypotheses from the conclusion
      (let ((parts (coq-eglot--format-goals-parts goals t)))
        (coq-eglot--set-buffer-text (coq-eglot--goals-name)
                                    #'coq-eglot-goals-mode (car parts))
        ;; the conclusion comes right below the hypotheses
        (coq-eglot--set-mode-line (coq-eglot--goals-name) nil)
        (coq-eglot--set-buffer-text (coq-eglot--conclusion-name)
                                    #'coq-eglot-goals-mode (cdr parts))
        (coq-eglot--set-separator (coq-eglot--conclusion-name))))
    (coq-hyps-decorate new)
    (coq-eglot--offer-late-context-compaction)
    (coq-eglot--scroll-goals)
    ;; the windows may have been created or resized meanwhile
    (coq-eglot--schedule-width-refresh)
    (run-hooks 'coq-eglot-output-hook)))

(defun coq-eglot--goals-buffer ()
  "The goals buffer holding the goals after the first one, or nil.
The conclusion buffer if `coq-eglot-split-goals'.  This is
`coq-goals-buffer-function' for the Eglot backend."
  (get-buffer (if coq-eglot-split-goals (coq-eglot--conclusion-name)
                (coq-eglot--goals-name))))

(setq coq-goals-buffer-function #'coq-eglot--goals-buffer)
(setq coq-response-buffer-function
      (lambda () (get-buffer (coq-eglot--response-name))))

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
  (let ((goals (get-buffer (coq-eglot--goals-name)))
        (conclusion (get-buffer (coq-eglot--conclusion-name))))
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
    (let ((buffer (get-buffer (coq-eglot--conclusion-name))))
      (when buffer
        (dolist (window (get-buffer-window-list buffer nil t))
          (if (frame-root-window-p window)
              ;; its own frame, see `proof-multiple-frames-enable'
              (when (frame-parameter (window-frame window) 'coq-eglot)
                (delete-frame (window-frame window)))
            (delete-window window)))
        (kill-buffer buffer))))
  (let ((output (coq-eglot--output)))
    (coq-eglot--show-goals
     (coq-eglot-lsp-make-answer
      :goals (coq-eglot--output-goals output)
      :printing-width (coq-eglot--output-width output)
      :printing-flags (coq-eglot--output-flags output))))
  (message "Coq: conclusion %s" (if coq-eglot-split-goals "apart" "with the hypotheses")))

(defun coq-eglot--show-response (text)
  "Display TEXT in the response buffer.
Run `coq-eglot-output-hook'.  Do nothing in a script buffer that is not
active, see `coq-eglot--displays-p'."
  (when (coq-eglot--displays-p)
    (coq-eglot--set-buffer-text (coq-eglot--response-name)
                                #'coq-eglot-response-mode text)
    (run-hooks 'coq-eglot-output-hook)))

(defvar-local coq-eglot--hyp-sorts-answer nil
  "Answer whose displayed goals are waiting for hypothesis sorts.")

(defvar-local coq-eglot--hyp-sorts-context nil
  "Context of the auxiliary hypothesis-sorts request, or nil.")

(defvar-local coq-eglot--hyp-sorts-wait-timer nil
  "Timer displaying goals without hypothesis sorts after the short wait.")

(defvar-local coq-eglot--hyp-sorts-deadline-timer nil
  "Timer cancelling an auxiliary hypothesis-sorts request.")

(defvar-local coq-eglot--hyp-sorts-displayed nil
  "Non-nil if `coq-eglot--hyp-sorts-answer' is already displayed.")

(defun coq-eglot-presentation-ready-p ()
  "Non-nil when the current goals have had their initial display.
This is independent of `coq-eglot-busy-p': a semantic goals answer may
already be complete while presentation waits briefly for hypothesis
sorts.  A late enrichment still in flight does not make this nil."
  (or (null coq-eglot--hyp-sorts-answer)
      coq-eglot--hyp-sorts-displayed))

(defun coq-eglot--cancel-hyp-sorts-timers ()
  "Cancel the timers of the current hypothesis-sorts enrichment."
  (when (timerp coq-eglot--hyp-sorts-wait-timer)
    (cancel-timer coq-eglot--hyp-sorts-wait-timer))
  (when (timerp coq-eglot--hyp-sorts-deadline-timer)
    (cancel-timer coq-eglot--hyp-sorts-deadline-timer))
  (setq coq-eglot--hyp-sorts-wait-timer nil
        coq-eglot--hyp-sorts-deadline-timer nil))

(defun coq-eglot--cancel-hyp-sorts ()
  "Cancel and forget the presentation enrichment currently in flight."
  (coq-eglot--cancel-hyp-sorts-timers)
  (when coq-eglot--hyp-sorts-context
    (coq-eglot-lsp-cancel-request coq-eglot--hyp-sorts-context))
  (setq coq-eglot--hyp-sorts-answer nil
        coq-eglot--hyp-sorts-context nil
        coq-eglot--hyp-sorts-displayed nil))

(defun coq-eglot--show-answer-now (answer &optional goals-only)
  "Display ANSWER immediately, without asking for presentation enrichment."
  (coq-eglot--show-goals answer)
  (unless goals-only
    (coq-eglot--show-response
     (coq-eglot--format-messages
      (and answer (coq-eglot-lsp-answer-messages answer))))))

(defun coq-eglot--hyp-sorts-display (answer goals-only)
  "Display ANSWER if it is still the one waiting for hypothesis sorts."
  (when (eq answer coq-eglot--hyp-sorts-answer)
    (setq coq-eglot--hyp-sorts-wait-timer nil
          coq-eglot--hyp-sorts-displayed t)
    (coq-eglot--show-answer-now answer goals-only)))

(defun coq-eglot--hyp-sorts-finished (answer goals-only sorts)
  "Use SORTS for ANSWER, if its presentation enrichment is still current."
  (when (eq answer coq-eglot--hyp-sorts-answer)
    (setq coq-eglot--hyp-sorts-context nil)
    (coq-eglot--cancel-hyp-sorts-timers)
    (if coq-eglot--hyp-sorts-displayed
        (progn
          (coq-eglot-lsp-add-hyp-sorts answer sorts t)
          ;; Do not move a displayed goal after the deadline.  Offer the
          ;; enrichment only if this exact answer is still on screen.
          (when (eq (coq-eglot-lsp-answer-goals answer)
                    (coq-eglot--output-goals (coq-eglot--output)))
            (coq-eglot--offer-late-context-compaction)))
      (coq-eglot-lsp-add-hyp-sorts answer sorts)
      (coq-eglot--show-answer-now answer goals-only))
    (setq coq-eglot--hyp-sorts-answer nil
          coq-eglot--hyp-sorts-displayed nil)))

(defun coq-eglot--hyp-sorts-failed (answer goals-only _failure)
  "Display ANSWER without sorts if its auxiliary request failed."
  (when (eq answer coq-eglot--hyp-sorts-answer)
    (setq coq-eglot--hyp-sorts-context nil)
    (coq-eglot--cancel-hyp-sorts-timers)
    (unless coq-eglot--hyp-sorts-displayed
      (coq-eglot--show-answer-now answer goals-only))
    (setq coq-eglot--hyp-sorts-answer nil
          coq-eglot--hyp-sorts-displayed nil)))

(defun coq-eglot--hyp-sorts-deadline (answer goals-only)
  "Cancel the sorts request of ANSWER when its presentation deadline expires."
  (when (eq answer coq-eglot--hyp-sorts-answer)
    (setq coq-eglot--hyp-sorts-deadline-timer nil)
    (when coq-eglot--hyp-sorts-context
      (coq-eglot-lsp-cancel-request coq-eglot--hyp-sorts-context))
    (setq coq-eglot--hyp-sorts-context nil)
    (unless coq-eglot--hyp-sorts-displayed
      (coq-eglot--show-answer-now answer goals-only))
    ;; Ignore a success racing with cancellation.
    (setq coq-eglot--hyp-sorts-answer nil
          coq-eglot--hyp-sorts-displayed nil)))

(defun coq-eglot--show-answer-enriched (answer goals-only)
  "Display ANSWER, asking separately for hypothesis sorts when useful."
  (coq-eglot--cancel-hyp-sorts)
  (let* ((goal (and answer
                    (coq-eglot--first-goal
                     (coq-eglot-lsp-answer-goals answer))))
         (already (and goal (plist-get goal :hyp-sorts))))
    (if (or (not (coq-eglot--displays-p))
            (not answer)
            already
            (not (coq-eglot--compact-contexts-p)))
        (coq-eglot--show-answer-now answer goals-only)
      (setq coq-eglot--hyp-sorts-answer answer
            coq-eglot--hyp-sorts-displayed nil)
      (let ((context
             (coq-eglot-lsp-hyp-sorts-async
              answer
              (lambda (sorts)
                (coq-eglot--hyp-sorts-finished answer goals-only sorts))
              (lambda (failure)
                (coq-eglot--hyp-sorts-failed answer goals-only failure)))))
        (if (null context)
            (progn
              (setq coq-eglot--hyp-sorts-answer nil)
              (coq-eglot--show-answer-now answer goals-only))
          (setq coq-eglot--hyp-sorts-context context
                coq-eglot--hyp-sorts-wait-timer
                (run-at-time coq-eglot-lsp-hyp-sorts-wait nil
                             #'coq-eglot--hyp-sorts-display
                             answer goals-only)
                coq-eglot--hyp-sorts-deadline-timer
                (run-at-time coq-eglot-lsp-hyp-sorts-deadline nil
                             #'coq-eglot--hyp-sorts-deadline
                             answer goals-only)))))))

(defun coq-eglot--show-answer (answer &optional goals-only)
  "Display the goals and the messages of ANSWER of the server.
Only the goals if GOALS-ONLY."
  ;; Messages are part of the semantic answer and need no enrichment.
  (unless goals-only
    (coq-eglot--show-response
     (coq-eglot--format-messages
      (and answer (coq-eglot-lsp-answer-messages answer)))))
  ;; If goals are delayed, display the messages again after them: in the
  ;; two-window layout they share a window and messages have precedence.
  (coq-eglot--show-answer-enriched answer goals-only))

(defun coq-eglot--show-error (text)
  "Display error TEXT in the response buffer."
  ;; not face: font-lock would remove it
  (coq-eglot--show-response (propertize text 'font-lock-face 'error)))

(defun coq-eglot--goals-at-position (&optional ask goals-only)
  "Display the goals and messages at the proof position, without waiting.
Use the answer kept for the last processed sentence if any and ASK is
nil.  Otherwise ask the server, and display the answer when it comes,
if the proof position did not move meanwhile.  Only the goals if
GOALS-ONLY: the response buffer keeps an error."
  (unless goals-only (coq-eglot--clear-error))
  (let ((last (coq-eglot-session-last-sentence)))
    (cond
     ((null last)
      (coq-eglot--show-goals nil)
      (unless goals-only (coq-eglot--show-response "")))
     ((and (not ask) (coq-eglot-session-sentence-answer last))
      (coq-eglot--show-answer (coq-eglot-session-sentence-answer last)
                              goals-only))
     (t
      (coq-eglot--ask-goals
       (1- (overlay-end last))
       (lambda (answer)
         (when (eq (coq-eglot-session-last-sentence) last)
           (coq-eglot-session-set-sentence-answer last answer)
           (coq-eglot--show-answer answer goals-only))))))))

(defun coq-eglot--goals-at-position-async ()
  "Display the goals and messages at the proof position, without waiting.
See `coq-eglot--goals-at-position'."
  (coq-eglot--goals-at-position))

;;; Moving forward

(defun coq-eglot--check-busy ()
  "Signal an error if a check is running."
  (when (coq-eglot-checking-p)
    (user-error "Coq is busy, use \\[coq-eglot-interrupt] to interrupt")))

;; The user sets the target, the planner starts the operations moving
;; the proof position toward it, one at a time, see
;; `coq-eglot-session-next-action'.  When an operation ends, the
;; planner starts the next one, if the target is not reached.

(defun coq-eglot--go (target)
  "Process the sentences up to the one containing the character before TARGET.
Asynchronously, see `coq-eglot--plan'."
  (coq-eglot--new-intent)
  (coq-eglot-session-set-target target)
  (coq-eglot--clear-error)
  (coq-eglot--plan))

(defun coq-eglot--plan ()
  "Start the next operation toward the target, if any and none runs."
  (pcase (coq-eglot-session-next-action)
    (`(step ,start)
     (unless (coq-eglot--known-error start) (coq-eglot--step start)))
    (`(check ,start ,target)
     (unless (coq-eglot--known-error start)
       (coq-eglot--advance start target))))
  (coq-eglot--update-overlays))

(defun coq-eglot--continue (before)
  "An operation ended, it started at proof position BEFORE: start the next.
Stop if the proof position did not move since: the planner would start
the same operation again.  It may have moved before the end, with the
progress of the server."
  (if (> (coq-eglot-position) before)
      (coq-eglot--plan)
    (coq-eglot--stop)))

(defvar-local coq-eglot--work-context nil
  "Context of the request currently moving the proof position, or nil.")

(defvar-local coq-eglot--work-start nil
  "Start of the text covered by the operation moving the proof position.
Unlike the proof position, it does not move with progress notifications.")

(defun coq-eglot--start-work (start)
  "Note that an operation starts at START, return its session work object."
  (setq coq-eglot--work-context nil
        coq-eglot--work-start start)
  (prog1 (coq-eglot-session-start-work)
    (coq-eglot--update-overlays)))

(defun coq-eglot--send (work request-fn pos on-success)
  "Send the request of WORK, the running operation, with REQUEST-FN at POS.
ON-SUCCESS is called with the answer.  The answer is ignored if WORK
was cancelled meanwhile: an answer or an error may still come for a
cancelled request."
  (condition-case err
      (let ((context
             (funcall request-fn pos
                      (lambda (answer)
                        (when (coq-eglot-session-work-p work)
                          (setq coq-eglot--work-context nil)
                          (funcall on-success answer)))
                      (lambda (failure)
                        (when (coq-eglot-session-work-p work)
                          (setq coq-eglot--work-context nil)
                          (coq-eglot--failed-request failure))))))
        (when (coq-eglot-session-work-p work)
          (setq coq-eglot--work-context context)))
    ;; not sent, like without server: nothing runs
    (error (when (coq-eglot-session-work-p work)
             (coq-eglot--stop))
           (signal (car err) (cdr err)))))

(defun coq-eglot--stop ()
  "Forget the target and the running operation: nothing is checked."
  (setq coq-eglot--work-context nil
        coq-eglot--work-start nil)
  (coq-eglot-session-stop-work)
  (coq-eglot--update-overlays))

(defun coq-eglot--queue (target)
  "Move the target further, to TARGET, during a check.
Like the queue of Proof General: the part being checked grows at once,
the check of the rest starts when the running operation is finished,
unless it fails.  The running request is not replaced: cancelling it
could interrupt Coq.  Signal an error if TARGET is not after the part
being checked: moving back while checking is not possible."
  (when (<= target (coq-eglot-check-target))
    (coq-eglot--check-busy))
  (coq-eglot-session-set-target target)
  (coq-eglot--update-overlays))

(defun coq-eglot--fail (start end text &optional _answer)
  "The sentence between START and END failed with error TEXT.
Move the proof position before it, without waiting, see
`coq-eglot--move-back', and display the error, with the goals before
the sentence."
  (coq-eglot--trace-error start end text)
  (coq-eglot--move-back start t)
  (coq-eglot--show-error text)
  (coq-eglot--highlight-error start end))

(defun coq-eglot--failed-request (failure)
  "Handle FAILURE of a request, a `coq-eglot-lsp-failure': stop the check."
  (coq-eglot--stop)
  (message "Coq request failed: %s" (coq-eglot-lsp-failure-message failure)))

(defun coq-eglot--next-sentence-start-after (pos)
  "The start of the first sentence after POS, or nil if none."
  (let ((start (coq-eglot--skip-forward pos)))
    (and (< start (point-max)) start)))

(defun coq-eglot--observe (event)
  "Observe EVENT of the server: progress or an error moves the interface.
A function of `coq-eglot-lsp-event-functions', after the session."
  (cond ((coq-eglot-lsp-progress-p event) (coq-eglot--progress event))
        ((coq-eglot-lsp-diagnostics-p event) (coq-eglot--diagnostics))
        ((and (coq-eglot-lsp-answer-p event)
              (coq-eglot--answer-valid-p event)
              (eq (coq-eglot-lsp-answer-goals event)
                  (coq-eglot--output-goals (coq-eglot--output))))
         ;; A second publication of the same answer may carry hypothesis
         ;; sorts that missed the initial display deadline.
         (coq-eglot--offer-late-context-compaction))))

(defun coq-eglot--stop-at-error (diag start &optional cancel)
  "Stop at DIAG, the first error of an operation starting at START.
With CANCEL, cancel the request of the running operation first."
  (let ((sentence (coq-eglot-lsp-diagnostic-sentence diag)))
    (when cancel
      (coq-eglot-lsp-cancel-request coq-eglot--work-context))
    (coq-eglot--stop)
    (if sentence
        (progn
          (when (< start (car sentence))
            (coq-eglot--trace-check start (car sentence) nil))
          (coq-eglot--fail (car sentence) (cdr sentence)
                           (coq-eglot-lsp-diagnostic-message diag)))
      ;; Document-level errors, such as an invalid filename, have no
      ;; sentence.  Keep the anchor and at least report their range.
      (coq-eglot--show-error (coq-eglot-lsp-diagnostic-message diag))
      (coq-eglot--highlight-error
       (coq-eglot-lsp-diagnostic-start diag)
       (coq-eglot-lsp-diagnostic-end diag)))))

(defun coq-eglot--known-error (start)
  "Stop at a valid error already known between START and the target.
Return non-nil if no operation should be sent."
  (let ((diag (coq-eglot-session-error start (coq-eglot-check-target))))
    (when diag
      (coq-eglot--stop-at-error diag start)
      t)))

(defun coq-eglot--diagnostics ()
  "Stop the running check immediately at its first recorded error.
The session observer ran first and recorded the latest valid diagnostic
snapshot.  Errors have their sentence range because the server is run
with `send_diags_extra_data'."
  (when (coq-eglot-session-working-p)
    (let* ((start coq-eglot--work-start)
           (diag (coq-eglot-session-error start (coq-eglot-check-target))))
      (when diag
        ;; The request can otherwise keep checking toward a distant target,
        ;; or never answer when that target is beyond the error.
        (coq-eglot--stop-at-error diag start t)))))

(defun coq-eglot--progress (progress)
  "The server checked the sentences up to the start of PROGRESS.
While an operation moves the proof position.
PROGRESS is a `coq-eglot-lsp-progress', ignored if no longer valid,
see `coq-eglot-session-valid-p'.  Move the proof position there, but
not past the target, nor past an error."
  (let ((pos (coq-eglot-lsp-progress-start progress)))
    (when (and (coq-eglot-session-working-p)
               (coq-eglot-session-valid-p
                (coq-eglot-lsp-progress-version progress) pos)
               (> pos (coq-eglot-position))
               (<= pos (coq-eglot-check-target))
               (not (coq-eglot-session-error-range (coq-eglot-position) pos)))
      (coq-eglot--set-position pos nil))))

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

(defun coq-eglot--compile-then (work start end continue)
  "Compile the libraries required between START and END, then CONTINUE.
For WORK, the running operation.  CONTINUE is called with nil, or with
the start of the first Require sentence whose compilation failed.  It
is called right away if there is nothing to compile, never if WORK is
cancelled meanwhile.  See `coq-eglot-compile-requires'.  If the
compilation signals an error, like a missing program, the check stops:
it is not left running without anything to wait for."
  (unless (condition-case err
              (coq-eglot-compile-requires
               start end
               (lambda (failed)
                 (when (coq-eglot-session-work-p work)
                   (funcall continue failed))))
            (error (when (coq-eglot-session-work-p work)
                     (coq-eglot--stop))
                   (signal (car err) (cdr err))))
    (funcall continue nil)))

(defun coq-eglot--compilation-failed (start)
  "Report that the compilation for the Require sentence at START failed."
  (coq-eglot--show-error
   (format "Compilation of the required libraries failed, see buffer %s."
           coq--compile-response-buffer))
  (coq-eglot--highlight-error start (coq-eglot--guess-end start)))

(defun coq-eglot--step (start)
  "Process the sentence starting at START, after the proof position.
Compile first the libraries it requires, if any.  First ask the server
to check the sentence without goals, then ask its goals: the long,
resumable verification and the short final presentation request are
therefore distinct, like for a distant target."
  (let ((work (coq-eglot--start-work start))
        (before (coq-eglot-position)))
    (coq-eglot--compile-then
     work start (1+ start)
     (lambda (failed)
       (if (not failed)
           ;; Inside the sentence: at the start of the buffer the server
           ;; finds no sentence.  `coq-eglot--advance-done' asks the final
           ;; goals after this lightweight check answers.
           (coq-eglot--check work before start (1+ start) nil)
         (coq-eglot--stop)
         (coq-eglot--compilation-failed failed))))))

(defun coq-eglot--advance (start target)
  "Process the sentences from START up to the one before TARGET.
The one containing the character before TARGET.
Asynchronously: the libraries required there are compiled, then the
server is asked to check up to it, without goals.  If a compilation
fails, the server checks up to the Require sentence."
  (let ((last (1- (coq-eglot--skip-backward target)))
        (work (coq-eglot--start-work start))
        (before (coq-eglot-position)))
    (coq-eglot--compile-then
     work start target
     (lambda (failed)
       (coq-eglot--check work before start
                         (if failed (1- (coq-eglot--skip-backward failed))
                           last)
                         failed)))))

(defun coq-eglot--check (work before start last failed)
  "Ask the server to check from START up to the sentence containing LAST.
For WORK, the running operation, started at proof position BEFORE.
FAILED is the start of a Require sentence after LAST whose compilation
failed, or nil.  It is reported after the check."
  (if (< last start)
      (progn
        (coq-eglot--stop)
        (coq-eglot--compilation-failed failed))
    (coq-eglot--send work #'coq-eglot-lsp-check-async last
                     (lambda (_checked)
                       (coq-eglot--advance-done work before start last
                                                failed)))))

(defun coq-eglot--advance-done (work before start last &optional failed)
  "The server checked from START up to the sentence containing LAST.
For WORK, the running operation, started at proof position BEFORE.
Ask the goals after the last sentence, without waiting: its range, and
an error the diagnostics did not report.  FAILED is the start of a
Require sentence after LAST whose compilation failed, reported if there
was no error before."
  (coq-eglot--send work #'coq-eglot-lsp-final-goals-async last
                   (lambda (answer)
                     (coq-eglot--advance-answered work before start last
                                                  failed answer))))

(defun coq-eglot--advance-answered (work before start last failed answer)
  "Finish WORK with ANSWER, the goals after the sentence containing LAST.
See `coq-eglot--advance-done'.  Stop at the first error."
  (let* ((bounds (and answer (coq-eglot-lsp-answer-sentence answer)))
         ;; an error may be located after LAST in this sentence
         (diag (coq-eglot-session-error
                start (max (1+ last) (if bounds (cdr bounds) 0))))
         (error (and diag (cons (coq-eglot-lsp-diagnostic-start diag)
                                (coq-eglot-lsp-diagnostic-end diag))))
         (sentence (and diag (coq-eglot-lsp-diagnostic-sentence diag))))
    (cond
     (sentence
      ;; the diagnostic says the sentence that failed and why: no request
      (coq-eglot-session-finish-work work)
      (coq-eglot--stop)
      (when (< start (car sentence))
        (coq-eglot--trace-check start (car sentence) nil))
      (coq-eglot--fail (car sentence) (cdr sentence)
                       (coq-eglot-lsp-diagnostic-message diag)))
     (error
      ;; the sentence that failed and its error message, not its goals
      (coq-eglot--send
       work #'coq-eglot-lsp-final-goals-async (car error)
       (lambda (answer)
         (coq-eglot-session-finish-work work)
         (coq-eglot--stop)
         (let ((bounds (or (and answer (coq-eglot-lsp-answer-sentence answer))
                           error)))
           (when (< start (car bounds))
             (coq-eglot--trace-check start (car bounds) nil))
           (coq-eglot--fail (car bounds) (cdr bounds)
                            (or (and answer (coq-eglot-lsp-answer-error answer))
                                "Error."))))))
     ;; an error the diagnostics did not report
     ((and bounds (coq-eglot-lsp-answer-error answer))
      (coq-eglot-session-finish-work work)
      (coq-eglot--stop)
      (when (< start (car bounds))
        (coq-eglot--trace-check start (car bounds) nil))
      (coq-eglot--fail (car bounds) (cdr bounds)
                       (coq-eglot-lsp-answer-error answer)))
     (t
      (coq-eglot-session-finish-work work)
      (when bounds
        (coq-eglot--trace-check start (cdr bounds) answer)
        (coq-eglot--set-position (cdr bounds) answer)
        (coq-eglot--show-answer answer))
      (if failed
          (progn (coq-eglot--stop)
                 (coq-eglot--compilation-failed failed))
        (coq-eglot--continue before))))))

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
  (let ((goals (and answer (coq-eglot-lsp-answer-goals answer))))
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
                            (coq-eglot-lsp-answer-messages answer)))
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
A sentence ending exactly at POS stays processed.  Display the goals.
Without waiting, see `coq-eglot--move-back'."
  (coq-eglot--trace-retract pos)
  (coq-eglot--move-back pos))

;;; Commands

(defun coq-eglot-assert-next-command ()
  "Process the next sentence.
During a check, the sentence after the part being checked, see
`coq-eglot--queue'."
  (interactive)
  (coq-eglot--with-script
    (if (not (coq-eglot-checking-p))
        (let ((start (coq-eglot--next-sentence-start)))
          (when start
            (coq-eglot--go (coq-eglot--guess-end start))))
      ;; the sentence after the part being checked
      (let ((start (coq-eglot--skip-forward (coq-eglot-check-target))))
        (when (< start (point-max))
          (coq-eglot--queue (coq-eglot--guess-end start)))))))

(defun coq-eglot-undo-last-command ()
  "Move the proof position back one sentence."
  (interactive)
  (coq-eglot--with-script
    (coq-eglot--check-busy)
    (let ((last (coq-eglot-session-last-sentence)))
      (when last
        (coq-eglot--retract
         (or (coq-eglot-session-sentence-start last)
             (car (coq-eglot-sentences-range-ending-at (overlay-end last)))
             (1- (overlay-end last))))))))

(defun coq-eglot-goto-point ()
  "Move the proof position to the sentence at point.
Process the sentences up to the one containing point, or move back to
the end of the last sentence before point.  During a check, only
forward, after the part being checked, see `coq-eglot--queue'."
  (interactive)
  (coq-eglot--with-script
    (cond
     ((coq-eglot-checking-p) (coq-eglot--queue (point)))
     ((< (point) (coq-eglot-position)) (coq-eglot--retract (point)))
     (t (coq-eglot--go (point))))))

(defun coq-eglot-process-buffer ()
  "Process the whole buffer, also during a check, see `coq-eglot--queue'."
  (interactive)
  (coq-eglot--with-script
    (if (coq-eglot-checking-p)
        (coq-eglot--queue (point-max))
      (coq-eglot--go (point-max)))))

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
  (coq-eglot--cancel-hyp-sorts)
  (coq-eglot-compile-cancel)
  (coq-eglot--stop)
  (coq-eglot-session-forget-requests)
  (coq-eglot-lsp-cancel-all))

(defvar-local coq-eglot--interrupting nil
  "Non-nil while the server did not answer since an interruption.
It may still be finishing a computation that cannot be interrupted.")

(defun coq-eglot--wait-interruption ()
  "Note that an interruption was sent, clear it when the server answers.
Send a cheap request: its answer, coming after the interruption, tells
that the server is ready again."
  (setq coq-eglot--interrupting t)
  (force-mode-line-update)
  (let ((buffer (current-buffer)))
    (coq-eglot-lsp-ping (lambda ()
                          (when (buffer-live-p buffer)
                            (with-current-buffer buffer
                              (setq coq-eglot--interrupting nil)
                              (force-mode-line-update)))))))

(defun coq-eglot-interrupt ()
  "Interrupt the running check and the requests in flight, without waiting.
Like the queries or the insertions waiting for their answer.  The proof
position stays where the server was.  If the server does not answer
since the last interruption, because it is finishing a computation that
cannot be interrupted, restart it: see `coq-eglot-restart-server'.
While the server connects, only forget what waits for it: the
connection goes on."
  (interactive)
  (coq-eglot--with-script
    (let ((checking (coq-eglot-checking-p)))
      (cond
       ;; even if requests are in flight, like the goals asked then
       (coq-eglot--interrupting (coq-eglot-restart-server))
       ((and (or checking (not (coq-eglot-session-settled-p)))
             (or (coq-eglot-lsp-connecting-p)
                 (not (coq-eglot-lsp-current-server))))
        ;; nothing sent yet: no ping, no goals, they would wait for the
        ;; connection again
        (coq-eglot--cancel)
        (message "Coq: %s" (if checking "interrupted" "request cancelled")))
       ((or checking (not (coq-eglot-session-settled-p)))
        (coq-eglot--cancel)
        (coq-eglot--wait-interruption)
        (when checking (coq-eglot--goals-at-position-async))
        (message "Coq: %s (%s again to restart the server if it stays busy)"
                 (if checking "interrupted" "request cancelled")
                 (substitute-command-keys "\\[coq-eglot-interrupt]")))
       (t (message "Coq: nothing to interrupt"))))))

(defun coq-eglot--forget-checks (buffers)
  "Forget the checks of BUFFERS, whose server stopped.
Their running checks, compilations and interruptions: no answer will
come.  Their proof positions stay."
  (dolist (buffer buffers)
    (when (buffer-live-p buffer)
      (with-current-buffer buffer
        (when coq-eglot-mode
          (coq-eglot--cancel-hyp-sorts)
          (coq-eglot-compile-cancel)
          (coq-eglot--stop)
          (coq-eglot-session-forget-requests)
          (setq coq-eglot--interrupting nil))))))

(defun coq-eglot-restart-server ()
  "Restart the server, even if it is busy.
The proof position and the kept goals stay: the text did not change.
The new server checks again the processed part when needed.  The
checks of all the buffers of the server stop."
  (interactive)
  (coq-eglot--with-script
    (coq-eglot--cancel)
    (coq-eglot--forget-checks (cons (current-buffer) (coq-eglot-lsp-shutdown)))
    ;; without waiting: the goals are asked once it is connected
    (coq-eglot-lsp-connect)
    (coq-eglot--goals-at-position-async)
    (message "Coq: server restarted")))

(defun coq-eglot-exit ()
  "Stop the server, like `proof-shell-exit' in Proof General.
The proof position goes back to the beginning in all the buffers the
server managed.  The next command starts a new server."
  (interactive)
  (coq-eglot--with-script
    (coq-eglot--cancel)
    (let ((buffers (cons (current-buffer) (coq-eglot-lsp-shutdown))))
      (coq-eglot--forget-checks buffers)
      (dolist (buffer buffers)
        (when (buffer-live-p buffer)
          (with-current-buffer buffer
            (when coq-eglot-mode
              (coq-eglot--set-position nil nil)
              (coq-eglot--clear-error))))))
    (setq coq-eglot--printing-flags nil)
    (coq-eglot--show-goals nil)
    (coq-eglot--show-response "")
    (message "Coq: server stopped")))

(defun coq-eglot-show-goals ()
  "Ask the server the goals at the proof position and display them."
  (interactive)
  (coq-eglot--with-script
    (coq-eglot--check-busy)
    (coq-eglot--goals-at-position t)))

(defun coq-eglot-show-at-point ()
  "Display the goals and messages after the sentence at point.
Only in the processed part, return nil elsewhere.  The proof position
does not move.  This is `coq-show-at-point-function' for the Eglot
backend, see `coq-Show'."
  (when (< (point) (coq-eglot-position))
    (coq-eglot--activate)
    (coq-eglot--check-busy)
    (coq-eglot--clear-error)
    ;; displayed when it comes, without waiting
    (coq-eglot--ask-goals (point) #'coq-eglot--show-answer)
    t))

(defun coq-eglot-goto-end-of-locked ()
  "Move point to the proof position.
In the goals and response buffers, go to the script buffer first."
  (interactive)
  (let ((buffer (coq-eglot-script-buffer)))
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

(defvar-local coq-eglot--after-edit-timer nil
  "Timer finishing the handling of an edition, or nil.
See `coq-eglot--after-edit-later'.")

(defun coq-eglot--user-edit-p ()
  "Non-nil if the user is editing the current buffer.
In a command, in the buffer of the selected window: not an edition by
a program from a timer or a process, like the revert of a buffer whose
file an agent wrote, nor by a command in another buffer."
  (and this-command
       (eq (current-buffer) (window-buffer (selected-window)))))

(defun coq-eglot--after-change (beg _end _len)
  "Move the proof position before the sentence edited at BEG.
Typing right at the proof position does not move it.  Editing the
processed part, or the part being checked, interrupts the server: all
pending requests are cancelled, and the edition is sent to the server
at the end of the command (not here, see `coq-eglot-lsp-send-changes'),
or right after it for an edition by a program, see
`coq-eglot--after-edit-later'.  The buffer becomes the one where the
user works if the user edits it, see `coq-eglot--user-edit-p'."
  (when (coq-eglot--user-edit-p)
    (setq coq-eglot--command-buffer (current-buffer)))
  (when (< beg (if (coq-eglot-checking-p)
                   (coq-eglot-check-target)
                 (coq-eglot-position)))
    (coq-eglot--cancel)
    (setq coq-eglot--interrupted t))
  (when (< beg (coq-eglot-position))
    ;; a sentence ending at BEG is edited too
    (coq-eglot--new-intent)
    (coq-eglot-session-forget-sentences (1- beg))
    (coq-eglot--update-overlays)
    (coq-eglot--clear-error)
    (setq coq-eglot--edited (min beg (or coq-eglot--edited beg))))
  (when (and (or coq-eglot--edited coq-eglot--interrupted)
             (not coq-eglot--after-edit-timer))
    ;; for the editions that no command of this buffer ends
    (setq coq-eglot--after-edit-timer
          (run-at-time 0 nil #'coq-eglot--after-edit-later
                       (current-buffer)))))

(defun coq-eglot--post-command ()
  "Finish the handling of an edition of the current buffer by the user.
At the end of the command, see `coq-eglot--after-edit'."
  (coq-eglot--after-edit t))

(defun coq-eglot--after-edit-later (buffer)
  "Finish the handling of an edition of BUFFER no command of it ended.
An edition by a program, or by a command in another buffer: BUFFER is
not made active, see `coq-eglot--after-edit'."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (setq coq-eglot--after-edit-timer nil)
      (when coq-eglot-mode
        (coq-eglot--after-edit nil)))))

(defun coq-eglot--after-edit (activate)
  "Display the goals after an edition moved back or interrupted.
Make the buffer the active one if ACTIVATE.  Never wait for the server
here: it may still be finishing an interrupted sentence.  The proof
position is first the end of the last known sentence before the
edition (see `coq-eglot--after-change').  The server is then asked
asynchronously for the last sentence before the edition, see
`coq-eglot--move-back'."
  (when (or coq-eglot--edited coq-eglot--interrupted)
    (when activate (coq-eglot--activate))
    (let ((beg coq-eglot--edited))
      (setq coq-eglot--edited nil coq-eglot--interrupted nil)
      ;; the server must work on the new text right now
      (coq-eglot-lsp-send-changes)
      (coq-eglot--wait-interruption)
      (if beg
          ;; a sentence ending at BEG is edited too
          (coq-eglot--move-back (1- beg))
        (coq-eglot--goals-at-position)))))

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

(defvar-local coq-eglot--query-results 0
  "Number of the last query sent by `coq-eglot-query-result'.")

(defun coq-eglot-query-result (command callback)
  "Run Coq COMMAND at the proof position, call CALLBACK with its answer.
Without waiting, display nothing.  With nil if Coq answers an error,
or outside of the processed part.  Not called if the answer is stale
when it comes: the proof position moved, or the text before it was
edited.  Nor if it is cancelled, like by \\[coq-eglot-interrupt].
The request is one of the session, see `coq-eglot-busy-p'.  This is
`coq-query-result-function' for the Eglot backend, used by the
insertions built from a query, like `coq-insert-intros'."
  (coq-eglot--with-script
    (let ((position (coq-eglot-position)))
      (if (<= position (point-min))
          (funcall callback nil)
        (let ((pos (1- position))
              (context nil))
          (unless (string-match-p "\\.[ \t\n]*\\'" command)
            (setq command (concat command ".")))
          (coq-eglot-session-ask
           (list 'query-result (cl-incf coq-eglot--query-results))
           (lambda (result)
             (when (and result
                        (= (coq-eglot-position) position)
                        (coq-eglot-session-valid-p
                         (coq-eglot-lsp-context-version context) pos))
               (pcase result
                 (`(messages . ,messages)
                  (funcall callback (string-join messages "\n")))
                 (`(failure . ,failure)
                  (unless (coq-eglot-lsp-failure-cancelled failure)
                    (funcall callback nil))))))
           (lambda (done)
             (setq context
                   (coq-eglot-lsp-query-async
                    pos command
                    (lambda (messages) (funcall done (cons 'messages messages)))
                    (lambda (failure)
                      (funcall done (cons 'failure failure))))))))))))

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

(defvar-local coq-eglot--last-query 0
  "Number of the last query sent: only its answer is displayed.")

(defun coq-eglot--query (command flags then)
  "Run Coq COMMAND after FLAGS, then THEN, see `coq-eglot-run-query'.
THEN is called with the messages, once displayed.  Only the answer of
the last query sent is displayed: an older one coming after it is
ignored.  The query is a request of the session, see
`coq-eglot-busy-p'."
  (when (<= (coq-eglot-position) (point-min))
    (user-error "Coq: process at least one sentence before a query"))
  ;; Do not let an old automatic goals refresh replace the explicit answer
  ;; in the shared output window just after it is displayed.
  (coq-eglot--cancel-width-refresh)
  (unless (string-match-p "\\.[ \t\n]*\\'" command)
    (setq command (concat command ".")))
  (let ((script (current-buffer))
        ;; the server runs all the sentences on a copy of the state
        (sentences (concat (let ((width (coq-eglot--query-printing-width)))
                             (if width (format "Set Printing Width %d. " width) ""))
                           (mapconcat (lambda (flag) (concat flag ". "))
                                      (append (coq-eglot--search-blacklist-commands)
                                              coq-eglot--printing-flags flags)
                                      "")
                           command)))
    (let ((number (cl-incf coq-eglot--last-query)))
      (coq-eglot-session-ask
       (list 'query number)
       (lambda (result)
         (when (= number coq-eglot--last-query)
           (pcase result
             (`(messages . ,messages)
              (with-current-buffer script
                (coq-eglot--trace-query command flags messages))
              (coq-eglot--show-response
               (coq-eglot--trim-lines (mapconcat #'identity messages "\n")))
              (unless messages (message "Coq: no output"))
              (when then (funcall then messages)))
             (`(failure . ,failure)
              ;; cancelled by an edition or a new check: nothing to tell
              (unless (coq-eglot-lsp-failure-cancelled failure)
                (coq-eglot--show-error
                 (coq-eglot-lsp-failure-message failure)))))))
       (lambda (done)
         ;; in the last processed sentence: the state after it
         (coq-eglot-lsp-query-async
          (1- (coq-eglot-position)) sentences
          (lambda (messages) (funcall done (cons 'messages messages)))
          (lambda (failure) (funcall done (cons 'failure failure)))))))))

;;; Double hit

(defun coq-eglot-terminator-insert (&optional count)
  "Insert the key typed, COUNT times, or process up to it on a double hit.
On a double hit, \".\" replaces the key.  See `proof-double-hit-enable'.
This is `coq-terminator-insert-function' for the Eglot backend, the key
is bound to `coq-terminator-insert'."
  (proof-double-hit-insert #'coq-eglot-goto-point count "."))

;;; Hover

(defun coq-eglot--hover-eldoc-function (callback &rest _args)
  "Ask the pseudo-server for Eldoc information through CALLBACK.
Only ask in the processed part.  The pseudo-server drops the hover if
another request is active instead of letting it interrupt useful work."
  (when (< (point) (coq-eglot-position))
    (and (coq-eglot-lsp-hover-async
          (point)
          (lambda (info echo) (funcall callback info :echo echo))
          (lambda (_failure) (funcall callback nil)))
         t)))

(defun coq-eglot--setup-eldoc ()
  "Replace the hover function of Eglot by `coq-eglot--hover-eldoc-function'.
Run when Eglot starts or stops managing the buffer."
  (when (eglot-managed-p)
    (setq-local eldoc-documentation-functions
                (cl-substitute #'coq-eglot--hover-eldoc-function
                               #'eglot-hover-eldoc-function
                               eldoc-documentation-functions))))

;;; Interface of the extensions
;;
;; What the extensions of the backend, the two Rocq mode and the
;; sandboxes (coq-eglot-twin.el, coq-eglot-sandbox.el), use of it, to
;; keep them away from its internals: the check running, the proof
;; position, the output of a script buffer, the buffer where the user
;; works.

(defun coq-eglot-busy-p ()
  "Non-nil if the current script buffer waits for the server.
A check runs, a request is in flight, or an interruption is not
answered yet: the opposite of at rest, see
`coq-eglot-session-settled-p'."
  (or (not (coq-eglot-session-settled-p))
      coq-eglot--interrupting
      (coq-eglot-lsp-connecting-p)))

(defun coq-eglot-checking-p ()
  "Non-nil if the server checks a part of the current script buffer.
The user asked to go further than the proof position, see
`coq-eglot-session-target'."
  (and (coq-eglot-session-target) t))

(defun coq-eglot-check-target ()
  "End of the part of the current script buffer being checked, or nil."
  (coq-eglot-session-target-end))

(defun coq-eglot-move-proof-position (target)
  "Move the proof position of the current script buffer to TARGET.
Forward or back, without making the buffer the one where the user
works, see `coq-eglot-working-buffer'.  During a check, only further
than the part being checked: return nil if TARGET is before its end,
non-nil otherwise."
  (cond
   ((coq-eglot-checking-p)
    (let ((end (coq-eglot-check-target)))
      (cond ((> target end) (coq-eglot--queue target) t)
            ((= target end) t))))
   ((< target (coq-eglot-position)) (coq-eglot--retract target) t)
   ((> target (coq-eglot-position)) (coq-eglot--go target) t)
   (t t)))

(defun coq-eglot-next-sentence-position (pos)
  "Position after the blanks and comments following POS."
  (coq-eglot--skip-forward pos))

(defun coq-eglot-processed-overlays ()
  "Overlays of the processed part and of the part being checked.
Those that are displayed, not empty."
  (seq-filter (lambda (overlay)
                (and (overlayp overlay) (overlay-buffer overlay)
                     (< (overlay-start overlay) (overlay-end overlay))))
              (list coq-eglot--locked-overlay coq-eglot--queue-overlay)))

(defun coq-eglot-working-buffer ()
  "The script buffer where the user works, or nil.
The one of the last command of the backend or of the last edition by
the user, if still live."
  (and (buffer-live-p coq-eglot--command-buffer) coq-eglot--command-buffer))

(defun coq-eglot-set-working-buffer (buffer)
  "Make BUFFER the script buffer where the user works."
  (setq coq-eglot--command-buffer buffer))

(defun coq-eglot-own-output-p ()
  "Non-nil if the current script buffer has an output of its own.
See `coq-eglot-give-own-output'."
  (and coq-eglot--buffer-output t))

(defun coq-eglot-give-own-output (suffix)
  "Give the current script buffer an output of its own.
Its goals and messages are displayed in buffers named with SUFFIX,
like \"*goals*SUFFIX\", at the same time as the ones of the other
script buffers.  See `coq-eglot-share-output'."
  ;; it leaves the output it shared
  (coq-eglot--forget-active)
  (setq coq-eglot--buffer-output (coq-eglot--make-output suffix))
  (coq-eglot--update-overlays))

(defun coq-eglot-share-output ()
  "Give the current script buffer the output of the other ones back.
The buffers of its own output are killed, see
`coq-eglot-give-own-output'."
  (when coq-eglot--buffer-output
    (dolist (name (list (coq-eglot--goals-name)
                        (coq-eglot--conclusion-name)
                        (coq-eglot--response-name)))
      (let ((output (get-buffer name)))
        (when output
          (coq-eglot--delete-windows name)
          (kill-buffer output))))
    (setq coq-eglot--buffer-output nil)
    (coq-eglot--update-overlays)))

(defun coq-eglot-output-buffers ()
  "The goals, conclusion and response buffers of the current script buffer.
A list of three, each a buffer or nil: the conclusion only if
`coq-eglot-split-goals'."
  (mapcar (lambda (name) (and name (get-buffer name)))
          (list (coq-eglot--goals-name)
                (and coq-eglot-split-goals (coq-eglot--conclusion-name))
                (coq-eglot--response-name))))

(defun coq-eglot-display-script (buffer)
  "Display the output of script BUFFER, in the selected window.
BUFFER becomes the active script buffer of its output, its goals and
messages windows are laid out."
  (with-current-buffer buffer
    (coq-eglot--activate)
    (coq-eglot-layout-windows)))

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
  "C-c C-o" #'coq-eglot-display-some-buffers
  "C-c C-." #'coq-eglot-goto-end-of-locked
  "C-c C-v" #'coq-eglot-query)

;; like in Proof General, in the goals buffer only
(coq-hyps-define-keys coq-eglot-goals-mode-map)

(easy-menu-define coq-eglot-menu coq-eglot-mode-map
  "Menu of the Eglot backend of Coq."
  coq-eglot--menu-spec)

(defconst coq-eglot-all-buffers-commands
  '(coq-eglot-assert-next-command
    coq-eglot-undo-last-command
    coq-eglot-process-buffer
    coq-eglot-retract-buffer
    coq-eglot-interrupt
    coq-eglot-exit
    coq-eglot-show-goals
    coq-eglot-layout-windows
    coq-eglot-display-some-buffers
    coq-eglot-toggle-compact-contexts
    coq-eglot-goto-end-of-locked
    coq-eglot-query
    coq-toggle-highlight-hyp-at-point)
  "Commands of the Eglot backend valid in the goals and response buffers.
Their bindings in `coq-mode-map', those of the user, also apply in the
goals and response buffers, see `coq-all-buffers-keymap'.  Like in
Proof General, highlighting a hypothesis depends on point in the current
buffer, not in the script.")

(defun coq-eglot--set-output-keys ()
  "Set the parent of the keymap of the goals and response buffers.
The keys of the backend, `coq-eglot-mode-map', then those of
`coq-all-buffers-keymap': the queries, the display, C-c C-a C-r and
C-c C-a C-g, and the bindings of the user in `coq-mode-map' for these
commands and `coq-eglot-all-buffers-commands'.  Called each time such a
buffer is set up, after the configuration of the user."
  (set-keymap-parent coq-eglot-output-mode-map
                     (make-composed-keymap
                      coq-eglot-mode-map
                      (coq-all-buffers-keymap
                       coq-eglot-all-buffers-commands))))

(coq-eglot--set-output-keys)

;; The queries at mouse click, see `coq-remap-mouse-1'.
(coq-mouse-query-add-keymap coq-eglot-output-mode-map)

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
        ;; the observers of the events of the server: the session and
        ;; the bounds of the sentences, then the interface
        (coq-eglot-session-start #'coq-eglot-lsp-version)
        (add-hook 'coq-eglot-lsp-event-functions #'coq-eglot--observe 90 t)
        (setq coq-eglot-session-sentence-start-function
              #'coq-eglot--next-sentence-start-after)
        (setq coq-eglot-sentences-start-function
              #'coq-eglot--next-sentence-start-after)
        (setq coq-eglot-session-sentence-end-function #'coq-eglot--guess-end)
        ;; the server opens the document again, from version 0
        (add-hook 'eglot-managed-mode-hook #'coq-eglot-session-reset nil t)
        (add-hook 'coq-eglot-session-state-hook #'force-mode-line-update nil t)
        (setq coq-terminator-insert-function #'coq-eglot-terminator-insert)
        (setq coq-query-function #'coq-eglot-run-query)
        (setq coq-query-result-function #'coq-eglot-query-result)
        (setq coq-ask-printing-width-function #'coq-eglot-ask-printing-width)
        (setq coq-set-flag-function #'coq-eglot-set-flag)
        (setq coq-set-search-blacklist-function #'coq-eglot-set-search-blacklist)
        (setq coq-show-at-point-function #'coq-eglot-show-at-point)
        (setq coq-processed-end-function #'coq-eglot-position)
        (add-hook 'project-find-functions #'coq-eglot-lsp-project nil t)
        (add-hook 'eglot-managed-mode-hook #'coq-eglot--setup-eldoc nil t)
        (add-hook 'eglot-managed-mode-hook #'coq-eglot-lsp-check-load-path nil t)
        (add-hook 'after-change-functions #'coq-eglot--after-change nil t)
        (add-hook 'post-command-hook #'coq-eglot--post-command nil t)
        (add-hook 'kill-buffer-hook #'coq-eglot--on-kill nil t)
        (coq-eglot--update-overlays)
        (coq-eglot--layout-on-visit))
    (remove-hook 'coq-eglot-lsp-event-functions #'coq-eglot--observe t)
    (kill-local-variable 'coq-terminator-insert-function)
    (kill-local-variable 'coq-query-function)
    (kill-local-variable 'coq-query-result-function)
    (kill-local-variable 'coq-ask-printing-width-function)
    (kill-local-variable 'coq-set-flag-function)
    (kill-local-variable 'coq-set-search-blacklist-function)
    (kill-local-variable 'coq-show-at-point-function)
    (kill-local-variable 'coq-processed-end-function)
    (remove-hook 'project-find-functions #'coq-eglot-lsp-project t)
    (remove-hook 'eglot-managed-mode-hook #'coq-eglot--setup-eldoc t)
    (remove-hook 'eglot-managed-mode-hook #'coq-eglot-session-reset t)
    (remove-hook 'coq-eglot-session-state-hook #'force-mode-line-update t)
    (remove-hook 'eglot-managed-mode-hook #'coq-eglot-lsp-check-load-path t)
    (remove-hook 'after-change-functions #'coq-eglot--after-change t)
    (remove-hook 'post-command-hook #'coq-eglot--post-command t)
    (remove-hook 'kill-buffer-hook #'coq-eglot--on-kill t)
    (coq-eglot--forget-active)
    (coq-eglot--cancel)
    (coq-eglot--set-position nil nil)
    (coq-eglot-session-stop)
    (coq-eglot--clear-error)))

(defun coq-eglot-setup ()
  "Set up the current `coq-mode' buffer for the Eglot backend."
  (coq-eglot-mode 1)
  (eglot-ensure))

(autoload 'coq-eglot-twin-pair "coq-eglot-twin" nil t)
(autoload 'coq-eglot-twin-unpair "coq-eglot-twin" nil t)
(autoload 'coq-eglot-twin-layout "coq-eglot-twin" nil t)
(autoload 'coq-eglot-twin-set-opam-switch "coq-eglot-twin" nil t)
(autoload 'coq-eglot-twin-goto-twin-position "coq-eglot-twin" nil t)
(autoload 'coq-eglot-twin-toggle-synchronize "coq-eglot-twin" nil t)
(autoload 'coq-eglot-twin-swap-reference "coq-eglot-twin" nil t)

(provide 'coq-eglot)

;;; coq-eglot.el ends here
