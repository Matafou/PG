;;; coq-eglot-output.el --- Where the Eglot backend displays goals and messages  -*- lexical-binding:t -*-

;; This file is part of Proof General.

;; Portions © Copyright 2026  Pierre Courtieu

;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;;
;; The output of the script buffers: where they display their goals and
;; messages.  Its state, `coq-eglot--output': the active script buffer,
;; the goals displayed and their printing width.  Its buffers, goals,
;; conclusion and response, and their windows, laid out like in Proof
;; General: in three windows, two, or frames of their own, each one as
;; high as it needs.
;;
;; The modes of these buffers, and the commands laying out the windows
;; again, are in coq-eglot.el: they use the commands of the backend.

;;; Code:

(require 'cl-lib)
(require 'seq)
(require 'coq-goals)                    ; folding the other goals
(require 'coq-eglot-goals)              ; folding their hypotheses

(defvar coq-eglot-mode)
(defvar coq-eglot-split-goals)
(defvar coq-eglot--twin)
(declare-function coq-eglot-goals-mode "coq-eglot" ())
(declare-function coq-eglot-response-mode "coq-eglot" ())

;;; The output

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

(defun coq-eglot--twin-layout-p ()
  "Non-nil if the active script buffer of the current output has a twin.
Then its goals and messages have windows of their own below it, see
`coq-eglot-twin-layout'."
  (let ((active (coq-eglot--active-buffer)))
    (and (buffer-live-p active)
         (buffer-live-p (buffer-local-value 'coq-eglot--twin active)))))

;;; Windows

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

;;; Contents and heights

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

(provide 'coq-eglot-output)

;;; coq-eglot-output.el ends here
