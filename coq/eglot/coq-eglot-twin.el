;;; coq-eglot-twin.el --- Two Rocq: two script buffers side by side  -*- lexical-binding:t -*-

;; This file is part of Proof General.

;; Portions © Copyright 2026  Pierre Courtieu

;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;;
;; The two Rocq mode of the Eglot backend: two script buffers, one
;; supposedly a modification of the other, checked at the same time,
;; side by side.  The typical use is the repair of a development for a
;; new version of Rocq: the reference in a worktree, the repaired copy
;; in another one, each checked by its Rocq, see `coq-eglot-set-rocq'.
;;
;; The server of each twin is the one of its project (see
;; `coq-eglot-lsp-project'): twins in two projects, like two
;; worktrees, are checked at the same time.  Twins in the same project
;; share a server, unless the twin gets one of its own, see "The Rocq
;; of the twins" below.
;;
;; Each twin displays its goals and messages in its own output (see
;; `coq-eglot--output'): both are active at the same time.  The layout
;; puts each script above its goals and messages, in two columns.
;;
;; The sentences of the twins are aligned, their diverging sentences
;; highlighted, and in them the words that differ, comments and blanks
;; ignored.  The proof position of the one the user works in,
;; the leader, is followed by the other one, see
;; `coq-eglot-twin-synchronize'.  When their positions correspond, their
;; goals and messages are compared.
;;
;; The differences are highlighted like the diffs of Coq, see
;; `coq-diffs-added-face', so like `diff-mode' and Magit: removed in
;; one twin, the reference, added in the other one.  Their faces inherit
;; from those, their colors come from the theme.

;;; Code:

(require 'cl-lib)
(require 'subr-x)
(require 'pg-lcs)                        ; the alignment of sentences
(require 'coq-indent)                   ; coq-script-parse-cmdend-forward
(require 'diff-mode)                    ; the faces of the diffs
(require 'coq-db)                       ; the faces of the diffs of Coq
(require 'coq-eglot)
(require 'coq-eglot-servers)              ; the Rocq of the twins

;;; The twins
;;
;; Each twin points to the other one, see `coq-eglot--twin', and both
;; share a `coq-eglot-twin--twins': which one is the reference, their
;; alignment, the timers of the pair.

(cl-defstruct (coq-eglot-twin--twins
               (:constructor coq-eglot-twin--make-twins (this other)))
  "Two twins and what they share.
THIS is the buffer `coq-eglot-twin-pair' was called in, OTHER the one
paired with it, with an output of its own, see
`coq-eglot-give-own-output'.  REFERENCE is the twin of reference, see
`coq-eglot-twin-swap-reference'.  ALIGNMENT is the alignment of their
sentences, see `coq-eglot-twin--align'.  HIGHLIGHT-TIMER and
COMPARE-TIMER update their highlighting and compare their outputs, see
`coq-eglot-twin--once'.  TWO-SERVERS is non-nil if OTHER, in the
project of THIS, has a server of its own even with the same Rocq, see
`coq-eglot-twin-toggle-two-servers'."
  this other reference alignment highlight-timer compare-timer two-servers)

(defvar-local coq-eglot-twin--twins nil
  "The twins of the current script buffer, a `coq-eglot-twin--twins', or nil.
The same in both twins.")
(put 'coq-eglot-twin--twins 'permanent-local t)

(defun coq-eglot-twin--link (this other)
  "Make THIS and OTHER twins, OTHER the reference.  Return their twins.
See `coq-eglot-twin--twins'."
  (let ((twins (coq-eglot-twin--make-twins this other)))
    (setf (coq-eglot-twin--twins-reference twins) other)
    (with-current-buffer this
      (setq coq-eglot--twin other
            coq-eglot-twin--twins twins))
    (with-current-buffer other
      (setq coq-eglot--twin this
            coq-eglot-twin--twins twins))
    twins))

(defun coq-eglot-twin--live-p (twins)
  "Non-nil if TWINS are still paired: both live, none unpaired."
  (and twins
       (let ((this (coq-eglot-twin--twins-this twins))
             (other (coq-eglot-twin--twins-other twins)))
         (and (buffer-live-p this) (buffer-live-p other)
              (eq (buffer-local-value 'coq-eglot-twin--twins this) twins)
              (eq (buffer-local-value 'coq-eglot-twin--twins other) twins)))))

(defun coq-eglot-twin--reference-p (&optional buffer)
  "Non-nil if BUFFER, by default the current one, is the twin of reference."
  (let* ((buffer (or buffer (current-buffer)))
         (twins (buffer-local-value 'coq-eglot-twin--twins buffer)))
    (and twins (eq (coq-eglot-twin--twins-reference twins) buffer))))

(defun coq-eglot-twin--script-and-twin ()
  "The script buffer of the command and its twin, (THIS . TWIN).
A user error if it has none."
  (let* ((this (coq-eglot-script-buffer))
         (twin (buffer-local-value 'coq-eglot--twin this)))
    (unless (buffer-live-p twin)
      (user-error "Coq: this buffer has no twin, see `coq-eglot-twin-pair'"))
    (cons this twin)))

(defmacro coq-eglot-twin--once (place timer)
  "Set PLACE to TIMER, a form starting a timer, unless PLACE has one.
To do something once after several events: the function of the timer
sets PLACE to nil first."
  (declare (debug (gv-place form)))
  `(unless ,place (setf ,place ,timer)))

(defmacro coq-eglot-twin--cancel (place)
  "Cancel the timer in PLACE, if any, and set PLACE to nil."
  (declare (debug (gv-place)))
  `(when ,place
     (cancel-timer ,place)
     (setf ,place nil)))

(defun coq-eglot-twin--update-label ()
  "Set the label of the server of the current buffer in the mode line.
See `coq-eglot--twin-label'."
  (setq coq-eglot--twin-label
        (ignore-errors
          ;; an absolute file name: its opam switch
          (coq-eglot-servers-label (coq-eglot-lsp-rocq))))
  (force-mode-line-update))

(defun coq-eglot-twin--candidates ()
  "Script buffers of the Eglot backend that can be the twin of this one."
  (seq-filter (lambda (buffer)
                (and (not (eq buffer (current-buffer)))
                     (buffer-local-value 'coq-eglot-mode buffer)
                     (not (buffer-local-value 'coq-eglot--twin buffer))))
              (buffer-list)))

(defun coq-eglot-twin--read-buffer ()
  "Ask a script buffer to pair with the current one."
  (let ((candidates (mapcar #'buffer-name (coq-eglot-twin--candidates))))
    (unless candidates
      (user-error "Coq: no other script buffer to pair with, visit it first"))
    (get-buffer (completing-read "Twin script buffer: " candidates nil t
                                 nil nil (car candidates)))))

(defun coq-eglot-twin-pair (other)
  "Pair the current script buffer with OTHER, its twin, side by side.
Both display their goals and messages at the same time: OTHER gets an
output of its own, see `coq-eglot--output', whose buffers are named
after it, like \"*goals*<OTHER>\".  The windows are laid out again, see
`coq-eglot-twin-layout'.  Killing one of them unpairs them, see
`coq-eglot-twin-unpair'.  OTHER is the reference: its differences are
highlighted as removed, see `coq-eglot-twin-swap-reference'.  Each one
is checked by the Rocq of its project, see `coq-eglot-set-rocq'; in the
same project, by the same server, unless OTHER gets another one, see
`coq-eglot-twin-set-rocq' and `coq-eglot-twin-toggle-two-servers'."
  (interactive
   (with-current-buffer (coq-eglot-script-buffer)
     (when coq-eglot--twin
       (user-error "Coq: this buffer has a twin already, %s"
                   (buffer-name coq-eglot--twin)))
     (list (coq-eglot-twin--read-buffer))))
  (let ((this (coq-eglot-script-buffer)))
    (when (eq this other)
      (user-error "Coq: a buffer cannot be its own twin"))
    (unless (buffer-local-value 'coq-eglot-mode other)
      (user-error "Coq: %s is not a script buffer of the Eglot backend"
                  (buffer-name other)))
    (when (or (buffer-local-value 'coq-eglot--twin this)
              (buffer-local-value 'coq-eglot--twin other))
      (user-error "Coq: unpair first, see `coq-eglot-twin-unpair'"))
    (with-current-buffer other
      (coq-eglot-give-own-output (format "<%s>" (buffer-name other))))
    (coq-eglot-twin--link this other)
    (dolist (side (list this other))
      (with-current-buffer side
        (add-hook 'kill-buffer-hook #'coq-eglot-twin--on-kill nil t)
        (add-hook 'coq-eglot-server-changed-hook
                  #'coq-eglot-twin--update-label nil t)
        (coq-eglot-twin--update-label)))
    (coq-eglot-twin--start-alignment other)
    (coq-eglot-twin--start-alignment this)
    (coq-eglot-twin-layout)
    (message "Coq: %s and %s are twins%s"
             (buffer-name this) (buffer-name other)
             (if (coq-eglot-twin--same-project-p this other)
                 ", in the same project: checked one after the other by \
one server, see Two Servers in the menu"
               ""))))

;;; The Rocq of the twins
;;
;; Each twin is checked by the Rocq of its project, see
;; `coq-eglot-set-rocq'.  Twins in two projects, like two worktrees,
;; have two servers, which check them at the same time.  Twins in the
;; same project share its server, which checks them one after the
;; other.  Then OTHER, the twin with an output of its own, may get a
;; server of its own, see `coq-eglot-lsp-own-rocq': with the same
;; Rocq, faster but one more server in memory, see
;; `coq-eglot-twin-toggle-two-servers'; or with another Rocq, if it
;; requires no library of the project, compiled by the Rocq of the
;; project only, see `coq-eglot-twin-set-rocq'.  Unpaired, it shares
;; the server of its project again.

(defun coq-eglot-twin--same-project-p (this other)
  "Non-nil if THIS and OTHER are in the same project.
Then they share its server, unless OTHER has one of its own."
  (equal (with-current-buffer this (coq-eglot-lsp-project-id))
         (with-current-buffer other (coq-eglot-lsp-project-id))))

(defun coq-eglot-twin--set-own-server (rocq)
  "Give the current buffer, a twin, a server of its own with ROCQ.
ROCQ is a Rocq program.  Or share again the server of its project if
ROCQ is nil.  Confirm if its proof position goes back to its beginning.
Do nothing if it already has this server."
  (unless (if rocq
              (coq-eglot-lsp-same-rocq-p rocq coq-eglot-lsp-own-rocq)
            (null coq-eglot-lsp-own-rocq))
    (coq-eglot-servers-confirm-restart
     (list (current-buffer))
     (or rocq (coq-eglot-lsp-default-rocq)))
    (coq-eglot-change-server
     (lambda () (setq coq-eglot-lsp-own-rocq rocq)))))

(defun coq-eglot-twin--check-requires (buffer rocq)
  "Signal a user error if BUFFER cannot be checked by ROCQ.
In the project of its twin, another Rocq than the one of the project
cannot load its libraries, see `coq-eglot-compile-local-requires'."
  (with-current-buffer buffer
    (when-let ((require (car (coq-eglot-compile-local-requires))))
      (user-error "Coq: %s requires libraries of its project at line %d: \
they are compiled for the Rocq of the project, %s cannot load them.  \
Change the Rocq of the whole project instead, see `coq-eglot-set-rocq'"
                  (buffer-name) (line-number-at-pos (car require))
                  (coq-eglot-servers-label rocq)))))

(defun coq-eglot-twin-set-rocq (rocq &optional buffer)
  "Check BUFFER, a twin, with ROCQ, a Rocq program.
BUFFER defaults to the twin with an output of its own.  In another
project than its twin, the Rocq of its project changes, see
`coq-eglot-set-rocq'.  In the same project, it gets a server of its
own, see `coq-eglot-twin--set-own-server': with another Rocq, only if
it requires no library of the project.  Choosing the Rocq of the
project again, it shares its server again, unless Two Servers is on,
see `coq-eglot-twin-toggle-two-servers'.  Interactively, ask ROCQ
among the candidates, see `coq-eglot-servers-candidates'."
  (interactive
   (let ((twin (coq-eglot-twin--twins-other
                (buffer-local-value
                 'coq-eglot-twin--twins
                 (car (coq-eglot-twin--script-and-twin))))))
     (list (with-current-buffer twin
             (coq-eglot-servers-read
              (format "Rocq of %s: " (buffer-name twin))
              (ignore-errors (coq-eglot-lsp-rocq))))
           twin)))
  (coq-eglot-servers-check rocq)
  (let* ((twins (buffer-local-value
                 'coq-eglot-twin--twins
                 (or buffer (car (coq-eglot-twin--script-and-twin)))))
         (this (coq-eglot-twin--twins-this twins))
         (other (coq-eglot-twin--twins-other twins))
         (buffer (or buffer other)))
    (cond
     ((not (coq-eglot-twin--same-project-p this other))
      (with-current-buffer buffer
        (coq-eglot-servers-set-project-rocq rocq)))
     ;; THIS shares the server of the project: the Rocq of the project
     ((eq buffer this)
      (with-current-buffer this
        (coq-eglot-servers-set-project-rocq rocq)))
     ((coq-eglot-lsp-same-rocq-p
       rocq (with-current-buffer other (coq-eglot-lsp-default-rocq)))
      (with-current-buffer other
        (coq-eglot-twin--set-own-server
         (and (coq-eglot-twin--twins-two-servers twins) rocq))))
     (t
      (coq-eglot-twin--check-requires other rocq)
      (with-current-buffer other
        (coq-eglot-twin--set-own-server rocq))))
    (with-current-buffer buffer
      (message "Coq: %s is checked by %s%s"
               (buffer-name)
               (coq-eglot-servers-describe (coq-eglot-servers-label rocq) rocq)
               (if coq-eglot-lsp-own-rocq ", with a server of its own" "")))))

(defun coq-eglot-twin-toggle-two-servers ()
  "Give the twin a server of its own, or share the server of its project.
Only for twins in the same project, otherwise they have two servers
already.  With two servers, the twins are checked at the same time,
but one more server uses memory.  With another Rocq for the twin, two
servers are needed, see `coq-eglot-twin-set-rocq'."
  (interactive)
  (let* ((twins (buffer-local-value 'coq-eglot-twin--twins
                                    (car (coq-eglot-twin--script-and-twin))))
         (this (coq-eglot-twin--twins-this twins))
         (other (coq-eglot-twin--twins-other twins)))
    (unless (coq-eglot-twin--same-project-p this other)
      (user-error "Coq: the twins are in two projects, they have two servers"))
    (with-current-buffer other
      (if (coq-eglot-twin--twins-two-servers twins)
          (progn
            (when (coq-eglot-lsp-foreign-p)
              (user-error "Coq: %s is checked by another Rocq, it needs \
a server of its own" (buffer-name)))
            (coq-eglot-twin--set-own-server nil)
            (setf (coq-eglot-twin--twins-two-servers twins) nil)
            (message "Coq: the twins share one server, which checks them \
one after the other"))
        (unless coq-eglot-lsp-own-rocq
          (coq-eglot-twin--set-own-server (coq-eglot-lsp-default-rocq)))
        (setf (coq-eglot-twin--twins-two-servers twins) t)
        (message "Coq: %s has a server of its own: the twins are checked \
at the same time, one more server uses memory" (buffer-name))))))

(defun coq-eglot-twin-two-servers-p ()
  "Non-nil if the twins of the current buffer, in one project, have two servers."
  (let ((twins coq-eglot-twin--twins))
    (and twins
         (buffer-live-p (coq-eglot-twin--twins-other twins))
         (buffer-local-value 'coq-eglot-lsp-own-rocq
                             (coq-eglot-twin--twins-other twins))
         t)))

(defun coq-eglot-twin--rocq-menu (_items)
  "Submenu choosing the Rocq of the twin, a :filter of `easy-menu-define'.
See `coq-eglot-twin-set-rocq'."
  (let* ((this (ignore-errors (coq-eglot-script-buffer)))
         (twins (and this (buffer-local-value 'coq-eglot-twin--twins this)))
         (other (and twins (coq-eglot-twin--twins-other twins))))
    (if (not (buffer-live-p other))
        (list ["No twin" ignore :active nil])
      (with-current-buffer other
        (coq-eglot-servers-menu-items
         (ignore-errors (coq-eglot-lsp-rocq))
         (lambda (rocq) (coq-eglot-twin-set-rocq rocq other)))))))

(defun coq-eglot-twin--forget (buffer)
  "Forget the twin of BUFFER, in BUFFER only."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (setq coq-eglot--twin nil
            coq-eglot--twin-label nil
            coq-eglot-twin--twins nil)
      (remove-hook 'kill-buffer-hook #'coq-eglot-twin--on-kill t)
      (remove-hook 'coq-eglot-server-changed-hook
                   #'coq-eglot-twin--update-label t))))

(defvar coq-eglot-twin--dying nil
  "The buffer being killed, while it is unpaired.")

(defun coq-eglot-twin--unpair (buffer)
  "Unpair BUFFER and its twin.
The one with an output of its own goes back to the default output, the
buffers of its output are killed."
  (let* ((twin (buffer-local-value 'coq-eglot--twin buffer))
         (twins (buffer-local-value 'coq-eglot-twin--twins buffer))
         (side (and twins (coq-eglot-twin--twins-other twins))))
    (when twins
      (coq-eglot-twin--cancel (coq-eglot-twin--twins-highlight-timer twins))
      (coq-eglot-twin--cancel (coq-eglot-twin--twins-compare-timer twins)))
    (when (buffer-live-p side)
      (with-current-buffer side
        (coq-eglot-share-output)
        ;; the exception of the twins: back to the server of its project
        (when coq-eglot-lsp-own-rocq
          (if (eq side coq-eglot-twin--dying)
              ;; its own server stops with it
              (coq-eglot-lsp-detach)
            (coq-eglot-change-server
             (lambda () (setq coq-eglot-lsp-own-rocq nil)))
            (message "Coq: %s is checked again by the server of its project"
                     (buffer-name))))))
    (coq-eglot-twin--stop-alignment buffer)
    (coq-eglot-twin--stop-alignment twin)
    (coq-eglot-twin--forget buffer)
    (coq-eglot-twin--forget twin)))

(defun coq-eglot-twin-unpair ()
  "Unpair the current script buffer and its twin.
See `coq-eglot-twin-pair'.  Its twin goes back to the shared output, its
goals and messages buffers are killed."
  (interactive)
  (pcase-let ((`(,this . ,twin) (coq-eglot-twin--script-and-twin)))
    (coq-eglot-twin--unpair this)
    (message "Coq: %s and %s are no longer twins"
             (buffer-name this) (buffer-name twin))))

(defun coq-eglot-twin--on-kill ()
  "Unpair the buffer being killed and its twin."
  (when coq-eglot--twin
    (let ((coq-eglot-twin--dying (current-buffer)))
      (coq-eglot-twin--unpair (current-buffer)))))

(defun coq-eglot-twin-layout ()
  "Display the twins side by side, each above its goals and messages.
The current script buffer on the left, its twin on the right, in the
selected frame.  Each one displays its goals and messages below it, in
windows of their own: in the twin mode, the goals and messages windows
are laid out like with `proof-three-window-enable' and the policy
vertical, see `coq-eglot--twin-layout-p'."
  (interactive)
  (pcase-let ((`(,this . ,twin) (coq-eglot-twin--script-and-twin)))
    (select-window (or (get-buffer-window this) (selected-window)))
    (set-window-dedicated-p (selected-window) nil)
    (delete-other-windows)
    (let ((left (selected-window))
          (right (split-window nil nil 'right)))
      (set-window-buffer left this)
      (set-window-buffer right twin)
      (mapc #'coq-eglot-display-script (list this twin))
      (select-window left))))

;;; Alignment of the sentences of the twins
;;
;; The sentences of each buffer are delimited locally, like the
;; compilation before Require does: the server may not have checked
;; them.  Their texts are normalized, without comments and with blanks
;; compacted, then compared: a longest common subsequence of the two
;; lists of sentences pairs the sentences that did not change, the
;; anchors.  The others make the diverging zones, highlighted like a
;; diff, blended with the processed part, see
;; `coq-eglot-twin--update-blend'.  A
;; position of one twin has a position in the other: the same offset in
;; the paired sentence, or the end of the last anchor before a
;; diverging zone, see `coq-eglot-twin-position'.
;;
;; The alignment is computed again when needed, if one of the buffers
;; changed, and when idle after a change to update the highlighting.

(defface coq-eglot-twin-removed
  '((t :inherit coq-diffs-removed-bg-face :extend nil))
  "Face of the diverging sentences of the twin of reference.
And of the different lines of its goals and messages.  Like the diffs
of Coq, see `coq-diffs-removed-bg-face', so like `diff-removed'.  Not
extended to the end of the line: the processed part remains visible.
See `coq-eglot-twin-swap-reference'."
  :group 'coq-eglot)

(defface coq-eglot-twin-added
  '((t :inherit coq-diffs-added-bg-face :extend nil))
  "Face of the diverging sentences of the twin that is not the reference.
And of the different lines of its goals and messages.  Like the diffs
of Coq, see `coq-diffs-added-bg-face', so like `diff-added'.  Not
extended to the end of the line: the processed part remains visible.
See `coq-eglot-twin-swap-reference'."
  :group 'coq-eglot)

(defcustom coq-eglot-twin-max-differences 1000
  "Maximal number of different sentences the alignment looks for.
Beyond, after their common beginning and end, the twins are considered
different: aligning them would take too long."
  :type 'natnum
  :group 'coq-eglot)

(defcustom coq-eglot-twin-max-refine-characters 8000
  "Maximal combined size of two diverging zones refined word by word.
Larger zones keep their sentence-level highlighting.  Refinement repeatedly
checks syntax to exclude comments, which is disproportionately expensive for
a single command spanning hundreds of lines."
  :type 'natnum
  :group 'coq-eglot)

(defcustom coq-eglot-twin-idle-delay 1.0
  "Seconds after the last edit before updating the twin highlighting.
Every new change restarts this debounce delay.  The update reparses the
changed script and realigns the twins, so it should not interrupt typing."
  :type 'number
  :group 'coq-eglot)

(cl-defstruct (coq-eglot-twin--sentence
               (:constructor coq-eglot-twin--make-sentence (start end text)))
  "A sentence of a script buffer: its bounds and its normalized text."
  start end text)

(defvar-local coq-eglot-twin--sentences nil
  "The sentences of the buffer, (TICK . VECTOR), or nil.
TICK is the `buffer-chars-modified-tick' they were computed at.")

(defvar-local coq-eglot-twin--sentences-dirty-start nil
  "Earliest position changed since `coq-eglot-twin--sentences' was computed.
Sentences ending there or before are intact and can be reused.  In particular,
after an ordinary user edit this includes the whole locked region.")

(defvar-local coq-eglot-twin--sentences-dirty-end nil
  "Marker after the latest changed region since the sentence cache was made.
Together with `coq-eglot-twin--sentences-dirty-start', it bounds the part that
must be reparsed.  The markers follow later edits, so unchanged cached
sentences after this marker can be recognized and reused.")

(defvar-local coq-eglot-twin--sentences-buffer-size nil
  "Buffer size when `coq-eglot-twin--sentences' was computed.
The difference with the current size shifts cached sentences after all edits.")

(defun coq-eglot-twin--normalize (start end)
  "Text of the region START..END without comments, blanks compacted."
  (save-excursion
    (goto-char start)
    (let ((from start) (parts nil))
      (while (re-search-forward "(\\*" end t)
        (let ((comment (match-beginning 0)))
          ;; in a string? syntax-ppss moves point to COMMENT
          (unless (nth 3 (save-excursion (syntax-ppss comment)))
            (push (buffer-substring-no-properties from comment) parts)
            (goto-char comment)
            (unless (forward-comment 1) (goto-char end))
            (push " " parts)
            (setq from (min (point) end)))))
      (push (buffer-substring-no-properties from end) parts)
      (string-trim (replace-regexp-in-string
                    "[ \t\n\r]+" " " (apply #'concat (nreverse parts)))))))

(defun coq-eglot-twin--shift-sentence (sentence delta)
  "Shift the bounds of SENTENCE by DELTA and return SENTENCE."
  (setf (coq-eglot-twin--sentence-start sentence)
        (+ (coq-eglot-twin--sentence-start sentence) delta)
        (coq-eglot-twin--sentence-end sentence)
        (+ (coq-eglot-twin--sentence-end sentence) delta))
  sentence)

(defun coq-eglot-twin--parse-sentences-from (start &optional old suffix delta)
  "Vector of the sentences from the sentence boundary START to buffer end.
If OLD is a previous sentence vector, try to rejoin it at or after index
SUFFIX.  Its bounds after the edits are shifted by DELTA.  A cached suffix is
reused only after a freshly parsed sentence has exactly the expected bounds
and normalized text, so edits changing comments or command boundaries merely
delay the rejoin."
  (save-excursion
    (save-restriction
      (widen)
      (goto-char start)
      (forward-comment (buffer-size))
      (let ((sentences nil)
            (candidate suffix)
            (rejoined nil))
        (while (and (< (point) (point-max))
                    (not rejoined)
                    (let ((sentence-start (point)))
                      (when (eq (coq-script-parse-cmdend-forward) 'cmd)
                        (let* ((sentence-end (point))
                               (text (coq-eglot-twin--normalize
                                      sentence-start sentence-end)))
                          ;; Candidates before the parsed sentence cannot be
                          ;; the resynchronization point.
                          (while (and old candidate (< candidate (length old))
                                      (< (+ (coq-eglot-twin--sentence-start
                                             (aref old candidate))
                                            delta)
                                         sentence-start))
                            (setq candidate (1+ candidate)))
                          (if (and old candidate (< candidate (length old))
                                   (= sentence-start
                                      (+ (coq-eglot-twin--sentence-start
                                          (aref old candidate))
                                         delta))
                                   (= sentence-end
                                      (+ (coq-eglot-twin--sentence-end
                                          (aref old candidate))
                                         delta))
                                   (equal text (coq-eglot-twin--sentence-text
                                                (aref old candidate))))
                              (progn
                                (setq rejoined candidate)
                                ;; The freshly parsed sentence is identical;
                                ;; retain its old object with the whole suffix.
                                (cl-loop for i from candidate below (length old)
                                         do (push (coq-eglot-twin--shift-sentence
                                                   (aref old i) delta)
                                                  sentences)))
                            (push (coq-eglot-twin--make-sentence
                                   sentence-start sentence-end text)
                                  sentences)))
                        t)))
          (forward-comment (buffer-size)))
        (if rejoined
            ;; The reused suffix was pushed in increasing order after the
            ;; parsed prefix, hence appears reversed independently of it.
            (let* ((suffix-length (- (length old) rejoined))
                   (reused (seq-take sentences suffix-length))
                   (parsed (seq-drop sentences suffix-length)))
              (vconcat (nreverse parsed) (nreverse reused)))
          (vconcat (nreverse sentences)))))))

(defun coq-eglot-twin--sentences-before (sentences pos)
  "Number of SENTENCES ending at POS or before."
  (let ((low 0) (high (length sentences)))
    (while (< low high)
      (let ((middle (/ (+ low high) 2)))
        (if (<= (coq-eglot-twin--sentence-end (aref sentences middle)) pos)
            (setq low (1+ middle))
          (setq high middle))))
    low))

(defun coq-eglot-twin--sentences (&optional buffer)
  "Vector of the sentences of BUFFER, by default the current one.
See `coq-eglot-twin--sentence'.  Reuse the cached prefix preceding the first
change.  Parsing rejoins and reuses the cached suffix at the first unchanged
sentence after the last change."
  (with-current-buffer (or buffer (current-buffer))
    (let ((tick (buffer-chars-modified-tick)))
      (unless (eql (car coq-eglot-twin--sentences) tick)
        (let* ((old (cdr coq-eglot-twin--sentences))
               (kept (if (and old coq-eglot-twin--sentences-dirty-start)
                         (coq-eglot-twin--sentences-before
                          old coq-eglot-twin--sentences-dirty-start)
                       0))
               (prefix (and (> kept 0) (seq-subseq old 0 kept)))
               (start (if (> kept 0)
                          (coq-eglot-twin--sentence-end
                           (aref old (1- kept)))
                        (point-min)))
               (delta (if coq-eglot-twin--sentences-buffer-size
                          (- (buffer-size)
                             coq-eglot-twin--sentences-buffer-size)
                        0))
               (dirty-end (and (markerp coq-eglot-twin--sentences-dirty-end)
                               (marker-position
                                coq-eglot-twin--sentences-dirty-end)))
               ;; A candidate starts after every edit.  Its old coordinates,
               ;; shifted by the total size change, must reach DIRTY-END.
               (suffix
                (and old dirty-end
                     (let ((i kept))
                       (while (and (< i (length old))
                                   (< (+ (coq-eglot-twin--sentence-start
                                          (aref old i))
                                         delta)
                                      dirty-end))
                         (setq i (1+ i)))
                       i))))
          (setq coq-eglot-twin--sentences
                (cons tick
                      (vconcat prefix
                               (coq-eglot-twin--parse-sentences-from
                                start old suffix delta)))
                coq-eglot-twin--sentences-buffer-size (buffer-size))
          (when (markerp coq-eglot-twin--sentences-dirty-start)
            (set-marker coq-eglot-twin--sentences-dirty-start nil))
          (when (markerp coq-eglot-twin--sentences-dirty-end)
            (set-marker coq-eglot-twin--sentences-dirty-end nil))
          (setq coq-eglot-twin--sentences-dirty-start nil
                coq-eglot-twin--sentences-dirty-end nil)))
      (cdr coq-eglot-twin--sentences))))

(defun coq-eglot-twin--align (&optional buffer)
  "Vector of the pairs of sentences of BUFFER and its twin.
The pairs (I . J) of the indices of the paired sentences, I in BUFFER,
J in its twin.  BUFFER defaults to the current one.  Kept in the
alignment of their `coq-eglot-twin--twins', (TICK-THIS TICK-OTHER
PAIRS-THIS PAIRS-OTHER), computed again when one of them changed: the
ticks are their `buffer-chars-modified-tick', PAIRS-THIS the pairs seen
from THIS, PAIRS-OTHER from OTHER."
  (let* ((buffer (or buffer (current-buffer)))
         (twins (buffer-local-value 'coq-eglot-twin--twins buffer))
         (this (coq-eglot-twin--twins-this twins))
         (other (coq-eglot-twin--twins-other twins))
         (ticks (list (buffer-chars-modified-tick this)
                      (buffer-chars-modified-tick other)))
         (alignment (coq-eglot-twin--twins-alignment twins)))
    (unless (equal ticks (take 2 alignment))
      (let ((pairs (vconcat
                    (pg-lcs-common-subsequence
                     (cl-map 'vector #'coq-eglot-twin--sentence-text
                             (coq-eglot-twin--sentences this))
                     (cl-map 'vector #'coq-eglot-twin--sentence-text
                             (coq-eglot-twin--sentences other))
                     coq-eglot-twin-max-differences))))
        (setq alignment
              (append ticks
                      (list pairs
                            (cl-map 'vector (lambda (pair)
                                              (cons (cdr pair) (car pair)))
                                    pairs))))
        (setf (coq-eglot-twin--twins-alignment twins) alignment)))
    (nth (if (eq buffer this) 2 3) alignment)))

(defun coq-eglot-twin--last-sentence (sentences pos)
  "Index of the last of SENTENCES starting before POS, or -1."
  (let ((low 0) (high (length sentences)))
    ;; the first one starting at or after POS
    (while (< low high)
      (let ((middle (/ (+ low high) 2)))
        (if (< (coq-eglot-twin--sentence-start (aref sentences middle)) pos)
            (setq low (1+ middle))
          (setq high middle))))
    (1- low)))

(defun coq-eglot-twin--pairs-before (pairs i)
  "Number of PAIRS whose first index is at most I."
  (let ((low 0) (high (length pairs)))
    (while (< low high)
      (let ((middle (/ (+ low high) 2)))
        (if (<= (car (aref pairs middle)) i)
            (setq low (1+ middle))
          (setq high middle))))
    low))

(defun coq-eglot-twin-position (pos &optional buffer)
  "Position in the twin of BUFFER corresponding to POS in BUFFER.
BUFFER defaults to the current one.  In a sentence paired with one of
the twin, the same offset in it, at most its end; at its end or after
it, the end of the twin sentence.  At the end of a diverging zone or
after it, the end of the twin zone: both have checked their version of
the zone.  Inside a diverging zone, or after one whose twin zone is
empty, the end of the last paired sentence before it, the beginning of
the twin if none."
  (with-current-buffer (or buffer (current-buffer))
    (let* ((sentences (coq-eglot-twin--sentences))
           (twin-sentences (coq-eglot-twin--sentences coq-eglot--twin))
           (pairs (coq-eglot-twin--align))
           (i (coq-eglot-twin--last-sentence sentences pos))
           (k (coq-eglot-twin--pairs-before pairs i))
           (pair (and (> k 0) (aref pairs (1- k))))
           ;; the next pair, after the end of the buffers if none
           (next (if (< k (length pairs)) (aref pairs k)
                   (cons (length sentences) (length twin-sentences))))
           ;; the last sentence of the twin zone, if any
           (last-twin (1- (cdr next)))
           (this (and (>= i 0) (aref sentences i))))
      (cond
       ;; in or after a paired sentence
       ((and pair (= (car pair) i))
        (let ((twin (aref twin-sentences (cdr pair))))
          (if (< pos (coq-eglot-twin--sentence-end this))
              (min (+ (coq-eglot-twin--sentence-start twin)
                      (- pos (coq-eglot-twin--sentence-start this)))
                   (coq-eglot-twin--sentence-end twin))
            (coq-eglot-twin--sentence-end twin))))
       ;; at the end of a diverging zone, the twin zone not empty
       ((and this
             (= (1+ i) (car next))
             (>= pos (coq-eglot-twin--sentence-end this))
             (> last-twin (if pair (cdr pair) -1)))
        (coq-eglot-twin--sentence-end (aref twin-sentences last-twin)))
       (pair
        (coq-eglot-twin--sentence-end (aref twin-sentences (cdr pair))))
       (t (with-current-buffer coq-eglot--twin (point-min)))))))

(defun coq-eglot-twin--zones (&optional buffer)
  "The diverging zones of BUFFER and of its twin.
A list of (THIS . TWIN), the indices of the sentences of the zone in
BUFFER and in its twin, each (FIRST . END), END excluded, or nil if the
zone is empty on this side.  BUFFER defaults to the current one."
  (with-current-buffer (or buffer (current-buffer))
    (pg-lcs-gaps (coq-eglot-twin--align)
                 (length (coq-eglot-twin--sentences))
                 (length (coq-eglot-twin--sentences coq-eglot--twin)))))

;;; Highlighting of the diverging zones

(defvar-local coq-eglot-twin--overlays nil
  "Overlays of the diverging sentences of the buffer.")

(defvar-local coq-eglot-twin--blend-colors nil
  "Alist of the blended colors, ((FACE . PART-FACE) . COLOR-OR-NONE).
Emptied when the twins are highlighted again, see
`coq-eglot-twin--update-blend'.")

(defvar-local coq-eglot-twin--blend-state nil
  "The parts the differences were blended with, see `coq-eglot-twin--update-blend'.
A list of (START END FACE), or nil to blend them all again.")

(defvar-local coq-eglot-twin--follow-timer nil
  "Timer moving the proof position of the follower, or nil.")

(defvar-local coq-eglot-twin--out-of-sync nil
  "Non-nil if the follower has to move when its check is finished.")

(defvar-local coq-eglot-twin--following nil
  "Where the follower moves, or nil when it got there.
Then its windows show its proof position, see
`coq-eglot-twin--show-position'.")

(defvar-local coq-eglot-twin--show-timer nil
  "Timer showing the proof position of the follower, or nil.")

(defvar coq-eglot-twin--stopping-at-error nil
  "Non-nil while an error stops and aligns both twins.
It prevents the induced position change from scheduling ordinary following.")

(defun coq-eglot-twin--unhighlight ()
  "Remove the highlighting of the diverging sentences of the buffer."
  (dolist (overlay coq-eglot-twin--overlays)
    (mapc #'delete-overlay (overlay-get overlay 'coq-eglot-twin-blend))
    (delete-overlay overlay))
  (setq coq-eglot-twin--overlays nil))

(defun coq-eglot-twin--face (&optional words buffer)
  "Face of the differences of BUFFER, the current one by default.
Of its sentences or lines, of the WORDS of its lines if non-nil.  The
removed ones in the twin of reference, the added ones in the other."
  (if (coq-eglot-twin--reference-p buffer)
      (if words 'coq-eglot-twin-refine-removed 'coq-eglot-twin-removed)
    (if words 'coq-eglot-twin-refine-added 'coq-eglot-twin-added)))

(defun coq-eglot-twin--highlight-zones (zones)
  "Highlight the diverging ZONES of the current buffer.
A list of (RANGE . OTHER): the indices (FIRST . END) of the sentences of
the zone in the buffer, or nil, and in the other twin."
  (coq-eglot-twin--unhighlight)
  (let ((sentences (coq-eglot-twin--sentences)))
    (pcase-dolist (`(,range . ,_other) zones)
      (when range
        (let ((overlay (make-overlay
                        (coq-eglot-twin--sentence-start
                         (aref sentences (car range)))
                        (coq-eglot-twin--sentence-end
                         (aref sentences (1- (cdr range))))
                        nil nil nil)))
          (overlay-put overlay 'face (coq-eglot-twin--face))
          ;; over the processed and checked parts
          (overlay-put overlay 'priority 10)
          (overlay-put overlay 'coq-eglot-twin t)
          (push overlay coq-eglot-twin--overlays))))))

(defconst coq-eglot-twin--word-regexp "\\(?:\\w\\|\\s_\\)+\\|[^ \t\n]"
  "A word compared in the differences: an identifier, or another character.")

(defun coq-eglot-twin--refine-zones (zones this twin)
  "Highlight the words that differ in the diverging ZONES of THIS and TWIN.
Only in the zones with sentences on both sides, see
`coq-eglot-twin--zones'.  Not the comments, nor the blanks."
  (let ((sentences (coq-eglot-twin--sentences this))
        (twin-sentences (coq-eglot-twin--sentences twin))
        (face (coq-eglot-twin--face t this))
        (twin-face (coq-eglot-twin--face t twin)))
    (pcase-dolist (`(,range . ,twin-range) zones)
      (when (and range twin-range)
        (let* ((start (coq-eglot-twin--sentence-start
                       (aref sentences (car range))))
               (end (coq-eglot-twin--sentence-end
                     (aref sentences (1- (cdr range)))))
               (twin-start (coq-eglot-twin--sentence-start
                            (aref twin-sentences (car twin-range))))
               (twin-end (coq-eglot-twin--sentence-end
                          (aref twin-sentences (1- (cdr twin-range))))))
          (when (<= (+ (- end start) (- twin-end twin-start))
                    coq-eglot-twin-max-refine-characters)
            (let ((words (coq-eglot-twin--pieces
                          this coq-eglot-twin--word-regexp start end t))
                  (twin-words (coq-eglot-twin--pieces
                               twin coq-eglot-twin--word-regexp
                               twin-start twin-end t)))
              (pcase-dolist (`(,run . ,twin-run)
                             (coq-eglot-twin--unmatched words twin-words))
                (when run
                  (coq-eglot-twin--mark-refine this words run face 12))
                (when twin-run
                  (coq-eglot-twin--mark-refine twin twin-words twin-run
                                              twin-face 12))))))))))

(defun coq-eglot-twin--highlight (&optional buffer)
  "Highlight the diverging sentences of BUFFER and of its twin.
BUFFER defaults to the current one."
  (with-current-buffer (or buffer (current-buffer))
    (when (buffer-live-p coq-eglot--twin)
      (let ((zones (coq-eglot-twin--zones))
            (twin coq-eglot--twin))
        (coq-eglot-twin--highlight-zones zones)
        (with-current-buffer twin
          (coq-eglot-twin--highlight-zones
           (mapcar (lambda (zone) (cons (cdr zone) (car zone))) zones)))
        (coq-eglot-twin--refine-zones zones (current-buffer) twin)
        (dolist (side (list (current-buffer) twin))
          (with-current-buffer side
            ;; the colors of the theme may have changed
            (setq coq-eglot-twin--blend-colors nil
                  coq-eglot-twin--blend-state nil)
            (coq-eglot-twin--update-blend)))))))

(defun coq-eglot-twin--background (face)
  "The background color of FACE, or nil.
FACE is a face, an attribute list, or a list of them, like the value of
the property `face'."
  (let ((color
         (cond ((null face) nil)
               ((symbolp face) (face-background face nil t))
               ((keywordp (car-safe face))
                (or (plist-get face :background)
                    (coq-eglot-twin--background (plist-get face :inherit))))
               ((consp face) (seq-some #'coq-eglot-twin--background face)))))
    (and (stringp color) (color-defined-p color) color)))

(defun coq-eglot-twin--blend (face1 face2 &optional face2-weight)
  "Weighted mean of the backgrounds of FACE1 and FACE2.
FACE2-WEIGHT defaults to 0.5.  Return nil if either face has no background."
  (let ((color1 (coq-eglot-twin--background face1))
        (color2 (coq-eglot-twin--background face2))
        (weight (or face2-weight 0.5)))
    (when (and color1 color2)
      (apply #'color-rgb-to-hex
             (append (cl-mapcar (lambda (a b)
                                  (+ (* (- 1 weight) a) (* weight b)))
                                (color-name-to-rgb color1)
                                (color-name-to-rgb color2))
                     '(2))))))

(defun coq-eglot-twin--blend-spec (overlay parts)
  "Where and how OVERLAY of a difference is blended with PARTS.
A list of (START END COLOR), see `coq-eglot-twin--update-blend'."
  (delq nil
        (mapcar
         (lambda (part)
           (let ((start (max (overlay-start overlay) (overlay-start part)))
                 (end (min (overlay-end overlay) (overlay-end part))))
             (when (< start end)
               (let* ((key (cons (overlay-get overlay 'face)
                                 (overlay-get part 'face)))
                      (color (with-memoization
                                 (alist-get key coq-eglot-twin--blend-colors
                                            nil nil #'equal)
                               (or (coq-eglot-twin--blend
                                    (car key) (cdr key)
                                    ;; Make a locked difference retain mostly
                                    ;; the locked-region background.  The
                                    ;; checked queue keeps the neutral mean.
                                    (if (eq (cdr key) 'proof-locked-face)
                                        0.65
                                      0.5))
                                   'none))))
                 (and (stringp color) (list start end color))))))
         parts)))

(defun coq-eglot-twin--update-blend ()
  "Blend the diverging zones with the processed and checked parts.
Where they overlap, the background of a zone is the mean of its own and
of the one of the part, so that both are visible.  Run when the proof
position moves, see `coq-eglot-position-hook': only the differences
around the bounds that moved are blended again."
  (let* ((parts (coq-eglot-processed-overlays))
         (state (mapcar (lambda (part)
                          (list (overlay-start part) (overlay-end part)
                                (overlay-get part 'face)))
                        parts))
         (old coq-eglot-twin--blend-state)
         (overlays
          (if (or (null old) (not (equal (mapcar #'caddr old)
                                         (mapcar #'caddr state))))
              coq-eglot-twin--overlays
            ;; the same faces: only around the bounds that moved
            (let ((old-bounds (sort (flatten-tree
                                     (mapcar (lambda (s) (list (car s) (cadr s))) old))
                                    #'<))
                  (new-bounds (sort (flatten-tree
                                     (mapcar (lambda (s) (list (car s) (cadr s))) state))
                                    #'<)))
              (if (/= (length old-bounds) (length new-bounds))
                  coq-eglot-twin--overlays
                (delete-dups
                 (seq-filter
                  (lambda (overlay)
                    (or (overlay-get overlay 'coq-eglot-twin)
                        (overlay-get overlay 'coq-eglot-twin-refine)))
                  (apply #'append
                         (cl-mapcar (lambda (o n)
                                      (unless (= o n)
                                        (overlays-in (min o n) (max o n))))
                                    old-bounds new-bounds)))))))))
    (setq coq-eglot-twin--blend-state state)
    (dolist (overlay overlays)
      (let ((spec (coq-eglot-twin--blend-spec overlay parts)))
        (unless (equal spec (overlay-get overlay 'coq-eglot-twin-blend-spec))
          (mapc #'delete-overlay (overlay-get overlay 'coq-eglot-twin-blend))
          (overlay-put overlay 'coq-eglot-twin-blend-spec spec)
          (overlay-put
           overlay 'coq-eglot-twin-blend
           (mapcar (lambda (blend-spec)
                     (pcase-let ((`(,start ,end ,color) blend-spec))
                       (let ((blend (make-overlay start end nil nil nil)))
                         (overlay-put blend 'face (list :background color))
                         ;; right above the overlay
                         (overlay-put blend 'priority
                                      (1+ (overlay-get overlay 'priority)))
                         blend)))
                   spec)))))))

(defun coq-eglot-twin--idle-update (twins)
  "Update the highlighting of TWINS, if still paired."
  (setf (coq-eglot-twin--twins-highlight-timer twins) nil)
  (when (coq-eglot-twin--live-p twins)
    (coq-eglot-twin--highlight (coq-eglot-twin--twins-this twins))))

(defun coq-eglot-twin--after-change (start &optional end &rest _)
  "Update the highlighting after no twin has changed for the debounce delay."
  (setq end (or end start))
  (if (markerp coq-eglot-twin--sentences-dirty-start)
      (when (< start (marker-position coq-eglot-twin--sentences-dirty-start))
        (set-marker coq-eglot-twin--sentences-dirty-start start))
    (setq coq-eglot-twin--sentences-dirty-start (copy-marker start nil)))
  (if (markerp coq-eglot-twin--sentences-dirty-end)
      (when (> end (marker-position coq-eglot-twin--sentences-dirty-end))
        (set-marker coq-eglot-twin--sentences-dirty-end end))
    (setq coq-eglot-twin--sentences-dirty-end (copy-marker end t)))
  (let ((twins coq-eglot-twin--twins))
    (when twins
      (coq-eglot-twin--cancel
       (coq-eglot-twin--twins-highlight-timer twins))
      (setf (coq-eglot-twin--twins-highlight-timer twins)
            (run-at-time coq-eglot-twin-idle-delay nil
                         #'coq-eglot-twin--idle-update twins)))))

(defconst coq-eglot-twin--hooks
  '((after-change-functions . coq-eglot-twin--after-change)
    (coq-eglot-position-hook . coq-eglot-twin--position-changed)
    (coq-eglot-position-hook . coq-eglot-twin--update-blend)
    (coq-eglot-error-hook . coq-eglot-twin--show-error)
    (coq-eglot-output-hook . coq-eglot-twin--output-changed))
  "The local hooks of the twins and their functions, (HOOK . FUNCTION).
See `coq-eglot-twin--start-alignment'.")

(defun coq-eglot-twin--start-alignment (buffer)
  "Start aligning BUFFER and its twin, in BUFFER."
  (with-current-buffer buffer
    (pcase-dolist (`(,hook . ,function) coq-eglot-twin--hooks)
      (add-hook hook function nil t)))
  (coq-eglot-twin--highlight buffer))

(defun coq-eglot-twin--stop-alignment (buffer)
  "Stop aligning BUFFER with its twin, in BUFFER only."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (pcase-dolist (`(,hook . ,function) coq-eglot-twin--hooks)
        (remove-hook hook function t))
      (coq-eglot-twin--uncompare-outputs)
      (coq-eglot-twin--cancel coq-eglot-twin--follow-timer)
      (coq-eglot-twin--cancel coq-eglot-twin--show-timer)
      (setq coq-eglot-twin--out-of-sync nil
            coq-eglot-twin--following nil)
      (coq-eglot-twin--unhighlight))))

;;; Synchronization of the proof positions
;;
;; The twin where the user works leads, the other one follows: the last
;; command of the backend or the last edition was in the leader, see
;; `coq-eglot-working-buffer'.  When the proof position of the leader
;; moves, the follower moves its own to the corresponding position,
;; really: its server checks up to there, or it goes back.  Its errors
;; are displayed in its own output, they do not stop the leader.  It
;; moves after the current command, from a timer, with its internal
;; functions: it does not become the leader.  If it is checking, it
;; goes on further if needed, otherwise it waits for the end of its
;; check.  When it has moved, its windows show its new proof position,
;; or its error.  An error on either side stops the scripting of the
;; other side too, at or before the corresponding proof position.

(defcustom coq-eglot-twin-synchronize t
  "If non-nil, the proof position of a twin follows the one of the other.
The twin where the user works leads, see `coq-eglot-twin-pair'."
  :type 'boolean
  :group 'coq-eglot)

(defun coq-eglot-twin--leader-p (&optional buffer)
  "Non-nil if BUFFER, by default the current one, leads its twin."
  (let ((buffer (or buffer (current-buffer))))
    (and (eq (coq-eglot-working-buffer) buffer)
         (buffer-live-p (buffer-local-value 'coq-eglot--twin buffer)))))

(defun coq-eglot-twin--target ()
  "Where the current buffer, a follower, must move its proof position.
The position corresponding to the destination of its twin, the leader.
While the leader is checking, use its target rather than its current proof
position, so both sides start checking concurrently."
  (let ((leader coq-eglot--twin))
    (coq-eglot-twin-position
     (with-current-buffer leader
       (if (coq-eglot-checking-p)
           (coq-eglot-check-target)
         (coq-eglot-position)))
     leader)))

(defun coq-eglot-twin--move (target)
  "Move the proof position of the current buffer to TARGET.
During a check, only further: otherwise wait for its end, see
`coq-eglot-twin--out-of-sync'."
  ;; before: starting the check may let the follower move again
  (setq coq-eglot-twin--out-of-sync nil
        coq-eglot-twin--following target)
  (unless (coq-eglot-move-proof-position target)
    (setq coq-eglot-twin--out-of-sync t))
  ;; shown at the end of the check, or now
  (unless (coq-eglot-checking-p)
    (coq-eglot-twin--schedule-show (current-buffer))))

(defun coq-eglot-twin--show (pos)
  "Move point to POS in the current buffer and in its windows."
  (goto-char pos)
  (dolist (window (get-buffer-window-list (current-buffer) nil t))
    (set-window-point window pos)))

(defun coq-eglot-twin--show-position (buffer)
  "Show the proof position of BUFFER, a follower, in its windows.
If it moves and is not checking.  It got where it moves if no sentence
is left before, see `coq-eglot-twin--following'."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (setq coq-eglot-twin--show-timer nil)
      (when (and coq-eglot-twin--following (not (coq-eglot-checking-p)))
        (coq-eglot-twin--show (coq-eglot-position))
        (when (>= (coq-eglot-next-sentence-position (coq-eglot-position))
                  coq-eglot-twin--following)
          (setq coq-eglot-twin--following nil))))))

(defun coq-eglot-twin--show-error ()
  "Retarget both twins at the earliest error and show the current one.
The other side moves to the position corresponding to the proof position
before this error.  If it finds an earlier error on the way, its own error
hook retargets this side in turn: targets can only move backward until the
earliest error wins.  See `coq-eglot-error-hook'."
  (when (and coq-eglot-twin-synchronize (buffer-live-p coq-eglot--twin))
    (let* ((failed (current-buffer))
           (other coq-eglot--twin)
           (error-position (point))
           (failed-position (coq-eglot-position))
           (other-position (coq-eglot-twin-position failed-position failed)))
      (coq-eglot-twin--cancel coq-eglot-twin--follow-timer)
      (coq-eglot-twin--cancel coq-eglot-twin--show-timer)
      (setq coq-eglot-twin--following nil)
      (let ((coq-eglot-twin--stopping-at-error t))
        (with-current-buffer other
          (coq-eglot-twin--cancel coq-eglot-twin--follow-timer)
          (coq-eglot-twin--cancel coq-eglot-twin--show-timer)
          (setq coq-eglot-twin--out-of-sync nil
                coq-eglot-twin--following other-position)
          ;; Replace a farther target, go back if already past the error, or
          ;; continue up to it if still behind.  A new, earlier error repeats
          ;; the same operation symmetrically.
          (coq-eglot-retarget-proof-position other-position)
          (unless (coq-eglot-checking-p)
            (coq-eglot-twin--schedule-show (current-buffer)))))
      (with-current-buffer failed
        (coq-eglot-twin--show error-position)))))

(defun coq-eglot-twin--schedule-show (buffer)
  "Show the proof position of BUFFER after the current command.
Once for several moves, see `coq-eglot-twin--show-position'."
  (with-current-buffer buffer
    (coq-eglot-twin--once coq-eglot-twin--show-timer
      (run-at-time 0 nil #'coq-eglot-twin--show-position buffer))))

(defun coq-eglot-twin--follow (buffer)
  "Move the proof position of BUFFER, a follower, after its leader's."
  (when (and (buffer-live-p buffer)
             (buffer-local-value 'coq-eglot-mode buffer))
    (with-current-buffer buffer
      (setq coq-eglot-twin--follow-timer nil)
      (when (and coq-eglot-twin-synchronize
                 (buffer-live-p coq-eglot--twin)
                 (not (coq-eglot-twin--leader-p)))
        ;; without waiting for its server: its requests wait for it
        ;; to connect, see `coq-eglot-lsp--when-connected'
        (condition-case err
            (let ((target (coq-eglot-twin--target)))
              ;; In particular, do not replace the window showing an error
              ;; merely because the other side has now converged to it.
              (if (= target (coq-eglot-position))
                  (progn
                    (setq coq-eglot-twin--out-of-sync nil)
                    ;; Preserve a show already owed by this follower, but do
                    ;; not create one when its window deliberately shows an
                    ;; error and FOLLOWING is nil.
                    (when (and coq-eglot-twin--following
                               (not (coq-eglot-checking-p)))
                      (coq-eglot-twin--schedule-show (current-buffer))))
                (coq-eglot-twin--move target)))
          (error (setq coq-eglot-twin--following nil)
                 (message "Coq: %s does not follow its twin: %s"
                          (buffer-name) (error-message-string err))))))))

(defun coq-eglot-twin--schedule-follow (buffer)
  "Move the proof position of BUFFER after the current command.
Once for several moves of the leader."
  (with-current-buffer buffer
    (coq-eglot-twin--once coq-eglot-twin--follow-timer
      (run-at-time 0 nil #'coq-eglot-twin--follow buffer))))

(defun coq-eglot-twin--position-changed ()
  "The proof position of the current buffer may have moved.
In the leader, the follower follows; in a follower that waited for the
end of its check, it moves now.  See `coq-eglot-position-hook'."
  (when (and (not coq-eglot-twin--stopping-at-error)
             coq-eglot-twin-synchronize (buffer-live-p coq-eglot--twin))
    (cond
     ((coq-eglot-twin--leader-p)
      (coq-eglot-twin--schedule-follow coq-eglot--twin)
      ;; An error of the follower may have retargeted the leader backward.
      ;; Once that shorter check ends, show and clear its convergence target
      ;; just as for an ordinary follower.
      (when (and coq-eglot-twin--following (not (coq-eglot-checking-p)))
        (coq-eglot-twin--schedule-show (current-buffer))))
     ((coq-eglot-checking-p))
     (coq-eglot-twin--out-of-sync
      (coq-eglot-twin--schedule-follow (current-buffer)))
     (coq-eglot-twin--following
      (coq-eglot-twin--schedule-show (current-buffer))))))

(defun coq-eglot-twin-toggle-synchronize ()
  "Turn the synchronization of the proof positions of twins on or off.
See `coq-eglot-twin-synchronize'.  Turned on, the twin of the current
buffer follows it."
  (interactive)
  (setq coq-eglot-twin-synchronize (not coq-eglot-twin-synchronize))
  (when coq-eglot-twin-synchronize
    (let ((this (ignore-errors (coq-eglot-script-buffer))))
      (when (and this (buffer-live-p (buffer-local-value 'coq-eglot--twin this)))
        (coq-eglot-set-working-buffer this)
        (coq-eglot-twin--schedule-follow
         (buffer-local-value 'coq-eglot--twin this)))))
  (message "Coq: synchronization of the twins %s"
           (if coq-eglot-twin-synchronize "on" "off")))

(defun coq-eglot-twin-goto-twin-position ()
  "Go to the position of the twin corresponding to point.
In its window, if any.  See `coq-eglot-twin-position'."
  (interactive)
  (pcase-let ((`(,this . ,twin) (coq-eglot-twin--script-and-twin)))
    (let ((pos (coq-eglot-twin-position
                (with-current-buffer this (point)) this))
          (window (get-buffer-window twin)))
      (if window
          (progn (select-window window) (goto-char pos))
        (pop-to-buffer twin)
        (goto-char pos)))))

;;; Comparison of the goals and messages
;;
;; When the proof positions of the twins correspond, their goals and
;; their messages are compared like their scripts: the lines without a
;; match in the other twin are highlighted, and in the changed ones the
;; words that differ.  The hypotheses are on their own lines, see
;; `coq-eglot--format-hyps': a changed hypothesis is a changed line.

(defcustom coq-eglot-twin-compare-outputs t
  "If non-nil, highlight the differences of the goals and messages of twins.
When their proof positions correspond, see `coq-eglot-twin-position'."
  :type 'boolean
  :group 'coq-eglot)

(defface coq-eglot-twin-refine-removed
  '((t :inherit coq-diffs-removed-face))
  "Face of the words that differ in the goals and messages of the reference.
Like the diffs of Coq, see `coq-diffs-removed-face', so like
`diff-refine-removed'."
  :group 'coq-eglot)

(defface coq-eglot-twin-refine-added
  '((t :inherit coq-diffs-added-face))
  "Face of the words that differ in the goals and messages of the other twin.
Like the diffs of Coq, see `coq-diffs-added-face', so like
`diff-refine-added'."
  :group 'coq-eglot)

(defvar-local coq-eglot-twin--output-overlays nil
  "Overlays of the differences in a goals or response buffer.")

(defun coq-eglot-twin--output-changed ()
  "Compare the outputs of the twins after the current command.
Once for several changes, see `coq-eglot-output-hook'."
  (let ((twins coq-eglot-twin--twins))
    (when (and coq-eglot-twin-compare-outputs twins)
      (coq-eglot-twin--once (coq-eglot-twin--twins-compare-timer twins)
        (run-at-time 0 nil #'coq-eglot-twin--compare-later twins)))))

(defun coq-eglot-twin--compare-later (twins)
  "Compare the outputs of TWINS, if still paired."
  (setf (coq-eglot-twin--twins-compare-timer twins) nil)
  (when (coq-eglot-twin--live-p twins)
    (coq-eglot-twin--compare-outputs (coq-eglot-twin--twins-this twins))))

(defun coq-eglot-twin--corresponding-p (buffer)
  "Non-nil if the proof positions of BUFFER and its twin correspond.
And none is checking."
  (with-current-buffer buffer
    (let ((twin coq-eglot--twin))
      (and (not (coq-eglot-checking-p))
           (not (with-current-buffer twin (coq-eglot-checking-p)))
           (let ((this-pos (coq-eglot-position))
                 (twin-pos (with-current-buffer twin (coq-eglot-position))))
             (or (= (coq-eglot-twin-position this-pos) twin-pos)
                 (= (coq-eglot-twin-position twin-pos twin) this-pos)))))))

(defun coq-eglot-twin--uncompare (buffer)
  "Remove the highlighting of the differences in output BUFFER, if live."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (mapc #'delete-overlay coq-eglot-twin--output-overlays)
      (setq coq-eglot-twin--output-overlays nil))))

(defun coq-eglot-twin--uncompare-outputs ()
  "Remove the highlighting of the differences of the outputs of the buffer."
  (mapc #'coq-eglot-twin--uncompare (coq-eglot-output-buffers)))

(defun coq-eglot-twin--compare-outputs (buffer)
  "Compare the goals and messages of BUFFER and of its twin.
If their proof positions do not correspond, only remove the highlighting.
Compare response buffers only when both responses come from scripting: an
explicit query such as About or Search is local to the buffer where it ran."
  (let* ((twin (buffer-local-value 'coq-eglot--twin buffer))
         (output-state (with-current-buffer buffer (coq-eglot--output)))
         (twin-output-state (with-current-buffer twin (coq-eglot--output)))
         (outputs (with-current-buffer buffer (coq-eglot-output-buffers)))
         (twin-outputs (with-current-buffer twin (coq-eglot-output-buffers)))
         (compare (and coq-eglot-twin-compare-outputs
                       (coq-eglot-twin--corresponding-p buffer)))
         (compare-response
          (and (coq-eglot--output-response-scripted output-state)
               (coq-eglot--output-response-scripted twin-output-state))))
    (cl-mapc (lambda (output twin-output kind)
               (coq-eglot-twin--uncompare output)
               (coq-eglot-twin--uncompare twin-output)
               (when (and compare (buffer-live-p output)
                          (buffer-live-p twin-output)
                          (or (not (eq kind 'response)) compare-response))
                 (coq-eglot-twin--compare-buffers
                  output twin-output
                  (coq-eglot-twin--face nil buffer)
                  (coq-eglot-twin--face t buffer)
                  (coq-eglot-twin--face nil twin)
                  (coq-eglot-twin--face t twin))))
             outputs twin-outputs '(goals conclusion response))))

(defun coq-eglot-twin--pieces (buffer regexp &optional start end no-comments)
  "Vector of the matches of REGEXP in BUFFER, between START and END.
Each one (START END . TEXT).  Not those in comments if NO-COMMENTS."
  (with-current-buffer buffer
    (save-excursion
      (goto-char (or start (point-min)))
      (let ((pieces nil))
        (while (re-search-forward regexp (or end (point-max)) t)
          (let ((match-start (match-beginning 0)))
            (unless (and no-comments
                         (save-excursion
                           (or (nth 4 (syntax-ppss match-start))
                               ;; the end of the opening of a comment
                               (nth 4 (syntax-ppss (match-end 0)))
                               ;; its beginning
                               (progn (goto-char match-start)
                                      (forward-comment 1)))))
              (push (cons match-start
                          (cons (match-end 0) (match-string-no-properties 0)))
                    pieces))))
        (vconcat (nreverse pieces))))))

(defun coq-eglot-twin--unmatched (a b)
  "The runs of the pieces of A and B without match in the other one.
A list of (RANGE-A . RANGE-B), each (FIRST . END), END excluded, or nil
if the run is empty on this side.  A and B are vectors of pieces, see
`coq-eglot-twin--pieces'."
  (pg-lcs-gaps (pg-lcs-common-subsequence
                (cl-map 'vector #'cddr a) (cl-map 'vector #'cddr b)
                coq-eglot-twin-max-differences)
               (length a) (length b)))

(defun coq-eglot-twin--mark (buffer pieces range face priority property record)
  "Highlight the PIECES of BUFFER in RANGE with FACE, at PRIORITY.
Line by line.  Each overlay gets PROPERTY set to t, and is passed to
the function RECORD, called in BUFFER.  Return the bounds (START . END)
of the range."
  (with-current-buffer buffer
    (let ((i (car range)))
      (while (< i (cdr range))
        (let ((start (car (aref pieces i)))
              (end (cadr (aref pieces i))))
          ;; the next pieces on the same line
          (while (and (< (1+ i) (cdr range))
                      (not (string-search
                            "\n" (buffer-substring-no-properties
                                   end (car (aref pieces (1+ i)))))))
            (setq i (1+ i) end (cadr (aref pieces i))))
          (let ((overlay (make-overlay start end nil nil nil)))
            (overlay-put overlay 'face face)
            (overlay-put overlay 'priority priority)
            (overlay-put overlay property t)
            (funcall record overlay))
          (setq i (1+ i))))))
  (cons (car (aref pieces (car range)))
        (cadr (aref pieces (1- (cdr range))))))

(defun coq-eglot-twin--mark-refine (buffer pieces range face priority)
  "Highlight the words PIECES of a script BUFFER in RANGE.
With FACE, at PRIORITY, see `coq-eglot-twin--mark'.  The words of its
diverging zones, see `coq-eglot-twin--refine-zones'."
  (coq-eglot-twin--mark buffer pieces range face priority
                        'coq-eglot-twin-refine
                        (lambda (overlay)
                          (push overlay coq-eglot-twin--overlays))))

(defun coq-eglot-twin--mark-output (buffer pieces range face priority)
  "Highlight the PIECES of an output BUFFER in RANGE.
With FACE, at PRIORITY, see `coq-eglot-twin--mark'."
  (coq-eglot-twin--mark buffer pieces range face priority
                        'coq-eglot-twin
                        (lambda (overlay)
                          (push overlay coq-eglot-twin--output-overlays))))

(defun coq-eglot-twin--compare-buffers (a b face-a words-a face-b words-b)
  "Highlight the lines of buffers A and B without match in the other one.
With FACE-A in A and FACE-B in B.  In the lines that differ in both,
the words that differ, with WORDS-A and WORDS-B."
  (let ((lines-a (coq-eglot-twin--pieces a "^.+$"))
        (lines-b (coq-eglot-twin--pieces b "^.+$"))
        (word coq-eglot-twin--word-regexp))
    (pcase-dolist (`(,range-a . ,range-b)
                   (coq-eglot-twin--unmatched lines-a lines-b))
      (let ((bounds-a (and range-a (coq-eglot-twin--mark-output
                                    a lines-a range-a face-a 10)))
            (bounds-b (and range-b (coq-eglot-twin--mark-output
                                    b lines-b range-b face-b 10))))
        (when (and bounds-a bounds-b)
          (let ((pieces-a (coq-eglot-twin--pieces a word (car bounds-a)
                                                  (cdr bounds-a)))
                (pieces-b (coq-eglot-twin--pieces b word (car bounds-b)
                                                  (cdr bounds-b))))
            (pcase-dolist (`(,run-a . ,run-b)
                           (coq-eglot-twin--unmatched pieces-a pieces-b))
              (when run-a
                (coq-eglot-twin--mark-output a pieces-a run-a words-a 11))
              (when run-b
                (coq-eglot-twin--mark-output b pieces-b run-b words-b 11)))))))))

;;; The twin of reference

(defun coq-eglot-twin-swap-reference ()
  "Make the other twin the reference.
The differences of the reference are highlighted as removed, the ones
of the other twin as added, see `coq-eglot-twin-removed'.  The
reference is the buffer paired by `coq-eglot-twin-pair' at first."
  (interactive)
  (pcase-let ((`(,this . ,twin) (coq-eglot-twin--script-and-twin)))
    (let ((reference (if (coq-eglot-twin--reference-p this) twin this)))
      (setf (coq-eglot-twin--twins-reference
             (buffer-local-value 'coq-eglot-twin--twins this))
            reference)
      (coq-eglot-twin--highlight this)
      (coq-eglot-twin--compare-outputs this)
      (message "Coq: %s is the reference" (buffer-name reference)))))

(provide 'coq-eglot-twin)

;;; coq-eglot-twin.el ends here
