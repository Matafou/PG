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
;; in another one, each with its own server (a .dir-locals.el setting
;; `coq-eglot-server-program').
;;
;; The server of each twin is the one of its project (see
;; `coq-eglot-lsp-project'), so the twins must be in two projects, like
;; two worktrees.  Its program is `coq-eglot-server-program', set by a
;; .dir-locals.el, or, for the twin, by an opam switch of its own while
;; the other one uses the current switch of Emacs: see
;; `coq-eglot-twin-set-opam-switch'.
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
(require 'coq-indent)                   ; coq-script-parse-cmdend-forward
(require 'diff-mode)                    ; the faces of the diffs
(require 'coq-db)                       ; the faces of the diffs of Coq
(require 'coq-eglot)

(defcustom coq-eglot-twin-opam-switch nil
  "Opam switch of the server of the twin, or nil.
If non-nil, `coq-eglot-twin-pair' gives the twin the server of this
switch, see `coq-eglot-twin-set-opam-switch', while the other buffer
uses the current switch of Emacs.  If nil, the twin keeps its server,
see `coq-eglot-server-program'."
  :type '(choice (const :tag "The server of the twin" nil)
                 (string :tag "Opam switch"))
  :group 'coq-eglot)

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
`coq-eglot-twin--once'."
  this other reference alignment highlight-timer compare-timer)

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

;;; Opam switches

(defun coq-eglot-twin--opam (&rest args)
  "Output lines of opam with ARGS, or a user error if it fails."
  (condition-case err
      (apply #'process-lines "opam" args)
    (error (user-error "Coq: opam %s failed: %s"
                       (string-join args " ") (error-message-string err)))))

(defun coq-eglot-twin--read-opam-switch ()
  "Ask an opam switch."
  (completing-read "Opam switch of the twin: "
                   (coq-eglot-twin--opam "switch" "list" "--short")
                   nil t nil nil coq-eglot-twin-opam-switch))

(defun coq-eglot-twin--switch-server (switch)
  "Command line of the server of opam SWITCH, a list of strings.
The first of rocq-lsp and coq-lsp in the bin directory of SWITCH."
  (let* ((prefix (car (coq-eglot-twin--opam "var" "prefix"
                                            (concat "--switch=" switch))))
         (program (seq-find #'file-executable-p
                            (mapcar (lambda (name)
                                      (expand-file-name name
                                                        (expand-file-name
                                                         "bin" prefix)))
                                    coq-eglot-lsp--program-names))))
    (unless program
      (user-error "Coq: no language server in opam switch %s, \
install coq-lsp there" switch))
    (list program)))

(defun coq-eglot-twin--server-label (program)
  "Short name of the server PROGRAM: its opam switch, or its file name.
The switch of ~/.opam/SWITCH/bin/PROGRAM, or the project of a local
switch PROJECT/_opam/bin/PROGRAM."
  (let* ((bin (directory-file-name (or (file-name-directory program) "")))
         (prefix (file-name-directory bin))
         (prefix-name (and prefix (file-name-nondirectory
                                   (directory-file-name prefix))))
         (parent (and prefix (file-name-directory (directory-file-name prefix))))
         (parent-name (and parent (file-name-nondirectory
                                   (directory-file-name parent)))))
    (cond
     ((not (equal (file-name-nondirectory bin) "bin"))
      (file-name-nondirectory program))
     ((equal prefix-name "_opam") parent-name)
     ((equal parent-name ".opam") prefix-name)
     (t (file-name-nondirectory program)))))

(defun coq-eglot-twin--update-label ()
  "Set the label of the server of the current buffer in the mode line.
See `coq-eglot--twin-label'."
  (setq coq-eglot--twin-label
        (ignore-errors
          (let ((program (car (coq-eglot-lsp-server-command))))
            ;; found in exec-path: its opam switch
            (coq-eglot-twin--server-label (or (executable-find program)
                                              program)))))
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

(defun coq-eglot-twin-pair (other &optional switch)
  "Pair the current script buffer with OTHER, its twin, side by side.
Both display their goals and messages at the same time: OTHER gets an
output of its own, see `coq-eglot--output', whose buffers are named
after it, like \"*goals*<OTHER>\".  The windows are laid out again, see
`coq-eglot-twin-layout'.  Killing one of them unpairs them, see
`coq-eglot-twin-unpair'.  OTHER is the reference: its differences are
highlighted as removed, see `coq-eglot-twin-swap-reference'.
With SWITCH, or `coq-eglot-twin-opam-switch', the server of OTHER is the
one of this opam switch, see `coq-eglot-twin-set-opam-switch'.
Interactively, with a prefix argument, ask SWITCH."
  (interactive
   (with-current-buffer (coq-eglot-script-buffer)
     (when coq-eglot--twin
       (user-error "Coq: this buffer has a twin already, %s"
                   (buffer-name coq-eglot--twin)))
     (list (coq-eglot-twin--read-buffer)
           (and current-prefix-arg (coq-eglot-twin--read-opam-switch)))))
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
        (add-hook 'kill-buffer-hook #'coq-eglot-twin--on-kill nil t)))
    (with-current-buffer this
      (coq-eglot-twin--update-label))
    (coq-eglot-twin--start-alignment other)
    (coq-eglot-twin--start-alignment this)
    (let ((switch (or switch coq-eglot-twin-opam-switch)))
      (if switch
          (with-current-buffer other
            (coq-eglot-twin--set-switch switch))
        (with-current-buffer other
          (coq-eglot-twin--update-label))))
    (coq-eglot-twin-layout)
    (message "Coq: %s and %s are twins" (buffer-name this) (buffer-name other))))

(defun coq-eglot-twin--set-switch (switch)
  "Give the current buffer the server of opam SWITCH.
See `coq-eglot-twin-set-opam-switch'."
  (let ((command (coq-eglot-twin--switch-server switch)))
    (unless (equal command (ignore-errors (coq-eglot-lsp-server-command)))
      ;; the goals and checks of another version of Rocq do not hold:
      ;; the proof positions of the buffers of the server go back
      (when (coq-eglot-lsp-current-server)
        (coq-eglot-exit))
      ;; a server still connecting, started when the twin was visited:
      ;; killed, like Eglot does when the connection is canceled
      (coq-eglot-lsp-kill-connecting-servers)
      (setq-local coq-eglot-server-program command)
      (coq-eglot-lsp-ensure-server))
    (coq-eglot-twin--update-label)))

(defun coq-eglot-twin-set-opam-switch (switch)
  "Give the twin the server of opam SWITCH, the other buffer keeps its own.
The twin is the buffer paired by `coq-eglot-twin-pair', with an output
of its own.  The server of SWITCH is its rocq-lsp or coq-lsp: the value
of `coq-eglot-server-program' in the twin.  If the server of the twin
ran another program, it stops: the proof positions of its buffers go
back to their beginning.  It is shared by the buffers of the project of
the twin.  The mode line of the twins shows their servers.  The twin
keeps this server when unpaired."
  (interactive (list (coq-eglot-twin--read-opam-switch)))
  (let ((twin (coq-eglot-twin--twins-other
               (buffer-local-value 'coq-eglot-twin--twins
                                   (car (coq-eglot-twin--script-and-twin))))))
    (with-current-buffer twin
      (coq-eglot-twin--set-switch switch))
    (message "Coq: the server of %s is the one of opam switch %s"
             (buffer-name twin) switch)))

(defun coq-eglot-twin--forget (buffer)
  "Forget the twin of BUFFER, in BUFFER only."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (setq coq-eglot--twin nil
            coq-eglot--twin-label nil
            coq-eglot-twin--twins nil)
      (remove-hook 'kill-buffer-hook #'coq-eglot-twin--on-kill t))))

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
        (coq-eglot-share-output)))
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
    (coq-eglot-twin--unpair (current-buffer))))

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

(defcustom coq-eglot-twin-idle-delay 0.5
  "Seconds of idleness before updating the highlighting of the twins.
After a change in one of them."
  :type 'number
  :group 'coq-eglot)

(cl-defstruct (coq-eglot-twin--sentence
               (:constructor coq-eglot-twin--make-sentence (start end text)))
  "A sentence of a script buffer: its bounds and its normalized text."
  start end text)

(defvar-local coq-eglot-twin--sentences nil
  "The sentences of the buffer, (TICK . VECTOR), or nil.
TICK is the `buffer-chars-modified-tick' they were computed at.")

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

(defun coq-eglot-twin--sentences (&optional buffer)
  "Vector of the sentences of BUFFER, by default the current one.
See `coq-eglot-twin--sentence'.  Computed again if the buffer changed."
  (with-current-buffer (or buffer (current-buffer))
    (let ((tick (buffer-chars-modified-tick)))
      (unless (eql (car coq-eglot-twin--sentences) tick)
        (setq coq-eglot-twin--sentences
              (cons tick
                    (save-excursion
                      (save-restriction
                        (widen)
                        (goto-char (point-min))
                        (forward-comment (buffer-size))
                        (let ((sentences nil))
                          (while (and (< (point) (point-max))
                                      (let ((start (point)))
                                        (when (eq (coq-script-parse-cmdend-forward)
                                                  'cmd)
                                          (push (coq-eglot-twin--make-sentence
                                                 start (point)
                                                 (coq-eglot-twin--normalize
                                                  start (point)))
                                                sentences)
                                          t)))
                            (forward-comment (buffer-size)))
                          (vconcat (nreverse sentences))))))))
      (cdr coq-eglot-twin--sentences))))

(defun coq-eglot-twin--common-subsequence (a b)
  "Pairs (I . J) of a longest common subsequence of vectors A and B.
In increasing order: A[I] and B[J] are `equal'.  The common beginning
and end are paired first, the middle part with the algorithm of Myers.
If the middle parts differ by more than
`coq-eglot-twin-max-differences' elements, they are not paired."
  (let* ((n (length a)) (m (length b))
         (prefix 0) (suffix 0) (pairs nil))
    (while (and (< prefix n) (< prefix m)
                (equal (aref a prefix) (aref b prefix)))
      (push (cons prefix prefix) pairs)
      (setq prefix (1+ prefix)))
    (while (and (< (+ prefix suffix) n) (< (+ prefix suffix) m)
                (equal (aref a (- n suffix 1)) (aref b (- m suffix 1))))
      (setq suffix (1+ suffix)))
    (let ((middle (coq-eglot-twin--myers
                   (substring a prefix (- n suffix))
                   (substring b prefix (- m suffix)))))
      (dolist (pair middle)
        (push (cons (+ prefix (car pair)) (+ prefix (cdr pair))) pairs)))
    (dotimes (i suffix)
      (push (cons (- n suffix (- i)) (- m suffix (- i))) pairs))
    (nreverse pairs)))

(defun coq-eglot-twin--myers (a b)
  "Pairs (I . J) of a longest common subsequence of vectors A and B.
In increasing order.  The algorithm of Myers, in O((N+M)D) for D
differences.  Nil if D exceeds `coq-eglot-twin-max-differences'."
  (let* ((n (length a)) (m (length b))
         (max-d (min (+ n m) coq-eglot-twin-max-differences))
         (offset (1+ max-d))
         (v (make-vector (+ 3 (* 2 max-d)) 0))
         ;; the part -D-1..D+1 of V before each step D, for the way back
         (trace nil)
         (found nil))
    (catch 'found
      (dotimes (d (1+ max-d))
        (push (substring v (- offset d 1) (+ offset d 2)) trace)
        (let ((k (- d)))
          (while (<= k d)
            (let* ((x (if (or (= k (- d))
                              (and (/= k d)
                                   (< (aref v (+ offset k -1))
                                      (aref v (+ offset k 1)))))
                          (aref v (+ offset k 1))
                        (1+ (aref v (+ offset k -1)))))
                   (y (- x k)))
              (while (and (< x n) (< y m) (equal (aref a x) (aref b y)))
                (setq x (1+ x) y (1+ y)))
              (aset v (+ offset k) x)
              (when (and (>= x n) (>= y m))
                (setq found d)
                (throw 'found nil)))
            (setq k (+ k 2))))))
    (when found
      (let ((x n) (y m) (pairs nil) (d found))
        (dolist (before trace)
          ;; BEFORE is V before step D, indexed from -D-1
          (let* ((k (- x y))
                 (get (lambda (k) (aref before (+ k d 1))))
                 (prev-k (if (or (= k (- d))
                                 (and (/= k d)
                                      (< (funcall get (1- k))
                                         (funcall get (1+ k)))))
                             (1+ k)
                           (1- k)))
                 (prev-x (funcall get prev-k))
                 (prev-y (- prev-x prev-k)))
            (while (and (> x prev-x) (> y prev-y))
              (setq x (1- x) y (1- y))
              (push (cons x y) pairs))
            (when (> d 0)
              (setq x prev-x y prev-y))
            (setq d (1- d))))
        pairs))))

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
                    (coq-eglot-twin--common-subsequence
                     (cl-map 'vector #'coq-eglot-twin--sentence-text
                             (coq-eglot-twin--sentences this))
                     (cl-map 'vector #'coq-eglot-twin--sentence-text
                             (coq-eglot-twin--sentences other))))))
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

(defun coq-eglot-twin--gaps (pairs n m)
  "The runs of two sequences of lengths N and M between their PAIRS.
PAIRS, a list or a vector, are the pairs (I . J) of the indices of
their paired elements, in increasing order.  A list of (RUN-A . RUN-B),
the indices of the elements of the run in each sequence, each (FIRST
. END), END excluded, or nil if the run is empty on this side."
  (let ((runs nil) (i 0) (j 0))
    (seq-doseq (pair (vconcat pairs (vector (cons n m))))
      (when (or (< i (car pair)) (< j (cdr pair)))
        (push (cons (and (< i (car pair)) (cons i (car pair)))
                    (and (< j (cdr pair)) (cons j (cdr pair))))
              runs))
      (setq i (1+ (car pair)) j (1+ (cdr pair))))
    (nreverse runs)))

(defun coq-eglot-twin--zones (&optional buffer)
  "The diverging zones of BUFFER and of its twin.
A list of (THIS . TWIN), the indices of the sentences of the zone in
BUFFER and in its twin, each (FIRST . END), END excluded, or nil if the
zone is empty on this side.  BUFFER defaults to the current one."
  (with-current-buffer (or buffer (current-buffer))
    (coq-eglot-twin--gaps (coq-eglot-twin--align)
                          (length (coq-eglot-twin--sentences))
                          (length (coq-eglot-twin--sentences
                                   coq-eglot--twin)))))

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
        (let ((words (coq-eglot-twin--pieces
                      this coq-eglot-twin--word-regexp
                      (coq-eglot-twin--sentence-start (aref sentences (car range)))
                      (coq-eglot-twin--sentence-end
                       (aref sentences (1- (cdr range))))
                      t))
              (twin-words (coq-eglot-twin--pieces
                           twin coq-eglot-twin--word-regexp
                           (coq-eglot-twin--sentence-start
                            (aref twin-sentences (car twin-range)))
                           (coq-eglot-twin--sentence-end
                            (aref twin-sentences (1- (cdr twin-range))))
                           t)))
          (pcase-dolist (`(,run . ,twin-run)
                         (coq-eglot-twin--unmatched words twin-words))
            (when run
              (coq-eglot-twin--mark this words run face 12 t))
            (when twin-run
              (coq-eglot-twin--mark twin twin-words twin-run twin-face 12 t))))))))

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

(defun coq-eglot-twin--blend (face1 face2)
  "The mean of the backgrounds of FACE1 and FACE2, or nil if one has none."
  (let ((color1 (coq-eglot-twin--background face1))
        (color2 (coq-eglot-twin--background face2)))
    (when (and color1 color2)
      (apply #'color-rgb-to-hex
             (append (cl-mapcar (lambda (a b) (/ (+ a b) 2))
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
                               (or (coq-eglot-twin--blend (car key) (cdr key))
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

(defun coq-eglot-twin--after-change (&rest _)
  "Schedule the update of the highlighting of the twins."
  (let ((twins coq-eglot-twin--twins))
    (when twins
      (coq-eglot-twin--once (coq-eglot-twin--twins-highlight-timer twins)
        (run-with-idle-timer coq-eglot-twin-idle-delay nil
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
;; or its error.

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
The position corresponding to the one of its twin, the leader."
  (let ((leader coq-eglot--twin))
    (coq-eglot-twin-position
     (with-current-buffer leader (coq-eglot-position)) leader)))

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
  "Show the error of the current buffer, a follower, in its windows.
See `coq-eglot-error-hook'."
  (when (and coq-eglot-twin-synchronize (buffer-live-p coq-eglot--twin)
             (not (coq-eglot-twin--leader-p)))
    (setq coq-eglot-twin--following nil)
    (coq-eglot-twin--show (point))))

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
        (condition-case err
            (cond
             ((coq-eglot-lsp-ensure-server t)
              (coq-eglot-twin--move (coq-eglot-twin--target)))
             ;; later: waiting for its server here would block the
             ;; answers to the leader
             ((coq-eglot-lsp-connecting-servers)
              (setq coq-eglot-twin--follow-timer
                    (run-at-time 0.1 nil #'coq-eglot-twin--follow buffer)))
             (t (error "No Coq language server")))
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
  (when (and coq-eglot-twin-synchronize (buffer-live-p coq-eglot--twin))
    (cond
     ((coq-eglot-twin--leader-p)
      (coq-eglot-twin--schedule-follow coq-eglot--twin))
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
If their proof positions do not correspond, only remove the highlighting."
  (let* ((twin (buffer-local-value 'coq-eglot--twin buffer))
         (outputs (with-current-buffer buffer (coq-eglot-output-buffers)))
         (twin-outputs (with-current-buffer twin (coq-eglot-output-buffers)))
         (compare (and coq-eglot-twin-compare-outputs
                       (coq-eglot-twin--corresponding-p buffer))))
    (cl-mapc (lambda (output twin-output)
               (coq-eglot-twin--uncompare output)
               (coq-eglot-twin--uncompare twin-output)
               (when (and compare (buffer-live-p output)
                          (buffer-live-p twin-output))
                 (coq-eglot-twin--compare-buffers
                  output twin-output
                  (coq-eglot-twin--face nil buffer)
                  (coq-eglot-twin--face t buffer)
                  (coq-eglot-twin--face nil twin)
                  (coq-eglot-twin--face t twin))))
             outputs twin-outputs)))

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
  (coq-eglot-twin--gaps (coq-eglot-twin--common-subsequence
                         (cl-map 'vector #'cddr a) (cl-map 'vector #'cddr b))
                        (length a) (length b)))

(defun coq-eglot-twin--mark (buffer pieces range face priority &optional script)
  "Highlight the PIECES of BUFFER in RANGE with FACE, at PRIORITY.
Line by line.  In a SCRIPT buffer if non-nil, the words of its
diverging zones, see `coq-eglot-twin--refine-zones', otherwise an
output buffer.  Return the bounds (START . END) of the range."
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
            (if script
                (progn (overlay-put overlay 'coq-eglot-twin-refine t)
                       (push overlay coq-eglot-twin--overlays))
              (overlay-put overlay 'coq-eglot-twin t)
              (push overlay coq-eglot-twin--output-overlays)))
          (setq i (1+ i))))))
  (cons (car (aref pieces (car range)))
        (cadr (aref pieces (1- (cdr range))))))

(defun coq-eglot-twin--compare-buffers (a b face-a words-a face-b words-b)
  "Highlight the lines of buffers A and B without match in the other one.
With FACE-A in A and FACE-B in B.  In the lines that differ in both,
the words that differ, with WORDS-A and WORDS-B."
  (let ((lines-a (coq-eglot-twin--pieces a "^.+$"))
        (lines-b (coq-eglot-twin--pieces b "^.+$"))
        (word coq-eglot-twin--word-regexp))
    (pcase-dolist (`(,range-a . ,range-b)
                   (coq-eglot-twin--unmatched lines-a lines-b))
      (let ((bounds-a (and range-a (coq-eglot-twin--mark a lines-a range-a
                                                         face-a 10)))
            (bounds-b (and range-b (coq-eglot-twin--mark b lines-b range-b
                                                         face-b 10))))
        (when (and bounds-a bounds-b)
          (let ((pieces-a (coq-eglot-twin--pieces a word (car bounds-a)
                                                  (cdr bounds-a)))
                (pieces-b (coq-eglot-twin--pieces b word (car bounds-b)
                                                  (cdr bounds-b))))
            (pcase-dolist (`(,run-a . ,run-b)
                           (coq-eglot-twin--unmatched pieces-a pieces-b))
              (when run-a
                (coq-eglot-twin--mark a pieces-a run-a words-a 11))
              (when run-b
                (coq-eglot-twin--mark b pieces-b run-b words-b 11)))))))))

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
