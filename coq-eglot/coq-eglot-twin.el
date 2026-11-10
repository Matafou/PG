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
;; Later: the alignment of the sentences of the two buffers, and the
;; synchronization of their proof positions.

;;; Code:

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
`coq-eglot-twin-unpair'.
With SWITCH, or `coq-eglot-twin-opam-switch', the server of OTHER is the
one of this opam switch, see `coq-eglot-twin-set-opam-switch'.
Interactively, with a prefix argument, ask SWITCH."
  (interactive
   (with-current-buffer (coq-eglot--script-buffer)
     (when coq-eglot--twin
       (user-error "Coq: this buffer has a twin already, %s"
                   (buffer-name coq-eglot--twin)))
     (list (coq-eglot-twin--read-buffer)
           (and current-prefix-arg (coq-eglot-twin--read-opam-switch)))))
  (let ((this (coq-eglot--script-buffer)))
    (when (eq this other)
      (user-error "Coq: a buffer cannot be its own twin"))
    (unless (buffer-local-value 'coq-eglot-mode other)
      (user-error "Coq: %s is not a script buffer of the Eglot backend"
                  (buffer-name other)))
    (when (or (buffer-local-value 'coq-eglot--twin this)
              (buffer-local-value 'coq-eglot--twin other))
      (user-error "Coq: unpair first, see `coq-eglot-twin-unpair'"))
    (with-current-buffer other
      ;; it leaves the output it shared
      (coq-eglot--forget-active)
      (setq coq-eglot--buffer-output
            (coq-eglot--make-output (format "<%s>" (buffer-name other))))
      (setq coq-eglot--twin this)
      (add-hook 'kill-buffer-hook #'coq-eglot-twin--on-kill nil t)
      (coq-eglot--update-overlays))
    (with-current-buffer this
      (setq coq-eglot--twin other)
      (add-hook 'kill-buffer-hook #'coq-eglot-twin--on-kill nil t)
      (coq-eglot-twin--update-label))
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
      (mapc #'jsonrpc-shutdown (coq-eglot-lsp-connecting-servers))
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
  (let* ((this (coq-eglot--script-buffer))
         (twin (and (buffer-local-value 'coq-eglot--twin this)
                    (coq-eglot-twin--own-output-side this))))
    (unless (buffer-live-p twin)
      (user-error "Coq: this buffer has no twin, see `coq-eglot-twin-pair'"))
    (with-current-buffer twin
      (coq-eglot-twin--set-switch switch))
    (message "Coq: the server of %s is the one of opam switch %s"
             (buffer-name twin) switch)))

(defun coq-eglot-twin--own-output-side (buffer)
  "The one of BUFFER and its twin with an output of its own."
  (if (buffer-local-value 'coq-eglot--buffer-output buffer)
      buffer
    (buffer-local-value 'coq-eglot--twin buffer)))

(defun coq-eglot-twin--forget (buffer)
  "Forget the twin of BUFFER, in BUFFER only."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (setq coq-eglot--twin nil)
      (setq coq-eglot--twin-label nil)
      (remove-hook 'kill-buffer-hook #'coq-eglot-twin--on-kill t))))

(defun coq-eglot-twin--unpair (buffer)
  "Unpair BUFFER and its twin.
The one with an output of its own goes back to the default output, the
buffers of its output are killed."
  (let* ((twin (buffer-local-value 'coq-eglot--twin buffer))
         (side (coq-eglot-twin--own-output-side buffer)))
    (when (buffer-live-p side)
      (with-current-buffer side
        (dolist (name (list (coq-eglot--goals-name)
                            (coq-eglot--conclusion-name)
                            (coq-eglot--response-name)))
          (let ((output (get-buffer name)))
            (when output
              (coq-eglot--delete-windows name)
              (kill-buffer output))))
        (setq coq-eglot--buffer-output nil)
        (coq-eglot--update-overlays)))
    (coq-eglot-twin--forget buffer)
    (coq-eglot-twin--forget twin)))

(defun coq-eglot-twin-unpair ()
  "Unpair the current script buffer and its twin.
See `coq-eglot-twin-pair'.  Its twin goes back to the shared output, its
goals and messages buffers are killed."
  (interactive)
  (let ((this (coq-eglot--script-buffer)))
    (unless (buffer-local-value 'coq-eglot--twin this)
      (user-error "Coq: this buffer has no twin"))
    (let ((twin (buffer-local-value 'coq-eglot--twin this)))
      (coq-eglot-twin--unpair this)
      (message "Coq: %s and %s are no longer twins"
               (buffer-name this) (buffer-name twin)))))

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
  (let* ((this (coq-eglot--script-buffer))
         (twin (buffer-local-value 'coq-eglot--twin this)))
    (unless (buffer-live-p twin)
      (user-error "Coq: this buffer has no twin, see `coq-eglot-twin-pair'"))
    (select-window (or (get-buffer-window this) (selected-window)))
    (set-window-dedicated-p (selected-window) nil)
    (delete-other-windows)
    (let ((left (selected-window))
          (right (split-window nil nil 'right)))
      (set-window-buffer left this)
      (set-window-buffer right twin)
      (dolist (side (list this twin))
        (with-current-buffer side
          (coq-eglot--activate)
          (coq-eglot-layout-windows)))
      (select-window left))))

(provide 'coq-eglot-twin)

;;; coq-eglot-twin.el ends here
