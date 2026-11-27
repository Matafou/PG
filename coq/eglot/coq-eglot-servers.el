;;; coq-eglot-servers.el --- The Rocq checking a project  -*- lexical-binding:t -*-

;; This file is part of Proof General.

;; Portions © Copyright 2026  Pierre Courtieu

;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;;
;; Which Rocq checks the script buffers: an installation of Rocq is
;; designated by its program rocq (or coqtop), like `coq-prog-name' for
;; Proof General; its language server is next to it, see
;; `coq-eglot-lsp-server-program'.  The candidates are those of the opam
;; switches, if opam is installed, the one found in `exec-path', and the
;; executables designated during the session.  Those without a language
;; server cannot be chosen.
;;
;; The Rocq is a setting of the project, see `coq-eglot-lsp-project':
;; all the files of a project are checked by the same Rocq, which
;; compiles their libraries; an isolated file is a project of its own.
;; Unless chosen, the Rocq of a project is the one of `coq-prog-name'
;; if set by the user, or else of `exec-path', until its first server
;; starts, see `coq-eglot-lsp--project-rocqs': an opam switch selected
;; after visiting a file is taken into account.  Choosing another one
;; stops the server of the project, after confirmation if some buffers
;; go back to their beginning.  The choice holds for the session: a
;; .dir-locals.el file setting `coq-prog-name' is neither written nor
;; changed, the choice takes precedence over it.  The only exception is
;; a twin in the project of its twin, see `coq-eglot-twin-set-rocq'.

;;; Code:

(require 'cl-lib)
(require 'subr-x)
(require 'coq-eglot)

;;; Installations

(defvar coq-eglot-servers--designated nil
  "Rocq programs designated during the session, file names.
The most recent first, see `coq-eglot-servers-read'.")

(defvar coq-eglot-servers--candidates 'unknown
  "Cache of `coq-eglot-servers-candidates', or `unknown'.
See `coq-eglot-servers-rescan'.")

(defconst coq-eglot-servers--rocq-names '("rocq" "coqtop")
  "Names of the Rocq program, tried in this order.")

(defun coq-eglot-servers--program-in (bin)
  "The first of rocq and coqtop in directory BIN, or nil."
  (seq-find #'file-executable-p
            (mapcar (lambda (name) (expand-file-name name bin))
                    coq-eglot-servers--rocq-names)))

(defun coq-eglot-servers--opam (&rest args)
  "Output lines of opam with ARGS, or nil if opam is absent or fails."
  (and (executable-find "opam")
       (ignore-errors (apply #'process-lines "opam" args))))

(defun coq-eglot-servers--opam-rocqs ()
  "Rocq programs of the opam switches, a list of (LABEL . FILE).
LABEL is the name of the switch, or the directory of a local switch."
  (let ((root (car (coq-eglot-servers--opam "var" "root"))))
    (delq nil
          (mapcar (lambda (switch)
                    (let* ((local (file-name-absolute-p switch))
                           (prefix (if local
                                       (expand-file-name "_opam" switch)
                                     (and root (expand-file-name switch root))))
                           (program (and prefix
                                         (coq-eglot-servers--program-in
                                          (expand-file-name "bin" prefix)))))
                      (and program
                           (cons (if local
                                     (file-name-nondirectory
                                      (directory-file-name switch))
                                   switch)
                                 program))))
                  (coq-eglot-servers--opam "switch" "list" "--short")))))

(defun coq-eglot-servers-label (program)
  "Short name of the Rocq PROGRAM: its opam switch, or its file name.
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

(defun coq-eglot-servers-candidates ()
  "Rocq programs that may check a project, a list of (LABEL . FILE).
Those of the opam switches, the one found in `exec-path', those
designated during the session.  Each executable once.  Cached, see
`coq-eglot-servers-rescan'.  With or without a language server, see
`coq-eglot-lsp-server-program'."
  (when (eq coq-eglot-servers--candidates 'unknown)
    (setq coq-eglot-servers--candidates
          (append (coq-eglot-servers--opam-rocqs)
                  (let ((program (seq-some #'executable-find
                                           coq-eglot-servers--rocq-names)))
                    (and program
                         (list (cons (format "%s (exec-path)"
                                             (coq-eglot-servers-label program))
                                     program)))))))
  (let ((seen nil))
    (seq-filter (lambda (candidate)
                  (let ((file (file-truename (cdr candidate))))
                    (unless (member file seen)
                      (push file seen))))
                (append (mapcar (lambda (file)
                                  (cons (abbreviate-file-name file) file))
                                coq-eglot-servers--designated)
                        coq-eglot-servers--candidates))))

(defun coq-eglot-servers-rescan ()
  "Look again for the installations of Rocq, see `coq-eglot-servers-candidates'."
  (interactive)
  (setq coq-eglot-servers--candidates 'unknown)
  (clrhash coq-eglot-compile--rocq-versions)
  (message "Coq: %d installations of Rocq found"
           (length (coq-eglot-servers-candidates))))

(defun coq-eglot-servers-describe (label program)
  "Name of the Rocq PROGRAM in menus: LABEL and its version."
  (let ((version (coq-eglot-compile-rocq-version program)))
    (concat (if version (format "%s (Rocq %s)" label version) label)
            (if (coq-eglot-lsp-server-program program)
                ""
              ", no language server"))))

(defconst coq-eglot-servers--other "Other executable..."
  "Choice of `coq-eglot-servers-read' asking an executable.")

(defun coq-eglot-servers-check (rocq)
  "Signal a user error if the Rocq program ROCQ has no language server.
See `coq-eglot-lsp-server-program'.  Return ROCQ."
  (unless (coq-eglot-lsp-server-program rocq)
    (user-error "Coq: no language server (rocq-lsp or coq-lsp) next to %s"
                rocq))
  rocq)

(defun coq-eglot-servers-read-executable ()
  "Ask a Rocq program, remember it for the session, return it.
It must have a language server, see `coq-eglot-servers-check'."
  (let ((file (expand-file-name
               (read-file-name "Executable of rocq or coqtop: "
                               nil nil t nil #'file-executable-p))))
    (unless (and (file-executable-p file) (not (file-directory-p file)))
      (user-error "Coq: %s is not an executable" file))
    (coq-eglot-servers-check file)
    (setq coq-eglot-servers--designated
          (cons file (delete file coq-eglot-servers--designated)))
    file))

(defun coq-eglot-servers-read (prompt &optional current)
  "Ask a Rocq program with PROMPT, return it.
Among the candidates with a language server, see
`coq-eglot-servers-candidates'.  CURRENT, a Rocq program, is the
default."
  (let* ((candidates
          (mapcar (lambda (candidate)
                    (cons (coq-eglot-servers-describe (car candidate)
                                                      (cdr candidate))
                          (cdr candidate)))
                  (seq-filter (lambda (candidate)
                                (coq-eglot-lsp-server-program (cdr candidate)))
                              (coq-eglot-servers-candidates))))
         (default (car (seq-find (lambda (candidate)
                                   (coq-eglot-lsp-same-rocq-p
                                    (cdr candidate) current))
                                 candidates)))
         (choice (completing-read
                  prompt
                  (append (mapcar #'car candidates)
                          (list coq-eglot-servers--other))
                  nil t nil nil default)))
    (if (equal choice coq-eglot-servers--other)
        (coq-eglot-servers-read-executable)
      (cdr (assoc choice candidates)))))

;;; The Rocq of a project

(defun coq-eglot-servers-project-buffers ()
  "Script buffers sharing the server of the project of the current buffer.
Not those with a server of their own, see `coq-eglot-lsp-own-rocq'."
  (let ((project (coq-eglot-lsp-project-id)))
    (seq-filter (lambda (buffer)
                  (with-current-buffer buffer
                    (and (bound-and-true-p coq-eglot-mode)
                         (not coq-eglot-lsp-own-rocq)
                         (equal (coq-eglot-lsp-project-id) project))))
                (buffer-list))))

(defun coq-eglot-servers--started-p (buffer)
  "Non-nil if BUFFER would lose something by restarting.
It has a processed part or a check running."
  (with-current-buffer buffer
    (or (> (coq-eglot-position) (point-min))
        (coq-eglot-checking-p))))

(defun coq-eglot-servers-confirm-restart (buffers rocq)
  "Ask whether BUFFERS may go back to their beginning with ROCQ.
Only those with a processed part or a check running count.  Signal a
user error if not."
  (let ((started (seq-filter #'coq-eglot-servers--started-p buffers)))
    (when (and started
               (not (yes-or-no-p
                     (format "Coq: %s will go back to the beginning, \
checked by %s.  Continue? "
                             (mapconcat #'buffer-name started ", ")
                             (coq-eglot-servers-describe
                              (coq-eglot-servers-label rocq) rocq)))))
      (user-error "Coq: Rocq not changed"))))

(defun coq-eglot-set-rocq (rocq)
  "Check the files of the project of the current buffer with ROCQ.
ROCQ is a Rocq program, rocq or coqtop, with a language server next to
it: it designates an installation of Rocq.  The server of the project
stops, after confirmation if buffers of the project go back to their
beginning.  For this session: a .dir-locals.el setting `coq-prog-name'
does not change, ROCQ takes precedence.  A buffer with a server of its
own, a twin, changes alone, see `coq-eglot-twin-set-rocq'.
Interactively, ask among the candidates, see
`coq-eglot-servers-candidates'."
  (interactive
   (with-current-buffer (coq-eglot-script-buffer)
     (list (coq-eglot-servers-read
            (format "Rocq of %s: " (coq-eglot-lsp-project-name))
            (ignore-errors (coq-eglot-lsp-rocq))))))
  (coq-eglot-servers-check rocq)
  (with-current-buffer (coq-eglot-script-buffer)
    (if (and coq-eglot-lsp-own-rocq (fboundp 'coq-eglot-twin-set-rocq)
             coq-eglot--twin)
        (coq-eglot-twin-set-rocq rocq (current-buffer))
      (coq-eglot-servers-set-project-rocq rocq))))

(defun coq-eglot-servers-set-project-rocq (rocq)
  "Check the files of the project of the current buffer with ROCQ.
See `coq-eglot-set-rocq'."
  (let ((project (coq-eglot-lsp-project-id))
        (buffers (coq-eglot-servers-project-buffers)))
    (if (coq-eglot-lsp-same-rocq-p
         rocq (ignore-errors (coq-eglot-lsp-default-rocq)))
        (message "Coq: %s is already checked by %s"
                 (coq-eglot-lsp-project-name project)
                 (coq-eglot-servers-label rocq))
      (coq-eglot-servers-confirm-restart buffers rocq)
      (coq-eglot-stop-server-of-buffers
       buffers (lambda () (coq-eglot-lsp-set-project-rocq project rocq)))
      ;; no buffer to stop, like when none is visited yet
      (coq-eglot-lsp-set-project-rocq project rocq)
      ;; without waiting, the commands wait for it to connect
      (when (memq (current-buffer) buffers)
        (coq-eglot-lsp-connect))
      (message "Coq: %s is checked by %s%s"
               (coq-eglot-lsp-project-name project)
               (coq-eglot-servers-describe (coq-eglot-servers-label rocq) rocq)
               (if (seq-some (lambda (buffer)
                               (local-variable-p 'coq-prog-name buffer))
                             buffers)
                   ", instead of its .dir-locals.el for this session"
                 "")))))

;;; Menus

(defun coq-eglot-servers-menu-items (current action)
  "Menu items choosing a Rocq, one per candidate, then another one.
CURRENT is the Rocq program in use, selected.  ACTION is a function
called with the Rocq program chosen.  Those without a language server
are inactive."
  (append
   (mapcar (lambda (candidate)
             (let ((rocq (cdr candidate)))
               (vector (coq-eglot-servers-describe (car candidate) rocq)
                       (lambda () (interactive) (funcall action rocq))
                       :style 'radio
                       :selected (coq-eglot-lsp-same-rocq-p rocq current)
                       :active (and (coq-eglot-lsp-server-program rocq) t))))
           (coq-eglot-servers-candidates))
   (list "---"
         (vector coq-eglot-servers--other
                 (lambda () (interactive)
                   (funcall action (coq-eglot-servers-read-executable))))
         ["Look Again for Installations" coq-eglot-servers-rescan])))

(defun coq-eglot-servers-menu (_items)
  "Submenu choosing the Rocq of the project of the script buffer.
A :filter of `easy-menu-define', see `coq-eglot-set-rocq'."
  (let ((buffer (ignore-errors (coq-eglot-script-buffer))))
    (if (not buffer)
        (list ["No script buffer" ignore :active nil])
      (with-current-buffer buffer
        (coq-eglot-servers-menu-items
         (ignore-errors (coq-eglot-lsp-rocq))
         (lambda (rocq)
           (with-current-buffer buffer
             (coq-eglot-set-rocq rocq))))))))

(provide 'coq-eglot-servers)

;;; coq-eglot-servers.el ends here
