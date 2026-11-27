;;; coq-eglot-test-servers.el --- Tests of the Eglot backend: the Rocq of a project  -*- lexical-binding: t -*-
;;
;; This file is part of Proof General.
;;
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Test the choice of the Rocq checking a project, and the servers of
;; twins in the same project, with the Eglot backend.
;; See coq-eglot-test-common.el for the settings and the utilities.

;;; Code:

(require 'coq-eglot-test-common
         (expand-file-name "coq-eglot-test-common"
                           (file-name-directory
                            (or load-file-name buffer-file-name))))
(require 'coq-eglot-servers)
(require 'coq-eglot-twin)

;;; Without server

(defmacro with-project (files &rest body)
  "Run BODY in a temporary project with a _CoqProject and FILES.
FILES is a list of (NAME . TEXT).  The directory is bound to `dir', its
files are visited by `visit'.  Their buffers and servers are killed
afterwards, the choices of Rocq for the project are forgotten."
  (declare (indent 1) (debug t))
  `(let* ((dir (file-name-as-directory (make-temp-file "coq-eglot-project-" t)))
          (proof-three-window-enable nil))
     (with-temp-file (expand-file-name "_CoqProject" dir)
       (insert "-R . Proj\n"))
     (pcase-dolist (`(,name . ,text) ,files)
       (let ((file (expand-file-name name dir)))
         (make-directory (file-name-directory file) t)
         (with-temp-file file (insert text))))
     (unwind-protect
         (cl-flet ((visit (name)
                     (find-file-noselect (expand-file-name name dir))))
           ,@body)
       (coq-eglot-lsp-set-project-server (cons 'transient dir) nil)
       (dolist (buffer (buffer-list))
         (when (and (buffer-file-name buffer)
                    (string-prefix-p dir (buffer-file-name buffer)))
           (with-current-buffer buffer
             (when coq-eglot--twin (coq-eglot-twin-unpair))
             (ignore-errors (coq-eglot-lsp-shutdown))
             (set-buffer-modified-p nil))
           (kill-buffer buffer)))
       (delete-directory dir t)
       (delete-other-windows))))

(ert-deftest coq-eglot-servers-own-project ()
  "A buffer with a server of its own has a project of its own, with the
root of the project shared by the other files."
  (with-project '(("a.v" . "Definition a := 0.\n"))
    (with-current-buffer (visit "a.v")
      (should (equal (eglot--current-project) (cons 'transient dir)))
      (should (equal (coq-eglot-lsp-project-root) dir))
      (setq coq-eglot-lsp-own-server (list "sh"))
      (unwind-protect
          (progn
            (should (equal (eglot--current-project)
                           (list 'coq-eglot-own (cons 'transient dir)
                                 (buffer-file-name))))
            (should (equal (project-root (eglot--current-project)) dir))
            (should (equal (coq-eglot-lsp-project-root) dir)))
        (setq coq-eglot-lsp-own-server nil)))))

(ert-deftest coq-eglot-servers-isolated-files ()
  "Without project file, each file is a project of its own, in its
directory.  Also with `coq-use-project-file' nil."
  (let ((dir (file-name-as-directory (make-temp-file "coq-eglot-isolated-" t)))
        (buffers nil))
    (unwind-protect
        (progn
          (dolist (name '("a.v" "b.v"))
            (with-temp-file (expand-file-name name dir)
              (insert "Definition x := 0.\n"))
            (push (find-file-noselect (expand-file-name name dir)) buffers))
          (let ((projects (mapcar (lambda (buffer)
                                    (with-current-buffer buffer
                                      (should (equal (coq-eglot-lsp-project-root)
                                                     dir))
                                      (eglot--current-project)))
                                  buffers)))
            (should-not (equal (car projects) (cadr projects)))
            (should (equal (car projects)
                           (list 'coq-eglot-file
                                 (buffer-file-name (car buffers)) dir)))
            (should (equal (with-current-buffer (car buffers)
                             (coq-eglot-lsp-project-name))
                           "b.v"))))
      (dolist (buffer buffers) (kill-buffer buffer))
      (delete-directory dir t)))
  (with-project '(("a.v" . "Definition a := 0.\n"))
    (with-current-buffer (visit "a.v")
      (let ((coq-use-project-file nil))
        (should (eq (car (coq-eglot-lsp-project-id)) 'coq-eglot-file))))))

(ert-deftest coq-eglot-servers-fixed-at-first-start ()
  "The Rocq of a project follows `exec-path' until its first server
starts, then it is fixed for the session: like an opam switch selected
after visiting the file, and not after."
  (skip-unless-server)
  (with-project '(("a.v" . "Definition a := 0.\n"))
    (with-current-buffer (visit "a.v")
      (let ((server (coq-eglot-lsp--absolute-command
                     (coq-eglot-lsp-server-command))))
        (should-not (coq-eglot-lsp-project-server))
        ;; another switch before the start: not found
        (with-programs nil
          (should-error (coq-eglot-lsp-server-command) :type 'user-error))
        (coq-eglot-lsp-connect)
        (should (wait-until #'coq-eglot-lsp-current-server 10))
        (should (equal (coq-eglot-lsp-project-server) server))
        ;; another switch after the start: the same server
        (with-programs (list (car server))
          (should (equal (coq-eglot-lsp-server-command) server)))))))

(ert-deftest coq-eglot-servers-compile-version ()
  "The compilation uses the programs and the version of the Rocq of the
project, not those of `exec-path'."
  (skip-unless-server)
  (with-project '(("a.v" . "Definition a := 0.\n"))
    (with-current-buffer (visit "a.v")
      (let ((server (other-server)))
        (skip-unless server)
        (coq-eglot-lsp-set-project-server (coq-eglot-lsp-project-id) server)
        (coq-eglot-compile--set-programs)
        (should (equal (file-name-directory coq-compiler)
                       (file-name-directory (car server))))
        (should (local-variable-p 'coq-autodetected-version))
        (should (equal (coq-version) (coq-eglot-compile-rocq-version
                                      (car server))))))))

(ert-deftest coq-eglot-servers-command-precedence ()
  "The server of the buffer alone, then the one chosen for the project,
then `coq-eglot-server-program'."
  (with-project '(("a.v" . "Definition a := 0.\n"))
    (with-current-buffer (visit "a.v")
      (let ((coq-eglot-server-program (list "cat")))
        (should (equal (coq-eglot-lsp-server-command) '("cat")))
        (coq-eglot-lsp-set-project-server (cons 'transient dir) (list "sh"))
        (should (equal (coq-eglot-lsp-server-command) '("sh")))
        (should (equal (coq-eglot-lsp-project-command) '("sh")))
        (setq coq-eglot-lsp-own-server (list "ls"))
        (unwind-protect
            (progn
              (should (equal (coq-eglot-lsp-server-command) '("ls")))
              (should (equal (coq-eglot-lsp-project-command) '("sh")))
              (should (coq-eglot-lsp-foreign-p)))
          (setq coq-eglot-lsp-own-server nil))
        (should-not (coq-eglot-lsp-foreign-p))))))

(ert-deftest coq-eglot-servers-same-server ()
  "The same executable through other names is the same server."
  (let ((sh (file-truename (executable-find "sh"))))
    (should (coq-eglot-lsp-same-server-p (list "sh") (list sh)))
    (should-not (coq-eglot-lsp-same-server-p (list "sh") (list "cat")))
    (should-not (coq-eglot-lsp-same-server-p (list "sh" "-x") (list "sh")))
    ;; a server not found, like no coq-lsp in exec-path
    (should-not (coq-eglot-lsp-same-server-p (list "sh") nil))
    (should-not (coq-eglot-lsp-same-server-p nil (list "sh")))))

(ert-deftest coq-eglot-servers-without-server-in-exec-path ()
  "Without server in `exec-path', the Rocq of a project can be chosen,
the buffers of the project then use it."
  (skip-unless-server)
  (with-project '(("a.v" . "Definition a := 0.\n"))
    (with-current-buffer (visit "a.v")
      (let ((server (coq-eglot-lsp--program-file
                     (car (coq-eglot-lsp-server-command)))))
        ;; only its absolute file name is found
        (with-programs (list server)
          (should-error (coq-eglot-lsp-project-command) :type 'user-error)
          (coq-eglot-servers-set-project-rocq (list server))
          (should (equal (coq-eglot-lsp-project-server (cons 'transient dir)) (list server)))
          (should (equal (coq-eglot-lsp-server-command) (list server)))
          (run #'coq-eglot-process-buffer)
          (should (= (coq-eglot-position)
                     (coq-eglot--skip-backward (point-max)))))))))

(ert-deftest coq-eglot-servers-local-requires ()
  "The Require sentences loading a library of the project, fully or
partially qualified, with or without From, not those of other libraries."
  (with-project '(("lib.v" . "Definition l := 0.\n")
                  ("sub/deep.v" . "Definition d := 0.\n")
                  ("a.v" . "From Stdlib Require Import Arith.
Require Import (* comment *) Proj.lib.
From Proj Require Export deep.
Require Import -(notations) lib.
Require Stdlib.Lists.List.
"))
    (with-current-buffer (visit "a.v")
      (should (equal (mapcar (lambda (bounds)
                               (line-number-at-pos (car bounds)))
                             (coq-eglot-compile-local-requires))
                     '(2 3 4)))
      (should (equal (coq-eglot-compile--required-names
                      (point-min) (line-end-position))
                     '((("Stdlib") "Arith")))))))

;;; With servers

(defmacro with-project-twins (twin-text &rest body)
  "Run BODY in a.v paired with b.v of TWIN-TEXT, in the same project.
The text of a.v is the one of eglot_slow.v.  Bound to `this' and `twin'."
  (declare (indent 1) (debug t))
  `(progn
     (skip-unless-server)
     (let ((slow (with-temp-buffer
                   (insert-file-contents "eglot_slow.v")
                   (buffer-string))))
       (with-project (list (cons "lib.v" "Definition l := 0.\n")
                           (cons "a.v" slow)
                           (cons "b.v" (or ,twin-text slow)))
         (let ((this (visit "a.v"))
               (twin (visit "b.v"))
               (coq-eglot-twin-synchronize nil))
           (with-current-buffer this
             (switch-to-buffer this)
             (delete-other-windows)
             (coq-eglot-twin-pair twin)
             ,@body))))))

(defun twin-server (buffer)
  "The server of BUFFER, connected, or nil after 10 seconds."
  (with-current-buffer buffer
    (wait-until #'coq-eglot-lsp-current-server 10)))

(ert-deftest coq-eglot-servers-two-servers ()
  "Twins in one project share its server, unless Two Servers is on: then
the twin has a server of its own, with the same Rocq, and both are
checked at the same time."
  (with-project-twins nil
    (coq-eglot-lsp-connect)
    (with-current-buffer twin (coq-eglot-lsp-connect))
    (should (eq (twin-server this) (twin-server twin)))
    (should-not (coq-eglot-twin-two-servers-p))
    (coq-eglot-twin-toggle-two-servers)
    (should (coq-eglot-twin-two-servers-p))
    (should (twin-server twin))
    (should-not (eq (twin-server this) (twin-server twin)))
    (should (equal (with-current-buffer twin (server-program))
                   (server-program)))
    ;; both check at the same time
    (goto-char (point-max))
    (coq-eglot-goto-point)
    (with-current-buffer twin
      (goto-char (point-max))
      (coq-eglot-goto-point))
    (should (wait-until (lambda ()
                          (and (> (coq-eglot-position) (point-min))
                               (with-current-buffer twin
                                 (> (coq-eglot-position) (point-min)))))
                        30))
    (should (coq-eglot-checking-p))
    (should (with-current-buffer twin (coq-eglot-checking-p)))
    (wait-for-coq)
    (with-current-buffer twin (wait-for-coq))
    ;; shared again: the twin goes back to its beginning
    (cl-letf (((symbol-function 'yes-or-no-p) (lambda (_) t)))
      (coq-eglot-twin-toggle-two-servers))
    (should-not (coq-eglot-twin-two-servers-p))
    (with-current-buffer twin
      (should (= (coq-eglot-position) (point-min))))
    (should (> (coq-eglot-position) (point-min)))
    (should (eq (twin-server this) (twin-server twin)))))

(ert-deftest coq-eglot-servers-kill-own-server ()
  "Killing a twin with a server of its own stops this server, the other
twin keeps the server of the project."
  (with-project-twins nil
    (coq-eglot-twin-toggle-two-servers)
    (let ((own (twin-server twin))
          (shared (progn (coq-eglot-lsp-connect) (twin-server this))))
      (should own)
      (should-not (eq own shared))
      (with-current-buffer twin (set-buffer-modified-p nil))
      (kill-buffer twin)
      (should-not coq-eglot--twin)
      (should (wait-until (lambda () (not (jsonrpc-running-p own))) 5))
      (should (jsonrpc-running-p shared))
      (should (eq (coq-eglot-lsp-current-server) shared)))))

(ert-deftest coq-eglot-servers-twin-other-rocq ()
  "In the project of its twin, a twin gets another Rocq on a server of
its own, unless it requires a library of the project.  Unpaired, it
shares the server of the project again."
  (with-project-twins "Definition b := 0.\n"
    (let ((server (other-server))
          (program (coq-eglot-lsp--program-file
                    (car (coq-eglot-lsp-server-command)))))
      (skip-unless server)
      (coq-eglot-twin-set-rocq server)
      (with-current-buffer twin
        (should (equal coq-eglot-lsp-own-server server))
        (should (coq-eglot-lsp-foreign-p))
        (should (twin-server twin))
        (should (equal (server-program) (file-truename (car server))))
        ;; a library of the project cannot be compiled for it
        (should-error (coq-eglot-compile--check-version
                       (progn (goto-char (point-max))
                              (insert "Require Proj.lib.\n")
                              (coq-eglot-compile--require-sentences
                               (point-min) (point-max))))
                      :type 'user-error))
      (coq-eglot-lsp-connect)
      (should (twin-server this))
      (should (equal (server-program) program))
      ;; the Rocq of the project again: the server of the project
      (coq-eglot-twin-set-rocq (coq-eglot-lsp-project-command))
      (with-current-buffer twin
        (should-not coq-eglot-lsp-own-server))
      (should (eq (twin-server this) (twin-server twin)))
      ;; now it requires a library of the project
      (should-error (coq-eglot-twin-set-rocq server) :type 'user-error)
      (with-current-buffer twin
        (should-not coq-eglot-lsp-own-server)
        (goto-char (point-max))
        (delete-region (line-beginning-position 0) (point)))
      (coq-eglot-twin-set-rocq server)
      (with-current-buffer twin (should coq-eglot-lsp-own-server))
      (coq-eglot-twin-unpair)
      (with-current-buffer twin
        (should-not coq-eglot-lsp-own-server)
        (should (eq (twin-server twin) (twin-server this)))))))

(ert-deftest coq-eglot-servers-project-rocq ()
  "Another Rocq for a project restarts all its buffers, after
confirmation if one has a processed part."
  (skip-unless-server)
  (with-project '(("a.v" . "Definition a := 0.\n")
                  ("b.v" . "Definition b := 0.\n"))
    (let ((a (visit "a.v")) (b (visit "b.v"))
          (server nil) (program nil) (asked nil))
      (with-current-buffer a
        (setq server (other-server)
              program (coq-eglot-lsp--program-file
                       (car (coq-eglot-lsp-server-command))))
        (skip-unless server)
        (run #'coq-eglot-process-buffer)
        (should (> (coq-eglot-position) (point-min)))
        ;; refused: nothing changes
        (cl-letf (((symbol-function 'yes-or-no-p)
                   (lambda (prompt) (setq asked prompt) nil)))
          (should-error (coq-eglot-set-rocq server) :type 'user-error))
        (should (string-search "a.v" asked))
        (should-not (string-search "b.v" asked))
        (should (> (coq-eglot-position) (point-min)))
        ;; fixed by its first server
        (should (coq-eglot-lsp-same-server-p
                 (coq-eglot-lsp-project-server (cons 'transient dir))
                 (list program)))
        ;; accepted
        (cl-letf (((symbol-function 'yes-or-no-p) (lambda (_) t)))
          (coq-eglot-set-rocq server))
        (should (= (coq-eglot-position) (point-min)))
        (should (equal (coq-eglot-lsp-project-server (cons 'transient dir)) server))
        (should (twin-server a))
        (should (equal (server-program) (file-truename (car server)))))
      ;; the other file of the project too
      (with-current-buffer b
        (should (equal (coq-eglot-lsp-server-command) server))
        (run #'coq-eglot-process-buffer)
        (should (eq (coq-eglot-lsp-current-server)
                    (with-current-buffer a (coq-eglot-lsp-current-server)))))
      ;; the same Rocq again: nothing to do
      (with-current-buffer a
        (coq-eglot-set-rocq server)
        (should (equal (server-program) (file-truename (car server)))))
      )))

(provide 'coq-eglot-test-servers)

;;; coq-eglot-test-servers.el ends here
