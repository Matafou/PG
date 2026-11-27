;;; coq-eglot-test-compile.el --- Tests of the Eglot backend: the compilation of the libraries  -*- lexical-binding: t -*-
;;
;; This file is part of Proof General.
;;
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Test the compilation of the required libraries, with the Eglot backend.
;; See coq-eglot-test-common.el for the settings and the utilities.

;;; Code:

(require 'coq-eglot-test-common
         (expand-file-name "coq-eglot-test-common"
                           (file-name-directory
                            (or load-file-name buffer-file-name))))

;;; compilation of the required libraries

(defun clean-compiled ()
  "Delete the files produced by the compilation in `compile-directory'."
  (dolist (file (directory-files
                 compile-directory t "\\.\\(vo[sk]?\\|glob\\|aux\\)\\'"))
    (delete-file file)))

(defun compiled-p (library)
  "Non-nil if LIBRARY of `compile-directory' is compiled."
  (file-exists-p (expand-file-name (concat library ".vo") compile-directory)))

(defmacro with-compile-file (&rest body)
  "Run BODY visiting compile/eglot_compile.v, nothing compiled before.
The compilation before Require is on.  The server forgets the
libraries loaded by the previous tests."
  (declare (indent 0) (debug t))
  `(let ((coq-compile-before-require t))
     (clean-compiled)
     (unwind-protect
         (with-file (expand-file-name "eglot_compile.v" compile-directory)
           (coq-eglot-lsp-workspace-update)
           ,@body)
       (clean-compiled))))

(ert-deftest coq-eglot-compile-project-root ()
  "The server of a file runs in the directory of its _CoqProject."
  (skip-unless-server)
  (let ((project (coq-eglot-lsp-project compile-directory)))
    (should (eq (car project) 'transient))
    (should (file-equal-p (cdr project) compile-directory)))
  (should-not (coq-eglot-lsp-project default-directory)))

(ert-deftest coq-eglot-compile-before-require ()
  "Required libraries are compiled before the server checks the Require."
  (with-compile-file
    (goto-marker "def")
    (run #'coq-eglot-goto-point)
    (should (position-at-marker-p "def"))
    (should (equal (buffer-text "*response*") "a is defined"))
    (should (compiled-p "eglot_compile_b"))
    (should (compiled-p "eglot_compile_c"))
    (should-not (compiled-p "eglot_compile_bad"))
    ;; the compiler is the one of the server
    (should (equal (file-name-directory coq-compiler)
                   (file-name-directory
                    (executable-find (car (coq-eglot-lsp-server-command))))))))

(ert-deftest coq-eglot-no-implicit-root-load-path ()
  "Without project file, the server does not recursively bind its root."
  (skip-unless-server)
  (let* ((dir (file-name-as-directory (make-temp-file "coq-eglot-" t)))
         (buffer nil))
    (unwind-protect
        (progn
          (with-temp-file (expand-file-name "x.v" dir)
            (insert "Definition one := 1.\n"))
          (setq buffer (find-file-noselect (expand-file-name "x.v" dir)))
          (with-current-buffer buffer
            (should-not (member (concat (directory-file-name dir) ",")
                                (cdr (coq-eglot-lsp--contact
                                      nil (project-current)))))))
      (when (buffer-live-p buffer)
        (with-current-buffer buffer (set-buffer-modified-p nil))
        (kill-buffer buffer))
      (delete-directory dir t))))

(defconst load-path-directory (expand-file-name "loadpath/")
  "Directory of the tests of the load path, without project file.
Its .dir-locals.el sets `coq-load-path'.")

(defun clean-load-path-library ()
  "Delete the files produced by the compilation of loadpath/lib."
  (dolist (file (directory-files
                 (expand-file-name "lib" load-path-directory) t
                 "\\.\\(vo[sk]?\\|glob\\|aux\\)\\'"))
    (delete-file file)))

(ert-deftest coq-eglot-load-path ()
  "The server gets the load path of the buffer, here from .dir-locals.el,
like the compilation."
  (skip-unless-server)
  (let ((coq-compile-before-require t)
        (enable-local-variables :all))
    (clean-load-path-library)
    (unwind-protect
        (with-file (expand-file-name "eglot_load_path.v" load-path-directory)
          (should (equal coq-load-path '((rec "lib" "LoadPathLib"))))
          (should (equal (coq-eglot-lsp-load-path-args)
                         (list "-R" (concat load-path-directory
                                            "lib,LoadPathLib"))))
          ;; without project file, the server may be the one of the
          ;; other tests, in the same version control repository
          (coq-eglot-exit)
          (goto-marker "check")
          (run #'coq-eglot-goto-point)
          (should (position-at-marker-p "check"))
          (should (string-match-p "\\`eglot_lib\\.x\\s-+: nat"
                                  (buffer-text "*response*")))
          ;; another load path than the one of the server: a warning
          (let ((coq-load-path nil) warned)
            (cl-letf (((symbol-function 'display-warning)
                       (lambda (&rest args) (setq warned args))))
              (coq-eglot-lsp-check-load-path))
            (should (string-match-p "another load path" (nth 1 warned))))
          (coq-eglot-exit))
      (clean-load-path-library))))

(ert-deftest coq-eglot-load-path-no-guessed-root ()
  "Only the explicit load path of the buffer is passed to the server."
  (let ((enable-local-variables :all)
        ;; not the directory of the buffer
        (project-dir (file-name-directory
                      (directory-file-name load-path-directory))))
    (with-file (expand-file-name "eglot_load_path.v" load-path-directory)
      (cl-letf (((symbol-function 'eglot--current-project)
                 (lambda () (cons 'transient project-dir))))
        (let ((args (cdr (coq-eglot-lsp--contact nil))))
          (should-not
           (member (directory-file-name project-dir)
                   (mapcar (lambda (arg) (string-remove-suffix "," arg)) args)))
          (should (member (concat load-path-directory "lib,LoadPathLib")
                          args)))))))

(ert-deftest coq-eglot-use-project-file-nil ()
  "Without `coq-use-project-file', a file is a project of its own: its
server runs in its directory, not in the one of the dominating project
file."
  (skip-unless-server)
  (let* ((coq-use-project-file nil)
         (dir (expand-file-name "lib/" load-path-directory))
         (file (expand-file-name "eglot_lib.v" dir)))
    (with-current-buffer (find-file-noselect file)
      (unwind-protect
          (progn
            (should (equal (coq-eglot-lsp-project dir)
                           (list 'coq-eglot-file file dir)))
            (should (equal (project-root (coq-eglot-lsp-project dir)) dir)))
        (kill-buffer)))))

(ert-deftest coq-eglot-compile-vo-no-locks ()
  "The compilation produces .vo files and locks nothing, whatever the
options of Proof General, set again globally before each compilation:
the server loads the .vo files only, the locks are for the proof shell
of Proof General."
  (let ((coq-compile-vos 'vos)
        (coq-lock-ancestors t))
    (with-compile-file
      (goto-marker "def")
      (run #'coq-eglot-goto-point)
      (should (position-at-marker-p "def"))
      (should (compiled-p "eglot_compile_b"))
      (should (compiled-p "eglot_compile_c"))
      (should (eq coq-compile-vos 'ensure-vo))
      (should-not coq-lock-ancestors))))

(ert-deftest coq-eglot-compile-next ()
  "A Require processed alone is compiled first too.
The file starts with a sentence, not a comment."
  (with-compile-file
    (run #'coq-eglot-assert-next-command)
    (should-not (compiled-p "eglot_compile_b"))
    (run #'coq-eglot-assert-next-command)
    (should (position-at-marker-p "require"))
    (should (compiled-p "eglot_compile_b"))))

(ert-deftest coq-eglot-compile-failure ()
  "A failed compilation stops the proof position before its Require.
The sentences before it are checked."
  (with-compile-file
    (run #'coq-eglot-process-buffer)
    (should (position-at-marker-p "def"))
    (should (string-match-p "Compilation of the required libraries failed"
                            (buffer-text "*response*")))
    (should (string-match-p "undefined_identifier"
                            (buffer-text coq--compile-response-buffer)))
    (should (string-prefix-p "From EglotCompile Require eglot_compile_bad."
                             (error-overlay-text 'proof-boring-face)))
    ;; nothing is compiled when the Require is the next sentence
    (run #'coq-eglot-assert-next-command)
    (should (position-at-marker-p "def"))
    (should (string-match-p "Compilation of the required libraries failed"
                            (buffer-text "*response*")))))

(ert-deftest coq-eglot-compile-off ()
  "Nothing is compiled if `coq-compile-before-require' is nil."
  (with-compile-file
    (let ((coq-compile-before-require nil))
      (goto-marker "def")
      (run #'coq-eglot-goto-point)
      (should (position-at-marker-p "before"))
      (should-not (compiled-p "eglot_compile_b")))))

(ert-deftest coq-eglot-compile-interrupt ()
  "Interrupting kills the compilation, the proof position stays."
  (with-compile-file
    (goto-marker "def")
    (coq-eglot-goto-point)
    (should (coq-eglot-compile-running-p))
    (coq-eglot-interrupt)
    (should-not (coq-eglot-checking-p))
    (should-not (coq-eglot-compile-running-p))
    (should-not (cl-some (lambda (p) (process-get p 'coq-compilation-job))
                         (process-list)))
    (accept-process-output nil 0.3)
    (should (= (coq-eglot-position) (point-min)))))

(ert-deftest coq-eglot-compile-changed-library ()
  "A library changed after it was loaded is recompiled and reloaded."
  (let ((source (expand-file-name "eglot_compile_c.v" compile-directory)))
    (with-compile-file
      (unwind-protect
          (progn
            (goto-marker "def")
            (run #'coq-eglot-goto-point)
            (should (equal (query #'coq-eglot-query "Compute a")
                           "= 42\n     : nat"))
            (run #'coq-eglot-retract-buffer)
            (with-temp-file source (insert "Definition c := 1.\n"))
            (goto-marker "def")
            (run #'coq-eglot-goto-point)
            (should (position-at-marker-p "def"))
            (should (equal (query #'coq-eglot-query "Compute a")
                           "= 2\n     : nat")))
        (with-temp-file source (insert "Definition c := 41.\n"))))))

(defun outdated-require ()
  "Text of the processed Require sentence marked as outdated, or nil."
  (cl-loop for ov in coq-eglot-compile--loaded
           when (eq (overlay-get ov 'face) 'coq-eglot-outdated-require)
           return (buffer-substring (overlay-start ov) (overlay-end ov))))

(ert-deftest coq-eglot-compile-outdated ()
  "A processed Require loading a library changed since is marked.
Until the user goes back before it."
  (let* ((source (expand-file-name "eglot_compile_c.v" compile-directory))
         (contents (with-temp-buffer
                     (insert-file-contents source) (buffer-string)))
         library)
    (with-compile-file
      (unwind-protect
          (let ((script (current-buffer)))
            (goto-marker "def")
            (run #'coq-eglot-goto-point)
            (should-not (outdated-require))
            (should (equal (coq-eglot--lighter) " Coq-LSP"))
            ;; an indirect dependency is edited in a buffer
            (setq library (find-file-noselect source))
            (with-current-buffer library
              (goto-char (point-max))
              (insert "(* edited *)\n"))
            (accept-process-output nil 0.1)
            (should (equal (outdated-require)
                           "From EglotCompile Require eglot_compile_b."))
            (should (string-match-p "eglot_compile_c\\.v"
                                    (get-char-property
                                     (save-excursion (goto-marker "require")
                                                     (line-beginning-position))
                                     'help-echo)))
            (should (equal (coq-eglot--lighter) " Coq-LSP!"))
            ;; undone by reverting
            (with-current-buffer library (revert-buffer t t))
            (should-not (outdated-require))
            ;; saved: the source is newer than the loaded library
            (with-current-buffer library
              (goto-char (point-max))
              (insert "(* edited *)\n")
              (let ((inhibit-message t)) (save-buffer)))
            (accept-process-output nil 0.1)
            (with-current-buffer script
              (should (outdated-require))
              ;; the proof position does not move
              (should (position-at-marker-p "def"))
              ;; going back before the Require removes the mark
              (goto-marker "before")
              (run #'coq-eglot-goto-point)
              (should-not (outdated-require))
              (should (equal (coq-eglot--lighter) " Coq-LSP"))
              ;; processing it again compiles the new version
              (goto-marker "def")
              (run #'coq-eglot-goto-point)
              (should (position-at-marker-p "def"))
              (should-not (outdated-require))))
        (when (buffer-live-p library)
          (with-current-buffer library (set-buffer-modified-p nil))
          (kill-buffer library))
        (with-temp-file source (insert contents))))))

(ert-deftest coq-eglot-compile-shared-library ()
  "Two scripts loading the same library are both marked when it changes.
When one of them loads the new version, the other stays marked."
  (let* ((source (expand-file-name "eglot_compile_c.v" compile-directory))
         (contents (with-temp-buffer
                     (insert-file-contents source) (buffer-string)))
         library)
    (with-compile-file
      (unwind-protect
          (let ((script (current-buffer)))
            (goto-marker "def")
            (run #'coq-eglot-goto-point)
            (with-file (expand-file-name "eglot_compile2.v" compile-directory)
              (goto-marker "def")
              (run #'coq-eglot-goto-point)
              (should (position-at-marker-p "def"))
              (should-not (outdated-require))
              ;; the shared library changes
              (setq library (find-file-noselect source))
              (with-current-buffer library
                (goto-char (point-max))
                (insert "(* edited *)\n")
                (let ((inhibit-message t)) (save-buffer)))
              (should (outdated-require))
              (with-current-buffer script (should (outdated-require)))
              ;; the second script loads the new version
              (goto-marker "before")
              (run #'coq-eglot-goto-point)
              (goto-marker "def")
              (run #'coq-eglot-goto-point)
              (should (position-at-marker-p "def"))
              (should-not (outdated-require))
              (with-current-buffer script
                (should (outdated-require))
                (should (position-at-marker-p "def")))))
        (when (buffer-live-p library)
          (with-current-buffer library (set-buffer-modified-p nil))
          (kill-buffer library))
        (with-temp-file source (insert contents))))))

;;; coq-eglot-test-compile.el ends here
