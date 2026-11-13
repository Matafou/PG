;;; coq-eglot-test-sandbox.el --- Tests of the sandboxes of the Eglot backend  -*- lexical-binding: t -*-
;;
;; This file is part of Proof General.
;;
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Test the sandboxes, copies of a project: their build products are
;; kept, plain copies and git worktrees, their script buffers are the
;; twins of the ones of the project.  The tests that compile need
;; coqc, the ones that check need the language server: they are skipped
;; otherwise.

;;; Code:

(defvar coq-backend)                    ; before loading Proof General
(setq coq-backend 'eglot)

(require 'subr-x)
(require 'proof-site)
(proof-add-to-load-path (expand-file-name "coq/" proof-home-directory))
(require 'coq-mode)
(add-to-list 'load-path coq-eglot-directory)
(require 'coq-eglot)
(require 'coq-eglot-sandbox)

(when (getenv "COQ_LSP")
  (setq coq-eglot-server-program (list (getenv "COQ_LSP"))))

(setq proof-three-window-mode-policy 'hybrid)
(setq coq-auto-adapt-printing-width nil)


;;; utility functions

(defun server-usable-p ()
  "Non-nil if the server is found and recent enough."
  (let ((exe (ignore-errors (car (coq-eglot-lsp-server-command)))))
    (and exe
         (let ((version (car (ignore-errors (process-lines exe "--version")))))
           (and version
                (not (version< version coq-eglot-lsp-minimal-version)))))))

(defun skip-unless-server ()
  "Skip the test if the server is not usable, fail in the CI."
  (unless (server-usable-p)
    (if (getenv "COQ_EGLOT_REQUIRE_SERVER")
        (ert-fail "No usable Coq language server")
      (ert-skip "No usable Coq language server"))))

(defun compiler ()
  "The command compiling a Coq file: rocq compile, or coqc."
  (cond ((executable-find "rocq") (list "rocq" "compile"))
        ((executable-find "coqc") (list "coqc"))))

(defun skip-unless-coqc ()
  "Skip the test if the compiler is not found, fail in the CI."
  (unless (compiler)
    (if (getenv "COQ_EGLOT_REQUIRE_SERVER")
        (ert-fail "No compiler")
      (ert-skip "No compiler"))))

(defun write-file-text (file text)
  "Write TEXT in FILE, its directory made if needed."
  (make-directory (file-name-directory file) t)
  (with-temp-file file (insert text)))

(defun file-text (file)
  "The content of FILE."
  (with-temp-buffer
    (insert-file-contents file)
    (buffer-string)))

(defun file-mtime (file)
  "The modification time of FILE."
  (file-attribute-modification-time (file-attributes file)))

(defun coqc (dir &rest files)
  "Compile FILES in DIR, the project of the tests: -R theories Proj."
  (let ((default-directory dir))
    (dolist (file files)
      (should (eq 0 (apply #'call-process (car (compiler)) nil nil nil
                           (append (cdr (compiler))
                                   (list "-R" "theories" "Proj" file))))))))

(defun git (dir &rest args)
  "Run git with ARGS in DIR, return its output."
  (let ((default-directory dir))
    (with-temp-buffer
      (should (eq 0 (apply #'call-process "git" nil t nil
                           "-c" "user.name=test" "-c" "user.email=test@test"
                           args)))
      (buffer-string))))

(defmacro with-project (&rest body)
  "Run BODY with `root', a compiled project in a temporary directory.
theories/A.v, theories/B.v requiring A, with -R theories Proj in
_CoqProject.  Its sandboxes go in the same temporary directory, deleted
afterwards."
  (declare (indent 0) (debug t))
  `(progn
     (skip-unless-coqc)
     (let* ((parent (file-name-as-directory (make-temp-file "coq-sandbox-" t)))
            (coq-eglot-sandbox-parent parent)
            (coq-eglot-sandbox-size-limit nil)
            (root (file-name-as-directory (expand-file-name "proj" parent))))
       (unwind-protect
           (progn
             (write-file-text (expand-file-name "_CoqProject" root)
                              "-R theories Proj\ntheories/A.v\ntheories/B.v\n")
             (write-file-text (expand-file-name "theories/A.v" root)
                              "Definition a := 1.\n")
             (write-file-text (expand-file-name "theories/B.v" root)
                              "Require Import Proj.A.\nLemma b : a = 1.\nProof. reflexivity. Qed.\n")
             (coqc root "theories/A.v" "theories/B.v")
             ,@body)
         ;; worktrees first: git refuses to delete their directories
         (when (file-directory-p (expand-file-name ".git" root))
           (ignore-errors (git root "worktree" "prune")))
         (delete-directory parent t)))))


;;; tests

(ert-deftest coq-eglot-sandbox-copy ()
  "A copy keeps the build products and their dates: nothing to compile.
Described in .rocq-sandbox, with the sources of the project at the time."
  (with-project
    (let* ((coq-eglot-sandbox-method 'copy)
           (sandbox (coq-eglot-sandbox--make root "t"))
           (description (coq-eglot-sandbox--read sandbox)))
      (should (equal sandbox (expand-file-name "proj-t/" parent)))
      (should (equal (alist-get 'origin description) root))
      (should (equal (alist-get 'method description) "copy"))
      (should (equal (coq-eglot-sandbox--copy-root sandbox) sandbox))
      (should (equal (coq-eglot-sandbox--sandboxes root)
                     (list (directory-file-name sandbox))))
      ;; the compiled libraries, with their dates
      (should (equal (file-mtime (expand-file-name "theories/B.vo" sandbox))
                     (file-mtime (expand-file-name "theories/B.vo" root))))
      ;; usable there
      (write-file-text (expand-file-name "C.v" sandbox)
                       "Require Import Proj.B.\nCheck b.\n")
      (coqc sandbox "C.v")
      ;; the base of merges
      (should (equal (file-text (coq-eglot-sandbox--meta-file
                                 sandbox "base/theories/B.v"))
                     (file-text (expand-file-name "theories/B.v" root))))
      (should (file-exists-p (coq-eglot-sandbox--meta-file
                              sandbox "base/_CoqProject")))
      (should-not (file-exists-p (coq-eglot-sandbox--meta-file
                                  sandbox "base/theories/B.vo")))
      ;; a second one of the same name
      (should-error (coq-eglot-sandbox--make root "t") :type 'user-error))))

(ert-deftest coq-eglot-sandbox-separate ()
  "Writing and compiling in a sandbox leave the project unchanged."
  (with-project
    (let* ((coq-eglot-sandbox-method 'copy)
           (sandbox (coq-eglot-sandbox--make root "t"))
           (before (file-text (expand-file-name "theories/B.vo" root))))
      (write-file-text (expand-file-name "theories/B.v" sandbox)
                       "Require Import Proj.A.\nLemma b : a = 1.\nProof. reflexivity. Qed.\nLemma c : True.\nProof. exact I. Qed.\n")
      (coqc sandbox "theories/B.v")
      (should (equal (file-text (expand-file-name "theories/B.vo" root))
                     before))
      (should-not (string-match-p "Lemma c" (file-text (expand-file-name
                                                        "theories/B.v" root)))))))

(ert-deftest coq-eglot-sandbox-worktree ()
  "A worktree on a branch of its own, with the files of the project over it:
its changes not committed, its untracked and ignored files, their dates.
Its description is ignored by git.  Deleted, its branch is kept."
  (skip-unless (executable-find "git"))
  (with-project
    (write-file-text (expand-file-name ".gitignore" root) "*.vo\n*.vo[sk]\n*.glob\n.*.aux\n")
    (git root "init" "-q")
    (git root "add" ".")
    (git root "commit" "-q" "-m" "init")
    ;; not committed
    (write-file-text (expand-file-name "theories/B.v" root)
                     "Require Import Proj.A.\nLemma b : a = 1.\nProof. reflexivity. Qed.\n(* changed *)\n")
    (coqc root "theories/B.v")
    (write-file-text (expand-file-name "U.v" root) "(* untracked *)\n")
    (let* ((coq-eglot-sandbox-method 'auto)
           (status (git root "status" "--porcelain"))
           (sandbox (coq-eglot-sandbox--make root "t")))
      (should (equal (alist-get 'method (coq-eglot-sandbox--read sandbox))
                     "worktree"))
      (should (string-match-p "(\\* changed \\*)"
                              (file-text (expand-file-name "theories/B.v" sandbox))))
      (should (file-exists-p (expand-file-name "U.v" sandbox)))
      (should (equal (file-mtime (expand-file-name "theories/B.vo" sandbox))
                     (file-mtime (expand-file-name "theories/B.vo" root))))
      (should (equal (file-mtime (expand-file-name "theories/B.v" sandbox))
                     (file-mtime (expand-file-name "theories/B.v" root))))
      (should (string-match-p "sandbox/t" (git root "branch")))
      ;; the description is not a change of the sandbox
      (should-not (string-match-p "rocq-sandbox"
                                  (git sandbox "status" "--porcelain")))
      ;; the project did not change
      (should (equal (git root "status" "--porcelain") status))
      (cl-letf (((symbol-function 'yes-or-no-p) (lambda (&rest _) t)))
        (coq-eglot-sandbox-delete sandbox))
      (should-not (file-exists-p sandbox))
      (should (string-match-p "sandbox/t" (git root "branch"))))))

(ert-deftest coq-eglot-sandbox-delete-only-sandboxes ()
  "Deleting a directory that is not a sandbox is refused."
  (with-project
    (cl-letf (((symbol-function 'yes-or-no-p) (lambda (&rest _) t)))
      (should-error (coq-eglot-sandbox-delete root) :type 'user-error))
    (should (file-exists-p (expand-file-name "theories/B.v" root)))))

(ert-deftest coq-eglot-sandbox-absolute-paths ()
  "The generated build files naming the project are found."
  (with-project
    (write-file-text (expand-file-name "Makefile.conf" root)
                     (format "COQMF_ROOT = %s\n" root))
    (write-file-text (expand-file-name "theories/.B.d" root) "B.vo: B.v\n")
    (let ((coq-eglot-sandbox-method 'copy)
          (warnings nil))
      (cl-letf (((symbol-function 'display-warning)
                 (lambda (_type message &rest _) (push message warnings))))
        (let ((sandbox (coq-eglot-sandbox--make root "t")))
          (should (equal (coq-eglot-sandbox--absolute-paths
                          root (coq-eglot-sandbox--copy-root sandbox))
                         '("Makefile.conf")))))
      (should (string-match-p "Makefile.conf" (car warnings))))))

(ert-deftest coq-eglot-sandbox-outside-load-path ()
  "The directories of the load path outside the project are reported:
shared with the project when the sandbox is beside it, not found from
it elsewhere."
  (with-project
    (write-file-text (expand-file-name "_CoqProject" root)
                     "-R theories Proj\n-Q ../lib Lib\n-I /abs/ml\ntheories/A.v\n")
    (make-directory (expand-file-name "lib" parent))
    (let ((coq-eglot-sandbox-method 'copy)
          (lib (expand-file-name "lib/" parent))
          (warnings nil))
      (cl-letf (((symbol-function 'display-warning)
                 (lambda (_type message &rest _) (push message warnings))))
        (let ((sandbox (coq-eglot-sandbox--make root "t")))
          (should (equal (coq-eglot-sandbox--outside-load-path root sandbox)
                         (list (cons lib lib)
                               (cons "/abs/ml/" "/abs/ml/"))))
          (should (string-match-p "lib/: shared with the project"
                                  (car warnings)))
          ;; elsewhere
          (let ((elsewhere (expand-file-name "other/proj-t/" parent)))
            (should (equal (coq-eglot-sandbox--outside-load-path root elsewhere)
                           (list (cons lib (expand-file-name "other/lib/" parent))
                                 (cons "/abs/ml/" "/abs/ml/"))))))))))

(ert-deftest coq-eglot-sandbox-project-root ()
  "The project of a file of a sandbox is the sandbox, without project
file or git: like its project, whose root its server binds."
  (with-project
    (delete-file (expand-file-name "_CoqProject" root))
    (let* ((coq-eglot-sandbox-method 'copy)
           (sandbox (coq-eglot-sandbox--make root "t")))
      (should (equal (coq-eglot-sandbox--project-root
                      (expand-file-name "theories/" sandbox))
                     sandbox)))))

(ert-deftest coq-eglot-sandbox-twin ()
  "The copy of the buffer is its twin, read only, reverted when its file
changes, in the sandbox, the buffer of the project the reference."
  (skip-unless-server)
  (with-project
    (let* ((coq-eglot-sandbox-method 'copy)
           (proof-three-window-enable nil)
           (coq-eglot-twin-synchronize nil)
           ;; the notifications of the file system need the command loop
           (auto-revert-use-notify nil)
           (this (find-file-noselect (expand-file-name "theories/B.v" root)))
           twin)
      (unwind-protect
          (with-current-buffer this
            (switch-to-buffer this)
            (delete-other-windows)
            (should coq-eglot-mode)
            (coq-eglot-sandbox-create "t")
            (setq twin coq-eglot--twin)
            (should (buffer-live-p twin))
            (should (equal (buffer-file-name twin)
                           (expand-file-name "proj-t/theories/B.v" parent)))
            (should (string-match-p "\\`cd .*/proj-t/ && claude\\'"
                                    (car kill-ring)))
            (with-current-buffer twin
              (should coq-eglot--sandbox)
              (should buffer-read-only)
              (should auto-revert-mode)
              (should (string-match-p "Sandbox" (coq-eglot--lighter)))
              (should-not (coq-eglot-twin--reference-p)))
            (should (coq-eglot-twin--reference-p))
            (should-not coq-eglot--sandbox)
            ;; the agent writes
            (write-file-text (buffer-file-name twin)
                             "Require Import Proj.A.\nLemma b : a = 1.\nProof. reflexivity. Qed.\n(* agent *)\n")
            (with-current-buffer twin
              (auto-revert-handler)
              (should (string-match-p "(\\* agent \\*)" (buffer-string)))
              (should buffer-read-only)
              (should (eq coq-eglot--twin this))
              (should coq-eglot--sandbox)
              ;; checked by its own server, with the load path of the copy
              (goto-char (point-min))
              (search-forward "Qed.")
              (coq-eglot-goto-point)
              (while coq-eglot--running (accept-process-output nil 0.02))
              (should (= (coq-eglot-position) (point)))
              (should-not (eq (coq-eglot-lsp-current-server)
                              (with-current-buffer this
                                (coq-eglot-lsp-current-server)))))
            ;; the sandbox has a twin, the project has a twin: no other
            (should-error (coq-eglot-sandbox-create "u") :type 'user-error))
        (dolist (buffer (list twin this))
          (when (buffer-live-p buffer)
            (with-current-buffer buffer
              (ignore-errors (coq-eglot-lsp-shutdown))
              (set-buffer-modified-p nil))
            (kill-buffer buffer)))
        (delete-other-windows)))))

;;; points of robustness

(ert-deftest coq-eglot-sandbox-size ()
  "The size counts the files, not .git, and follows no link."
  (let ((dir (file-name-as-directory (make-temp-file "coq-size-" t))))
    (unwind-protect
        (progn
          (write-file-text (expand-file-name "a/x" dir) "12345")
          (write-file-text (expand-file-name "y" dir) "123")
          (write-file-text (expand-file-name ".git/z" dir) "1234567890")
          (make-symbolic-link (expand-file-name "a" dir)
                              (expand-file-name "link" dir))
          (should (= (coq-eglot-sandbox--size dir) 8))
          (should-not (coq-eglot-sandbox--size
                       (expand-file-name "missing/" dir))))
      (delete-directory dir t))))

(ert-deftest coq-eglot-sandbox-size-unknown ()
  "An unknown size is reported, not skipped silently."
  (with-project
    (let ((coq-eglot-sandbox-method 'copy)
          (coq-eglot-sandbox-size-limit 1000)
          (warnings nil))
      (cl-letf (((symbol-function 'coq-eglot-sandbox--size) (lambda (_) nil))
                ((symbol-function 'display-warning)
                 (lambda (_type message &rest _) (push message warnings))))
        (coq-eglot-sandbox--make root "t"))
      (should (string-match-p "size of .* is unknown" (car (last warnings)))))))

(ert-deftest coq-eglot-sandbox-copy-emacs ()
  "Without cp, Emacs copies, merges, keeps dates and links."
  (with-project
    (let ((coq-eglot-sandbox-method 'copy))
      (make-symbolic-link "A.v" (expand-file-name "theories/L.v" root))
      (cl-letf* ((orig (symbol-function 'executable-find))
                 ((symbol-function 'executable-find)
                  (lambda (program &rest args)
                    (unless (equal program "cp")
                      (apply orig program args)))))
        (let ((sandbox (coq-eglot-sandbox--make root "t")))
          (should (equal (file-mtime (expand-file-name "theories/B.vo" sandbox))
                         (file-mtime (expand-file-name "theories/B.vo" root))))
          (should-not (time-less-p
                       (file-mtime (expand-file-name "theories/B.v" sandbox))
                       (file-mtime (expand-file-name "theories/B.v" root))))
          ;; the library is not older than its source: not compiled again
          (should-not (time-less-p
                       (file-mtime (expand-file-name "theories/B.vo" sandbox))
                       (file-mtime (expand-file-name "theories/B.v" sandbox))))
          (should (equal (file-symlink-p
                          (expand-file-name "theories/L.v" sandbox))
                         "A.v"))
          ;; merged into an existing directory
          (let ((target (expand-file-name "merged/" parent)))
            (make-directory target)
            (write-file-text (expand-file-name "other" target) "x")
            (coq-eglot-sandbox--copy-entry
             (expand-file-name "theories" root) target)
            (should (file-exists-p (expand-file-name "other" target)))
            (should (file-exists-p (expand-file-name "B.vo" target)))))))))

(ert-deftest coq-eglot-sandbox-through-link ()
  "A project reached through a link, with \"~\" or a trailing slash, has
the same sandboxes."
  (with-project
    (let* ((coq-eglot-sandbox-method 'copy)
           (sandbox (coq-eglot-sandbox--make root "t"))
           (link (expand-file-name "other/proj" parent)))
      (make-directory (file-name-directory link))
      (make-symbolic-link (directory-file-name root) link)
      (should (equal (coq-eglot-sandbox--sandboxes (file-name-as-directory link))
                     (list (directory-file-name sandbox))))
      (should (coq-eglot-sandbox--same-file-p root (directory-file-name root)))
      (should (coq-eglot-sandbox--same-file-p root link))
      (should-not (coq-eglot-sandbox--same-file-p root sandbox))
      (should-not (coq-eglot-sandbox--same-file-p nil root)))))

(ert-deftest coq-eglot-sandbox-link-other-name ()
  "A sandbox made through a link of another name, beside the project, is
beside the true project, and found from both."
  (with-project
    (let* ((coq-eglot-sandbox-method 'copy)
           (coq-eglot-sandbox-parent nil)
           (link (file-name-as-directory
                  (expand-file-name "other/current" parent))))
      (make-directory (expand-file-name "other" parent))
      (make-symbolic-link (directory-file-name root) (directory-file-name link))
      (let ((sandbox (coq-eglot-sandbox--make link "t")))
        (should (equal sandbox (expand-file-name "proj-t/" parent)))
        (should (equal (coq-eglot-sandbox--sandboxes root)
                       (list (directory-file-name sandbox))))
        (should (equal (coq-eglot-sandbox--sandboxes link)
                       (list (directory-file-name sandbox))))))))

(ert-deftest coq-eglot-sandbox-no-parent ()
  "A project whose parent directory does not exist has no sandbox."
  (let ((coq-eglot-sandbox-parent "/nonexistent-coq-sandboxes/"))
    (should-not (coq-eglot-sandbox--sandboxes "/tmp/proj/"))))

(ert-deftest coq-eglot-sandbox-hook-without-module ()
  "The root of a file of a sandbox is the sandbox with only coq-eglot loaded."
  (with-project
    (let* ((coq-eglot-sandbox-method 'copy)
           (sandbox (coq-eglot-sandbox--make root "t"))
           (output (with-temp-buffer
                     ;; only the hook finds the root: no project file
                     (delete-file (expand-file-name "_CoqProject" sandbox))
                     (let ((default-directory proof-home-directory))
                       (call-process
                        (expand-file-name invocation-name invocation-directory)
                        nil t nil "-Q" "--batch"
                        "-l" "generic/proof-site.el"
                        "--eval" "(setq coq-backend 'eglot)"
                        "--eval" "(proof-add-to-load-path (expand-file-name \"coq/\" proof-home-directory))"
                        "--eval" "(require 'coq-mode)"
                        "--eval" "(add-to-list 'load-path coq-eglot-directory)"
                        "--eval" "(require 'coq-eglot)"
                        "--eval" (format "(princ (format \"ROOT=%%S MODULE=%%S\" (project-root (project-current nil %S)) (featurep 'coq-eglot-sandbox)))"
                                         (expand-file-name "theories/" sandbox))))
                     (buffer-string))))
      (should (string-match-p
               (format "ROOT=%S MODULE=nil" sandbox) output)))))

(provide 'coq-eglot-test-sandbox)

;;; coq-eglot-test-sandbox.el ends here
