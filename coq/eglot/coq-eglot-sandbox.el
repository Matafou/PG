;;; coq-eglot-sandbox.el --- A sandbox: a copy of the project, beside it  -*- lexical-binding:t -*-

;; This file is part of Proof General.

;; Portions © Copyright 2026  Pierre Courtieu

;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;;
;; A sandbox of a project of the Eglot backend: a copy of its tree
;; where someone else, typically an AI agent, works, while the user
;; keeps the real development.  Its script buffers are the twins of the
;; ones of the project, see `coq-eglot-twin-pair': side by side, their
;; differences highlighted, each with its own server.  The user does
;; not edit them: they are read only, and reverted when the other one
;; writes their files.
;;
;; The copy includes what the build produced, the compiled libraries,
;; and the generated makefiles: nothing to compile again.  Rocq checks
;; the consistency of compiled libraries by their contents, not their
;; paths, so the copies are valid, unless the sources they were compiled
;; from change.  No links: Rocq and the agent would write through them,
;; into the real development.  The copy is a plain one, or a git
;; worktree, see `coq-eglot-sandbox-method'.
;;
;; The directory .rocq-sandbox/ at the root of a sandbox holds what
;; other tools may read: sandbox.json, where it comes from, and base/,
;; the sources of the project when it was created, the base of later
;; merges.

;;; Code:

(require 'cl-lib)
(require 'subr-x)
(require 'project)
(require 'autorevert)
(require 'coq-project)                  ; coq--read-options-from-project-file
(require 'coq-eglot)
(require 'coq-eglot-twin)

(defgroup coq-eglot-sandbox nil
  "Sandboxes, copies of a project where an agent works."
  :group 'coq-eglot)

(defcustom coq-eglot-sandbox-method 'auto
  "How a sandbox copies its project, see `coq-eglot-sandbox-create'.
`copy': a copy of its directory, build products included.
`worktree': a git worktree on a branch of its own, sandbox/NAME, then
a copy of the files of the project over it: its changes not committed,
its build products, with their dates, so that nothing is compiled again.
The agent can commit in it.  Only in a git repository.
`auto': `worktree' in a git repository, `copy' otherwise."
  :type '(choice (const :tag "Git worktree if possible" auto)
                 (const :tag "Copy" copy)
                 (const :tag "Git worktree" worktree))
  :group 'coq-eglot-sandbox)

(defcustom coq-eglot-sandbox-parent nil
  "Directory of the sandboxes, or nil for the parent of their project.
The sandbox NAME of the project in directory ROOT is ROOT-NAME in it."
  :type '(choice (const :tag "Beside the project" nil) directory)
  :group 'coq-eglot-sandbox)

(defcustom coq-eglot-sandbox-size-limit (* 500 1024 1024)
  "Size of a project, in bytes, above which a copy asks confirmation.
Nil: never ask."
  :type '(choice (const :tag "Never ask" nil) integer)
  :group 'coq-eglot-sandbox)

(defcustom coq-eglot-sandbox-agent-command "claude"
  "Command starting the agent, run in the sandbox by the user.
`coq-eglot-sandbox-create' puts \"cd SANDBOX && COMMAND\" in the kill
ring."
  :type 'string
  :group 'coq-eglot-sandbox)

;;; Where things are

(defun coq-eglot-sandbox--project-root (&optional dir)
  "Root of the project of DIR, `default-directory' by default.
The one of its server, see `coq-eglot-lsp-project'."
  (let* ((default-directory (or dir default-directory))
         (project (project-current)))
    (file-name-as-directory
     (expand-file-name (if project (project-root project) default-directory)))))

(defun coq-eglot-sandbox--directory (root name)
  "Directory of the sandbox NAME of the project in ROOT.
From the true name of ROOT: the same through links."
  (let ((root (directory-file-name (file-truename root))))
    (expand-file-name (format "%s-%s" (file-name-nondirectory root) name)
                      (or coq-eglot-sandbox-parent
                          (file-name-directory root)))))

(defun coq-eglot-sandbox--meta-file (sandbox &optional file)
  "FILE of the description of SANDBOX, or its directory."
  (expand-file-name (or file "")
                    (expand-file-name coq-eglot-sandbox-meta sandbox)))

(defun coq-eglot-sandbox--read (sandbox)
  "The description of SANDBOX, an alist, or nil if it is not one."
  (let ((file (coq-eglot-sandbox--meta-file sandbox "sandbox.json")))
    (when (file-readable-p file)
      (ignore-errors
        (with-temp-buffer
          (insert-file-contents file)
          (json-parse-buffer :object-type 'alist))))))

(defun coq-eglot-sandbox--copy-root (sandbox)
  "Root of the copy of its project in SANDBOX.
SANDBOX itself, or a subdirectory if the project is one of its git
repository."
  (file-name-as-directory
   (expand-file-name (or (alist-get 'project (coq-eglot-sandbox--read sandbox))
                         "")
                     sandbox)))

(defun coq-eglot-sandbox--same-file-p (a b)
  "Non-nil if the file names A and B, or nil, are the same file.
Through links, \"~\" and trailing slashes."
  (and a b (file-equal-p a b)))

(defun coq-eglot-sandbox--sandboxes (root)
  "Directories of the sandboxes of the project in ROOT.
Nil if their parent directory does not exist.  From the true name of
ROOT, like `coq-eglot-sandbox--directory'."
  (let* ((root (file-name-as-directory (file-truename root)))
         (parent (or coq-eglot-sandbox-parent
                     (file-name-directory (directory-file-name root))))
         (prefix (concat (file-name-nondirectory (directory-file-name root))
                         "-")))
    (when (file-directory-p parent)
      (seq-filter
       (lambda (dir)
         (coq-eglot-sandbox--same-file-p
          (alist-get 'origin (coq-eglot-sandbox--read dir)) root))
       (directory-files parent t (concat "\\`" (regexp-quote prefix)))))))

;;; Creation

(defun coq-eglot-sandbox--call (program &rest args)
  "Run PROGRAM with ARGS, signal an error with its output if it fails."
  (with-temp-buffer
    (let ((status (apply #'process-file program nil t nil args)))
      (unless (eq status 0)
        (error "Coq: %s %s failed: %s" program (string-join args " ")
               (string-trim (buffer-string))))
      (buffer-string))))

(defun coq-eglot-sandbox--git-toplevel (dir)
  "Root of the git repository of DIR, or nil."
  (let ((default-directory dir))
    (ignore-errors
      (file-name-as-directory
       (string-trim (coq-eglot-sandbox--call
                     "git" "rev-parse" "--show-toplevel"))))))

(defun coq-eglot-sandbox--size (root)
  "Size in bytes of ROOT without its .git, or nil if unknown.
Links are not followed."
  (ignore-errors
    (let ((size 0))
      (dolist (file (directory-files-recursively
                     root "" nil
                     (lambda (dir)
                       (and (not (file-symlink-p dir))
                            (not (equal (file-name-nondirectory
                                         (directory-file-name dir))
                                        ".git"))))))
        (cl-incf size (or (file-attribute-size (file-attributes file)) 0)))
      size)))

(defun coq-eglot-sandbox--entries (dir)
  "The files and directories of DIR to copy, absolute file names."
  (seq-remove (lambda (file)
                (member (file-name-nondirectory file)
                        (list "." ".." ".git" coq-eglot-sandbox-meta)))
              (directory-files dir t)))

(defun coq-eglot-sandbox--copy-emacs (file target)
  "Copy FILE to TARGET with Emacs, its dates and permissions kept.
A directory is merged with an existing TARGET.  Links are copied as
links, not followed."
  (cond ((file-symlink-p file)
         (when (file-symlink-p target) (delete-file target))
         (make-symbolic-link (file-symlink-p file) target t))
        ((file-directory-p file)
         (make-directory target t)
         (dolist (entry (directory-files file nil directory-files-no-dot-files-regexp))
           (coq-eglot-sandbox--copy-emacs (expand-file-name entry file)
                                          (expand-file-name entry target)))
         (set-file-times target (file-attribute-modification-time
                                 (file-attributes file)))
         (set-file-modes target (file-modes file)))
        (t (copy-file file target t t nil t))))

(defun coq-eglot-sandbox--copy-entry (file target)
  "Copy FILE to TARGET, its attributes and dates kept.
A directory is merged with an existing TARGET.  A light copy if the file
system can (reflink), a plain one otherwise.  With Emacs if there is no
cp program."
  (if (not (executable-find "cp"))
      (coq-eglot-sandbox--copy-emacs file target)
    (let ((source (if (file-directory-p file)
                      (progn (make-directory target t)
                             (concat (file-name-as-directory file) "."))
                    file)))
      (condition-case nil
          (coq-eglot-sandbox--call "cp" "-a" "--reflink=auto" source target)
        ;; cp of BSD or macOS: no --reflink
        (error (coq-eglot-sandbox--call "cp" "-a" source target))))))

(defun coq-eglot-sandbox--copy-tree (root sandbox)
  "Copy the files of ROOT in SANDBOX, but .git."
  (make-directory sandbox t)
  (dolist (file (coq-eglot-sandbox--entries root))
    (coq-eglot-sandbox--copy-entry
     file (expand-file-name (file-name-nondirectory file) sandbox))))

(defun coq-eglot-sandbox--worktree (root sandbox name)
  "Make SANDBOX a git worktree of the repository of ROOT.
On a branch of its own, sandbox/NAME.  The files of ROOT are copied
over it, see `coq-eglot-sandbox-method'.  Return the root of the copy
of ROOT in it, relative to SANDBOX: ROOT may be a subdirectory of its
repository."
  (let* ((top (coq-eglot-sandbox--git-toplevel root))
         (default-directory top)
         (branch (concat "sandbox/" name))
         (copy (file-name-as-directory
                (expand-file-name (file-relative-name root top) sandbox))))
    (coq-eglot-sandbox--call "git" "worktree" "add" "-b" branch sandbox "HEAD")
    (coq-eglot-sandbox--copy-tree root copy)
    ;; deleted in the project, not committed
    (let ((default-directory root))
      (dolist (file (split-string (coq-eglot-sandbox--call
                                   "git" "ls-files" "--deleted" "-z")
                                  "\0" t))
        (let ((deleted (expand-file-name file copy)))
          (when (file-exists-p deleted)
            (delete-file deleted)))))
    ;; the description of the sandbox is not part of the development
    (let* ((default-directory sandbox)
           (exclude (expand-file-name
                     (string-trim (coq-eglot-sandbox--call
                                   "git" "rev-parse" "--git-path"
                                   "info/exclude"))))
           (line (concat coq-eglot-sandbox-meta "/")))
      (make-directory (file-name-directory exclude) t)
      (unless (and (file-readable-p exclude)
                   (with-temp-buffer
                     (insert-file-contents exclude)
                     (re-search-forward
                      (concat "^" (regexp-quote line) "$") nil t)))
        (with-temp-buffer
          (insert line "\n")
          (append-to-file (point-min) (point-max) exclude))))
    (file-relative-name copy sandbox)))

(defun coq-eglot-sandbox--sources (root)
  "The sources of the project in ROOT, file names relative to ROOT.
Its Coq files and project files, outside hidden directories and the
build directory of dune."
  (mapcar
   (lambda (file) (file-relative-name file root))
   (directory-files-recursively
    root "\\.v\\'\\|\\`_\\(Coq\\|Rocq\\)Project\\'" nil
    (lambda (dir)
      (let ((name (file-name-nondirectory (directory-file-name dir))))
        (not (or (string-prefix-p "." name) (equal name "_build"))))))))

(defun coq-eglot-sandbox--snapshot (root sandbox)
  "Save the sources of ROOT in the description of SANDBOX, base of merges.
Their file names relative to ROOT."
  (let ((base (coq-eglot-sandbox--meta-file sandbox "base")))
    (dolist (file (coq-eglot-sandbox--sources root))
      (let ((target (expand-file-name file base)))
        (make-directory (file-name-directory target) t)
        (copy-file (expand-file-name file root) target t t t)))))

(defun coq-eglot-sandbox--absolute-paths (root copy)
  "Generated build files of COPY that name ROOT, relative file names.
Their builds would write into ROOT."
  (let ((root (directory-file-name root))
        found)
    (dolist (file (directory-files-recursively
                   copy
                   "\\`\\(Makefile.*\\|.*\\.conf\\|\\..*\\.d\\|dune\\(-project\\)?\\)\\'"
                   nil
                   (lambda (dir)
                     (not (string-prefix-p
                           "." (file-name-nondirectory
                                (directory-file-name dir)))))))
      (when (and (file-regular-p file)
                 (< (file-attribute-size (file-attributes file)) 10000000)
                 (with-temp-buffer
                   (insert-file-contents file)
                   (search-forward root nil t)))
        (push (file-relative-name file copy) found)))
    (nreverse found)))

(defun coq-eglot-sandbox--outside-load-path (root copy)
  "Directories of the load path of the project file of ROOT outside ROOT.
Not copied.  A list of (DIR . READ): DIR, the one of the project, READ,
the one the copy in COPY reads instead, the same DIR when absolute, or
when relative and the sandbox is beside its project."
  (when-let* ((file (seq-find #'file-exists-p
                              (mapcar (lambda (name) (expand-file-name name root))
                                      '("_CoqProject" "_RocqProject")))))
    (let (found)
      (dolist (option (coq--read-options-from-project-file
                       (with-temp-buffer
                         (insert-file-contents file)
                         (buffer-string))))
        (pcase option
          ((or `("-R" ,dir ,_) `("-Q" ,dir ,_) `("-I" ,dir))
           (let ((dir (file-name-as-directory (expand-file-name dir root))))
             (unless (file-in-directory-p dir root)
               (push (cons dir (file-name-as-directory
                                (expand-file-name (cadr option) copy)))
                     found))))))
      (nreverse found))))

(defun coq-eglot-sandbox--warn-outside (name root copy)
  "Warn about the load path of ROOT outside it, for the sandbox NAME in COPY.
See `coq-eglot-sandbox--outside-load-path'."
  (let ((outside (coq-eglot-sandbox--outside-load-path root copy)))
    (when outside
      (display-warning
       'coq-eglot
       (format "Sandbox %s: the project file loads directories outside \
the project, not copied:\n%s"
               name
               (mapconcat
                (pcase-lambda (`(,dir . ,read))
                  (cond ((equal dir read)
                         (format "  %s: shared with the project, a change \
there changes the project" dir))
                        ((file-directory-p read)
                         (format "  %s: the sandbox reads %s instead" dir read))
                        (t (format "  %s: not found from the sandbox, %s"
                                   dir read))))
                outside "\n"))))))

(defun coq-eglot-sandbox--describe (root sandbox project name method)
  "Write the description of SANDBOX of ROOT, NAME made by METHOD.
PROJECT: the root of the copy of ROOT, relative to SANDBOX."
  (let ((file (coq-eglot-sandbox--meta-file sandbox "sandbox.json")))
    (make-directory (file-name-directory file) t)
    (with-temp-file file
      (insert (json-serialize
               `((format . 1)
                 (name . ,name)
                 (origin . ,root)
                 (project . ,project)
                 (method . ,(symbol-name method))
                 (created . ,(format-time-string "%FT%T%z"))))
              "\n"))))

(defun coq-eglot-sandbox--make (root name)
  "Make the sandbox NAME of the project in ROOT, return its directory.
See `coq-eglot-sandbox-create'."
  (let* ((sandbox (coq-eglot-sandbox--directory root name))
         (top (coq-eglot-sandbox--git-toplevel root))
         (method (pcase coq-eglot-sandbox-method
                   ('auto (if top 'worktree 'copy))
                   ('worktree
                    (unless top
                      (user-error "Coq: %s is not in a git repository" root))
                    'worktree)
                   (_ 'copy))))
    (when (file-exists-p sandbox)
      (user-error "Coq: %s exists already" sandbox))
    ;; it would copy itself
    (when (file-in-directory-p sandbox root)
      (user-error "Coq: the sandbox %s is in its project" sandbox))
    (let ((size (coq-eglot-sandbox--size root)))
      (when (and (not size) coq-eglot-sandbox-size-limit)
        (display-warning
         'coq-eglot (format "Sandbox %s: the size of %s is unknown, \
not checked against `coq-eglot-sandbox-size-limit'" name root)))
      (when (and size coq-eglot-sandbox-size-limit
                 (> size coq-eglot-sandbox-size-limit)
                 (not (yes-or-no-p
                       (format "Coq: copy %s of %s? "
                               (file-size-human-readable size) root))))
        (user-error "Coq: no sandbox")))
    (condition-case err
        (let ((project (if (eq method 'worktree)
                           (coq-eglot-sandbox--worktree root sandbox name)
                         (coq-eglot-sandbox--copy-tree root sandbox)
                         "./")))
          (coq-eglot-sandbox--describe root sandbox project name method)
          (coq-eglot-sandbox--snapshot root sandbox))
      ;; no half made sandbox: it did not exist
      (error
       (if (eq method 'worktree)
           (let ((default-directory top))
             (ignore-errors
               (coq-eglot-sandbox--call "git" "worktree" "remove"
                                        "--force" sandbox)))
         (ignore-errors (delete-directory sandbox t)))
       (signal (car err) (cdr err))))
    (coq-eglot-sandbox--warn-outside
     name root (coq-eglot-sandbox--copy-root sandbox))
    (let ((named (coq-eglot-sandbox--absolute-paths
                  root (coq-eglot-sandbox--copy-root sandbox))))
      (when named
        (display-warning
         'coq-eglot
         (format "Sandbox %s: these generated files name the project %s, \
their builds may write into it, generate them again in the sandbox: %s"
                 name root (string-join named ", ")))))
    (file-name-as-directory sandbox)))

;;; The twins

(defun coq-eglot-sandbox--setup (sandbox)
  "Set up the current buffer, visiting a file of SANDBOX.
Read only for the user, reverted when its file changes."
  (setq coq-eglot--sandbox sandbox)
  (read-only-mode 1)
  (auto-revert-mode 1))

(defun coq-eglot-sandbox--pair-with (sandbox)
  "Pair the current script buffer with its file in SANDBOX.
Return the twin."
  (let* ((this (coq-eglot-script-buffer))
         (root (coq-eglot-sandbox--project-root))
         (copy (coq-eglot-sandbox--copy-root sandbox))
         (file (expand-file-name (file-relative-name (buffer-file-name this) root)
                                 copy)))
    (unless (file-exists-p file)
      (user-error "Coq: no %s in the sandbox" (file-relative-name file copy)))
    (let ((twin (find-file-noselect file)))
      (with-current-buffer twin
        (coq-eglot-sandbox--setup sandbox))
      (with-current-buffer this
        (coq-eglot-twin-pair twin)
        ;; the real development is the reference, the changes of the
        ;; sandbox are shown as added
        (coq-eglot-twin-swap-reference))
      twin)))

(defun coq-eglot-sandbox--check-buffer ()
  "Signal an error unless the current buffer can get a sandbox twin."
  (with-current-buffer (coq-eglot-script-buffer)
    (unless (buffer-file-name)
      (user-error "Coq: this buffer visits no file"))
    (when coq-eglot--sandbox
      (user-error "Coq: this buffer is in a sandbox already"))
    (when coq-eglot--twin
      (user-error "Coq: this buffer has a twin already, %s"
                  (buffer-name coq-eglot--twin)))))

(defun coq-eglot-sandbox-create (name)
  "Make a sandbox NAME of the project, pair the current buffer with its copy.
The sandbox is a copy of the project, build products included, see
`coq-eglot-sandbox-method', in the directory ROOT-NAME beside it, see
`coq-eglot-sandbox-parent'.  Modified buffers of the project are saved
first, with confirmation: the copy is the one on disk.  The copy of the
current file is its twin, see `coq-eglot-twin-pair', read only and
reverted when its file changes: the agent, started in the sandbox,
edits it.  The command starting it, see
`coq-eglot-sandbox-agent-command', is put in the kill ring."
  (interactive (progn (coq-eglot-sandbox--check-buffer)
                      (list (read-string "Sandbox name: " nil nil "ia"))))
  (coq-eglot-sandbox--check-buffer)
  (unless (string-match-p "\\`[[:alnum:]_.-]+\\'" name)
    (user-error "Coq: a sandbox name has letters, digits, _, . or - only"))
  (let* ((this (coq-eglot-script-buffer))
         (root (with-current-buffer this (coq-eglot-sandbox--project-root))))
    (save-some-buffers
     nil (lambda ()
           (and (buffer-file-name)
                (file-in-directory-p (buffer-file-name) root))))
    (let ((sandbox (coq-eglot-sandbox--make root name)))
      (with-current-buffer this
        (coq-eglot-sandbox--pair-with sandbox))
      (let ((command (format "cd %s && %s"
                             (shell-quote-argument
                              (coq-eglot-sandbox--copy-root sandbox))
                             coq-eglot-sandbox-agent-command)))
        (kill-new command)
        (message "Coq: sandbox %s, start the agent there: %s (in the kill ring)"
                 sandbox command)))))

(defun coq-eglot-sandbox-pair (sandbox)
  "Pair the current buffer with its copy in SANDBOX, one of its project.
See `coq-eglot-sandbox-create'."
  (interactive
   (progn
     (coq-eglot-sandbox--check-buffer)
     (let ((sandboxes (with-current-buffer (coq-eglot-script-buffer)
                        (coq-eglot-sandbox--sandboxes
                         (coq-eglot-sandbox--project-root)))))
       (unless sandboxes
         (user-error "Coq: this project has no sandbox"))
       (list (completing-read "Sandbox: " sandboxes nil t nil nil
                              (car sandboxes))))))
  (coq-eglot-sandbox--check-buffer)
  (let ((root (with-current-buffer (coq-eglot-script-buffer)
                (coq-eglot-sandbox--project-root)))
        (description (coq-eglot-sandbox--read sandbox)))
    (unless (coq-eglot-sandbox--same-file-p
             (alist-get 'origin description) root)
      (user-error "Coq: %s is not a sandbox of %s" sandbox root))
    (with-current-buffer (coq-eglot-script-buffer)
      (coq-eglot-sandbox--pair-with (file-name-as-directory sandbox)))))

(defun coq-eglot-sandbox-delete (sandbox)
  "Delete SANDBOX, a sandbox of the project of the current buffer.
After confirmation.  Its buffers are killed, unsaved changes lost.  A
worktree is removed, its branch kept: what the agent committed."
  (interactive
   (let ((sandboxes (coq-eglot-sandbox--sandboxes
                     (coq-eglot-sandbox--project-root))))
     (unless sandboxes
       (user-error "Coq: this project has no sandbox"))
     (list (completing-read "Delete sandbox: " sandboxes nil t nil nil
                            (car sandboxes)))))
  (let* ((sandbox (file-name-as-directory (expand-file-name sandbox)))
         (description (coq-eglot-sandbox--read sandbox)))
    ;; never delete what is not a sandbox
    (unless description
      (user-error "Coq: %s is not a sandbox" sandbox))
    (when (yes-or-no-p (format "Coq: delete the sandbox %s? " sandbox))
      (dolist (buffer (buffer-list))
        (let ((file (buffer-file-name buffer)))
          (when (and file (file-in-directory-p file sandbox))
            (with-current-buffer buffer (set-buffer-modified-p nil))
            (kill-buffer buffer))))
      (if (equal (alist-get 'method description) "worktree")
          (let ((default-directory (alist-get 'origin description)))
            (coq-eglot-sandbox--call "git" "worktree" "remove" "--force"
                                     sandbox))
        (delete-directory sandbox t))
      (message "Coq: sandbox %s deleted" sandbox))))

(provide 'coq-eglot-sandbox)

;;; coq-eglot-sandbox.el ends here
