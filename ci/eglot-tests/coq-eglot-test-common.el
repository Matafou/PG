;;; coq-eglot-test-common.el --- Utilities of the tests of the Eglot backend  -*- lexical-binding: t -*-
;;
;; This file is part of Proof General.
;;
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Loaded by the tests of the Eglot backend, coq-eglot-test-*.el: the
;; settings of the tests and their utilities.  The tests are skipped if
;; the language server is not found.  Set the environment variable
;; COQ_LSP to the server to use, coq-lsp in the path by default.

;;; Code:

(defvar coq-backend)                    ; before loading Proof General
(setq coq-backend 'eglot)

(require 'subr-x)
(require 'proof-site)
(proof-add-to-load-path (expand-file-name "coq/" proof-home-directory))
(require 'coq-mode)
(add-to-list 'load-path coq-eglot-directory)
(require 'coq-eglot)
(require 'coq-eglot-twin)

;; The server given by COQ_LSP: the Rocq next to it, set like a user
;; would, see `coq-eglot-lsp-user-rocq'.
(when (getenv "COQ_LSP")
  (let ((bin (file-name-directory (expand-file-name (getenv "COQ_LSP")))))
    (setq coq-prog-name
          (seq-find #'file-executable-p
                    (list (expand-file-name "rocq" bin)
                          (expand-file-name "coqtop" bin))))
    (put 'coq-prog-name 'customized-value (list coq-prog-name))))

;; The frame of batch mode is narrow: the smart policy would choose the
;; vertical layout.  The tests of the layouts bind it.
(setq proof-three-window-mode-policy 'hybrid)

;; Its windows are narrow too: Coq would print the goals and the answers
;; of the queries on several lines.  The tests of the printing width
;; bind it.
(setq coq-auto-adapt-printing-width nil)


;;; utility functions

(defun buffer-text (name)
  "Return the content of buffer NAME without surrounding blanks."
  (with-current-buffer name
    (string-trim (buffer-substring-no-properties (point-min) (point-max)))))

(defun goto-marker (marker)
  "Move point to the end of the command before comment MARKER."
  (goto-char (point-min))
  (should (search-forward (format "(* marker %s *)" marker) nil t))
  (goto-char (match-beginning 0))
  (skip-chars-backward " \t"))

(defun position-at-marker-p (marker)
  "Non-nil if the proof position is just before comment MARKER."
  (save-excursion
    (goto-marker marker)
    (= (point) (coq-eglot-position))))

(defun wait-for-coq ()
  "Wait until the current buffer is at rest and its goals are displayed.
Presentation may finish just after `coq-eglot-busy-p' becomes nil."
  (while (or (coq-eglot-busy-p)
             (not (coq-eglot-presentation-ready-p)))
    (accept-process-output nil 0.02)))

(defun run (command)
  "Run COMMAND and wait until it is finished."
  (funcall command)
  (wait-for-coq))

(defun query-result (command)
  "The answer of the query COMMAND, see `coq-query-result'.
`none' if it does not come."
  (let ((output 'none))
    (coq-query-result command (lambda (answer) (setq output answer)))
    (wait-for-coq)
    output))

(defun lsp-query (pos command)
  "The messages of COMMAND run at POS by the server, a list of strings."
  (let ((result 'none))
    (coq-eglot-lsp-query-async pos command
                               (lambda (messages) (setq result messages))
                               (lambda (failure) (setq result failure)))
    (should (wait-until (lambda () (not (eq result 'none))) 60))
    (should (listp result))
    result))

(defmacro as-user (buffer &rest body)
  "Run BODY in BUFFER as a command of the user there.
In the selected window, displaying BUFFER, with `this-command' set: an
edition by the user, see `coq-eglot--user-edit-p'."
  (declare (indent 1) (debug t))
  `(save-window-excursion
     (switch-to-buffer ,buffer)
     (let ((this-command 'test-command))
       ,@body)))

(defun end-of-command ()
  "Run what Emacs runs at the end of a command, wait for its requests.
After an edition, the goals and the proof position are updated
asynchronously."
  (run-hooks 'post-command-hook)
  (accept-process-output nil 0.3))

(defun server-usable-p ()
  "Non-nil if the server is found and recent enough."
  (let ((exe (ignore-errors (car (coq-eglot-lsp-server-command)))))
    (and exe
         (let ((version (car (ignore-errors (process-lines exe "--version")))))
           (and version
                (not (version< version coq-eglot-lsp-minimal-version)))))))

(defun skip-unless-server ()
  "Skip the test if the server is not usable.
Fail instead if COQ_EGLOT_REQUIRE_SERVER is set, as in the CI, where
a missing server should not go unnoticed."
  (unless (server-usable-p)
    (if (getenv "COQ_EGLOT_REQUIRE_SERVER")
        (ert-fail "No usable Coq language server")
      (ert-skip "No usable Coq language server"))))

(defun skip-unless-execinfo ()
  "Skip the test if the server does not tell the sentences it executes.
Before coq-lsp 0.2.4, see `coq-eglot-lsp-execution'.  In a script
buffer: the server depends on it."
  (let* ((exe (ignore-errors (car (coq-eglot-lsp-server-command))))
         (version (and exe (coq-eglot-lsp--server-version exe))))
    (unless (and version (not (version< version "0.2.4")))
      (ert-skip "The server does not tell the sentences it executes"))))

(defmacro with-test-file (&rest body)
  "Run BODY in a buffer visiting eglot_test.v, kill it afterwards."
  (declare (indent 0) (debug t))
  `(with-file "eglot_test.v" ,@body))

(defmacro with-file (file &rest body)
  "Run BODY in a buffer visiting FILE, kill it afterwards."
  (declare (indent 1) (debug t))
  `(progn
     (skip-unless-server)
     (let ((buffer (find-file-noselect ,file)))
       (unwind-protect
           (with-current-buffer buffer
             (should coq-eglot-mode)
             (coq-eglot-retract-buffer)
             ,@body)
         (with-current-buffer buffer (set-buffer-modified-p nil))
         (kill-buffer buffer)))))

(defun error-overlay-texts (face)
  "Texts under the error overlays with FACE, in the order of the buffer."
  (mapcar (lambda (ov) (buffer-substring (overlay-start ov) (overlay-end ov)))
          (sort (seq-filter (lambda (ov) (eq (overlay-get ov 'face) face))
                            coq-eglot--error-overlays)
                (lambda (a b) (< (overlay-start a) (overlay-start b))))))

(defun error-sentence-text ()
  "Text of the sentence that failed, under all the error overlays, or nil."
  (when coq-eglot--error-overlays
    (buffer-substring
     (apply #'min (mapcar #'overlay-start coq-eglot--error-overlays))
     (apply #'max (mapcar #'overlay-end coq-eglot--error-overlays)))))

(defun error-overlay-text (face)
  "Text under the first error overlay with FACE, or nil."
  (car (error-overlay-texts face)))

(defun query (command &rest args)
  "Run query COMMAND with ARGS, return the text of the response buffer."
  (with-current-buffer (get-buffer-create "*response*")
    (let ((inhibit-read-only t)) (erase-buffer)))
  (apply command args)
  (wait-until (lambda () (not (equal (buffer-text "*response*") ""))) 10)
  (buffer-text "*response*"))

(defmacro with-layout (three policy &rest body)
  "Run BODY with `proof-three-window-enable' THREE and POLICY.
From a frame showing only the current buffer, restored afterwards."
  (declare (indent 2) (debug t))
  `(let ((proof-three-window-enable ,three)
         (proof-three-window-mode-policy ,policy))
     (unwind-protect
         (progn
           (switch-to-buffer (current-buffer))
           (delete-other-windows)
           ,@body)
       (delete-other-windows))))

(defun windows-of (&rest names)
  "Windows of the buffers NAMES, all displayed."
  (mapcar (lambda (name) (or (get-buffer-window name)
                             (ert-fail (format "%s not displayed" name))))
          names))

(defvar coq-eglot-trace)                 ; let-bound

(defun locked-face ()
  "Face of the processed part of the current buffer.
The face of inactive buffers is simplified to its name."
  (let ((face (overlay-get coq-eglot--locked-overlay 'face)))
    (if (and (consp face) (memq 'coq-eglot-inactive-locked-face face))
        'coq-eglot-inactive-locked-face
      face)))

(defconst compile-directory (expand-file-name "compile/")
  "Directory of the tests of the compilation, with a _CoqProject.")

(defun force-new-check ()
  "Insert a fresh definition at the beginning of the buffer.
The server keeps the results of the sentences it checked, even in a
closed document: the following sentences are checked again."
  (goto-char (point-min))
  (insert (format "Definition fresh_%d := 0.\n" (random 1000000))))

(defun wait-until (pred seconds)
  "Wait until PRED returns non-nil, at most SECONDS.  Return its value."
  (let ((start (float-time)) value)
    (while (and (not (setq value (funcall pred)))
                (< (- (float-time) start) seconds))
      (accept-process-output nil 0.05))
    value))

(defmacro with-programs (programs &rest body)
  "Run BODY as if PROGRAMS were the only programs in `exec-path'."
  (declare (indent 1) (debug t))
  `(cl-letf (((symbol-function 'executable-find)
              (lambda (name &rest _) (car (member name ,programs)))))
     ,@body))

(defmacro with-installation (names &rest body)
  "Run BODY with a temporary installation of Rocq, executables NAMES.
Like (\"rocq\" \"coq-lsp\"): empty scripts in a directory bound to
`bin', deleted afterwards."
  (declare (indent 1) (debug t))
  `(let ((bin (file-name-as-directory (make-temp-file "coq-eglot-bin-" t))))
     (unwind-protect
         (progn
           (dolist (name ,names)
             (let ((file (expand-file-name name bin)))
               (with-temp-file file (insert "#!/bin/sh\n"))
               (set-file-modes file #o755)))
           ,@body)
       (delete-directory bin t))))

(defmacro without-user-rocq (&rest body)
  "Run BODY as if the user did not set `coq-prog-name' globally.
Like with COQ_LSP: then the Rocq is found in `exec-path'."
  (declare (indent 0) (debug t))
  `(let ((customized (get 'coq-prog-name 'customized-value))
         (saved (get 'coq-prog-name 'saved-value)))
     (put 'coq-prog-name 'customized-value nil)
     (put 'coq-prog-name 'saved-value nil)
     (unwind-protect
         (progn ,@body)
       (put 'coq-prog-name 'customized-value customized)
       (put 'coq-prog-name 'saved-value saved))))

(defun other-rocq ()
  "Rocq program of another opam switch with a server, or nil.
Of rocq-9.2 or rocq-9.0, not the one of the current buffer."
  (require 'coq-eglot-servers)
  (let ((current (coq-eglot-lsp--program-file (coq-eglot-lsp-rocq))))
    (seq-some (lambda (candidate)
                (and (member (car candidate) '("rocq-9.2" "rocq-9.0"))
                     (not (equal (file-truename (cdr candidate)) current))
                     (coq-eglot-lsp-server-program (cdr candidate))
                     (cdr candidate)))
              (coq-eglot-servers--opam-rocqs))))

(defun server-of (rocq)
  "True name of the program of the server of the Rocq program ROCQ."
  (file-truename (coq-eglot-lsp-server-program rocq)))

(defun server-program ()
  "True name of the program of the running server of the current buffer."
  (coq-eglot-lsp--program-file
   (car (process-command (jsonrpc--process (coq-eglot-lsp-current-server))))))

(provide 'coq-eglot-test-common)

;;; coq-eglot-test-common.el ends here
