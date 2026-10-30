;;; coq-eglot-test-basic.el --- Basic tests of the Eglot backend for Coq  -*- lexical-binding: t -*-
;;
;; This file is part of Proof General.
;;
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Test the proof position, the goals and response buffers, errors and
;; edition before the proof position, with the Eglot backend.  The
;; tests are skipped if the language server is not found.  Set the
;; environment variable COQ_LSP to the server to use, coq-lsp in the
;; path by default.

;;; Code:

(setq coq-backend 'eglot)

(require 'subr-x)
(require 'proof-site)
(proof-add-to-load-path (expand-file-name "coq/" proof-home-directory))
(require 'coq-mode)
(add-to-list 'load-path coq-eglot-directory)
(require 'coq-eglot)

(when (getenv "COQ_LSP")
  (setq coq-eglot-server-program (list (getenv "COQ_LSP"))))


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
  "Wait until the running check is finished."
  (while coq-eglot--running
    (accept-process-output nil 0.02)))

(defun run (command)
  "Run COMMAND and wait until it is finished."
  (funcall command)
  (wait-for-coq))

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


;;; tests

(ert-deftest coq-eglot-next-command ()
  "Process sentences one by one, comments are skipped."
  (with-test-file
    (run #'coq-eglot-assert-next-command)
    (should (position-at-marker-p "definition"))
    (should (equal (buffer-text "*response*") "double is defined"))
    (should (equal (buffer-text "*goals*") ""))
    (run #'coq-eglot-assert-next-command)
    (run #'coq-eglot-assert-next-command)
    (should (string-match-p "\\`1 goal\n\n *=+\n *forall n : nat"
                            (buffer-text "*goals*")))))

(ert-deftest coq-eglot-goto-point-and-undo ()
  "Go to point forward and backward, undo one sentence."
  (with-test-file
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (should (position-at-marker-p "split"))
    (should (string-match-p "\\`2 goals\n\n *n : nat\n" (buffer-text "*goals*")))
    (goto-marker "definition")
    (run #'coq-eglot-goto-point)
    (should (position-at-marker-p "definition"))
    (should (equal (buffer-text "*goals*") ""))
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (run #'coq-eglot-undo-last-command)
    (should (string-match-p "intros n\\.\\'"
                            (buffer-substring (point-min) (coq-eglot-position))))
    (should (string-match-p "\\`1 goal\n" (buffer-text "*goals*")))))

(ert-deftest coq-eglot-messages ()
  "Messages of the last processed sentence are in the response buffer."
  (with-test-file
    (goto-marker "hello")
    (run #'coq-eglot-goto-point)
    (should (equal (buffer-text "*response*") "hello"))
    (goto-marker "subproof")
    (run #'coq-eglot-goto-point)
    (should (equal (buffer-text "*goals*") "No more goals."))))

(defun error-overlay-text (face)
  "Text under the error overlay with FACE, or nil."
  (cl-loop for ov in coq-eglot--error-overlays
           when (eq (overlay-get ov 'face) face)
           return (buffer-substring (overlay-start ov) (overlay-end ov))))

(ert-deftest coq-eglot-error-stops ()
  "Processing stops before the sentence that fails.
Like Proof General, the sentence is highlighted with `proof-boring-face',
the error location with `proof-warning-face', and point moves there."
  (with-test-file
    (run #'coq-eglot-process-buffer)
    (should (position-at-marker-p "before error"))
    (should (string-match-p "unknown_lemma" (buffer-text "*response*")))
    (should (string-match-p "\\`1 goal\n\n *=+\n *1 = 2" (buffer-text "*goals*")))
    (should (equal (error-overlay-text 'proof-boring-face)
                   "rewrite unknown_lemma."))
    (should (equal (error-overlay-text 'proof-warning-face) "unknown_lemma"))
    (should (looking-at "unknown_lemma"))
    ;; the next command removes the highlighting
    (run #'coq-eglot-undo-last-command)
    (should-not coq-eglot--error-overlays)
    ;; Flymake is not used by default
    (should-not (bound-and-true-p flymake-mode))))

(ert-deftest coq-eglot-hover-only-processed ()
  "Eldoc asks the server only in the processed part."
  (with-test-file
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (should (memq #'coq-eglot--hover-eldoc-function eldoc-documentation-functions))
    (should-not (memq #'eglot-hover-eldoc-function eldoc-documentation-functions))
    (goto-marker "hello")
    (should (= 0 (let ((requests 0))
                   (cl-letf* ((ask (symbol-function 'eglot-hover-eldoc-function))
                              ((symbol-function 'eglot-hover-eldoc-function)
                               (lambda (&rest args) (cl-incf requests) (apply ask args))))
                     (coq-eglot--hover-eldoc-function #'ignore))
                   requests)))))

(ert-deftest coq-eglot-no-completion ()
  "Eglot does not ask completions: it would force a check up to point."
  (with-test-file
    (run #'coq-eglot-assert-next-command)
    ;; eglot--server-capable before Eglot 1.16 (Emacs 29)
    (cl-flet ((capable (feature)
                (if (fboundp 'eglot-server-capable)
                    (eglot-server-capable feature)
                  (with-no-warnings (eglot--server-capable feature)))))
      (should-not (capable :completionProvider))
      (should (capable :hoverProvider)))))

(defun query (command &rest args)
  "Run query COMMAND with ARGS, return the text of the response buffer."
  (with-current-buffer (get-buffer-create "*response*")
    (let ((inhibit-read-only t)) (erase-buffer)))
  (apply command args)
  (wait-until (lambda () (not (equal (buffer-text "*response*") ""))) 10)
  (buffer-text "*response*"))

(ert-deftest coq-eglot-queries ()
  "Queries run in the state at the proof position."
  (with-test-file
    (should-error (coq-eglot-About "double") :type 'user-error)
    (goto-marker "definition")
    (run #'coq-eglot-goto-point)
    (should (string-match-p "\\`double : nat -> nat"
                            (query #'coq-eglot-About "double")))
    ;; the final dot may be omitted
    (should (string-match-p ": nat\\'" (query #'coq-eglot-Check "double 2")))
    (should (string-match-p ": nat\\'" (query #'coq-eglot-query "Check 0.")))
    ;; l is defined after the proof position
    (should (string-match-p "not a defined object"
                            (query #'coq-eglot-About "l")))
    ;; errors are displayed as such
    (should (string-match-p "was not found" (query #'coq-eglot-Check "l")))
    (with-current-buffer "*response*"
      (should (eq (get-text-property (point-min) 'face) 'error)))
    ;; the proof position does not move
    (should (position-at-marker-p "definition"))))

(ert-deftest coq-eglot-id-at-point ()
  "The default argument of queries is the qualified identifier at point."
  (with-temp-buffer
    (insert "Check Nat.add_comm. foo' x.")
    (goto-char 10)
    (should (equal (coq-eglot--id-at-point) "Nat.add_comm"))
    (search-forward "foo")
    (should (equal (coq-eglot--id-at-point) "foo'"))
    (goto-char (point-max))
    (should (equal (coq-eglot--id-at-point) "x"))))

(ert-deftest coq-eglot-error-highlight-timeout ()
  "The highlighting of the error disappears after a while."
  (with-test-file
    (let ((coq-eglot-error-highlight-duration 0.3))
      (run #'coq-eglot-process-buffer)
      (should coq-eglot--error-overlays)
      (sleep-for 0.6)
      (should-not coq-eglot--error-overlays))))

(ert-deftest coq-eglot-edit-retracts ()
  "Editing before the proof position moves it before the edited sentence.
Typing right at the proof position does not move it."
  (with-test-file
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (goto-char (coq-eglot-position))
    (insert " ")
    (end-of-command)
    (should (position-at-marker-p "split"))
    ;; the goals after Proof. were not asked: the server is asked
    (goto-char (point-min))
    (search-forward "intros")
    (insert " ")
    (end-of-command)
    (should (string-match-p "Proof\\.\\'"
                            (buffer-substring (point-min) (coq-eglot-position))))
    (should (string-match-p "\\`1 goal\n\n *=+\n *forall n : nat"
                            (buffer-text "*goals*")))))

(defun count-goals-requests (fn)
  "Call FN, return the number of goals requests sent meanwhile."
  (let ((requests 0))
    (cl-letf* ((ask (symbol-function 'coq-eglot-lsp-goals))
               (ask-async (symbol-function 'coq-eglot-lsp-goals-async))
               ((symbol-function 'coq-eglot-lsp-goals)
                (lambda (pos) (cl-incf requests) (funcall ask pos)))
               ((symbol-function 'coq-eglot-lsp-goals-async)
                (lambda (&rest args) (cl-incf requests) (apply ask-async args))))
      (funcall fn))
    requests))

(ert-deftest coq-eglot-edit-retracts-kept-goals ()
  "Moving back to a sentence whose goals were displayed does not ask them."
  (with-test-file
    (dotimes (_ 3) (run #'coq-eglot-assert-next-command))
    (should (string-match-p "Proof\\.\\'"
                            (buffer-substring (point-min) (coq-eglot-position))))
    (run #'coq-eglot-assert-next-command)
    (goto-char (coq-eglot-position))
    (search-backward "intros")
    (insert " ")
    (should (= 0 (count-goals-requests
                  (lambda () (end-of-command)))))
    (should (string-match-p "Proof\\.\\'"
                            (buffer-substring (point-min) (coq-eglot-position))))
    (should (string-match-p "\\`1 goal\n\n *=+\n *forall n : nat"
                            (buffer-text "*goals*")))))

(defun force-new-check ()
  "Insert a fresh definition at the beginning of the buffer.
The server keeps the results of the sentences it checked, even in a
closed document: the following sentences are checked again."
  (goto-char (point-min))
  (insert (format "Definition fresh_%d := 0.\n" (random 1000000))))

(ert-deftest coq-eglot-progress ()
  "While checking, the part to check is displayed with `proof-queue-face'
and the proof position follows the progress of the server."
  (with-file "eglot_slow.v"
    (force-new-check)
    (coq-eglot-process-buffer)
    (should coq-eglot--running)
    (should (eq (overlay-get coq-eglot--queue-overlay 'face) 'proof-queue-face))
    (let ((positions nil))
      (while coq-eglot--running
        (cl-pushnew (coq-eglot-position) positions)
        (accept-process-output nil 0.02))
      ;; several intermediate positions were displayed
      (should (> (length positions) 3)))
    (should-not (overlay-buffer coq-eglot--queue-overlay))
    (should (position-at-marker-p "last"))))

(ert-deftest coq-eglot-edit-during-check ()
  "Editing before the proof position during a check does not block Emacs.
The check is interrupted, the proof position moves back before the
edited sentence and the goals are displayed when the server is ready."
  (with-file "eglot_slow.v"
    (force-new-check)
    (coq-eglot-process-buffer)
    ;; in the middle of the check
    (should (wait-until (lambda ()
                          (>= (how-many "Qed\\." (point-min) (coq-eglot-position))
                              2))
                        10))
    (should coq-eglot--running)
    (goto-char (coq-eglot-position))
    (search-backward "vm_compute")
    ;; a pending request on the part not checked yet, like the hover
    ;; of eldoc
    (let ((hover-answered nil)
          (start (float-time)))
      (jsonrpc-async-request (coq-eglot-lsp-current-server) :textDocument/hover
                             (list :textDocument (eglot--TextDocumentIdentifier)
                                   :position (eglot--pos-to-lsp-position
                                              (1- (point-max))))
                             :success-fn (lambda (_) (setq hover-answered t)))
      (insert " ")
      (run-hooks 'post-command-hook)
      (should (< (- (float-time) start) 0.1))
      ;; the edition is sent right away
      (should-not eglot--recent-changes)
      (accept-process-output nil 0.5)
      ;; the hover does not make the server check up to the end: coq-lsp
      ;; answers that the document is not ready, or drops the request
      ;; when it is cancelled first
      (should-not hover-answered))
    (should-not coq-eglot--running)
    (accept-process-output nil 1)
    ;; just before the edited sentence
    (should (string-match-p "Proof\\.\\'"
                            (buffer-substring (point-min) (coq-eglot-position))))
    (should (string-match-p "\\`1 goal" (buffer-text "*goals*")))))

(ert-deftest coq-eglot-interrupt ()
  "Interrupting a check leaves the proof position where the server was.
The next command works."
  (with-file "eglot_slow.v"
    (force-new-check)
    (coq-eglot-process-buffer)
    (sleep-for 0.5)
    (coq-eglot-interrupt)
    (should-not coq-eglot--running)
    (should (< (point-min) (coq-eglot-position)))
    (should-not (position-at-marker-p "last"))
    (run #'coq-eglot-process-buffer)
    (should (position-at-marker-p "last"))))

(defun wait-until (pred seconds)
  "Wait until PRED returns non-nil, at most SECONDS.  Return its value."
  (let ((start (float-time)) value)
    (while (and (not (setq value (funcall pred)))
                (< (- (float-time) start) seconds))
      (accept-process-output nil 0.05))
    value))

(defun start-cbn-check ()
  "Start checking the sentence that cannot be interrupted."
  (force-new-check)
  (goto-marker "cbn")
  (coq-eglot-goto-point)
  (sleep-for 0.5)
  (should coq-eglot--running))

(ert-deftest coq-eglot-second-interrupt-restarts ()
  "Interrupting does not wait for the server.  Interrupting again while
the server is still busy restarts it, keeping the proof position.
Without memprof-limits, cbn cannot be interrupted."
  (with-file "eglot_cbn.v"
    (let ((coq-eglot-strong-interrupt nil))
      (coq-eglot-restart-server))
    (start-cbn-check)
    (let ((server (coq-eglot-lsp-current-server))
          (position (coq-eglot-position))
          (start (float-time)))
      (coq-eglot-interrupt)
      (should (< (- (float-time) start) 0.1))
      (should coq-eglot--interrupting)
      ;; cbn cannot be interrupted: still busy
      (sleep-for 0.3)
      (should coq-eglot--interrupting)
      (setq start (float-time))
      (coq-eglot-interrupt)
      (should (< (- (float-time) start) 2))
      (should-not coq-eglot--interrupting)
      (should (coq-eglot-lsp-current-server))
      (should-not (eq server (coq-eglot-lsp-current-server)))
      (should (= position (coq-eglot-position))))))

(ert-deftest coq-eglot-exit ()
  "Stopping the server moves the proof position back to the beginning.
The next command starts a new server."
  (with-test-file
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (coq-eglot-exit)
    (should-not (coq-eglot-lsp-current-server))
    (should (= (point-min) (coq-eglot-position)))
    (run #'coq-eglot-assert-next-command)
    (should (coq-eglot-lsp-current-server))
    (should (position-at-marker-p "definition"))))

(ert-deftest coq-eglot-memprof-versions ()
  "memprof-limits is supported by OCaml 4.x and >= 5.3."
  (should (coq-eglot-lsp--memprof-p "4.14.2"))
  (should-not (coq-eglot-lsp--memprof-p "5.0.0"))
  (should-not (coq-eglot-lsp--memprof-p "5.2.1"))
  (should (coq-eglot-lsp--memprof-p "5.3.0"))
  (should (coq-eglot-lsp--memprof-p "5.4.1"))
  (should-not (coq-eglot-lsp--memprof-p nil)))

(defmacro with-programs (programs &rest body)
  "Run BODY as if PROGRAMS were the only programs in `exec-path'."
  (declare (indent 1) (debug t))
  `(cl-letf (((symbol-function 'executable-find)
              (lambda (name &rest _) (car (member name ,programs)))))
     ,@body))

(ert-deftest coq-eglot-server-command ()
  "The server is rocq-lsp, else coq-lsp, unless set by the user."
  (let ((coq-eglot-server-program nil))
    (with-programs '("rocq-lsp" "coq-lsp")
      (should (equal (coq-eglot-lsp-server-command) '("rocq-lsp"))))
    (with-programs '("coq-lsp")
      (should (equal (coq-eglot-lsp-server-command) '("coq-lsp"))))
    (with-programs '()
      (should-error (coq-eglot-lsp-server-command) :type 'user-error)))
  (let ((coq-eglot-server-program '("/opt/coq-lsp" "--foo")))
    (with-programs '("/opt/coq-lsp" "coq-lsp")
      (should (equal (coq-eglot-lsp-server-command) '("/opt/coq-lsp" "--foo"))))
    (with-programs '("coq-lsp")
      (should-error (coq-eglot-lsp-server-command) :type 'user-error))))

(ert-deftest coq-eglot-strong-interrupt-option ()
  "The option --int_backend=Mp is added according to the OCaml version."
  (with-programs '("coq-lsp")
    (let ((coq-eglot-server-program '("coq-lsp")))
      (cl-flet ((with-ocaml (version value)
                  (cl-letf (((symbol-function 'coq-eglot-lsp--ocaml-version)
                             (lambda (_) version)))
                    (let ((coq-eglot-strong-interrupt value))
                      (member "--int_backend=Mp" (coq-eglot-lsp--contact))))))
        (should (with-ocaml "5.4.1" 'auto))
        (should-not (with-ocaml "5.1.0" 'auto))
        (should-not (with-ocaml nil 'auto))
        (should (with-ocaml "5.1.0" t))
        (should-not (with-ocaml "5.4.1" nil))))
    ;; not added if the program already has the option
    (let ((coq-eglot-server-program '("coq-lsp" "--int_backend=Coq"))
          (coq-eglot-strong-interrupt t))
      (should-not (member "--int_backend=Mp" (coq-eglot-lsp--contact))))))

(ert-deftest coq-eglot-ocaml-version-detection ()
  "The OCaml version of the server is the one of ocamlc next to it."
  (let* ((program (ignore-errors (car (coq-eglot-lsp-server-command))))
         (exe (and program (executable-find program))))
    (skip-unless (and exe (file-executable-p
                           (expand-file-name "ocamlc" (file-name-directory
                                                       (file-truename exe))))))
    (should (string-match-p "\\`[0-9]+\\.[0-9]+"
                            (coq-eglot-lsp--ocaml-version program)))))

(ert-deftest coq-eglot-strong-interrupt ()
  "With `coq-eglot-strong-interrupt', even cbn is interrupted quickly.
Needs a server where memprof-limits is available (OCaml 4.x or
OCaml >= 5.3): set COQ_LSP_STRONG_INTERRUPT to run this test."
  (skip-unless (getenv "COQ_LSP_STRONG_INTERRUPT"))
  (let ((coq-eglot-strong-interrupt t))
    (should (member "--int_backend=Mp" (coq-eglot-lsp--contact)))
    (with-file "eglot_cbn.v"
      (coq-eglot-restart-server)
      (start-cbn-check)
      (coq-eglot-interrupt)
      (should (wait-until (lambda () (not coq-eglot--interrupting)) 1.5))
      ;; the server still works
      (coq-eglot-restart-server))))

(provide 'coq-eglot-test-basic)

;;; coq-eglot-test-basic.el ends here
