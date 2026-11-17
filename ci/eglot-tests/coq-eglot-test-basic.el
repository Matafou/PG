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

(defvar coq-backend)                    ; before loading Proof General
(setq coq-backend 'eglot)

(require 'subr-x)
(require 'proof-site)
(proof-add-to-load-path (expand-file-name "coq/" proof-home-directory))
(require 'coq-mode)
(add-to-list 'load-path coq-eglot-directory)
(require 'coq-eglot)
(require 'coq-eglot-twin)

(when (getenv "COQ_LSP")
  (setq coq-eglot-server-program (list (getenv "COQ_LSP"))))

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

(ert-deftest coq-eglot-eager-error-before-slow-tail ()
  "An eager error stops a distant check, and is reused after retracting."
  (with-file "eglot_error_slow.v"
    (let ((shown nil)
          (start (float-time)))
      (add-hook 'coq-eglot-error-hook (lambda () (setq shown t)) nil t)
      (coq-eglot-process-buffer)
      ;; Waiting for the request at the end would execute the slow tail.
      (should (wait-until (lambda () shown) 2))
      (should (< (- (float-time) start) 2))
      (should (position-at-marker-p "before slow error")))
    ;; On a server without strong interruption, the computation may still be
    ;; finishing before it can answer the request for the goals at the error.
    (wait-for-coq)
    (run #'coq-eglot-retract-buffer)
    ;; No edition: the diagnostic is still valid, so the planner must use it
    ;; before sending another distant check.
    (let ((requests 0)
          (ask (symbol-function 'coq-eglot-lsp-check-async)))
      (cl-letf (((symbol-function 'coq-eglot-lsp-check-async)
                 (lambda (&rest args)
                   (cl-incf requests)
                   (apply ask args))))
        (run #'coq-eglot-process-buffer))
      (should (= requests 0))
      (should (position-at-marker-p "before slow error")))))

(ert-deftest coq-eglot-hover-only-processed ()
  "Eldoc asks the server only in the processed part."
  (with-test-file
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (should (memq #'coq-eglot--hover-eldoc-function eldoc-documentation-functions))
    (should-not (memq #'eglot-hover-eldoc-function eldoc-documentation-functions))
    (goto-marker "hello")
    (should (= 0 (let ((requests 0))
                   (cl-letf (((symbol-function 'coq-eglot-lsp-hover-async)
                              (lambda (&rest _) (cl-incf requests))))
                     (coq-eglot--hover-eldoc-function #'ignore))
                   requests)))))

(ert-deftest coq-eglot-hover-through-pseudo-server ()
  "A useful hover is sent and formatted by the pseudo-server."
  (with-test-file
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (should (wait-until (lambda () (null coq-eglot-lsp--active-requests)) 2))
    (goto-char (point-min))
    (search-forward "double")
    (let ((result 'pending))
      (should
       (coq-eglot-lsp-hover-async
        (point)
        (lambda (info _echo) (setq result info))
        (lambda (failure) (setq result failure))))
      (should (wait-until (lambda () (not (eq result 'pending))) 2))
      (should (stringp result))
      (should (string-search "double" result)))))

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

(defun query-interactively (command prefix argument)
  "Run COMMAND with PREFIX as if typed, answering ARGUMENT.
Return the text of the response buffer."
  (cl-letf (((symbol-function 'read-string) (lambda (&rest _) argument)))
    (let ((current-prefix-arg prefix))
      (query #'call-interactively command))))

(ert-deftest coq-eglot-queries ()
  "Queries run in the state at the proof position.  The query commands
are common to all backends."
  (with-test-file
    (should (eq coq-query-function #'coq-eglot-run-query))
    (should (eq (key-binding (kbd "C-c C-a C-b")) #'coq-About))
    (should-error (coq-run-query "About double") :type 'user-error)
    (goto-marker "definition")
    (run #'coq-eglot-goto-point)
    (should (string-match-p "\\`double : nat -> nat"
                            (query-interactively #'coq-About nil "double")))
    ;; the final dot may be omitted
    (should (string-match-p ": nat\\'" (query #'coq-run-query "Check double 2")))
    (should (string-match-p ": nat\\'" (query #'coq-eglot-query "Check 0.")))
    ;; l is defined after the proof position
    (should (string-match-p "not a defined object"
                            (query #'coq-run-query "About l")))
    ;; errors are displayed as such
    (should (string-match-p "was not found" (query #'coq-run-query "Check l")))
    (with-current-buffer "*response*"
      (should (eq (get-text-property (point-min) 'font-lock-face) 'error)))
    ;; the proof position does not move
    (should (position-at-marker-p "definition"))))

(ert-deftest coq-eglot-query-flags ()
  "Queries can use other printing flags, for this query only.
Like in Proof General, \\[universal-argument] means Printing All."
  (with-test-file
    (goto-marker "before error")
    (run #'coq-eglot-goto-point)
    (should (equal (query-interactively #'coq-Check nil "double 2")
                   "double 2\n     : nat"))
    (should (string-match-p "\\`double (S (S O))"
                            (query-interactively #'coq-Check '(4) "double 2")))
    ;; not kept for the next query
    (should (string-match-p "\\`double 2"
                            (query-interactively #'coq-Check nil "double 2")))
    (should (string-match-p "\\`@id nat 0"
                            (query-interactively #'coq-Check-show-implicits nil
                                                 "id 0")))
    (should (string-match-p "\\`@eq nat 0 0"
                            (query #'coq-run-query "Check 0 = 0"
                                   '("Set Printing Implicit"
                                     "Unset Printing Notations"))))
    (should (string-match-p "\\`S (S O)"
                            (query-interactively #'coq-eglot-query '(4)
                                                 "Check 2")))
    (should (string-match-p "\\`0 = 0"
                            (query #'coq-run-query "Check 0 = 0")))))

(ert-deftest coq-eglot-query-flags-by-name ()
  "With \\[universal-argument] \\[universal-argument], the printing flags
are chosen by name, like in Proof General."
  (with-test-file
    (goto-marker "before error")
    (run #'coq-eglot-goto-point)
    (cl-letf (((symbol-function 'completing-read-multiple)
               (lambda (&rest _) '("Implicit" "No Notations"))))
      (should (string-match-p "\\`@eq nat 0 0"
                              (query-interactively #'coq-Check '(16)
                                                   "0 = 0"))))))

(ert-deftest coq-eglot-query-result ()
  "`coq-query-result' returns the answer of a query, nil on an error."
  (with-test-file
    (should (eq coq-query-result-function #'coq-eglot-query-result))
    (should-not (query-result "Check 0"))
    (goto-marker "definition")
    (run #'coq-eglot-goto-point)
    (should (string-match-p "double\\s-*:\\s-*nat -> nat"
                            (query-result "Check double")))
    (should-not (query-result "Check unknown_identifier"))
    ;; nothing displayed
    (should-not (string-match-p "nat -> nat" (buffer-text "*response*")))))

(ert-deftest coq-eglot-insert-intros ()
  "`coq-insert-intros' inserts the names given by Show Intros, like in
Proof General."
  (with-test-file
    (goto-marker "statement")
    (run #'coq-eglot-goto-point)
    (should (eq (key-binding (kbd "C-c C-a C-i")) #'coq-insert-intros))
    (let ((position (coq-eglot-position))
          (proof-double-hit-enable nil))
      (run #'coq-insert-intros)
      (should (looking-back "intros n\\." (line-beginning-position)))
      ;; inserted after the proof position, which does not move
      (should (= (coq-eglot-position) position)))))

(ert-deftest coq-eglot-insert-match ()
  "`coq-insert-match' inserts the match given by Show Match, like in Proof
General."
  (with-test-file
    (goto-marker "definition")
    (run #'coq-eglot-goto-point)
    (forward-line 1)
    (let ((coq-use-yasnippet nil)
          (start (point)))
      (cl-letf (((symbol-function 'read-string) (lambda (&rest _) "nat")))
        (run #'coq-insert-match))
      (let ((text (buffer-substring start (point-max))))
        (should (string-match-p "match\\s-+with" text))
        (should (string-match-p "| O =>" text))
        (should (string-match-p "| S [[:alnum:]_]+ =>" text))))))

(ert-deftest coq-eglot-query-result-without-waiting ()
  "`coq-query-result' does not wait: the insertion comes with the answer,
at the place where it was asked, even if point moved since."
  (with-test-file
    (goto-marker "statement")
    (run #'coq-eglot-goto-point)
    (let ((proof-double-hit-enable nil)
          (asked (point)))
      (cl-letf (((symbol-function 'jsonrpc-request)
                 (lambda (&rest _) (error "Synchronous request"))))
        (coq-insert-intros)
        ;; not yet
        (should (= (point) asked))
        (should (coq-eglot-busy-p))
        (goto-char (point-min))
        (wait-for-coq))
      (should (= (point) (point-min)))
      (goto-char asked)
      (should (looking-at "intros n\\.")))))

(ert-deftest coq-eglot-insert-intros-editions ()
  "An insertion is dropped if something was typed where it goes while
waiting for Coq, not for an edition elsewhere.  It is undone on its own,
not with the edition before it."
  (with-test-file
    (goto-marker "statement")
    (run #'coq-eglot-goto-point)
    (let ((proof-double-hit-enable nil)
          (asked (point)))
      ;; typed at the place
      (coq-insert-intros)
      (insert "X")
      (wait-for-coq)
      (should (looking-back "\\.X" (line-beginning-position)))
      (delete-char -1)
      ;; an edition elsewhere, then the insertion
      (undo-boundary)
      (coq-insert-intros)
      (save-excursion (goto-char (point-max)) (insert "(* end *)"))
      (wait-for-coq)
      (goto-char asked)
      (should (looking-at "intros n\\."))
      (should (string-suffix-p "(* end *)" (buffer-string)))
      ;; undone in two steps, the insertion first
      (undo-boundary)
      (undo-start)
      (undo-more 1)
      (undo-more 1)
      (goto-char asked)
      (should-not (looking-at "intros"))
      (should (string-suffix-p "(* end *)" (buffer-string)))
      (undo-more 1)
      (should-not (string-suffix-p "(* end *)" (buffer-string))))))

(ert-deftest coq-eglot-query-result-stale ()
  "The answer of `coq-query-result' is dropped if the proof position
moved before it came, or if the query is cancelled, like by a restart."
  (with-test-file
    (goto-marker "statement")
    (run #'coq-eglot-goto-point)
    (let ((called nil))
      (coq-query-result "Show Intros" (lambda (_) (setq called t)))
      (coq-eglot-undo-last-command)
      (wait-for-coq)
      (should-not called)
      (goto-marker "statement")
      (run #'coq-eglot-goto-point)
      ;; cancelled, the proof position stays
      (coq-query-result "Show Intros" (lambda (_) (setq called t)))
      (coq-eglot-restart-server)
      (wait-for-coq)
      (accept-process-output nil 0.2)
      (should-not called)
      ;; and when nothing changes, it comes
      (should (string-match-p "n" (query-result "Show Intros"))))))

(ert-deftest coq-eglot-insert-match-snippet ()
  "With snippets, the match is a snippet if point is still where it was
asked, plain text otherwise: a snippet would be edited away from point."
  (with-test-file
    (goto-marker "definition")
    (run #'coq-eglot-goto-point)
    (forward-line 1)
    (let ((coq-use-yasnippet t)
          (snippets 0)
          (start (point)))
      (cl-letf (((symbol-function 'read-string) (lambda (&rest _) "nat"))
                ((symbol-function 'yas-expand-snippet)
                 (lambda (text) (cl-incf snippets) (insert text))))
        (run #'coq-insert-match)
        (should (= snippets 1))
        (delete-region start (point-max))
        (save-excursion (insert "\n(* end *)\n"))
        (coq-insert-match)
        (goto-char (point-max))
        (wait-for-coq)
        (should (= snippets 1))
        (goto-char start)
        (should (looking-at "match\\s-+"))))))

(ert-deftest coq-eglot-insertions-without-query ()
  "The insertions without query of Proof General: keys, menu, Require."
  (with-test-file
    (dolist (binding '(("C-c C-a C-(" . coq-insert-section-or-module)
                       ("C-c C-a C-)" . coq-end-Section)
                       ("C-c C-a C-t" . coq-insert-tactic)
                       ("C-c C-a t" . coq-insert-tactical)
                       ("C-c C-a !" . coq-insert-solve-tactic)
                       ("C-c C-a C-SPC" . coq-insert-term)
                       ("C-c C-a C-<return>" . coq-insert-command)
                       ("C-c C-a C-r" . coq-insert-requires)))
      (should (eq (key-binding (kbd (car binding))) (cdr binding))))
    (let* ((menu (assoc "INSERT" (cdr coq-eglot--menu-spec)))
           (commands (delq nil (mapcar (lambda (item)
                                         (and (vectorp item) (aref item 1)))
                                       menu))))
      (should menu)
      (dolist (command '(coq-insert-intros coq-insert-tactic
                         coq-insert-requires coq-insert-named-goal-selectors))
        (should (memq command commands)))
      (should (assoc "Tactics (menu)" (cdr menu))))
    ;; Require completes on the files of the load path, "." by default
    (goto-char (point-max))
    (let ((answers '("Require Import" "eglot_other" "")))
      (cl-letf (((symbol-function 'completing-read)
                 (lambda (_prompt collection &rest _)
                   (let ((answer (pop answers)))
                     (should (or (equal answer "")
                                 (member answer (all-completions "" collection))))
                     answer))))
        (coq-insert-requires)))
    (should (looking-back "Require Import eglot_other\\.\n"
                          (line-beginning-position 0)))))

(ert-deftest coq-eglot-search ()
  "Search finds the lemmas proved before the proof position."
  (with-test-file
    (goto-marker "before error")
    (run #'coq-eglot-goto-point)
    (should (string-match-p "^l: forall n : nat, double n = n \\+ n /\\\\ True"
                            (query-interactively #'coq-Search nil "double")))))

(ert-deftest coq-eglot-print-and-search-pattern ()
  "Print and SearchPattern, on C-c C-a C-p and C-c C-a C-o like in
Proof General."
  (with-test-file
    (goto-marker "before error")
    (run #'coq-eglot-goto-point)
    (should (string-match-p "\\`double = fun n : nat => n \\+ n"
                            (query-interactively #'coq-Print nil "double")))
    (should (string-match-p "^l: forall n : nat, double n = n \\+ n /\\\\ True"
                            (query-interactively #'coq-SearchIsos nil
                                                 "(double _ = _ /\\ _)")))
    (should (eq (key-binding (kbd "C-c C-a C-p")) #'coq-Print))
    (should (eq (key-binding (kbd "C-c C-a C-o")) #'coq-SearchIsos))))

(ert-deftest coq-eglot-commands-from-output-buffers ()
  "The keys of the script buffer work in the goals and response
buffers, on the active script buffer, like in Proof General."
  (with-test-file
    (goto-marker "definition")
    (run #'coq-eglot-goto-point)
    (let ((script (current-buffer)))
      (with-current-buffer "*goals*"
        (should (eq (key-binding (kbd "C-c C-n"))
                    #'coq-eglot-assert-next-command))
        ;; not the keys of special-mode: q does not close the window
        (should-not (eq (key-binding "q") #'quit-window))
        (should-not (eq (key-binding "g") #'revert-buffer))
        (should buffer-read-only)
        (coq-eglot-assert-next-command))
      (wait-for-coq)
      (should (position-at-marker-p "statement"))
      (with-current-buffer "*goals*"
        (coq-eglot-undo-last-command))
      (wait-for-coq)
      (should (position-at-marker-p "definition"))
      ;; queries read their argument in the output buffer
      (with-current-buffer "*response*"
        (let ((inhibit-read-only t))
          (erase-buffer)
          (insert "double"))
        (goto-char (point-min))
        (should (string-match-p "\\`double : nat -> nat"
                                (query-interactively #'coq-About nil
                                                     "double")))
        (should (eq (key-binding (kbd "C-c C-a C-b")) #'coq-About)))
      (with-current-buffer "*goals*"
        (coq-eglot-goto-end-of-locked)
        (should (eq (current-buffer) script))
        (should (= (point) (coq-eglot-position))))))
  ;; no active script buffer: nothing to act on
  (with-temp-buffer
    (coq-eglot-goals-mode)
    (cl-letf (((coq-eglot--output-active coq-eglot--default-output) nil))
      (should-error (coq-eglot-assert-next-command) :type 'user-error))))

(defun face-of (buffer text)
  "Face of the first occurrence of TEXT in BUFFER, after fontification."
  (with-current-buffer buffer
    (font-lock-mode 1)                  ; not on in batch mode
    (font-lock-ensure)
    (goto-char (point-min))
    (should (search-forward text nil t))
    (or (get-text-property (match-beginning 0) 'face)
        (get-text-property (match-beginning 0) 'font-lock-face))))

(ert-deftest coq-eglot-highlighting ()
  "Goals and response buffers are highlighted like in Proof General."
  (with-test-file
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (should (eq (face-of "*goals*" "n :") 'proof-declaration-name-face))
    (query #'coq-run-query "About double")
    (should (eq (face-of "*response*" "double :") 'proof-declaration-name-face))
    (query #'coq-run-query "Check unknown_thing")
    ;; fontification keeps the face of errors
    (should (eq (face-of "*response*" "The reference") 'error))))

(ert-deftest coq-eglot-split-goals ()
  "The conclusion can be displayed apart from the hypotheses."
  (with-test-file
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (let ((whole (buffer-text "*goals*")))
      (should (string-match-p "n : nat\n *=+\n *double n = n \\+ n" whole))
      (unwind-protect
          (progn
            (coq-eglot-toggle-split-goals)
            (should (equal (buffer-text "*goals*") "2 goals\n\n  n : nat"))
            ;; no separator: the windows separate
            (should (equal (buffer-text "*conclusion*")
                           "double n = n + n\n\ngoal 2 is:\n True"))
            ;; the other goals are folded there
            (should (equal (with-current-buffer "*conclusion*"
                             (substring-no-properties
                              (overlay-get (other-goals-overlay) 'display)))
                           "▸ 1 more goal"))
            (should (eq (coq-eglot--goals-buffer) (get-buffer "*conclusion*")))
            ;; both are displayed, each in its window
            (should (get-buffer-window "*goals*" t))
            (should (get-buffer-window "*conclusion*" t))
            ;; the conclusion comes right below the hypotheses, after a
            ;; line drawn with our face
            (let ((window (get-buffer-window "*goals*" t)))
              (should (= (window-body-height window)
                         (window-total-height window))))
            (with-current-buffer "*conclusion*"
              ;; format-mode-line gives nothing in batch mode
              (should (string-match-p "\\`─+\\'" header-line-format))
              (should (eq (get-text-property 0 'face header-line-format)
                          'coq-eglot-goals-separator)))
            ;; next goals go to both buffers
            (goto-marker "subproof")
            (run #'coq-eglot-goto-point)
            (should (equal (buffer-text "*goals*") ""))
            (should (equal (buffer-text "*conclusion*") "No more goals."))
            (coq-eglot-toggle-split-goals)
            (should-not (get-buffer "*conclusion*"))
            (let ((window (get-buffer-window "*goals*" t)))
              (should (< (window-body-height window)
                         (window-total-height window))))
            (should (equal (buffer-text "*goals*") "No more goals."))
            (run #'coq-eglot-undo-last-command)
            (goto-marker "split")
            (run #'coq-eglot-goto-point)
            (should (equal (buffer-text "*goals*") whole)))
        (setq coq-eglot-split-goals nil)))))

(ert-deftest coq-eglot-allocate-heights ()
  "Windows get the height they need by priority, the first one the rest."
  ;; enough for everybody
  (should (equal (coq-eglot--allocate-heights 30 '(5 6 4) 4) '(20 6 4)))
  ;; the first one takes what it needs, the others their minimum
  (should (equal (coq-eglot--allocate-heights 30 '(40 6 4) 4) '(22 4 4)))
  (should (equal (coq-eglot--allocate-heights 30 '(10 40 4) 4) '(10 16 4)))
  ;; too small
  (should-not (coq-eglot--allocate-heights 10 '(5 6 4) 4)))

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

(ert-deftest coq-eglot-resize-windows ()
  "The response window gets the height it needs, the goals window the
rest, like with `coq-optimise-resp-windows-enable' in Proof General."
  (with-test-file
    (with-layout t 'hybrid
      (goto-marker "split")
      (run #'coq-eglot-goto-point)
      (query #'coq-eglot-run-query "Check double")
      (let ((goals (get-buffer-window "*goals*"))
            (response (get-buffer-window "*response*")))
        (should (and goals response))
        (should (= (window-total-height response)
                   (max window-min-height (coq-eglot--window-need response))))
        (should (> (window-total-height goals) (coq-eglot--window-need goals)))))))

(ert-deftest coq-eglot-resize-windows-off ()
  "Without `coq-optimise-resp-windows-enable', the heights of the windows
do not change."
  (with-test-file
    (with-layout t 'vertical
      (let ((coq-optimise-resp-windows-enable nil)
            (calls 0))
        (cl-letf (((symbol-function 'coq-eglot-resize-windows-by-priority)
                   (lambda () (setq calls (1+ calls)))))
          (goto-marker "split")
          (run #'coq-eglot-goto-point)
          (query #'coq-eglot-run-query "Check double"))
        (should (= calls 0))))))

(ert-deftest coq-eglot-resize-windows-split ()
  "With split goals, the conclusion gets its height first, and the rest,
the hypotheses and the response window the height they need."
  (with-test-file
    (unwind-protect
        (progn
          (setq coq-eglot-split-goals t)
          (goto-marker "split")
          (run #'coq-eglot-goto-point)
          (let ((goals (get-buffer-window "*goals*"))
                (conclusion (get-buffer-window "*conclusion*"))
                (response (get-buffer-window "*response*")))
            (should (and goals conclusion response))
            ;; at least the height it needs, the other goal folded
            ;; (batch mode ignores the display property in this
            ;; computation)
            (should (>= (window-total-height conclusion)
                        (coq-eglot--window-need conclusion)))
            ;; the hypotheses: never more than they need
            (should (= (window-total-height goals)
                       (max window-min-height (coq-eglot--window-need goals))))
            (should (= (window-total-height response)
                       (max window-min-height
                            (coq-eglot--window-need response))))))
      (setq coq-eglot-split-goals nil)
      (let ((buffer (get-buffer "*conclusion*")))
        (when buffer
          (mapc #'delete-window (get-buffer-window-list buffer nil t))
          (kill-buffer buffer))))))

(ert-deftest coq-eglot-layout-windows ()
  "C-c C-l displays the closed goals and response windows again, with
their default width, like in Proof General."
  (with-test-file
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (let ((script (current-buffer)))
      (switch-to-buffer script)
      (delete-window (get-buffer-window "*goals*"))
      (let ((response (get-buffer-window "*response*")))
        (window-resize response (- 10 (window-total-width response)) t))
      (should (eq (key-binding (kbd "C-c C-l")) #'coq-eglot-layout-windows))
      (coq-eglot-layout-windows)
      (should (get-buffer-window "*goals*"))
      (should (eq (window-buffer (selected-window)) script))
      ;; half of the frame
      (should (< (abs (- (window-total-width (get-buffer-window "*response*"))
                         (/ (frame-width) 2)))
                 3))
      ;; from the goals buffer, the selected window stays there
      (select-window (get-buffer-window "*goals*"))
      (coq-eglot-layout-windows)
      (should (eq (window-buffer (selected-window)) (get-buffer "*goals*"))))))

;;; window layouts, like in Proof General

(defun windows-of (&rest names)
  "Windows of the buffers NAMES, all displayed."
  (mapcar (lambda (name) (or (get-buffer-window name)
                             (ert-fail (format "%s not displayed" name))))
          names))

(defun output-windows ()
  "Windows displaying the goals, the conclusion or the messages."
  (seq-filter #'coq-eglot--output-window-p (window-list nil 'no-minibuffer)))

(ert-deftest coq-eglot-layout-vertical ()
  "Vertical policy: the goals and the messages below the script, in
dedicated windows."
  (with-test-file
    (with-layout t 'vertical
      (goto-marker "split")
      (run #'coq-eglot-goto-point)
      (pcase-let ((`(,script ,goals ,response)
                   (windows-of (current-buffer) "*goals*" "*response*")))
        (should (= (window-left-column script) (window-left-column goals)
                   (window-left-column response)))
        (should (< (window-top-line script) (window-top-line goals)
                   (window-top-line response)))
        (should (window-dedicated-p goals))
        (should (window-dedicated-p response))))))

(ert-deftest coq-eglot-layout-hybrid ()
  "Hybrid policy: the goals above the messages, on the right of the
script."
  (with-test-file
    (with-layout t 'hybrid
      (goto-marker "split")
      (run #'coq-eglot-goto-point)
      (pcase-let ((`(,script ,goals ,response)
                   (windows-of (current-buffer) "*goals*" "*response*")))
        (should (< (window-left-column script) (window-left-column goals)))
        (should (= (window-left-column goals) (window-left-column response)))
        (should (< (window-top-line goals) (window-top-line response)))))))

(ert-deftest coq-eglot-layout-hybrid-conclusion ()
  "The conclusion window is always created just below the goals window,
even when the messages window is higher."
  (with-test-file
    (with-layout t 'hybrid
      (goto-marker "split")
      (run #'coq-eglot-goto-point)
      (let ((coq-optimise-resp-windows-enable nil))
        (pcase-let ((`(,goals ,response)
                     (windows-of "*goals*" "*response*")))
          (window-resize goals (- window-min-height (window-total-height goals)))
          (should (> (window-total-height response)
                     (window-total-height goals))))
        (unwind-protect
            (progn
              (coq-eglot-toggle-split-goals)
              (pcase-let ((`(,goals ,conclusion ,response)
                           (windows-of "*goals*" "*conclusion*" "*response*")))
                (should (eq (window-in-direction 'below goals) conclusion))
                (should (eq (window-in-direction 'below conclusion) response))))
          (coq-eglot-toggle-split-goals))))))

(ert-deftest coq-eglot-layout-horizontal ()
  "Horizontal policy: three columns.  With the conclusion apart, it is
below the goals, the messages keep the whole height."
  (with-test-file
    (with-layout t 'horizontal
      (goto-marker "split")
      (run #'coq-eglot-goto-point)
      (pcase-let ((`(,script ,goals ,response)
                   (windows-of (current-buffer) "*goals*" "*response*")))
        (should (< (window-left-column script) (window-left-column goals)
                   (window-left-column response)))
        (should (= (window-top-line script) (window-top-line goals)
                   (window-top-line response))))
      (unwind-protect
          (progn
            (coq-eglot-toggle-split-goals)
            (pcase-let ((`(,goals ,conclusion ,response)
                         (windows-of "*goals*" "*conclusion*" "*response*")))
              (should (= (window-left-column goals)
                         (window-left-column conclusion)))
              (should (< (window-top-line goals) (window-top-line conclusion)))
              (should (= (window-top-line goals) (window-top-line response)))
              (should (> (window-left-column response)
                         (window-left-column conclusion)))))
        (coq-eglot-toggle-split-goals)))))

(ert-deftest coq-eglot-layout-two-windows ()
  "Without `proof-three-window-enable', the goals and the messages share
one window, not dedicated: the messages when there are some, the goals
otherwise."
  (with-test-file
    (with-layout nil 'hybrid
      (goto-marker "split")
      (run #'coq-eglot-goto-point)
      (should (equal (mapcar (lambda (w) (buffer-name (window-buffer w)))
                             (output-windows))
                     '("*goals*")))
      (should-not (window-dedicated-p (car (output-windows))))
      ;; the answer of a query
      (query #'coq-run-query "About double")
      (should (equal (mapcar (lambda (w) (buffer-name (window-buffer w)))
                             (output-windows))
                     '("*response*")))
      ;; a sentence printing a message
      (goto-marker "hello")
      (run #'coq-eglot-goto-point)
      (should (equal (buffer-text "*response*") "hello"))
      (should (equal (mapcar (lambda (w) (buffer-name (window-buffer w)))
                             (output-windows))
                     '("*response*")))
      ;; no message: the goals
      (goto-marker "split")
      (run #'coq-eglot-goto-point)
      (should (equal (mapcar (lambda (w) (buffer-name (window-buffer w)))
                             (output-windows))
                     '("*goals*")))
      ;; C-c C-l shows the goals only
      (delete-other-windows)
      (coq-eglot-layout-windows)
      (should (equal (mapcar (lambda (w) (buffer-name (window-buffer w)))
                             (output-windows))
                     '("*goals*"))))))

(ert-deftest coq-eglot-layout-menu ()
  "The menu chooses the layout, like the Buffers menu of Proof General."
  (with-test-file
    (with-layout t 'hybrid
      (goto-marker "split")
      (run #'coq-eglot-goto-point)
      (let ((items (mapcar (lambda (item) (and (vectorp item) (aref item 0)))
                           (cdr (assoc "3 Windows mode layout"
                                       (cdr (assoc "Windows"
                                                   (cdr coq-eglot--menu-spec))))))))
        (should (equal items '("smart" "hybrid" "horizontal" "vertical"))))
      (unwind-protect
          (progn
            (coq-eglot-set-layout-option 'proof-three-window-mode-policy
                                         'vertical)
            (should (eq proof-three-window-mode-policy 'vertical))
            (pcase-let ((`(,script ,goals)
                         (windows-of (current-buffer) "*goals*")))
              (should (= (window-left-column script)
                         (window-left-column goals)))
              (should (< (window-top-line script) (window-top-line goals))))
            (coq-eglot-set-layout-option 'proof-three-window-enable nil)
            (should (equal (mapcar (lambda (w) (buffer-name (window-buffer w)))
                                   (output-windows))
                           '("*goals*"))))
        (customize-set-variable 'proof-three-window-enable t)
        (customize-set-variable 'proof-three-window-mode-policy 'hybrid)))))

(ert-deftest coq-eglot-layout-policy ()
  "The smart policy depends on the width of the frame, like in Proof
General."
  (let ((split-width-threshold 40))
    (should (eq (proof-guess-3win-display-policy 'smart)
                (if (>= (frame-width) 60) 'horizontal 'hybrid))))
  (let ((split-width-threshold 1000))
    (should (eq (proof-guess-3win-display-policy 'smart) 'vertical)))
  (should (eq (proof-guess-3win-display-policy 'hybrid) 'hybrid)))

;;; other window options of Proof General

(defvar coq-eglot-trace)                 ; let-bound
(defvar coq-eglot--rotation)             ; let-bound

(ert-deftest coq-eglot-auto-raise-off ()
  "Without `proof-auto-raise-buffers', the goals and messages are not
displayed, their buffers are updated."
  (with-test-file
    (with-layout t 'vertical
      (let ((proof-auto-raise-buffers nil))
        (goto-marker "split")
        (run #'coq-eglot-goto-point)
        (should-not (output-windows))
        (should (string-match-p "double n = n \\+ n" (buffer-text "*goals*")))))))

(ert-deftest coq-eglot-delete-empty-windows ()
  "With `proof-delete-empty-windows', the window of an empty buffer is
deleted, and comes back with some content."
  (with-test-file
    (with-layout t 'vertical
      (let ((proof-delete-empty-windows t))
        (goto-marker "hello")
        (run #'coq-eglot-goto-point)
        (should (get-buffer-window "*goals*"))
        (should (get-buffer-window "*response*"))
        ;; no messages
        (goto-marker "split")
        (run #'coq-eglot-goto-point)
        (should (get-buffer-window "*goals*"))
        (should-not (get-buffer-window "*response*"))
        ;; outside of proofs, no goals
        (goto-marker "definition")
        (run #'coq-eglot-goto-point)
        (should-not (get-buffer-window "*goals*"))
        (goto-marker "hello")
        (run #'coq-eglot-goto-point)
        (should (get-buffer-window "*goals*"))
        (should (get-buffer-window "*response*"))))))

(ert-deftest coq-eglot-shrink-windows-tofit ()
  "With `proof-shrink-windows-tofit', the windows below the script get
the height they need, the script window the rest."
  (with-test-file
    (with-layout t 'vertical
      (let ((proof-shrink-windows-tofit t)
            (coq-optimise-resp-windows-enable nil)
            (script (selected-window)))
        (goto-marker "split")
        (run #'coq-eglot-goto-point)
        (pcase-let ((`(,goals ,response) (windows-of "*goals*" "*response*")))
          (should (= (window-total-height goals)
                     (max window-min-height (coq-eglot--window-need goals))))
          (should (= (window-total-height response) window-min-height))
          (should (> (window-total-height script)
                     (window-total-height goals))))))
    ;; two windows: the shared window too
    (with-layout nil 'vertical
      (let ((proof-shrink-windows-tofit t)
            (split-width-threshold 1000))
        (goto-marker "hello")
        (run #'coq-eglot-goto-point)
        (let ((shared (car (output-windows))))
          (should (= (window-total-height shared)
                     (max window-min-height
                          (coq-eglot--window-need shared)))))))))

(ert-deftest coq-eglot-shrink-windows-tofit-columns ()
  "`proof-shrink-windows-tofit' does nothing to windows on the right of
the script."
  (with-test-file
    (with-layout t 'hybrid
      (let ((proof-shrink-windows-tofit t)
            (coq-optimise-resp-windows-enable nil)
            (calls 0))
        (cl-letf (((symbol-function 'coq-eglot--resize-column)
                   (lambda (&rest _) (setq calls (1+ calls)))))
          (goto-marker "split")
          (run #'coq-eglot-goto-point))
        (should (= calls 0))))))

(ert-deftest coq-eglot-display-some-buffers ()
  "C-c C-o displays the messages, the trace and the goals in turn, in
the same window when they share it."
  (with-test-file
    (with-layout nil 'vertical
      (let ((coq-eglot-trace t)
            (split-width-threshold 1000))
        (goto-marker "hello")
        (run #'coq-eglot-goto-point)
        (should (eq (key-binding (kbd "C-c C-o"))
                    #'coq-eglot-display-some-buffers))
        (let ((window (car (output-windows)))
              (shown nil))
          (dotimes (i 4)
            (let ((last-command (and (> i 0) 'coq-eglot-display-some-buffers)))
              (coq-eglot-display-some-buffers))
            (push (buffer-name (window-buffer window)) shown))
          (should (equal (nreverse shown)
                         '("*response*" "*coq-trace*" "*goals*" "*response*")))
          (should (= (length (window-list)) 2)))))
    ;; three windows: the trace in the window of the messages, until the
    ;; next ones
    (with-layout t 'vertical
      (let ((coq-eglot-trace t))
        (goto-marker "split")
        (run #'coq-eglot-goto-point)
        (let ((response (car (windows-of "*response*")))
              (last-command 'coq-eglot-display-some-buffers)
              (coq-eglot--rotation 0))
          (coq-eglot-display-some-buffers)
          (should (equal (buffer-name (window-buffer response)) "*coq-trace*"))
          (should (get-buffer-window "*goals*"))
          (goto-marker "hello")
          (run #'coq-eglot-goto-point)
          (should (eq (get-buffer-window "*response*") response))
          (should (= (length (window-list)) 3)))))))

(ert-deftest coq-eglot-multiple-frames ()
  "With `proof-multiple-frames-enable', the goals and the messages are
displayed in frames of their own, not resized; without, these frames
are deleted.  Frames cannot be made in batch mode: their creation is
simulated by a window."
  (with-test-file
    (with-layout t 'vertical
      (let ((proof-multiple-frames-enable t)
            (proof-delete-empty-windows t)
            (popped nil)
            (resized 0)
            (deleted nil))
        (cl-letf (((symbol-function 'display-buffer-pop-up-frame)
                   (lambda (buffer alist)
                     (push (cons (buffer-name buffer)
                                 (alist-get 'pop-up-frame-parameters alist))
                           popped)
                     (let ((window (split-window (frame-root-window) nil 'below)))
                       (set-window-buffer window buffer)
                       window)))
                  ((symbol-function 'coq-eglot-resize-windows-by-priority)
                   (lambda () (setq resized (1+ resized))))
                  ((symbol-function 'coq-eglot--frames)
                   (lambda () '(frame-of-goals)))
                  ((symbol-function 'delete-frame)
                   (lambda (frame &rest _) (push frame deleted))))
          (goto-marker "split")
          (run #'coq-eglot-goto-point)
          (should (equal (sort (mapcar #'car popped) #'string<)
                         '("*goals*" "*response*")))
          (dolist (entry popped)
            (should (eq (alist-get 'coq-eglot (cdr entry)) t))
            (should (window-dedicated-p (get-buffer-window (car entry)))))
          ;; the empty messages keep their frame
          (should (get-buffer-window "*response*"))
          (should (= resized 0))
          (should-not deleted)
          (setq proof-multiple-frames-enable nil)
          (coq-eglot-layout-windows)
          (should (equal deleted '(frame-of-goals))))))))

(ert-deftest coq-eglot-layout-on-visit ()
  "With `proof-layout-windows-on-visit-file', the windows are laid out
when visiting a file."
  (with-test-file
    (with-layout t 'vertical
      (let ((proof-layout-windows-on-visit-file t))
        (coq-eglot--layout-on-visit)
        (should-not (output-windows))
        (accept-process-output nil 0.1)
        (should (get-buffer-window "*goals*"))
        (should (get-buffer-window "*response*"))))))

(defun other-goals-overlay ()
  "The overlay of the goals after the first one in the current buffer."
  (seq-find (lambda (ov) (overlay-get ov 'coq-other-goals))
            (overlays-in (point-min) (point-max))))

(defun window-last-position (window)
  "Position after the last line displayed in WINDOW."
  (save-excursion
    (goto-char (window-start window))
    (vertical-motion (window-body-height window) window)
    (point)))

(ert-deftest coq-eglot-goals-show-last-hyps ()
  "When the goals do not fit, the last hypotheses and the conclusion are
displayed, with arrows in the fringe, like in Proof General."
  (with-test-file
    (goto-marker "many")
    (run #'coq-eglot-goto-point)
    (let ((window (get-buffer-window "*goals*")))
      (should window)
      (with-current-buffer "*goals*"
        (should (equal indicate-buffer-boundaries '((up . left) (down . left))))
        (should (> (window-start window) (point-min)))
        ;; the conclusion is visible
        (should (string-match-p "True\\'" (buffer-text "*goals*")))
        (should (>= (window-last-position window) (1- (point-max))))
        ;; scrolling stops at the end
        (let ((max (proof-goals--max-window-start window)))
          (should (> max (point-min)))
          (proof-goals--scrolled window (1- (point-max)))
          (should (= (window-start window) max)))))
    ;; the same with the conclusion apart
    (unwind-protect
        (progn
          (coq-eglot-toggle-split-goals)
          (let ((window (get-buffer-window "*goals*")))
            (with-current-buffer "*goals*"
              (should (> (window-start window) (point-min)))
              (should (string-match-p "H28 : 30 = 30\\'" (buffer-text "*goals*")))
              (should (>= (window-last-position window) (1- (point-max)))))))
      (coq-eglot-toggle-split-goals))
    ;; everything fits: no scrolling
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (let ((window (get-buffer-window "*goals*")))
      (with-current-buffer "*goals*"
        (should (= (window-start window) (point-min)))
        (proof-goals--scrolled window (1- (point-max)))
        (should (= (window-start window) (point-min)))))))

(defvar coq-prefer-top-of-conclusion)     ; let-bound
(defvar coq-highlight-hyps-sticky)        ; let-bound
(defvar coq-eglot-trace)                 ; let-bound

(defun separator-line ()
  "Start of the line of the separator in the current buffer."
  (save-excursion
    (goto-char (point-min))
    (search-forward "=====")
    (line-beginning-position)))

(ert-deftest coq-eglot-goals-show-goal-first ()
  "When the goal does not fit, with `coq-prefer-top-of-conclusion', its
separator is on the first line, like in Proof General."
  (with-test-file
    (let ((coq-prefer-top-of-conclusion t))
      (goto-marker "long")
      (run #'coq-eglot-goto-point)
      (let ((window (get-buffer-window "*goals*")))
        (with-current-buffer "*goals*"
          (should (= (window-start window) (separator-line))))))
    (let ((coq-prefer-top-of-conclusion nil))
      (coq-eglot--scroll-goals)
      (let ((window (get-buffer-window "*goals*")))
        (with-current-buffer "*goals*"
          (should (> (window-start window) (separator-line))))))))

(ert-deftest coq-eglot-fold-other-goals ()
  "The goals after the first one are folded to their number, with the
number of unfocused goals.  A click unfolds them.  The mode line gives
the numbers of goals.  Like in Proof General."
  (with-test-file
    (unwind-protect
        (progn
          (goto-marker "split")
          (run #'coq-eglot-goto-point)
          (with-current-buffer "*goals*"
            (should (string-match-p "double n = n \\+ n\n\ngoal 2 is:\n True\\'"
                                    (buffer-text "*goals*")))
            (should (equal (substring-no-properties
                            (overlay-get (other-goals-overlay) 'display))
                           "▸ 1 more goal"))
            (should (equal (coq-goals-mode-line) " 2+0"))
            (goto-char (coq-goals-folded-start))
            (should (eq (key-binding (kbd "RET")) #'coq-toggle-other-goals))
            (call-interactively (key-binding (kbd "RET")))
            (should-not coq-fold-other-goals)
            (should (equal (substring-no-properties
                            (overlay-get (other-goals-overlay) 'before-string))
                           "▾ 1 more goal\n")))
          (coq-toggle-other-goals)
          ;; in a bullet, the other goal is unfocused
          (goto-marker "hello")
          (run #'coq-eglot-goto-point)
          (with-current-buffer "*goals*"
            (should (string-match-p "\\*\\*\\* Unfocused goals:\n\ngoal 2 is:\n True\\'"
                                    (buffer-text "*goals*")))
            (should (equal (substring-no-properties
                            (overlay-get (other-goals-overlay) 'display))
                           "▸ 1 unfocused goal"))
            (should (equal (coq-goals-mode-line) " 1+1"))
            (should (equal (get-text-property 1 'help-echo (coq-goals-mode-line))
                           "Goals: 1 focused, 1 unfocused")))
          ;; the bullet proved: no goal focused
          (goto-marker "subproof")
          (search-backward "-")
          (run #'coq-eglot-goto-point)
          (with-current-buffer "*goals*"
            (should (string-match-p "\\`This subproof is complete"
                                    (buffer-text "*goals*")))
            (should (equal (coq-goals-mode-line) " 0+1"))
            (should (= (window-start (get-buffer-window "*goals*"))
                       (point-min)))))
      (setq coq-fold-other-goals t))))

(defun hyp-overlay (name property)
  "Overlay with PROPERTY on the type of hypothesis NAME in the goals."
  (with-current-buffer "*goals*"
    (goto-char (point-min))
    (should (re-search-forward (format "^  %s : " name) nil t))
    (seq-find (lambda (ov) (overlay-get ov property))
              (overlays-at (point)))))

(defun hyp-cross (name)
  "The folding button of hypothesis NAME in the goals."
  (with-current-buffer "*goals*"
    (goto-char (point-min))
    (should (re-search-forward (format "^  %s : " name) nil t))
    (let ((ov (seq-find (lambda (ov) (overlay-get ov 'display))
                        (overlays-at (line-beginning-position)))))
      (and ov (overlay-get ov 'display)))))

(ert-deftest coq-eglot-highlight-and-fold-hyps ()
  "Hypotheses can be highlighted and folded, they stay so in the next
goals, like in Proof General: highlighted if `coq-highlight-hyps-sticky'."
  (with-test-file
    (unwind-protect
        (let ((coq-highlight-hyps-sticky t))
          (goto-marker "hyps")
          (run #'coq-eglot-goto-point)
          (with-current-buffer "*goals*"
            (should (eq (key-binding "h") #'coq-toggle-highlight-hyp-at-point))
            (should (eq (key-binding "f") #'coq-toggle-fold-hyp-at-point))
            (should (equal (hyp-cross "H") "-"))
            (goto-char (point-min))
            (search-forward "H :")
            (coq-toggle-highlight-hyp-at-point)
            (coq-toggle-fold-hyp-at-point))
          (should (hyp-overlay "H" 'face))
          (should (equal (overlay-get (hyp-overlay "H" 'display) 'display)
                         "....."))
          (should (equal (hyp-cross "H") "+"))
          ;; the type is still there, for copy
          (should (string-match-p "H : n = m" (buffer-text "*goals*")))
          (run #'coq-eglot-assert-next-command)
          (should (string-match-p "n = m\\'" (buffer-text "*goals*")))
          (should (hyp-overlay "H" 'face))
          (should (hyp-overlay "H" 'display))
          (should-not (hyp-overlay "n, m" 'face))
          ;; from the script, on the name of the hypothesis
          (goto-marker "hyps")
          (search-backward "H")
          (coq-toggle-highlight-hyp-at-point)
          (should-not (hyp-overlay "H" 'face))
          ;; n and m are on the same line
          (search-backward "m")
          (coq-toggle-highlight-hyp-at-point)
          (should (hyp-overlay "n, m" 'face))
          (should (equal (sort (copy-sequence coq-highlighted-hyps)
                               #'string<)
                         '("m" "n")))
          (coq-unfold-hyps)
          (should-not (hyp-overlay "H" 'display))
          (goto-char (point-min))
          (should-error (coq-toggle-highlight-hyp-at-point) :type 'user-error))
      (coq-unhighlight-selected-hyps)
      (coq-unfold-hyps))))

(ert-deftest coq-eglot-highlight-not-sticky ()
  "Without `coq-highlight-hyps-sticky', the highlighting stops at the
next goals, not when the same goals are displayed again."
  (with-test-file
    (unwind-protect
        (progn
          (goto-marker "hyps")
          (run #'coq-eglot-goto-point)
          (coq-toggle-highlight-hyp "H")
          (should (hyp-overlay "H" 'face))
          (coq-eglot-toggle-split-goals)
          (coq-eglot-toggle-split-goals)
          (should (hyp-overlay "H" 'face))
          (run #'coq-eglot-assert-next-command)
          (should-not (hyp-overlay "H" 'face))
          (should-not coq-highlighted-hyps))
      (coq-unhighlight-selected-hyps))))

(ert-deftest coq-eglot-search-highlights-hyps ()
  "Search highlights the hypotheses it finds, like in Proof General."
  (with-test-file
    (unwind-protect
        (progn
          (goto-marker "hyps")
          (run #'coq-eglot-goto-point)
          (should (string-match-p "^H: n = m" (query-interactively #'coq-Search nil "n")))
          (should (equal coq-highlighted-hyps '("H")))
          (should (hyp-overlay "H" 'face)))
      (coq-unhighlight-selected-hyps))))

(ert-deftest coq-eglot-query-at-mouse ()
  "Control click prints, shift click shows About, control shift click
checks, like in Proof General."
  (with-test-file
    (goto-marker "before error")
    (run #'coq-eglot-goto-point)
    (switch-to-buffer (current-buffer))
    (goto-marker "definition")
    (search-backward "double")
    (let ((click (lambda (type)
                   (list type (list (selected-window) (point) '(0 . 0) 0)))))
      (should (string-match-p "\\`double = fun"
                              (query #'coq-id-under-mouse-query
                                     (funcall click 'C-down-mouse-1))))
      (should (string-match-p "\\`double : nat -> nat"
                              (query #'coq-id-under-mouse-query
                                     (funcall click 'S-down-mouse-1))))
      (should (string-match-p "\\`double\n     : nat -> nat"
                              (query #'coq-id-under-mouse-query
                                     (funcall click 'C-S-down-mouse-1))))
      ;; with meta, with Printing All
      (should (string-match-p "Nat.add n n"
                              (query #'coq-id-under-mouse-query
                                     (funcall click 'C-M-down-mouse-1))))
      ;; also in the response buffer, if `coq-remap-mouse-1'
      (let ((remap coq-remap-mouse-1))
        (unwind-protect
            (progn
              (customize-set-variable 'coq-remap-mouse-1 t)
              (with-current-buffer "*response*"
                (should (eq (key-binding [C-down-mouse-1])
                            #'coq-id-under-mouse-query)))
              (should (eq (key-binding [C-down-mouse-1])
                          #'coq-id-under-mouse-query)))
          (customize-set-variable 'coq-remap-mouse-1 remap))))))

(defun type-dot ()
  "Type \".\" in the current buffer."
  (let ((last-command-event ?.))
    (call-interactively (key-binding "."))))

(ert-deftest coq-eglot-double-hit ()
  "With `proof-double-hit-enable', hitting \".\" twice quickly processes up
to it, like in Proof General.  The terminator command is common to all
backends."
  (with-test-file
    (should (eq (key-binding ".") #'coq-terminator-insert))
    (should (eq coq-terminator-insert-function #'coq-eglot-terminator-insert))
    (goto-marker "hyps next")
    (delete-char -1)
    (let ((proof-double-hit-enable nil))
      (type-dot)
      (type-dot)
      (wait-for-coq)
      (should (looking-back "symmetry\\.\\." (line-beginning-position)))
      (should (= (coq-eglot-position) (point-min)))
      (delete-char -2))
    (let ((proof-double-hit-enable t))
      ;; too slow
      (type-dot)
      (sleep-for (* 2 proof-double-hit-delay))
      (type-dot)
      (wait-for-coq)
      (should (looking-back "symmetry\\.\\." (line-beginning-position)))
      (delete-char -2)
      (type-dot)
      (type-dot)
      (wait-for-coq)
      (should (looking-back "symmetry\\." (line-beginning-position)))
      (should (position-at-marker-p "hyps next"))
      ;; another key bound to the terminator command gives "."
      (run #'coq-eglot-retract-buffer)
      (delete-char -1)
      (let ((last-command-event ?\;))
        (coq-terminator-insert)
        (coq-terminator-insert))
      (wait-for-coq)
      (should (looking-back "symmetry\\." (line-beginning-position)))
      (should (position-at-marker-p "hyps next")))))

(defun locked-face ()
  "Face of the processed part of the current buffer.
The face of inactive buffers is simplified to its name."
  (let ((face (overlay-get coq-eglot--locked-overlay 'face)))
    (if (and (consp face) (memq 'coq-eglot-inactive-locked-face face))
        'coq-eglot-inactive-locked-face
      face)))

(ert-deftest coq-eglot-active-buffer ()
  "Several buffers can be scripted at once, only the active one displays
its goals.  The processed part of the others is grayed."
  (with-test-file
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (should (eq (locked-face) 'proof-locked-face))
    (should (string-match-p "n : nat" (buffer-text "*goals*")))
    (let ((first (current-buffer)))
      (with-file "eglot_other.v"
        (goto-marker "proof")
        (run #'coq-eglot-goto-point)
        (should (eq (locked-face) 'proof-locked-face))
        (should (string-match-p "other = 0" (buffer-text "*goals*")))
        (with-current-buffer first
          (should (eq (locked-face) 'coq-eglot-inactive-locked-face))
          ;; the first buffer displays nothing now
          (coq-eglot--goals-at-position-async)
          (accept-process-output nil 0.3)
          (should (string-match-p "other = 0" (buffer-text "*goals*")))
          ;; a command wakes it up
          (run #'coq-eglot-assert-next-command)
          (should (eq (locked-face) 'proof-locked-face))
          (should (string-match-p "n : nat" (buffer-text "*goals*"))))
        (should (eq (locked-face) 'coq-eglot-inactive-locked-face))
        ;; the position of the other buffer did not move
        (should (position-at-marker-p "proof"))))
    ;; killing another buffer keeps the active one
    (should (eq (coq-eglot--active-buffer) (current-buffer)))))

(ert-deftest coq-eglot-two-outputs ()
  "Two script buffers with outputs of their own display their goals at
the same time, in their own goals buffers, and both stay active."
  (let ((output (coq-eglot--make-output "<2>"))
        (second nil))
    (unwind-protect
        (with-test-file
          (goto-marker "split")
          (run #'coq-eglot-goto-point)
          (let ((first (current-buffer)))
            (setq second (find-file-noselect "eglot_other.v"))
            (with-current-buffer second
              (should coq-eglot-mode)
              (setq coq-eglot--buffer-output output)
              (goto-marker "proof")
              (run #'coq-eglot-goto-point)
              (should (position-at-marker-p "proof"))
              (should (eq (locked-face) 'proof-locked-face))
              (should (eq (coq-eglot--active-buffer) second)))
            (should (string-match-p "other = 0" (buffer-text "*goals*<2>")))
            ;; the first buffer is still active, its goals still displayed
            (should (eq (locked-face) 'proof-locked-face))
            (should (eq (coq-eglot--active-buffer) first))
            (should (string-match-p "n : nat" (buffer-text "*goals*")))
            (should-not (string-match-p "other = 0" (buffer-text "*goals*")))
            ;; each one moves on its own
            (run #'coq-eglot-assert-next-command)
            (should (string-match-p "n : nat" (buffer-text "*goals*")))
            (should (string-match-p "other = 0" (buffer-text "*goals*<2>")))
            ;; the goals buffers know their output
            (with-current-buffer "*goals*<2>"
              (should (eq (coq-eglot--output) output))
              (should (eq (coq-eglot-script-buffer) second)))
            (with-current-buffer "*goals*"
              (should (eq (coq-eglot--output) coq-eglot--default-output))
              (should (eq (coq-eglot-script-buffer) first)))))
      (when (buffer-live-p second)
        (with-current-buffer second (set-buffer-modified-p nil))
        (kill-buffer second))
      (dolist (name '("*goals*<2>" "*conclusion*<2>" "*response*<2>"))
        (when (get-buffer name) (kill-buffer name))))))

(defmacro with-twin (&rest body)
  "Run BODY in eglot_test.v paired with eglot_other.v, its twin.
In a frame showing only them, three windows mode off: the twins force
it.  Not synchronized: the two scripts are unrelated.  Unpair and kill
eglot_other.v afterwards."
  (declare (indent 0) (debug t))
  `(let ((proof-three-window-enable nil)
         (coq-eglot-twin-synchronize nil)
         (twin nil))
     (with-test-file
       (unwind-protect
           (progn
             (switch-to-buffer (current-buffer))
             (delete-other-windows)
             (setq twin (find-file-noselect "eglot_other.v"))
             (with-current-buffer twin
               (should coq-eglot-mode)
               (coq-eglot-retract-buffer))
             (coq-eglot-twin-pair twin)
             ,@body)
         (when (buffer-live-p twin)
           (with-current-buffer twin (set-buffer-modified-p nil))
           (kill-buffer twin))
         (delete-other-windows)))))

(ert-deftest coq-eglot-twin-layout ()
  "Paired, the twins are side by side, each above its goals and messages,
both active: each one displays in its own goals and response buffers."
  (with-twin
    (let ((this (current-buffer)))
      (should (eq coq-eglot--twin twin))
      (should (eq (buffer-local-value 'coq-eglot--twin twin) this))
      (should (equal (coq-eglot--output-suffix
                      (buffer-local-value 'coq-eglot--buffer-output twin))
                     "<eglot_other.v>"))
      (goto-marker "split")
      (run #'coq-eglot-goto-point)
      (with-current-buffer twin
        (goto-marker "proof")
        (run #'coq-eglot-goto-point))
      (should (string-match-p "n : nat" (buffer-text "*goals*")))
      (should (string-match-p "other = 0"
                              (buffer-text "*goals*<eglot_other.v>")))
      (should (eq (locked-face) 'proof-locked-face))
      (with-current-buffer twin
        (should (eq (locked-face) 'proof-locked-face)))
      (pcase-let ((`(,script ,goals ,response ,twin-script ,twin-goals
                             ,twin-response)
                   (windows-of this "*goals*" "*response*" twin
                               "*goals*<eglot_other.v>"
                               "*response*<eglot_other.v>")))
        ;; two columns
        (should (= (window-left-column script) (window-left-column goals)
                   (window-left-column response) 0))
        (should (> (window-left-column twin-script) 0))
        (should (= (window-left-column twin-script)
                   (window-left-column twin-goals)
                   (window-left-column twin-response)))
        ;; each script above its goals above its messages
        (should (< (window-top-line script) (window-top-line goals)
                   (window-top-line response)))
        (should (< (window-top-line twin-script) (window-top-line twin-goals)
                   (window-top-line twin-response)))
        (should (= (length (window-list nil 'no-minibuffer)) 6)))
      ;; a step in one twin does not change what the other displays
      (with-current-buffer twin
        (run #'coq-eglot-assert-next-command))
      (should (string-match-p "n : nat" (buffer-text "*goals*")))
      ;; the layout again, from the goals of the twin
      (delete-other-windows)
      (with-current-buffer "*goals*<eglot_other.v>"
        (coq-eglot-twin-layout))
      (should (= (length (window-list nil 'no-minibuffer)) 6))
      (should (eq (window-buffer (window-at 0 0)) twin)))))

(ert-deftest coq-eglot-twin-unpair ()
  "Unpaired, the twin goes back to the shared output: its goals and
response buffers are killed.  Killing a twin unpairs."
  (with-twin
    (let ((this (current-buffer)))
      (with-current-buffer twin
        (goto-marker "proof")
        (run #'coq-eglot-goto-point))
      (should (get-buffer "*goals*<eglot_other.v>"))
      (coq-eglot-twin-unpair)
      (should-not coq-eglot--twin)
      (should-not (buffer-local-value 'coq-eglot--twin twin))
      (should-not (buffer-local-value 'coq-eglot--buffer-output twin))
      (should-not (get-buffer "*goals*<eglot_other.v>"))
      (should-not (get-buffer "*response*<eglot_other.v>"))
      ;; they share an output again: one of them is active
      (should (eq (coq-eglot--active-buffer) this))
      (with-current-buffer twin
        (should (eq (locked-face) 'coq-eglot-inactive-locked-face)))
      (should-error (coq-eglot-twin-unpair) :type 'user-error)
      ;; paired again, then the twin is killed
      (coq-eglot-twin-pair twin)
      (should (eq coq-eglot--twin twin))
      (with-current-buffer twin (set-buffer-modified-p nil))
      (kill-buffer twin)
      (should-not coq-eglot--twin)
      (should-not (get-buffer "*goals*<eglot_other.v>")))))

(ert-deftest coq-eglot-twin-server-label ()
  "The mode line shows the opam switch of the server of a twin."
  (should (equal (coq-eglot-twin--server-label
                  "/home/u/.opam/rocq-9.2/bin/coq-lsp")
                 "rocq-9.2"))
  (should (equal (coq-eglot-twin--server-label "/p/proj/_opam/bin/rocq-lsp")
                 "proj"))
  (should (equal (coq-eglot-twin--server-label "/usr/bin/coq-lsp") "coq-lsp"))
  (should (equal (coq-eglot-twin--server-label "coq-lsp") "coq-lsp")))

(defun other-opam-switch ()
  "An opam switch with coq-lsp, rocq-9.0 or rocq-9.2, not the current one.
Nil if there is none."
  (let ((current (file-name-nondirectory
                  (directory-file-name
                   (file-name-directory
                    (directory-file-name
                     (file-name-directory
                      (executable-find
                       (car (coq-eglot-lsp-server-command))))))))))
    (seq-find (lambda (switch)
                (and (not (equal switch current))
                     (ignore-errors (coq-eglot-twin--switch-server switch))))
              '("rocq-9.2" "rocq-9.0"))))

(defconst compile-directory (expand-file-name "compile/")
  "Directory of the tests of the compilation, with a _CoqProject.")

(ert-deftest coq-eglot-twin-opam-switch ()
  "Paired with an opam switch, the twin has the server of this switch,
the other buffer keeps the one of the current switch.  The twin must be
in another project: compile/ has a _CoqProject."
  (skip-unless (executable-find "opam"))
  (let ((twin nil))
    (with-test-file
      (let ((switch (other-opam-switch))
            (program (car (coq-eglot-lsp-server-command))))
        (skip-unless switch)
        (unwind-protect
            (progn
              (setq twin (find-file-noselect
                          (expand-file-name "eglot_compile_c.v"
                                            compile-directory)))
              ;; like C-u M-x coq-eglot-twin-pair
              (let ((current-prefix-arg '(4)))
                (coq-eglot-twin-pair twin switch))
              (with-current-buffer twin
                ;; its server connects without waiting
                (should (wait-until #'coq-eglot-lsp-current-server 10))
                (should (equal coq-eglot-server-program
                               (coq-eglot-twin--switch-server switch)))
                (should (string-match-p
                         (format "/%s/" (regexp-quote switch))
                         (car (process-command
                               (jsonrpc--process (eglot-current-server))))))
                (should (string-search (format "[%s]" switch)
                                       (coq-eglot--lighter)))
                (run #'coq-eglot-process-buffer)
                (should (string-match-p
                         (format "/%s/lib/" (regexp-quote switch))
                         (car (lsp-query
                               (point-max)
                               "Locate Library Corelib.Init.Prelude.")))))
              ;; the other buffer keeps its server
              (should (equal (executable-find
                              (car (process-command
                                    (jsonrpc--process (eglot-current-server)))))
                             (executable-find program)))
              (should (string-search
                       (format "[%s]" (coq-eglot-twin--server-label
                                       (executable-find program)))
                       (coq-eglot--lighter)))
              (should-not (eq (eglot-current-server)
                              (with-current-buffer twin (eglot-current-server))))
              ;; unpaired, the twin keeps its server, the label goes
              (coq-eglot-twin-unpair)
              (with-current-buffer twin
                (should (equal coq-eglot-server-program
                               (coq-eglot-twin--switch-server switch)))
                (should-not (string-search "[" (coq-eglot--lighter)))))
          (when (buffer-live-p twin)
            (with-current-buffer twin
              ;; the next tests of compile/ use the current switch
              (coq-eglot-lsp-shutdown)
              (set-buffer-modified-p nil))
            (kill-buffer twin))
          (delete-other-windows))))))

(ert-deftest coq-eglot-ensure-server-prefix ()
  "With a prefix argument, the server started is a Coq server: Eglot
ignores the class of the contact then."
  (with-file (expand-file-name "eglot_compile_c.v" compile-directory)
    (unwind-protect
        (progn
          (coq-eglot-lsp-shutdown)
          (let ((current-prefix-arg '(4)))
            (should (cl-typep (coq-eglot-lsp-ensure-server)
                              'coq-eglot-lsp-server))))
      (coq-eglot-lsp-shutdown))))

(ert-deftest coq-eglot-ensure-server-connecting ()
  "With a server still connecting, the server is that one, once
connected: no other one is started."
  (with-file (expand-file-name "eglot_compile_c.v" compile-directory)
    (unwind-protect
        (progn
          (coq-eglot-lsp-shutdown)
          (let ((eglot-sync-connect nil))
            (apply #'eglot (eglot--guess-contact)))
          (let ((connecting (coq-eglot-lsp-connecting-servers)))
            (should (= (length connecting) 1))
            (should (eq (coq-eglot-lsp-ensure-server) (car connecting))))
          (should-not (coq-eglot-lsp-connecting-servers))
          (should (= (length (gethash (eglot--current-project)
                                      eglot--servers-by-project))
                     1)))
      (coq-eglot-lsp-kill-connecting-servers)
      (coq-eglot-lsp-shutdown))))

(ert-deftest coq-eglot-request-not-sent ()
  "A check whose request cannot be sent, like without server, is not
running: the buffer is not busy afterwards."
  (with-test-file
    (cl-letf (((symbol-function 'coq-eglot-lsp-ensure-server) #'ignore))
      (goto-marker "split")
      (should-error (coq-eglot-goto-point) :type 'user-error)
      (should-not (coq-eglot-checking-p)))
    (run #'coq-eglot-goto-point)
    (should (position-at-marker-p "split"))))

(ert-deftest coq-eglot-connecting-servers ()
  "A server still connecting is not the current server, but
`coq-eglot-lsp-connecting-servers' finds it."
  (with-file (expand-file-name "eglot_compile_c.v" compile-directory)
    (unwind-protect
        (progn
          (coq-eglot-lsp-shutdown)
          (should-not (coq-eglot-lsp-connecting-servers))
          (let ((eglot-sync-connect nil))
            (apply #'eglot (eglot--guess-contact)))
          ;; no process output read since: not connected yet
          (should-not (eglot-current-server))
          (let ((servers (coq-eglot-lsp-connecting-servers)))
            (should (= (length servers) 1)))
          (coq-eglot-lsp-kill-connecting-servers)
          (should-not (coq-eglot-lsp-connecting-servers)))
      (coq-eglot-lsp-kill-connecting-servers)
      (coq-eglot-lsp-shutdown))))

(defmacro with-twin-texts (this-text twin-text &rest body)
  "Run BODY in a Coq buffer of THIS-TEXT, paired with one of TWIN-TEXT.
Bound to `twin' in BODY.  Not script buffers of the Eglot backend: no
server, only their sentences and their alignment."
  (declare (indent 2) (debug t))
  `(let ((twin (generate-new-buffer "twin"))
         (this (generate-new-buffer "this")))
     (unwind-protect
         (progn
           (with-current-buffer twin
             (insert ,twin-text)
             (coq-mode))
           (with-current-buffer this
             (insert ,this-text)
             (coq-mode))
           (coq-eglot-twin--link this twin)
           (with-current-buffer this
             ,@body))
       (kill-buffer this)
       (kill-buffer twin))))

(defun sentence-texts (&optional buffer)
  "Normalized texts of the sentences of BUFFER."
  (cl-map 'list #'coq-eglot-twin--sentence-text
          (coq-eglot-twin--sentences buffer)))

(defun search-position (string &optional buffer)
  "Position after the first STRING in BUFFER."
  (with-current-buffer (or buffer (current-buffer))
    (save-excursion
      (goto-char (point-min))
      (search-forward string)
      (point))))

(ert-deftest coq-eglot-twin-sentences ()
  "The sentences are delimited locally, their texts without comments
and with blanks compacted."
  (with-twin-texts "(* header *)
Lemma l :   (* a. comment *)  True.
Proof.
  - { exact I. }
Qed.
Definition s := \"a (* not a comment *) . string\"." ""
    (should (equal (sentence-texts)
                   '("Lemma l : True." "Proof." "-" "{" "exact I." "}" "Qed."
                     "Definition s := \"a (* not a comment *) . string\".")))
    ;; computed again after a change only
    (let ((sentences (coq-eglot-twin--sentences)))
      (should (eq (coq-eglot-twin--sentences) sentences))
      (goto-char (point-max))
      (insert "\nCheck s.")
      (should (equal (car (last (sentence-texts))) "Check s.")))))

(ert-deftest coq-eglot-twin-common-subsequence ()
  "The longest common subsequence of two vectors, as pairs of indices."
  (should (equal (pg-lcs-common-subsequence [] []) nil))
  (should (equal (pg-lcs-common-subsequence [a b c] [a b c])
                 '((0 . 0) (1 . 1) (2 . 2))))
  (should (equal (pg-lcs-common-subsequence [a b c d] [a x c d y])
                 '((0 . 0) (2 . 2) (3 . 3))))
  (should (equal (pg-lcs-common-subsequence [a b c] [x a y c])
                 '((0 . 1) (2 . 3))))
  ;; too many differences in the middle: only the beginning and end
  (should (equal (pg-lcs-common-subsequence
                  [s a b c e] [s x y z a e] 2)
                 '((0 . 0) (4 . 5)))))

(ert-deftest coq-eglot-twin-alignment ()
  "Sentences differing by comments and blanks only are paired, the
others diverge.  Positions in paired sentences have the same offset in
the twin, the others the end of the last paired sentence before."
  (with-twin-texts "Lemma l : True.
Proof.
  idtac. exact I.
Qed.
Check l." "Lemma l :  (* same *)
  True.
Proof.
  exact I.
  idtac \"new\".
Qed.
Check l."
    ;; idtac., then idtac "new".
    (should (equal (coq-eglot-twin--zones) '(((2 . 3) . nil) (nil . (3 . 4)))))
    ;; the other way
    (should (equal (coq-eglot-twin--zones twin)
                   '((nil . (2 . 3)) ((3 . 4) . nil))))
    ;; in a paired sentence
    (should (= (coq-eglot-twin-position (search-position "Pro"))
               (search-position "Pro" twin)))
    (should (= (coq-eglot-twin-position (search-position "exact I."))
               (search-position "exact I." twin)))
    ;; at the end of a sentence paired with a longer one
    (should (= (coq-eglot-twin-position (search-position "Lemma l : True."))
               (search-position "True." twin)))
    ;; in a diverging sentence: the end of the last paired one
    (should (= (coq-eglot-twin-position (search-position "idta"))
               (search-position "Proof." twin)))
    (should (= (coq-eglot-twin-position (search-position "idta" twin) twin)
               (search-position "exact I.")))
    ;; before the first sentence
    (should (= (coq-eglot-twin-position (point-min))
               (with-current-buffer twin (point-min))))
    ;; aligned again after a change of the twin
    (with-current-buffer twin
      (goto-char (search-position "idtac \"new\"."))
      (delete-region (line-beginning-position) (point)))
    (should (equal (coq-eglot-twin--zones) '(((2 . 3)))))))

(ert-deftest coq-eglot-twin-zone-end ()
  "At the end of a diverging zone, the end of the twin zone: both have
checked their version.  Inside, the end of the last paired sentence."
  (with-twin-texts "Check 1. Check 2. Check 3." "Check 1. Check 20. Check 3."
    (should (= (coq-eglot-twin-position (search-position "Check 2."))
               (search-position "Check 20." twin)))
    (should (= (coq-eglot-twin-position (search-position "Check 20." twin) twin)
               (search-position "Check 2.")))
    ;; after it, before the next sentence
    (should (= (coq-eglot-twin-position (1+ (search-position "Check 2.")))
               (search-position "Check 20." twin)))
    ;; inside
    (should (= (coq-eglot-twin-position (search-position "Check 2"))
               (search-position "Check 1." twin))))
  ;; at the beginning of the buffers
  (with-twin-texts "Check 0. Check 1." "Check 5. Check 6. Check 1."
    (should (= (coq-eglot-twin-position (search-position "Check 0."))
               (search-position "Check 6." twin)))
    (should (= (coq-eglot-twin-position (search-position "Check 5." twin) twin)
               (point-min)))
    (should (= (coq-eglot-twin-position (search-position "Check 6." twin) twin)
               (search-position "Check 0."))))
  ;; the twin zone is empty: the end of the last paired sentence
  (with-twin-texts "Check 1. Check 2. Check 3." "Check 1. Check 3."
    (should (= (coq-eglot-twin-position (search-position "Check 2."))
               (search-position "Check 1." twin))))
  ;; at the end of the buffers
  (with-twin-texts "Check 1. Check 2." "Check 1. Check 20."
    (should (= (coq-eglot-twin-position (search-position "Check 2."))
               (search-position "Check 20." twin)))))

(ert-deftest coq-eglot-twin-highlight ()
  "The diverging sentences of both twins are highlighted, contiguous
ones together, and updated when idle after a change."
  (with-twin-texts "Check 1. Check 2. Check 3. Check 4."
      "Check 1. Check 20. Check 30. Check 4. Check 5."
    (coq-eglot-twin--highlight)
    (cl-flet ((highlighted (buffer)
                (with-current-buffer buffer
                  (mapcar (lambda (overlay)
                            (buffer-substring (overlay-start overlay)
                                              (overlay-end overlay)))
                          (sort (seq-filter
                                 (lambda (overlay)
                                   (overlay-get overlay 'coq-eglot-twin))
                                 (overlays-in (point-min) (point-max)))
                                (lambda (o1 o2) (< (overlay-start o1)
                                                   (overlay-start o2))))))))
      (should (equal (highlighted (current-buffer)) '("Check 2. Check 3.")))
      (should (equal (highlighted twin) '("Check 20. Check 30." "Check 5.")))
      ;; like a diff: removed in the reference, added in the other
      (cl-flet ((faces (buffer)
                  (with-current-buffer buffer
                    (mapcar (lambda (overlay) (overlay-get overlay 'face))
                            (seq-filter (lambda (overlay)
                                          (overlay-get overlay 'coq-eglot-twin))
                                        coq-eglot-twin--overlays))))
                (refined (buffer)
                  (with-current-buffer buffer
                    (mapcar (lambda (overlay)
                              (cons (buffer-substring (overlay-start overlay)
                                                      (overlay-end overlay))
                                    (overlay-get overlay 'face)))
                            (sort (seq-filter
                                   (lambda (overlay)
                                     (overlay-get overlay 'coq-eglot-twin-refine))
                                   (copy-sequence coq-eglot-twin--overlays))
                                  (lambda (o1 o2) (< (overlay-start o1)
                                                     (overlay-start o2))))))))
        (should (equal (faces twin)
                       '(coq-eglot-twin-removed coq-eglot-twin-removed)))
        (should (equal (faces (current-buffer)) '(coq-eglot-twin-added)))
        ;; the words that differ, in the zones with sentences on both sides
        (should (equal (refined (current-buffer))
                       '(("2" . coq-eglot-twin-refine-added)
                         ("3" . coq-eglot-twin-refine-added))))
        (should (equal (refined twin)
                       '(("20" . coq-eglot-twin-refine-removed)
                         ("30" . coq-eglot-twin-refine-removed)))))
      ;; not to the end of the line: the processed part shows there
      (should-not (face-attribute 'coq-eglot-twin-removed :extend nil t))
      (should-not (face-attribute 'coq-eglot-twin-added :extend nil t))
      ;; the faces of the diffs of Coq
      (should (eq (face-attribute 'coq-eglot-twin-added :inherit)
                  'coq-diffs-added-bg-face))
      (should (eq (face-attribute 'coq-eglot-twin-refine-removed :inherit)
                  'coq-diffs-removed-face))
      (with-current-buffer twin
        (setq coq-eglot--buffer-output (coq-eglot--make-output "<twin>"))
        (add-hook 'after-change-functions #'coq-eglot-twin--after-change nil t)
        (goto-char (point-max))
        (delete-region (search-position "Check 4.") (point-max)))
      (should (coq-eglot-twin--twins-highlight-timer coq-eglot-twin--twins))
      (cancel-timer (coq-eglot-twin--twins-highlight-timer coq-eglot-twin--twins))
      (coq-eglot-twin--idle-update coq-eglot-twin--twins)
      (should-not (coq-eglot-twin--twins-highlight-timer coq-eglot-twin--twins))
      (should (equal (highlighted twin) '("Check 20. Check 30.")))
      (coq-eglot-twin--stop-alignment twin)
      (should-not (highlighted twin)))))

(ert-deftest coq-eglot-twin-refine-comments ()
  "The words of the comments and the blanks are not compared."
  (with-twin-texts "Check 1. Check (* a *)  2. Check 4." "Check 1. Check 3. Check 4."
    (coq-eglot-twin--highlight)
    (should (equal (mapcar (lambda (overlay)
                             (buffer-substring (overlay-start overlay)
                                               (overlay-end overlay)))
                           (seq-filter (lambda (overlay)
                                         (overlay-get overlay 'coq-eglot-twin-refine))
                                       coq-eglot-twin--overlays))
                   '("2")))))

(ert-deftest coq-eglot-twin-blend ()
  "Over the processed part, the diverging zones have a background
blending theirs with the one of the processed part."
  (should (equal (coq-eglot-twin--background '((:foreground "red")
                                               (:background "#000000")))
                 "#000000"))
  (should-not (coq-eglot-twin--blend '(:background "#000000") 'default))
  (with-twin-texts "Check 1. Check 2. Check 3. Check 4." "Check 1. Check 4."
    (cl-letf (((symbol-function 'coq-eglot-twin--blend)
               (lambda (face1 face2)
                 (and (eq face1 'coq-eglot-twin-added)
                      (eq face2 'proof-locked-face)
                      "#808080"))))
      (setq coq-eglot--locked-overlay
            (make-overlay (point-min) (search-position "Check 2")))
      (overlay-put coq-eglot--locked-overlay 'face 'proof-locked-face)
      (coq-eglot-twin--highlight)
      (cl-flet ((blends ()
                  (mapcar (lambda (overlay)
                            (list (buffer-substring (overlay-start overlay)
                                                    (overlay-end overlay))
                                  (overlay-get overlay 'face)))
                          (overlay-get (car coq-eglot-twin--overlays)
                                       'coq-eglot-twin-blend))))
        (should (equal (blends) '(("Check 2" (:background "#808080")))))
        ;; when the proof position moves
        (move-overlay coq-eglot--locked-overlay (point-min) (point-max))
        (coq-eglot-twin--update-blend)
        (should (equal (blends) '(("Check 2. Check 3." (:background "#808080")))))
        (move-overlay coq-eglot--locked-overlay (point-min) (point-min))
        (coq-eglot-twin--update-blend)
        (should-not (blends))
        (coq-eglot-twin--unhighlight)
        (should-not (cl-some (lambda (overlay) (overlay-get overlay 'face))
                             (overlays-in (search-position "Check 2")
                                          (search-position "Check 3."))))))))

(ert-deftest coq-eglot-twin-pair-alignment ()
  "Paired, the twins are aligned and highlighted; unpaired, no more."
  (with-twin
    (should (cl-some (lambda (overlay) (overlay-get overlay 'coq-eglot-twin))
                     (overlays-in (point-min) (point-max))))
    (should (memq #'coq-eglot-twin--after-change after-change-functions))
    ;; the twin paired is the reference: removed there, added here
    (should (coq-eglot-twin--reference-p twin))
    (should-not (coq-eglot-twin--reference-p))
    (cl-flet ((faces (buffer)
                (delete-dups (mapcar (lambda (overlay) (overlay-get overlay 'face))
                                     (seq-filter
                                      (lambda (overlay)
                                        (overlay-get overlay 'coq-eglot-twin))
                                      (buffer-local-value
                                       'coq-eglot-twin--overlays buffer))))))
      (should (equal (faces (current-buffer)) '(coq-eglot-twin-added)))
      (should (equal (faces twin) '(coq-eglot-twin-removed)))
      (coq-eglot-twin-swap-reference)
      (should (coq-eglot-twin--reference-p))
      (should (equal (faces (current-buffer)) '(coq-eglot-twin-removed)))
      (should (equal (faces twin) '(coq-eglot-twin-added))))
    (coq-eglot-twin-unpair)
    (should-not (coq-eglot-twin--reference-p))
    (should-not coq-eglot-twin--twins)
    (should-not (cl-some (lambda (overlay) (overlay-get overlay 'coq-eglot-twin))
                         (overlays-in (point-min) (point-max))))
    (should-not (memq #'coq-eglot-twin--after-change after-change-functions))
    (with-current-buffer twin
      (should-not coq-eglot-twin--overlays))))

(defconst sync-this-text "Lemma l1 : True.
Proof.
  exact I.
Qed. (* marker l1 *)
Lemma l2 : 1 = 1.
Proof. (* marker l2 proof *)
  reflexivity.
Qed. (* marker l2 *)
Lemma l3 : True.
Proof. exact I. Qed. (* marker l3 *)
"
  "Script of the leader in the tests of the synchronization.")

(defconst sync-twin-text "Lemma l1 : True.
Proof.
  exact I.
Qed.
Lemma l2 : 1 = 1.
Proof.
  idtac.
  reflexivity.
Qed.
Lemma l3 : True.
Proof.
  exact I.
Qed.
"
  "Script of the follower: the proof of l2 diverges.")

(defmacro with-sync-twins (twin-text &rest body)
  "Run BODY in a script of `sync-this-text' paired with one of TWIN-TEXT.
In two directories, so two servers.  The twin is bound to `twin'."
  (declare (indent 1) (debug t))
  `(progn
     (skip-unless-server)
     (let* ((proof-three-window-enable nil)
            (dirs (list (make-temp-file "coq-eglot-this-" t)
                        (make-temp-file "coq-eglot-twin-" t)))
            (files (cl-mapcar (lambda (dir text)
                                (let ((file (expand-file-name "s.v" dir)))
                                  (with-temp-file file (insert text))
                                  file))
                              dirs (list sync-this-text ,twin-text)))
            (this (find-file-noselect (car files)))
            (twin (find-file-noselect (cadr files))))
       (unwind-protect
           (with-current-buffer this
             (switch-to-buffer this)
             (delete-other-windows)
             (coq-eglot-twin-pair twin)
             ,@body)
         (dolist (buffer (list this twin))
           (when (buffer-live-p buffer)
             (with-current-buffer buffer
               (coq-eglot-lsp-shutdown)
               (set-buffer-modified-p nil))
             (kill-buffer buffer)))
         (dolist (dir dirs) (delete-directory dir t))
         (delete-other-windows)))))

(defun wait-for-twins ()
  "Wait until both twins finished their checks and their moves."
  (with-timeout (30 (error "Twins still busy: %S"
                            (mapcar (lambda (buffer)
                                      (with-current-buffer buffer
                                        (list (buffer-name)
                                              :running (coq-eglot-checking-p)
                                              :timer (and coq-eglot-twin--follow-timer t)
                                              :position (coq-eglot-position)
                                              :out-of-sync coq-eglot-twin--out-of-sync
                                              :leader (coq-eglot-twin--leader-p))))
                                    (list (current-buffer) coq-eglot--twin))))
    (while (cl-some (lambda (buffer)
                      (with-current-buffer buffer
                        (or (coq-eglot-checking-p) coq-eglot-twin--follow-timer
                            coq-eglot-twin--following
                            coq-eglot-twin--show-timer
                            (and coq-eglot-twin--twins
                                 (coq-eglot-twin--twins-compare-timer
                                  coq-eglot-twin--twins)))))
                    (list (current-buffer) coq-eglot--twin))
      (accept-process-output nil 0.02))))

(defun twin-window-point ()
  "Point of the window of the twin."
  (window-point (get-buffer-window coq-eglot--twin)))

(defun twin-position-at (marker)
  "Position of the twin after the sentence of MARKER in this buffer.
The end of the twin sentence of the one before the comment MARKER."
  (coq-eglot-twin-position
   (save-excursion (goto-marker marker) (coq-eglot--skip-backward (point)))))

(ert-deftest coq-eglot-twin-synchronize ()
  "The proof position of the twin follows the one of the leader,
forward and back, to the end of the last paired sentence in a
diverging zone.  The leader is the last one with a command."
  (with-sync-twins sync-twin-text
    (should coq-eglot-twin-synchronize)
    ;; forward, past the diverging proof
    (goto-marker "l2")
    (run #'coq-eglot-goto-point)
    (wait-for-twins)
    (should (position-at-marker-p "l2"))
    (should (= (with-current-buffer twin (coq-eglot-position))
               (with-current-buffer twin (search-position "1 = 1.\nProof.\n  idtac.\n  reflexivity.\nQed."))))
    (should (= (with-current-buffer twin (coq-eglot-position))
               (twin-position-at "l2")))
    ;; the window of the follower shows its new position
    (should (= (twin-window-point) (twin-position-at "l2")))
    ;; back, into the diverging proof: after its Proof
    (goto-marker "l2 proof")
    (run #'coq-eglot-goto-point)
    (wait-for-twins)
    (should (= (with-current-buffer twin (coq-eglot-position))
               (search-position "1 = 1.\nProof." twin)))
    (should (= (twin-window-point) (search-position "1 = 1.\nProof." twin)))
    ;; the twin leads, the other one follows
    (with-current-buffer twin
      (goto-char (point-max))
      (run #'coq-eglot-goto-point))
    (wait-for-twins)
    (should (= (with-current-buffer twin (coq-eglot-position))
               (with-current-buffer twin
                 (coq-eglot--skip-backward (point-max)))))
    (should (position-at-marker-p "l3"))
    ;; an edition of the leader moves the follower back
    (as-user twin
      (goto-char (search-position "  idtac." twin))
      (insert " idtac.")
      (run-hooks 'post-command-hook))
    (wait-for-twins)
    (should (position-at-marker-p "l2 proof"))
    ;; an edition by a program of the follower: still the follower
    (with-current-buffer (current-buffer)
      (let ((follower (current-buffer)))
        (should (coq-eglot-twin--leader-p twin))
        (goto-char (search-position "l2 proof"))
        (forward-line -1)
        (insert "(* by a program *) ")
        (should (coq-eglot-twin--leader-p twin))
        (should-not (coq-eglot-twin--leader-p follower))
        ;; its edition is handled without a command
        (should coq-eglot--after-edit-timer)
        (wait-for-twins)
        (accept-process-output nil 0.1)
        (should-not coq-eglot--after-edit-timer)
        (should-not coq-eglot--edited)))))

(defun twin-differences (buffer)
  "The texts highlighted as differences in BUFFER, with their faces."
  (with-current-buffer buffer
    (mapcar (lambda (overlay)
              (cons (buffer-substring-no-properties (overlay-start overlay)
                                                    (overlay-end overlay))
                    (overlay-get overlay 'face)))
            (sort (copy-sequence coq-eglot-twin--output-overlays)
                  (lambda (o1 o2)
                    (or (< (overlay-start o1) (overlay-start o2))
                        (and (= (overlay-start o1) (overlay-start o2))
                             (< (overlay-priority-value o1)
                                (overlay-priority-value o2)))))))))

(defun overlay-priority-value (overlay)
  "The priority of OVERLAY, a number."
  (or (overlay-get overlay 'priority) 0))

(ert-deftest coq-eglot-twin-compare-buffers ()
  "The lines without a match in the other buffer are highlighted, and
in the changed ones the words that differ."
  (let ((a (generate-new-buffer "a"))
        (b (generate-new-buffer "b")))
    (unwind-protect
        (progn
          (with-current-buffer a
            (insert "1 goal\n\n  n : nat\n  H : n = 0\n  ============================\n  n + 0 = n\n"))
          (with-current-buffer b
            (insert "1 goal\n\n  n : nat\n  H : n = 1\n  H2 : True\n  ============================\n  n + 0 = n\n"))
          (coq-eglot-twin--compare-buffers a b 'line-a 'word-a 'line-b 'word-b)
          (should (equal (twin-differences a)
                         '(("  H : n = 0" . line-a)
                           ("0" . word-a))))
          (should (equal (twin-differences b)
                         '(("  H : n = 1" . line-b)
                           ("1" . word-b)
                           ;; line by line
                           ("  H2 : True" . line-b)
                           ("H2 : True" . word-b))))
          (coq-eglot-twin--uncompare a)
          (should-not (twin-differences a)))
      (kill-buffer a)
      (kill-buffer b))))

(ert-deftest coq-eglot-twin-compare-goals ()
  "At corresponding positions, the differences of the goals of the
twins are highlighted; not while they are at other positions."
  (with-sync-twins (string-replace "1 = 1" "2 = 2" sync-twin-text)
    (goto-marker "l2 proof")
    (run #'coq-eglot-goto-point)
    (wait-for-twins)
    (let ((goals (get-buffer (coq-eglot--goals-name)))
          (twin-goals (with-current-buffer twin
                        (get-buffer (coq-eglot--goals-name)))))
      ;; the goals come after the check
      (should (wait-until (lambda ()
                            (and (with-current-buffer goals
                                   (string-search "1 = 1" (buffer-string)))
                                 (with-current-buffer twin-goals
                                   (string-search "2 = 2" (buffer-string)))))
                          10))
      (wait-for-twins)
      (should (member '("1" . coq-eglot-twin-refine-added)
                      (twin-differences goals)))
      ;; the twin is the reference
      (should (member '("2" . coq-eglot-twin-refine-removed)
                      (twin-differences twin-goals)))
      ;; the same hypotheses and number of goals: not highlighted
      (should-not (assoc "1 goal" (twin-differences goals)))
      ;; not compared when the positions do not correspond
      (let ((coq-eglot-twin-synchronize nil))
        (run #'coq-eglot-retract-buffer)
        (wait-for-twins)
        (should-not (twin-differences goals))
        (should-not (twin-differences twin-goals))))))

(ert-deftest coq-eglot-twin-synchronize-error ()
  "An error of the follower stops it, not the leader; off, the
synchronization does not move the twin."
  (with-sync-twins (string-replace "idtac." "exact 0." sync-twin-text)
    (goto-char (point-max))
    (run #'coq-eglot-process-buffer)
    (wait-for-twins)
    (should (position-at-marker-p "l3"))
    (with-current-buffer twin
      ;; stopped before the error
      (should (= (coq-eglot-position) (search-position "1 = 1.\nProof.")))
      ;; the sentence that failed
      (should (cl-some (lambda (overlay)
                         (equal (buffer-substring (overlay-start overlay)
                                                  (overlay-end overlay))
                                "exact 0."))
                       coq-eglot--error-overlays))
      ;; its window shows the error
      (should (<= (- (search-position "exact 0.") (length "exact 0."))
                  (window-point (get-buffer-window twin))
                  (search-position "exact 0."))))
    (let ((coq-eglot-twin-synchronize nil)
          (before (with-current-buffer twin (coq-eglot-position))))
      (run #'coq-eglot-retract-buffer)
      (wait-for-twins)
      (should (= (coq-eglot-position) (point-min)))
      (should (= (with-current-buffer twin (coq-eglot-position)) before)))))

(ert-deftest coq-eglot-twin-pair-errors ()
  "A buffer has at most one twin, and it is not itself."
  (with-twin
    (should-error (coq-eglot-twin-pair (current-buffer)) :type 'user-error)
    (should-error (coq-eglot-twin-pair twin) :type 'user-error)))

(ert-deftest coq-eglot-inactive-color ()
  "Inactive buffers use the color of `proof-locked-face', grayed."
  (should (equal (coq-eglot--desaturate-rgb '(1.0 0.0 0.0) 1) "#ff0000"))
  ;; color-rgb-to-hex truncates
  (should (equal (coq-eglot--desaturate-rgb '(1.0 0.0 0.0) 0) "#7f7f7f"))
  ;; same hue and lightness, less saturation
  (pcase-let* ((`(,h ,s ,l) (color-rgb-to-hsl 0.2 0.4 0.8))
               (hex (coq-eglot--desaturate-rgb '(0.2 0.4 0.8) 0.5))
               ;; not color-name-to-rgb: approximated in batch mode
               (`(,h2 ,s2 ,l2)
                (apply #'color-rgb-to-hsl
                       (mapcar (lambda (i)
                                 (/ (string-to-number (substring hex i (+ i 2)) 16)
                                    255.0))
                               '(1 3 5)))))
    (should (< (abs (- h h2)) 0.01))
    (should (< (abs (- l l2)) 0.01))
    (should (< (abs (- (/ s 2) s2)) 0.01)))
  ;; a background given to the face wins
  (cl-letf (((symbol-function 'face-background)
             (lambda (face &rest _)
               (if (eq face 'coq-eglot-inactive-locked-face) "gray50" "#eaf8ff"))))
    (should (eq (coq-eglot--inactive-locked-face)
                'coq-eglot-inactive-locked-face))))

(ert-deftest coq-eglot-id-at-point ()
  "The default argument of queries is the qualified identifier at point,
also in the goals and response buffers."
  (with-temp-buffer
    (coq-eglot-response-mode)
    (let ((inhibit-read-only t))
      (insert "Check Nat.add_comm. foo' x."))
    (goto-char 10)
    (should (equal (coq-id-at-point) "Nat.add_comm"))
    (search-forward "foo")
    (should (equal (coq-id-at-point) "foo'"))
    (goto-char (1- (point-max)))
    (should (equal (coq-id-at-point) "x"))))

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
    (cl-letf* ((ask-async (symbol-function 'coq-eglot-lsp-goals-async))
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

;; The base: the known sentences

(defun sentence-overlays ()
  "The overlays of the known sentences in the current buffer, in order."
  (sort (seq-filter (lambda (overlay) (overlay-get overlay 'coq-eglot-sentence))
                    (overlays-in (point-min) (point-max)))
        (lambda (a b) (< (overlay-start a) (overlay-start b)))))

(ert-deftest coq-eglot-sentences-overlays ()
  "The sentences processed one by one are overlays on their text.
An edition deletes those it touches, the others stay."
  (with-test-file
    (dotimes (_ 3) (run #'coq-eglot-assert-next-command))
    (let ((overlays (sentence-overlays)))
      (should (= (length overlays) 3))
      (should (equal (reverse (coq-eglot-session-sentences)) overlays))
      (should (equal (mapcar (lambda (overlay)
                               (buffer-substring (overlay-start overlay)
                                                 (overlay-end overlay)))
                             (cdr overlays))
                     '("Lemma l : forall n, double n = n + n /\\ True."
                       "Proof.")))
      (should (= (overlay-end (car (last overlays))) (coq-eglot-position))))
    ;; an edition in the second sentence
    (goto-char (overlay-start (cadr (coq-eglot-session-sentences))))
    (insert " ")
    (end-of-command)
    (should (= (length (sentence-overlays)) 1))
    (should (equal (sentence-overlays) (coq-eglot-session-sentences)))))

(ert-deftest coq-eglot-sentences-removed-by-others ()
  "Overlays of the sentences deleted by another package are forgotten."
  (with-test-file
    (dotimes (_ 2) (run #'coq-eglot-assert-next-command))
    (remove-overlays)
    (should (= (coq-eglot-position) (point-min)))
    (should-not (coq-eglot-session-sentences))
    (run #'coq-eglot-assert-next-command)
    (should (= (length (sentence-overlays)) 1))))

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
    (should (coq-eglot-checking-p))
    (should (eq (overlay-get coq-eglot--queue-overlay 'face) 'proof-queue-face))
    (let ((positions nil))
      (while (coq-eglot-checking-p)
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
    (should (coq-eglot-checking-p))
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
    (should-not (coq-eglot-checking-p))
    (accept-process-output nil 1)
    ;; just before the edited sentence
    (should (string-match-p "Proof\\.\\'"
                            (buffer-substring (point-min) (coq-eglot-position))))
    (should (string-match-p "\\`1 goal" (buffer-text "*goals*")))))

(ert-deftest coq-eglot-queue ()
  "Moving forward during a check extends it, like the queue of Proof
General: the rest is checked after, unless the check fails."
  (with-test-file
    (goto-marker "definition")
    (coq-eglot-goto-point)
    (should (coq-eglot-checking-p))
    (coq-eglot-assert-next-command)
    ;; the part being checked grows at once
    (should (>= (coq-eglot-check-target)
                (save-excursion (goto-marker "statement") (point))))
    (wait-for-coq)
    (should (position-at-marker-p "statement"))
    ;; up to point
    (coq-eglot-assert-next-command)
    (goto-marker "split")
    (coq-eglot-goto-point)
    (wait-for-coq)
    (should (position-at-marker-p "split"))
    (should (string-match-p "n : nat" (buffer-text "*goals*")))
    ;; moving back during a check is not possible, the check goes on
    (let ((before (coq-eglot-position)))
      (coq-eglot-assert-next-command)
      (goto-marker "definition")
      (should-error (coq-eglot-goto-point) :type 'user-error)
      (wait-for-coq)
      (should (> (coq-eglot-position) before)))
    ;; an error drops the rest
    (goto-marker "before error")
    (run #'coq-eglot-goto-point)
    (coq-eglot-assert-next-command)
    (coq-eglot-process-buffer)
    (wait-for-coq)
    (should (position-at-marker-p "before error"))
    (should (string-match-p "unknown_lemma" (buffer-text "*response*")))))

(ert-deftest coq-eglot-interrupt ()
  "Interrupting a check leaves the proof position where the server was.
The next command works."
  (with-file "eglot_slow.v"
    (force-new-check)
    (coq-eglot-process-buffer)
    (sleep-for 0.5)
    (coq-eglot-interrupt)
    (should-not (coq-eglot-checking-p))
    (should (< (point-min) (coq-eglot-position)))
    (should-not (position-at-marker-p "last"))
    (run #'coq-eglot-process-buffer)
    (should (position-at-marker-p "last"))))

(ert-deftest coq-eglot-interrupt-request ()
  "Interrupting cancels a request in flight, like an insertion waiting
for its answer: it is not called, the buffer is no longer busy."
  (with-test-file
    (goto-marker "statement")
    (run #'coq-eglot-goto-point)
    (let ((called nil))
      (coq-query-result "Show Intros" (lambda (_) (setq called t)))
      (should (coq-eglot-busy-p))
      (should-not (coq-eglot-checking-p))
      (coq-eglot-interrupt)
      (should (coq-eglot-session-settled-p))
      (wait-for-coq)
      (accept-process-output nil 0.2)
      (should-not called))))

(ert-deftest coq-eglot-interrupt-connecting ()
  "Interrupting while the server connects forgets what waits for it,
without sending anything that would wait for the connection again."
  (with-test-file
    (coq-eglot-restart-server)
    (goto-marker "split")
    (coq-eglot-goto-point)
    (should (coq-eglot-lsp-connecting-p))
    (coq-eglot-interrupt)
    (should-not (coq-eglot-lsp-connecting-p))
    (should-not coq-eglot--interrupting)
    (should-not (coq-eglot-busy-p))
    (should-not (coq-eglot-checking-p))
    ;; the next command works
    (run #'coq-eglot-goto-point)
    (should (position-at-marker-p "split"))))

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
  (should (coq-eglot-checking-p)))

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
      ;; the new server connects without waiting
      (should (wait-until #'coq-eglot-lsp-current-server 10))
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

(ert-deftest coq-eglot-exit-other-buffer-checking ()
  "Stopping or restarting the server from a buffer stops the check of
another buffer of the server: no answer will come, it is not busy."
  (dolist (command '(coq-eglot-restart-server coq-eglot-exit))
    (with-file "eglot_slow.v"
      (force-new-check)
      (let ((slow (current-buffer)))
        (coq-eglot-process-buffer)
        (should (coq-eglot-checking-p))
        (with-test-file
          (funcall command))
        (with-current-buffer slow
          (should-not (coq-eglot-checking-p))
          (should-not coq-eglot--interrupting)
          (should-not (overlay-buffer coq-eglot--queue-overlay))
          ;; not busy: a new command runs
          (goto-char (point-min))
          (re-search-forward "Fixpoint.*$")
          (run #'coq-eglot-goto-point)
          (should (> (coq-eglot-position) (point-min))))))))

(ert-deftest coq-eglot-kill-buffer-checking ()
  "Killing a buffer during its check forgets it: its markers are freed,
it is no longer the buffer where the user works."
  (with-file "eglot_slow.v"
    (force-new-check)
    (coq-eglot-process-buffer)
    (should (coq-eglot-checking-p))
    (let ((target coq-eglot-session--target))
      (coq-eglot-set-working-buffer (current-buffer))
      (run-hooks 'kill-buffer-hook)
      (should-not (coq-eglot-checking-p))
      (should-not (marker-buffer target))
      (should-not (coq-eglot-working-buffer)))))

(ert-deftest coq-eglot-inactive-keeps-output ()
  "A script buffer that is not active leaves the output alone: its goals,
its messages and the output hook are those of the active one."
  (with-test-file
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (let* ((output (coq-eglot--output))
           (goals (coq-eglot--output-goals output))
           (other (find-file-noselect "eglot_other.v"))
           (ran nil))
      (unwind-protect
          (with-current-buffer other
            (should-not (coq-eglot--active-p))
            (add-hook 'coq-eglot-output-hook (lambda () (setq ran t)) nil t)
            (coq-eglot--show-goals
             (coq-eglot-lsp-make-answer
              :goals '(:goals [] :stack [] :shelf [] :given_up [])))
            (coq-eglot--show-response "other")
            (should (equal (coq-eglot--output-goals output) goals))
            (should-not ran)
            (should-not (string-match-p "other"
                                        (buffer-text "*response*"))))
        (kill-buffer other)))))

(ert-deftest coq-eglot-error-after-point-in-sentence ()
  "Going to a point inside a sentence whose error is located after point
reports the error and stops before the sentence."
  (with-test-file
    (goto-marker "error")
    (search-backward "unknown_lemma")
    ;; inside the sentence, before the term Coq complains about
    (run #'coq-eglot-goto-point)
    (should (position-at-marker-p "before error"))
    (should (string-match-p "unknown_lemma" (buffer-text "*response*")))))

(ert-deftest coq-eglot-query-cancelled-silent ()
  "A query cancelled by an edition or a new check displays no error."
  (with-file "eglot_slow.v"
    (force-new-check)
    (goto-char (point-min))
    (re-search-forward "^Fixpoint.*$")
    (run #'coq-eglot-goto-point)
    (coq-eglot--show-response "before")
    (let ((done nil))
      (cl-letf* ((show-error (symbol-function 'coq-eglot--show-error))
                 ((symbol-function 'coq-eglot--show-error)
                  (lambda (text) (setq done t) (funcall show-error text))))
        (coq-eglot-run-query "Eval vm_compute in Nat.eqb (fact 11) 0"
                             nil (lambda () (setq done t)))
        (accept-process-output nil 0.05)
        (coq-eglot-lsp-cancel-all)
        (wait-until (lambda () done) 2)))
    (should (equal (buffer-text "*response*") "before"))))

(ert-deftest coq-eglot-compile-error-not-busy ()
  "An error when the compilation starts stops the check: not busy."
  (with-test-file
    (cl-letf (((symbol-function 'coq-eglot-compile-requires)
               (lambda (&rest _) (error "No coqdep"))))
      (goto-marker "split")
      (should-error (coq-eglot-goto-point))
      (should-not (coq-eglot-checking-p)))))

(ert-deftest coq-eglot-fail-unknown-sentence-before ()
  "A failure whose sentence before is unknown keeps the known proof
position before it, instead of going back to the beginning."
  (with-test-file
    (goto-marker "before error")
    (run #'coq-eglot-goto-point)
    (let ((position (coq-eglot-position))
          (start (save-excursion (goto-marker "error")
                                 (search-backward "rewrite"))))
      ;; the answer kept for the position is forgotten, the server
      ;; answers without the range of the sentence
      (coq-eglot-session-set-sentence-answer (coq-eglot-session-last-sentence) nil)
      (cl-letf (((symbol-function 'coq-eglot-lsp-goals-async)
                 (lambda (_pos on-success _on-error)
                   (run-at-time 0 nil on-success (coq-eglot-lsp-make-answer)))))
        (coq-eglot--fail start (point-max) "Error.")
        (wait-for-coq))
      (should (= (coq-eglot-position) position)))))

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
  "Without `coq-use-project-file', the server of a file runs in its
directory, not in the one of the dominating project file."
  (skip-unless-server)
  (let ((coq-use-project-file nil)
        (dir (expand-file-name "lib/" load-path-directory)))
    (should (equal (coq-eglot-lsp-project dir) (cons 'transient dir)))))

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

;;; printing width

(defmacro with-width-file (&rest body)
  "Run BODY in eglot_width.v, adapting the printing width, in the
hybrid layout."
  (declare (indent 0) (debug t))
  `(with-file "eglot_width.v"
     (with-layout t 'hybrid
       (let ((coq-auto-adapt-printing-width t))
         ,@body))))

(defun lines-fit-p (name)
  "Non-nil if the lines of buffer NAME fit in its window."
  (let ((width (window-max-chars-per-line (get-buffer-window name))))
    (seq-every-p (lambda (line) (<= (string-width line) width))
                 (split-string (buffer-text name) "\n"))))

(defun resize-goals-window (columns)
  "Make the goals window COLUMNS wider, print its goals again.
Narrower if COLUMNS is negative.  Wait for the goals printed at the new
width.  Batch mode has no redisplay to run `window-size-change-functions'."
  (let ((width (coq-eglot--displayed-width)))
    (with-selected-window (get-buffer-window "*goals*")
      (enlarge-window-horizontally columns))
    (coq-eglot--refresh-width)
    (wait-until (lambda () (not (eql (coq-eglot--displayed-width) width))) 10)))

(ert-deftest coq-eglot-printing-width-goals ()
  "The goals are printed at the width of their window, and again when it
changes, like with `coq-auto-adapt-printing-width' in Proof General."
  (with-width-file
    (goto-marker "intros")
    (run #'coq-eglot-goto-point)
    ;; printed again once displayed
    (wait-until (lambda () (coq-eglot--displayed-width)) 10)
    (should (= (coq-eglot--displayed-width)
               (- (window-max-chars-per-line (get-buffer-window "*goals*"))
                  coq-eglot--hyp-indentation
                  coq-eglot--printing-width-margin)))
    (should (string-match-p "Hyp_with_long_name :\n    aaaaaaaa"
                            (buffer-text "*goals*")))
    (should (lines-fit-p "*goals*"))
    (let ((width (coq-eglot--displayed-width)))
      (resize-goals-window -2)
      (should (= (coq-eglot--displayed-width) (- width 2)))
      (should (lines-fit-p "*goals*")))
    ;; column by column: the lines as wide as the window fit too, down
    ;; to the width of the separator line
    (dotimes (_ 6)
      (resize-goals-window -1)
      (should (lines-fit-p "*goals*")))
    ;; and with lines ending with an infix operator
    (goto-marker "limit")
    (run #'coq-eglot-goto-point)
    (wait-until (lambda () (string-match-p "H :" (buffer-text "*goals*"))) 10)
    (dotimes (_ 6)
      (resize-goals-window 1)
      (should (lines-fit-p "*goals*")))
    ;; the answer kept for the proof position is printed again
    (let ((width (coq-eglot--displayed-width)))
      (with-selected-window (get-buffer-window "*goals*")
        (enlarge-window-horizontally 4))
      (coq-eglot--goals-at-position)
      (wait-until (lambda () (eql (coq-eglot--displayed-width) (+ width 4))) 10)
      (should (= (coq-eglot--displayed-width) (+ width 4))))))

(ert-deftest coq-eglot-printing-width-split-goals ()
  "With the conclusion apart, the goals are printed at the width of the
narrowest of the goals and conclusion windows."
  (with-width-file
    (let ((coq-eglot-split-goals t))
      (goto-marker "intros")
      (run #'coq-eglot-goto-point)
      (wait-until (lambda () (coq-eglot--displayed-width)) 10)
      (should (lines-fit-p "*goals*"))
      (should (lines-fit-p "*conclusion*"))
      (should (= (coq-eglot--displayed-width)
                 (- (min (window-max-chars-per-line (get-buffer-window "*goals*"))
                         (window-max-chars-per-line
                          (get-buffer-window "*conclusion*")))
                    coq-eglot--hyp-indentation
                    coq-eglot--printing-width-margin))))))

(ert-deftest coq-eglot-printing-width-off ()
  "Without `coq-auto-adapt-printing-width', the goals are printed at the
default width of Coq."
  (with-width-file
    (let ((coq-auto-adapt-printing-width nil))
      (goto-marker "intros")
      (run #'coq-eglot-goto-point)
      (should (string-match-p "1 goal" (buffer-text "*goals*")))
      (should-not (coq-eglot--displayed-width))
      (should-not (coq-eglot--goals-printing-width))
      (should-not (coq-eglot--query-printing-width)))))

(ert-deftest coq-eglot-printing-width-query ()
  "The answers of the queries are printed at the width of the response
window, for this query only."
  (with-width-file
    (goto-marker "intros")
    (run #'coq-eglot-goto-point)
    (let ((answer (query #'coq-eglot-run-query "Check Hyp_with_long_name")))
      (should (string-match-p "\\`Hyp_with_long_name\n" answer))
      (should (lines-fit-p "*response*")))
    (should (string-match-p
             (format "\\b%d\\b" (- (window-max-chars-per-line
                                    (get-buffer-window "*response*"))
                                   coq-eglot--printing-width-margin))
             (query #'coq-eglot-run-query "Test Printing Width")))
    ;; for this query only: nothing leaks in the state of the server
    (let ((coq-auto-adapt-printing-width nil))
      (should (string-match-p "\\b78\\b" (query #'coq-eglot-run-query
                                                "Test Printing Width")))
      (coq-eglot--goals-at-position t)
      (wait-for-coq)
      (should (string-match-p "^  aaaaaaaa \\+ bbbbbbbbb \\* cccccccccc \\+ dddddddddd =$"
                              (buffer-text "*goals*"))))))

(ert-deftest coq-eglot-ask-printing-width ()
  "C-c C-a C-w sets the printing width of the goals and the queries, like
in Proof General, until the goals window changes width."
  (with-width-file
    (goto-marker "intros")
    (run #'coq-eglot-goto-point)
    (wait-until (lambda () (coq-eglot--displayed-width)) 10)
    (should (eq (key-binding (kbd "C-c C-a C-w")) #'coq-ask-printing-width))
    (should (eq coq-ask-printing-width-function #'coq-eglot-ask-printing-width))
    (with-current-buffer "*goals*"
      (should (eq (key-binding (kbd "C-c C-a C-w")) #'coq-ask-printing-width))
      (should (eq coq-ask-printing-width-function
                  #'coq-eglot-ask-printing-width)))
    (let ((auto (coq-eglot--displayed-width)))
      (unwind-protect
          (progn
            (cl-letf (((symbol-function 'read-number) (lambda (&rest _) 25)))
              (call-interactively #'coq-ask-printing-width))
            (wait-until (lambda () (eql (coq-eglot--displayed-width) 25)) 10)
            (should (eql (coq-eglot--displayed-width) 25))
            (should (string-match-p "\\b25\\b" (query #'coq-eglot-run-query
                                                      "Test Printing Width")))
            ;; the next goals too
            (run #'coq-eglot-assert-next-command)
            (should (eql (coq-eglot--displayed-width) 25))
            (run #'coq-eglot-undo-last-command)
            ;; the window changes: the width follows it again
            (resize-goals-window -2)
            (should (= (coq-eglot--displayed-width) (- auto 2))))
        (setf (coq-eglot--output-asked-width coq-eglot--default-output) nil)))))

(ert-deftest coq-eglot-set-flag ()
  "The printing flags of the common commands, like C-c C-a n, hold for
the next goals and queries, like in Proof General."
  (with-test-file
    (should (eq coq-set-flag-function #'coq-eglot-set-flag))
    (should (eq (key-binding (kbd "C-c C-a n")) #'coq-unset-printing-notations))
    (goto-marker "hyps")
    (run #'coq-eglot-goto-point)
    (should (string-match-p "^ *m = n$" (buffer-text "*goals*")))
    (unwind-protect
        (progn
          (with-current-buffer "*goals*"
            (should (eq coq-set-flag-function #'coq-eglot-set-flag))
            (call-interactively (key-binding (kbd "C-c C-a n"))))
          ;; the goals are printed again
          (should (wait-until (lambda () (string-match-p "^ *eq m n$"
                                                         (buffer-text "*goals*")))
                              10))
          ;; nothing checked again
          (should (position-at-marker-p "hyps"))
          (should (string-match-p "\\`eq 0 0" (query #'coq-run-query "Check 0 = 0")))
          ;; the next goals too
          (run #'coq-eglot-assert-next-command)
          (should (string-match-p "^ *eq n m$" (buffer-text "*goals*")))
          ;; one command per flag
          (coq-set-printing-notations)
          (should (equal coq-eglot--printing-flags '("Set Printing Notations")))
          (should (wait-until (lambda () (string-match-p "^ *n = m$"
                                                         (buffer-text "*goals*")))
                              10))
          (should (string-match-p "\\`0 = 0" (query #'coq-run-query "Check 0 = 0")))
          ;; forgotten when the server stops
          (coq-unset-printing-notations)
          (coq-eglot-exit)
          (should-not coq-eglot--printing-flags))
      (setq coq-eglot--printing-flags nil))))

(defvar coq-search-blacklist-current-string) ; let-bound

(ert-deftest coq-eglot-search-blacklist ()
  "The search blacklist holds for the next queries, like in Proof General."
  (with-test-file
    (should (eq coq-set-search-blacklist-function
                #'coq-eglot-set-search-blacklist))
    (goto-marker "before error")
    (run #'coq-eglot-goto-point)
    (with-current-buffer "*goals*"
      (should (eq coq-set-search-blacklist-function
                  #'coq-eglot-set-search-blacklist)))
    (let ((coq-search-blacklist-current-string coq-search-blacklist-string))
      (should (string-match-p "Private_"
                              (query #'coq-run-query "Test Search Blacklist")))
      (coq-change-search-blacklist "\"foo_\" \"_bar\"")
      (let ((answer (query #'coq-run-query "Test Search Blacklist")))
        (should (string-match-p "\\_<foo_\\_>" answer))
        (should (string-match-p "\\_<_bar\\_>" answer))
        (should-not (string-match-p "Private_" answer)))
      ;; not a list of strings: refused, the blacklist does not change
      (should-error (coq-change-search-blacklist "foo_") :type 'user-error)
      (should (equal coq-search-blacklist-current-string
                     "\"foo_\" \"_bar\"")))))

(defun menu-entry (menu name)
  "The entry NAME of MENU, at any depth, or nil."
  (seq-some (lambda (item)
              (cond ((and (vectorp item) (equal (aref item 0) name)) item)
                    ((consp item) (menu-entry (cdr item) name))))
            menu))

(ert-deftest coq-eglot-compile-menu ()
  "The menu of the compilation is the one of Proof General, with a
warning on its entries without effect."
  (let ((menu (assoc "Auto Compilation" (cdr coq-eglot--menu-spec))))
    (should menu)
    (should (equal (length menu) (length coq-compile-menu)))
    (should (eq (aref (menu-entry menu "Compile Before Require") 1)
                'coq-compile-before-require-toggle))
    (should (eq (car (aref (menu-entry menu "Lock Ancestors") 1))
                'coq-eglot--run-no-effect))
    (should (eq (car (aref (menu-entry menu "use -vos and -vok") 1))
                'coq-eglot--run-no-effect))
    (should (eq (aref (menu-entry menu "Keep going") 1)
                'coq-compile-keep-going-toggle)))
  (should (seq-some (lambda (item)
                      (and (vectorp item)
                           (eq (aref item 1)
                               'coq-change-search-blacklist-interactive)))
                    (cdr (assoc "Queries" (cdr coq-eglot--menu-spec))))))

(ert-deftest coq-eglot-options-menu ()
  "The printing menu has an Eglot presentation toggle and Rocq flags."
  (should (member coq-eglot--options-menu (cdr coq-eglot--menu-spec)))
  (should (equal (car coq-eglot--options-menu) "OPTIONS"))
  (dolist (item (cdr coq-eglot--options-menu))
    (should (commandp (aref item 1))))
  (let ((compact (menu-entry coq-eglot--options-menu "Compact Contexts")))
    (should compact)
    (should (eq (aref compact 1) 'coq-eglot-toggle-compact-contexts))
    (should (eq (plist-get (append compact nil) :style) 'toggle)))
  (should-not (menu-entry coq-eglot--options-menu
                          "Set Printing Compact Contexts"))
  (should-not (menu-entry coq-eglot--options-menu
                          "Unset Printing Compact Contexts"))
  (with-test-file
    (let ((coq-eglot--printing-flags nil))
      (coq-set-printing-coercions)
      (should (member "Set Printing Coercions" coq-eglot--printing-flags))
      (coq-unset-printing-coercions)
      (should (member "Unset Printing Coercions" coq-eglot--printing-flags))
      (should-not (member "Set Printing Coercions"
                          coq-eglot--printing-flags)))))

(ert-deftest coq-eglot-no-effect-warnings ()
  "The menu entries and the commands without effect in the Eglot backend
do what they do, and warn."
  (let ((coq-lock-ancestors t)
        (menu (assoc "Auto Compilation" (cdr coq-eglot--menu-spec))))
    (with-current-buffer (get-buffer-create "*Warnings*")
      (let ((inhibit-read-only t)) (erase-buffer)))
    (eval (aref (menu-entry menu "Lock Ancestors") 1) t)
    (should-not coq-lock-ancestors)
    (should (string-search "\"Lock Ancestors\" has no effect"
                           (with-current-buffer "*Warnings*" (buffer-string)))))
  (with-test-file
    (let ((coq-eglot--printing-flags nil))
      (with-current-buffer "*Warnings*"
        (let ((inhibit-read-only t)) (erase-buffer)))
      (coq-unset-printing-unfocused)
      (should (member "Unset Printing Unfocused" coq-eglot--printing-flags))
      (should (string-search "Unset Printing Unfocused has no effect"
                             (with-current-buffer "*Warnings*"
                               (buffer-string)))))))

(ert-deftest coq-eglot-compact-contexts ()
  "The display option puts compatible hypotheses on the same line."
  (with-test-file
    (let ((coq-eglot-compact-contexts nil))
      (goto-marker "compact")
      (run #'coq-eglot-goto-point)
      (should (string-search "  A : Type\n  a : A\n"
                             (with-current-buffer "*goals*" (buffer-string))))
      (coq-eglot-toggle-compact-contexts)
      (should
       (wait-until
        (lambda ()
          (with-current-buffer "*goals*"
            (or (string-search "A : Type   a : A" (buffer-string))
                (progn
                  (goto-char (point-min))
                  (text-property-search-forward
                   'coq-eglot-late-context-compaction t t)))))
        10))
      ;; On a loaded server the 50 ms display wait may expire.  The late
      ;; result is then offered without moving the goal by itself.
      (unless (with-current-buffer "*goals*"
                (string-search "A : Type   a : A" (buffer-string)))
        (coq-eglot-compact-late-context))
      (with-current-buffer "*goals*"
        (let ((text (buffer-substring-no-properties (point-min) (point-max))))
          (should (string-search "\n  n, m : nat   P : nat -> Prop\n" text))
          (should (string-search "\n  h : P n\n" text))
          (should (string-search "\n  A : Type   a : A\n" text))
          (should (string-search "\n  x := 3 : nat\n" text))
          (should (string-search "\n  q : SProp\n  pq : q\n  e : n = m\n"
                                 text))))
      (should (member "a" (coq-hyps-names)))
      (should (= (length (coq-hyps-regions)) 9))
      (coq-eglot-toggle-compact-contexts)
      (should (wait-until (lambda ()
                            (with-current-buffer "*goals*"
                              (string-search "A : Type\n  a : A"
                                             (buffer-string))))
                          10)))))

(ert-deftest coq-eglot-goals-do-not-wait-for-hyp-sorts ()
  "The semantic goals answer is delivered without an auxiliary request."
  (let (goals-success received published queried)
    (cl-letf (((symbol-function 'coq-eglot-lsp-query-async)
               (lambda (&rest _) (setq queried t)))
              ((symbol-function 'coq-eglot-lsp--async-request)
               (lambda (_pos _method _params success _error &rest _policy)
                 (setq goals-success success)
                 'goals-context))
              ((symbol-function 'coq-eglot-lsp--answer)
               (lambda (&rest _)
                 (coq-eglot-lsp-make-answer
                  :goals (list :goals (vector (list :hyps [] :ty "True"))))))
              ((symbol-function 'coq-eglot-lsp--publish)
               (lambda (answer) (push answer published))))
      (should (eq (coq-eglot-lsp-goals-async
                   1 (lambda (answer) (setq received answer)) #'ignore)
                  'goals-context))
      (funcall goals-success nil nil)
      (should received)
      (should-not queried)
      (should (= (length published) 1)))))

(ert-deftest coq-eglot-hyp-sorts-within-display-wait ()
  "Sorts received during the display wait compact the initial goals."
  (with-temp-buffer
    (let ((coq-eglot-compact-contexts t)
          (coq-eglot-lsp-hyp-sorts-wait 10)
          (coq-eglot-lsp-hyp-sorts-deadline 20)
          (answer (coq-eglot-lsp-make-answer
                   :context (coq-eglot-lsp--make-context :proof/goals 1)
                   :goals (list :goals
                                (vector (list :hyps [] :ty "True")))))
          sorts-success shown)
      (cl-letf (((symbol-function 'coq-eglot--displays-p) (lambda () t))
                ((symbol-function 'coq-eglot-lsp-hyp-sorts-async)
                 (lambda (_answer success _error)
                   (setq sorts-success success)
                   'sorts-context))
                ((symbol-function 'coq-eglot--show-answer-now)
                 (lambda (value &optional _goals-only) (setq shown value))))
        (unwind-protect
            (progn
              (coq-eglot--show-answer-enriched answer t)
              (should-not shown)
              (funcall sorts-success '(("x" . "Type")))
              (should (eq shown answer))
              (should (equal
                       (plist-get
                        (aref (plist-get (coq-eglot-lsp-answer-goals answer)
                                        :goals)
                              0)
                        :hyp-sorts)
                       '(("x" . "Type")))))
          (coq-eglot--cancel-hyp-sorts))))))

(ert-deftest coq-eglot-hyp-sorts-after-display ()
  "Late sorts are offered without moving an already displayed goal."
  (with-temp-buffer
    (let* ((coq-eglot-compact-contexts t)
           (coq-eglot-lsp-hyp-sorts-wait 10)
           (coq-eglot-lsp-hyp-sorts-deadline 20)
           (goals (list :goals (vector (list :hyps [] :ty "True"))))
           (output (coq-eglot--make-output))
           (answer (coq-eglot-lsp-make-answer
                    :context (coq-eglot-lsp--make-context :proof/goals 1)
                    :goals goals))
           sorts-success shown offered)
      (setf (coq-eglot--output-goals output) goals)
      (setq coq-eglot--buffer-output output)
      (cl-letf (((symbol-function 'coq-eglot--displays-p) (lambda () t))
                ((symbol-function 'coq-eglot-lsp-hyp-sorts-async)
                 (lambda (_answer success _error)
                   (setq sorts-success success)
                   'sorts-context))
                ((symbol-function 'coq-eglot--show-answer-now)
                 (lambda (value &optional _goals-only) (setq shown value)))
                ((symbol-function 'coq-eglot--offer-late-context-compaction)
                 (lambda () (setq offered t))))
        (unwind-protect
            (progn
              (coq-eglot--show-answer-enriched answer t)
              (coq-eglot--hyp-sorts-display answer t)
              (should (eq shown answer))
              (funcall sorts-success '(("x" . "Type")))
              (let ((goal (aref (plist-get goals :goals) 0)))
                (should-not (plist-get goal :hyp-sorts))
                (should (equal (plist-get goal :hyp-sorts-late)
                               '(("x" . "Type")))))
              (should offered))
          (coq-eglot--cancel-hyp-sorts))))))

(ert-deftest coq-eglot-hyp-sorts-timeout-cancels-enrichment ()
  "The auxiliary deadline cancels sorts and ignores a racing success."
  (with-temp-buffer
    (let* ((coq-eglot-compact-contexts t)
           (coq-eglot-lsp-hyp-sorts-wait 10)
           (coq-eglot-lsp-hyp-sorts-deadline 20)
           (answer (coq-eglot-lsp-make-answer
                    :context (coq-eglot-lsp--make-context :proof/goals 1)
                    :goals (list :goals
                                 (vector (list :hyps [] :ty "True")))))
           sorts-success shown cancelled)
      (cl-letf (((symbol-function 'coq-eglot--displays-p) (lambda () t))
                ((symbol-function 'coq-eglot-lsp-hyp-sorts-async)
                 (lambda (_answer success _error)
                   (setq sorts-success success)
                   'sorts-context))
                ((symbol-function 'coq-eglot-lsp-cancel-request)
                 (lambda (context) (setq cancelled context)))
                ((symbol-function 'coq-eglot--show-answer-now)
                 (lambda (value &optional _goals-only) (setq shown value))))
        (unwind-protect
            (progn
              (coq-eglot--show-answer-enriched answer t)
              (coq-eglot--hyp-sorts-deadline answer t)
              (should (eq cancelled 'sorts-context))
              (should (eq shown answer))
              (funcall sorts-success '(("x" . "Type")))
              (let ((goal (aref
                           (plist-get (coq-eglot-lsp-answer-goals answer)
                                      :goals)
                           0)))
                (should-not (plist-get goal :hyp-sorts))
                (should-not (plist-get goal :hyp-sorts-late))))
          (coq-eglot--cancel-hyp-sorts))))))

(ert-deftest coq-eglot-lsp-finalization-waits-for-user-request ()
  "Finalization neither interrupts an active read nor lets a new one in."
  (with-temp-buffer
    (let* ((user (coq-eglot-lsp--make-context :petanque/run_at_point 1))
           (critical (coq-eglot-lsp--make-context :proof/goals 1))
           (later (coq-eglot-lsp--make-context :petanque/run_at_point 1))
           sent)
      (setf (coq-eglot-lsp-context-policy user) coq-eglot-lsp-user-policy
            (coq-eglot-lsp-context-policy critical)
            coq-eglot-lsp-finalization-policy
            (coq-eglot-lsp-context-policy later) coq-eglot-lsp-user-policy)
      (setq coq-eglot-lsp--active-requests (list user)
            coq-eglot-lsp--request-queue
            (list (cons critical (lambda () (push 'critical sent)))
                  (cons later (lambda () (push 'later sent)))))
      ;; Finalization waits for the explicit user request.
      (coq-eglot-lsp--dispatch-scheduled)
      (should-not sent)
      (coq-eglot-lsp--request-finished user)
      (should (equal sent '(critical)))
      (should (equal coq-eglot-lsp--active-requests (list critical)))
      ;; The later read waits until finalization is over.
      (coq-eglot-lsp--request-finished critical)
      (should (equal sent '(later critical)))
      (should (equal coq-eglot-lsp--active-requests (list later))))))

(ert-deftest coq-eglot-lsp-request-policies ()
  "Final goals, sorts and checks have explicit independent policies."
  (let (goals-policy sorts-policy check-policy)
    (cl-letf (((symbol-function 'coq-eglot-lsp-goals-async)
               (lambda (_pos _success _error &optional policy _key)
                 (setq goals-policy policy)))
              ((symbol-function 'coq-eglot-lsp-query-async)
               (lambda (_pos _command _success _error &optional policy _key)
                 (setq sorts-policy policy)))
              ((symbol-function 'coq-eglot-lsp--async-request)
               (lambda (_pos _method _params _success _error
                        &optional policy _key)
                 (setq check-policy policy))))
      (coq-eglot-lsp-final-goals-async 1 #'ignore #'ignore)
      (let ((coq-eglot-lsp-hyp-sort-names-function nil))
        (coq-eglot-lsp-hyp-sorts-async
         (coq-eglot-lsp-make-answer
          :context (coq-eglot-lsp--make-context :proof/goals 1))
         #'ignore #'ignore))
      (coq-eglot-lsp-check-async 1 #'ignore #'ignore))
    (should (eq goals-policy coq-eglot-lsp-finalization-policy))
    (should (eq sorts-policy coq-eglot-lsp-background-policy))
    (should (eq check-policy coq-eglot-lsp-work-policy))))

(ert-deftest coq-eglot-lsp-policy-preemption ()
  "A foreground request passes work and discards background work."
  (with-temp-buffer
    (cl-letf (((symbol-function 'coq-eglot-lsp-current-server) #'ignore))
      (let ((work (coq-eglot-lsp--make-context :work 1))
            (user (coq-eglot-lsp--make-context :user 1))
            sent)
        (setf (coq-eglot-lsp-context-policy work) coq-eglot-lsp-work-policy
              (coq-eglot-lsp-context-policy user) coq-eglot-lsp-user-policy)
        (setq coq-eglot-lsp--active-requests (list work)
              coq-eglot-lsp--request-queue
              (list (cons user (lambda () (setq sent t)))))
        (coq-eglot-lsp--dispatch-scheduled)
        (should sent)
        (should (memq work coq-eglot-lsp--active-requests))
        (should (memq user coq-eglot-lsp--active-requests)))
      (let ((background (coq-eglot-lsp--make-context :background 1))
            (work (coq-eglot-lsp--make-context :work 1))
            sent)
        (setf (coq-eglot-lsp-context-policy background)
              coq-eglot-lsp-background-policy
              (coq-eglot-lsp-context-policy work) coq-eglot-lsp-work-policy)
        (setq coq-eglot-lsp--active-requests (list background)
              coq-eglot-lsp--request-queue
              (list (cons work (lambda () (setq sent t)))))
        (coq-eglot-lsp--dispatch-scheduled)
        (should sent)
        (should (coq-eglot-lsp-context-cancelled background))
        (should (equal coq-eglot-lsp--active-requests (list work)))))))

(ert-deftest coq-eglot-lsp-hover-is-dropped-while-busy ()
  "A hover is not queued behind useful work."
  (with-temp-buffer
    (let ((user (coq-eglot-lsp--make-context :user 1))
          (hover (coq-eglot-lsp--make-context :textDocument/hover 1)))
      (setf (coq-eglot-lsp-context-policy user) coq-eglot-lsp-user-policy
            (coq-eglot-lsp-context-policy hover) coq-eglot-lsp-hover-policy)
      (setq coq-eglot-lsp--active-requests (list user))
      (should-not (coq-eglot-lsp--schedule hover #'ignore))
      (should (coq-eglot-lsp-context-cancelled hover))
      (should-not coq-eglot-lsp--request-queue))))

(ert-deftest coq-eglot-lsp-interrupted-work-is-reissued ()
  "Work interrupted by a foreground request resumes after that request."
  (with-temp-buffer
    (let (sent failures)
      (cl-letf (((symbol-function 'coq-eglot-lsp-connect)
                 (lambda () 'server))
                ((symbol-function 'coq-eglot-lsp-current-server)
                 (lambda () 'server))
                ((symbol-function 'coq-eglot-lsp--flush-document)
                 (lambda () 1))
                ((symbol-function 'jsonrpc--async-request-1)
                 (lambda (_server method _params &rest args)
                   (push (list method
                               (plist-get args :success-fn)
                               (plist-get args :error-fn))
                         sent)
                   (list (length sent)))))
        (let ((work
               (coq-eglot-lsp--async-request
                1 :work #'ignore #'ignore
                (lambda (failure) (push failure failures))
                coq-eglot-lsp-work-policy 'check)))
          (coq-eglot-lsp--async-request
           1 :user #'ignore #'ignore
           (lambda (failure) (push failure failures)))
          (should (equal (mapcar #'car (reverse sent)) '(:work :user)))
          ;; The user request interrupts the synchronous part of work.
          (funcall (nth 2 (cadr sent))
                   '(:code -32001 :message "Interrupted"))
          (should (wait-until
                   (lambda ()
                     (and (memq work (mapcar #'car coq-eglot-lsp--request-queue))
                          (= (length coq-eglot-lsp--active-requests) 1)))
                   2))
          (should-not failures)
          ;; Once the protected user request answers, work is sent again.
          (funcall (nth 1 (car sent)) 'answer)
          (should (wait-until (lambda () (= (length sent) 3)) 2))
          (should (equal (mapcar #'car (reverse sent))
                         '(:work :user :work)))
          (funcall (nth 1 (car sent)) 'answer)
          (should (wait-until
                   (lambda () (null coq-eglot-lsp--active-requests)) 2)))))))

(ert-deftest coq-eglot-twins-do-not-compact-contexts ()
  "Twins neither compact contexts nor ask for their hypothesis sorts."
  (let ((twin (generate-new-buffer " *coq-eglot-twin-test*")))
    (unwind-protect
        (with-temp-buffer
          (setq coq-eglot-compact-contexts t
                coq-eglot--twin twin)
          (should-not (coq-eglot--compact-contexts-p))
          (should-not (coq-eglot--compact-contexts-p)))
      (kill-buffer twin))))

(ert-deftest coq-eglot-late-hyp-sorts-only-offered-when-useful ()
  "A late-sort action is offered only if it would change the formatting."
  (let ((coq-eglot-compact-contexts t)
        (coq-eglot--printing-flags nil)
        (goal (list :hyps (vector (list :names '("x") :ty "nat")
                                  (list :names '("y") :ty "nat"))
                    :ty "True")))
    (cl-letf (((symbol-function 'coq-eglot--hyps-width) (lambda () 80))
              ((symbol-function 'coq-eglot--twin-layout-p) (lambda () nil)))
      (let ((goals (list :goals (vector goal))))
        (should-not (coq-eglot--late-hyp-sorts-useful-p goals))
        (plist-put goal :hyp-sorts-late
                   '(("x" . "Prop") ("y" . "Prop")))
        (should-not (coq-eglot--late-hyp-sorts-useful-p goals))
        (plist-put goal :hyp-sorts-late
                   '(("x" . "Type") ("y" . "Type")))
        (should (coq-eglot--late-hyp-sorts-useful-p goals))))))

(ert-deftest coq-eglot-hyp-sort-names-only-formatting-candidates ()
  "Only one-line assumptions need sorts for compact context formatting."
  (let* ((goal (list
                :hyps (vector
                       (list :names '("x" "y") :ty "nat")
                       (list :names '("d") :def "0" :ty "nat")
                       (list :names '("long") :ty "nat\n  * nat"))
                :ty "True"))
         (answer (coq-eglot-lsp-make-answer
                  :goals (list :goals (vector goal)))))
    (should (equal (coq-eglot--hyp-sort-names answer) '("x" "y")))
    (let* ((coq-eglot-lsp-hyp-sort-names-function
            #'coq-eglot--hyp-sort-names)
           (command (coq-eglot-lsp--hyp-sorts-command
                     (coq-eglot--hyp-sort-names answer))))
      (should (string-search "COQ-EGLOT-SORT x" command))
      (should (string-search "COQ-EGLOT-SORT y" command))
      (should-not (string-search "COQ-EGLOT-SORT d" command))
      (should-not (string-search "COQ-EGLOT-SORT long" command)))))

(ert-deftest coq-eglot-show-at-point ()
  "C-c C-a C-s shows the goals and messages after the sentence at point,
in the processed part, like in Proof General.  Elsewhere it asks for a
goal number."
  (with-test-file
    (should (eq (key-binding (kbd "C-c C-a C-s")) #'coq-Show))
    (goto-marker "subproof")
    (run #'coq-eglot-goto-point)
    (let ((position (coq-eglot-position)))
      (goto-marker "hello")
      (search-backward "idtac")
      (call-interactively #'coq-Show)
      ;; displayed when the answer comes
      (wait-for-coq)
      (should (equal (buffer-text "*response*") "hello"))
      (should (string-match-p "^ *double n = n \\+ n$" (buffer-text "*goals*")))
      (search-backward "intros n")
      (call-interactively #'coq-Show)
      (wait-for-coq)
      (should (string-match-p "^ *double n = n \\+ n /\\\\ True$"
                              (buffer-text "*goals*")))
      ;; the proof position does not move
      (should (= (coq-eglot-position) position))
      ;; after it, Show for a goal number
      (goto-marker "hyps")
      (should-not (coq-eglot-show-at-point))
      (let (asked)
        (cl-letf (((symbol-function 'coq-ask-do)
                   (lambda (&rest args) (setq asked args))))
          (call-interactively #'coq-Show))
        (should (equal (nth 1 asked) "Show"))))))

(ert-deftest coq-eglot-insert-as ()
  "C-c C-a [ inserts the \"as\" clause of the next command, from the names
given by Coq, like in Proof General."
  (with-test-file
    (should (eq coq-processed-end-function #'coq-eglot-position))
    (should (eq (key-binding (kbd "C-c C-a [")) #'coq-insert-as-in-next-command))
    (goto-marker "as")
    (run #'coq-eglot-goto-point)
    (let ((position (coq-eglot-position)))
      (run #'coq-insert-as-in-next-command)
      (should (search-forward-regexp
               "destruct l as \\[ *| *[[:alnum:]_']+ +[[:alnum:]_']+ *\\]\\."
               (line-end-position 2) t))
      (should (= (coq-eglot-position) position)))))

(ert-deftest coq-eglot-insert-as-changed ()
  "The \"as\" clause is not inserted if the command changed while waiting
for Coq: replaced, or given an \"as\" clause."
  (with-test-file
    (goto-marker "as")
    (run #'coq-eglot-goto-point)
    (dolist (replacement '("exact I." "destruct l as [|a b]."))
      (save-excursion
        (coq-insert-as-in-next-command)
        ;; before the answer
        (search-forward "destruct l.")
        (replace-match replacement t t)
        ;; the callbacks may change the match data
        (let ((start (copy-marker (match-beginning 0))))
          (wait-for-coq)
          (goto-char start)
          (should (looking-at (concat (regexp-quote replacement) "\n")))
          (replace-match "destruct l.\n" t t))))))

(ert-deftest coq-eglot-output-buffers-keys ()
  "The goals and response buffers have the common keys of the queries
and of the display, like in Proof General, not those of the insertions:
they insert in the script."
  (dolist (mode '(coq-eglot-goals-mode coq-eglot-response-mode))
    (with-temp-buffer
      (funcall mode)
      (dolist (binding '(("C-c C-a C-s" . coq-Show)
                         ("C-c C-a C-c" . coq-Check)
                         ("C-c C-a C-w" . coq-ask-printing-width)
                         ("C-c C-a n" . coq-unset-printing-notations)
                         ("C-c C-a r" . coq-store-response-win)
                         ("C-c C-a g" . coq-store-goals-win)
                         ("C-c C-n" . coq-eglot-assert-next-command)))
        (should (eq (key-binding (kbd (car binding))) (cdr binding))))
      (dolist (key '("C-c C-a [" "C-c C-a C-i" "C-c C-a C-t" "."))
        (should-not (eq (key-binding (kbd key))
                        (lookup-key coq-mode-map (kbd key)))))))
  ;; like in Proof General, kept for compatibility, now in both buffers
  (dolist (mode '(coq-eglot-goals-mode coq-eglot-response-mode))
    (with-temp-buffer
      (funcall mode)
      (should (eq (key-binding (kbd "C-c C-a C-r")) #'coq-store-response-win))
      (should (eq (key-binding (kbd "C-c C-a C-g")) #'coq-store-goals-win)))))

(ert-deftest coq-eglot-output-buffers-user-keys ()
  "The bindings of the user in `coq-mode-map' for the commands valid in
all buffers, common ones and `coq-eglot-all-buffers-commands', apply
also in the goals and response buffers set up afterwards.  Not those of
other commands."
  (unwind-protect
      (progn
        (define-key coq-mode-map (kbd "C-c y") #'coq-Check)
        (define-key coq-mode-map (kbd "C-M-<down>")
                    #'coq-eglot-assert-next-command)
        (define-key coq-mode-map (kbd "C-M-b") #'coq-eglot-process-buffer)
        (define-key coq-mode-map (kbd "<f7>")
                    #'coq-toggle-highlight-hyp-at-point)
        ;; depends on point in the script: not in the output buffers
        (define-key coq-mode-map (kbd "C-M-e") #'coq-eglot-goto-point)
        (dolist (mode '(coq-eglot-goals-mode coq-eglot-response-mode))
          (with-temp-buffer
            (funcall mode)
            (should (eq (key-binding (kbd "C-c y")) #'coq-Check))
            (should (eq (key-binding (kbd "C-M-<down>"))
                        #'coq-eglot-assert-next-command))
            (should (eq (key-binding (kbd "C-M-b")) #'coq-eglot-process-buffer))
            (should (eq (key-binding (kbd "<f7>"))
                        #'coq-toggle-highlight-hyp-at-point))
            (should-not (eq (key-binding (kbd "C-M-e"))
                            #'coq-eglot-goto-point)))))
    (dolist (key '("C-c y" "C-M-<down>" "C-M-b" "<f7>" "C-M-e"))
      (define-key coq-mode-map (kbd key) nil))
    ;; the output buffers set up afterwards no longer have them
    (coq-eglot--set-output-keys)))

(ert-deftest coq-eglot-frozen-copies ()
  "C-c C-a r and C-c C-a g copy the response and the goals at the top of
a buffer of their own, like in Proof General."
  (with-test-file
    (goto-marker "hello")
    (run #'coq-eglot-goto-point)
    (when (get-buffer coq-store-buffer-name)
      (kill-buffer coq-store-buffer-name))
    (unwind-protect
        ;; another frame: a window in batch mode, see
        ;; `coq-eglot-multiple-frames'
        (cl-letf (((symbol-function 'display-buffer-other-frame)
                   (lambda (buffer) (display-buffer buffer))))
          (with-current-buffer "*response*"
            (call-interactively (key-binding (kbd "C-c C-a r"))))
          (should (equal (buffer-text coq-store-buffer-name)
                         (concat "hello\n" (make-string 36 ?*))))
          (should (eq (buffer-local-value 'major-mode
                                          (get-buffer coq-store-buffer-name))
                      'coq-eglot-response-mode))
          (should (get-buffer-window coq-store-buffer-name))
          ;; from the script: the goals, above the response
          (call-interactively (key-binding (kbd "C-c C-a g")))
          (let ((text (buffer-text coq-store-buffer-name)))
            (should (string-match-p "\\`1 goal" text))
            (should (string-match-p "double n = n \\+ n" text))
            (should (string-match-p "^hello$" text)))
          ;; with a prefix argument, erased first
          (let ((current-prefix-arg '(4)))
            (call-interactively #'coq-store-response-win))
          (should (equal (buffer-text coq-store-buffer-name) "hello")))
      (when (get-buffer coq-store-buffer-name)
        (kill-buffer coq-store-buffer-name)))))

(ert-deftest coq-eglot-trace ()
  "With `coq-eglot-trace', the sentences, queries, errors and moves back
are written in the trace, the outputs in comments."
  (with-test-file
    (let ((coq-eglot-trace t))
      (unwind-protect
          (progn
            (goto-marker "hello")
            (run #'coq-eglot-goto-point)
            (let ((trace (buffer-text "*coq-trace*")))
              (should (string-match-p "\\`(\\* File eglot_test.v \\*)\n" trace))
              (should (string-match-p "^Definition double" trace))
              (should (string-match-p "^  - idtac \"hello\".\n(\\* hello \\*)\n(\\* 1 goal, 1 unfocused \\*)\\'"
                                      trace)))
            (run #'coq-eglot-assert-next-command)
            (should (string-match-p "^reflexivity.\n(\\* No more goals, 1 unfocused \\*)\\'"
                                    (buffer-text "*coq-trace*")))
            (query #'coq-eglot-run-query "Check double" '("Set Printing All"))
            (should (string-match-p "(\\* Query, with Set Printing All \\*)\nCheck double.\n(\\* double\n *: forall _ : nat, nat \\*)\\'"
                                    (buffer-text "*coq-trace*")))
            (goto-marker "statement")
            (run #'coq-eglot-goto-point)
            (should (string-match-p "(\\* Back to line 10 \\*)\\'"
                                    (buffer-text "*coq-trace*")))
            (goto-marker "error")
            (run #'coq-eglot-goto-point)
            (should (string-match-p "(\\* Failed: rewrite unknown_lemma. \\*)\n(\\* .*unknown_lemma.* \\*)\\'"
                                    (buffer-text "*coq-trace*")))
            ;; off
            (let ((size (length (buffer-text "*coq-trace*"))))
              (setq coq-eglot-trace nil)
              (run #'coq-eglot-retract-buffer)
              (should (= (length (buffer-text "*coq-trace*")) size))))
        (kill-buffer "*coq-trace*")))))

(ert-deftest coq-eglot-format-hyp ()
  "A hypothesis is formatted like Coq does: on one line if it fits,
otherwise the names on several lines and the type below them."
  (cl-letf (((coq-eglot--output-width coq-eglot--default-output) 21))  ; lines of 28 characters
    (should (equal (coq-eglot--format-hyp '(:names ["n" "m"] :ty "nat"))
                   "  n, m : nat"))
    (should (equal (coq-eglot--format-hyp
                    '(:names ["aaaaaaaa" "bbbbbbbb" "cccccccc"] :ty "nat"))
                   "  aaaaaaaa, bbbbbbbb,\n  cccccccc : nat"))
    ;; room for the comma and the colon
    (should (equal (coq-eglot--format-hyp
                    '(:names ["aaaaaaaa" "bbbbbbbb" "ccccccc"] :ty "nat"))
                   "  aaaaaaaa, bbbbbbbb,\n  ccccccc : nat"))
    (should (equal (coq-eglot--format-hyp
                    '(:names ["aaaaaaaaaaaa" "bbbbbbbbbbb"] :ty "nat"))
                   "  aaaaaaaaaaaa,\n  bbbbbbbbbbb : nat"))
    (should (equal (coq-eglot--format-hyp
                    '(:names ["H"] :ty "aaaaaaaa + bbbbbbbb =\ncccccccc"))
                   "  H :\n    aaaaaaaa + bbbbbbbb =\n    cccccccc"))
    (should (equal (coq-eglot--format-hyp
                    '(:names ["Hyp_name"] :ty "aaaaaaaa = bbbbbbbb"))
                   "  Hyp_name :\n    aaaaaaaa = bbbbbbbb"))
    (should (equal (coq-eglot--format-hyp
                    '(:names ["x"] :def "aaaaaaaa +\nbbbbbbbb" :ty "nat"))
                   "  x :=\n    aaaaaaaa +\n    bbbbbbbb\n    : nat"))
    ;; the properties for highlighting and folding
    (let ((text (coq-eglot--format-hyp '(:names ["H"] :ty "a =\nb"))))
      (should (equal (get-text-property 2 'coq-hyp text) '("H")))
      (should-not (get-text-property 2 'coq-hyp-body text))
      (should (get-text-property 3 'coq-hyp-body text))
      (should (get-text-property (1- (length text)) 'coq-hyp-body text)))))

(ert-deftest coq-eglot-format-conclusion-indented ()
  "The lines of a conclusion are indented, like in Coq, without the
space Coq leaves before some line breaks: it would wrap in a line as
wide as the window."
  (should (equal (coq-eglot--format-conclusion '(:ty "a /\\ \nb ") t)
                 "  a /\\\n  b\n"))
  (cl-letf (((coq-eglot--output-width coq-eglot--default-output) 21))
    (should (equal (coq-eglot--format-hyp '(:names ["H"] :ty "a /\\ \nb"))
                   "  H :\n    a /\\\n    b"))))

;;; Robustness of the connection

(ert-deftest coq-eglot-lsp-internals-exist ()
  "The internals of Eglot and jsonrpc we use exist, one of the
alternatives of each.  Needs no server."
  (dolist (entry coq-eglot-lsp--internals)
    (should (seq-some (lambda (symbol)
                        (if (eq (car entry) 'function)
                            (fboundp symbol)
                          (boundp symbol)))
                      (cdr entry)))))

(ert-deftest coq-eglot-lsp-internals-are-contained ()
  "Only coq-eglot-lsp.el refers to private Eglot and jsonrpc symbols."
  (let ((directory (file-name-directory (locate-library "coq-eglot-lsp"))))
    (dolist (file (directory-files directory t "\\`coq-eglot.*\\.el\\'"))
      (unless (string= (file-name-nondirectory file) "coq-eglot-lsp.el")
        (with-temp-buffer
          (insert-file-contents file)
          (should-not
           (re-search-forward
            (rx symbol-start (or "eglot--" "jsonrpc--")) nil t)))))))

(defmacro with-fake-server (output &rest body)
  "Run BODY with the server `fake-server', printing OUTPUT with --version."
  (declare (indent 1) (debug t))
  `(let* ((fake-server (make-temp-file "fake-lsp" nil ".sh"))
          (coq-eglot-lsp--server-versions (make-hash-table :test #'equal))
          (coq-eglot-server-program (list fake-server)))
     (unwind-protect
         (progn
           (with-temp-file fake-server
             (insert "#!/bin/sh\n" ,output))
           (set-file-modes fake-server #o755)
           ,@body)
       (delete-file fake-server))))

(ert-deftest coq-eglot-server-version-check ()
  "A server older than the minimal version is refused before starting,
an unknown version is not."
  (let ((enable-local-variables nil))
    (with-fake-server "echo 0.1.9"
      (should (equal (coq-eglot-lsp--server-version fake-server) "0.1.9"))
      (let ((err (should-error (coq-eglot-lsp--contact nil (cons 'transient "/tmp/"))
                               :type 'user-error)))
        (should (string-match-p "too old" (cadr err)))))
    (with-fake-server "echo 'coq-lsp 0.2.5+9.2'"
      (should (equal (coq-eglot-lsp--server-version fake-server) "0.2.5"))
      (should (coq-eglot-lsp--contact nil (cons 'transient "/tmp/"))))
    (with-fake-server "echo unknown"
      (should-not (coq-eglot-lsp--server-version fake-server))
      (should (coq-eglot-lsp--contact nil (cons 'transient "/tmp/"))))
    (with-fake-server "exit 1"
      (should-not (coq-eglot-lsp--server-version fake-server))
      (should (coq-eglot-lsp--contact nil (cons 'transient "/tmp/"))))))

(ert-deftest coq-eglot-server-version-cached ()
  "The server is run once with --version."
  (with-fake-server "echo 0.2.5"
    (let ((calls 0))
      (cl-letf* ((orig (symbol-function 'process-lines))
                 ((symbol-function 'process-lines)
                  (lambda (&rest args) (cl-incf calls) (apply orig args))))
        (coq-eglot-lsp--server-version fake-server)
        (coq-eglot-lsp--server-version fake-server)
        (should (= calls 1))))))

(ert-deftest coq-eglot-load-path-server-program-args ()
  "The -R and -Q of `coq-eglot-server-program' are not compared with
the load path of the buffer."
  (let ((process (make-process :name "fake-coq-lsp" :noquery t
                               :command '("sleep" "30" "-R" "a,A"
                                          "-Q" "b,B" "-R" "c,C")))
        (coq-eglot-server-program '("sleep" "30" "-R" "a,A" "-Q" "b,B")))
    (unwind-protect
        (cl-letf (((symbol-function 'jsonrpc--process) (lambda (_) process)))
          (should (equal (coq-eglot-lsp--server-load-path-args nil)
                         '("-R" "c,C")))
          (let ((coq-eglot-server-program '("sleep" "30")))
            (should (equal (coq-eglot-lsp--server-load-path-args nil)
                           '("-R" "a,A" "-Q" "b,B" "-R" "c,C")))))
      (delete-process process))))

(ert-deftest coq-eglot-load-path-invalid ()
  "An invalid `coq-load-path' is a user error naming it."
  (let ((coq-eglot-server-program '("coq-lsp"))
        (coq-load-path '(42)))
    (with-programs '("coq-lsp")
      (let ((err (should-error (coq-eglot-lsp--contact nil (cons 'transient "/tmp/"))
                               :type 'user-error)))
        (should (string-match-p "coq-load-path" (cadr err)))))))

(ert-deftest coq-eglot-load-path-comma ()
  "A comma in a directory is a user error: coq-lsp splits -R DIR,LP there."
  (let ((coq-load-path '((rec "lib,x" "Lib"))))
    (should-error (coq-eglot-lsp-load-path-args) :type 'user-error))
  (should (equal (coq-eglot-lsp--logical-binding "/tmp/ab/" "Lib")
                 "/tmp/ab,Lib")))

(ert-deftest coq-eglot-lsp-cancel-one-request ()
  "A request context cancels only its JSON-RPC request."
  (let ((context (coq-eglot-lsp--make-context :proof/goals 1))
        notified)
    (setf (coq-eglot-lsp-context-id context) 42)
    (cl-letf (((symbol-function 'coq-eglot-lsp-current-server)
               (lambda () 'server))
              ((symbol-function 'jsonrpc-notify)
               (lambda (server method params)
                 (setq notified (list server method params)))))
      (coq-eglot-lsp-cancel-request context)
      (should (equal notified '(server :$/cancelRequest (:id 42)))))))

(ert-deftest coq-eglot-compile-hooks-cheap ()
  "The hooks of the outdated libraries schedule nothing if no buffer
has compiled Require sentences."
  (let (scheduled)
    (cl-letf (((symbol-function 'run-at-time)
               (lambda (&rest _) (setq scheduled t))))
      (with-temp-buffer
        (setq buffer-file-name "/tmp/not-a-real-file.v")
        (unwind-protect
            (progn
              (should-not (coq-eglot-compile--any-loaded-p))
              (coq-eglot-compile--file-modified)
              (should-not scheduled)
              (setq coq-eglot-compile--loaded (list 'overlay))
              (should (coq-eglot-compile--any-loaded-p))
              (coq-eglot-compile--file-modified)
              (should scheduled))
          (setq coq-eglot-compile--loaded nil
                buffer-file-name nil))))))

;; The events of the adapter, without server

(defmacro with-lsp-text (text &rest body)
  "Run BODY in a temporary buffer containing TEXT."
  (declare (indent 1) (debug t))
  `(with-temp-buffer
     (insert ,text)
     ,@body))

(defun lsp-range (l1 c1 l2 c2)
  "The LSP range from line L1 column C1 to line L2 column C2."
  (list :start (list :line l1 :character c1)
        :end (list :line l2 :character c2)))

(ert-deftest coq-eglot-lsp-answer-normalized ()
  "A goals answer of coq-lsp becomes a `coq-eglot-lsp-answer'.
With buffer positions for the sentence and messages with severities."
  (with-lsp-text "Lemma a : True.\nProof.\n"
    (let* ((context (coq-eglot-lsp--make-context :proof/goals 20))
           (answer (coq-eglot-lsp--answer
                    (list :textDocument (list :uri "file:///a.v" :version 7)
                          :range (lsp-range 1 0 1 6)
                          :goals '(:goals [] :stack [] :shelf [] :given_up [])
                          :messages (vector '(:level 3 :text "printed")
                                            '(:level 2 :text "careful")
                                            "plain")
                          :error "Oops.")
                    context 80 '("Set Printing All"))))
      (should (eq (coq-eglot-lsp-answer-context answer) context))
      (should (= (coq-eglot-lsp-answer-version answer) 7))
      (should (equal (coq-eglot-lsp-answer-sentence answer) '(17 . 23)))
      (should (equal (buffer-substring 17 23) "Proof."))
      (should (equal (mapcar #'coq-eglot-lsp-message-severity
                             (coq-eglot-lsp-answer-messages answer))
                     '(notice warning nil)))
      (should (equal (coq-eglot--format-messages
                      (coq-eglot-lsp-answer-messages answer))
                     "printed\ncareful\nplain"))
      (should (equal (coq-eglot-lsp-answer-error answer) "Oops."))
      (should (= (coq-eglot-lsp-answer-printing-width answer) 80))
      (should (equal (coq-eglot-lsp-answer-printing-flags answer)
                     '("Set Printing All")))
      (should-not (coq-eglot-lsp--answer nil context nil nil)))))

(ert-deftest coq-eglot-lsp-failure-normalized ()
  "Failures say whether the request was cancelled, and keep its context."
  (let ((context (coq-eglot-lsp--make-context :proof/goals 1)))
    (dolist (code '(-32800 -32001))
      (should (coq-eglot-lsp-failure-cancelled
               (coq-eglot-lsp--failure (list :code code :message "x")
                                       context))))
    (let ((failure (coq-eglot-lsp--failure (list :code -32603 :message "Bad")
                                           context)))
      (should-not (coq-eglot-lsp-failure-cancelled failure))
      (should (equal (coq-eglot-lsp-failure-message failure) "Bad"))
      (should (eq (coq-eglot-lsp-failure-context failure) context)))))

(ert-deftest coq-eglot-lsp-diagnostic-normalized ()
  "A diagnostic has the range of its message, and of its sentence if given."
  (with-lsp-text "Lemma a : True.\nProof. exact foo.\n"
    (let ((diag (coq-eglot-lsp--diagnostic
                 (list :range (lsp-range 1 13 1 16) :severity 1
                       :message "The reference foo was not found."
                       :data (list :sentenceRange (lsp-range 1 7 1 17))))))
      (should (equal (buffer-substring (coq-eglot-lsp-diagnostic-start diag)
                                       (coq-eglot-lsp-diagnostic-end diag))
                     "foo"))
      (should (eq (coq-eglot-lsp-diagnostic-severity diag) 'error))
      (let ((sentence (coq-eglot-lsp-diagnostic-sentence diag)))
        (should (equal (buffer-substring (car sentence) (cdr sentence))
                       "exact foo."))))
    (should-not (coq-eglot-lsp-diagnostic-sentence
                 (coq-eglot-lsp--diagnostic
                  (list :range (lsp-range 0 0 0 5) :severity 2
                        :message "Warning."))))))

;; Never waiting for the server

(ert-deftest coq-eglot-no-synchronous-request ()
  "Moving forward and back, failing, showing the goals: no command waits
for the server."
  (with-test-file
    (cl-letf (((symbol-function 'jsonrpc-request)
               (lambda (&rest _) (error "Synchronous request"))))
      (goto-marker "split")
      (run #'coq-eglot-goto-point)
      (should (position-at-marker-p "split"))
      (run #'coq-eglot-undo-last-command)
      (goto-marker "definition")
      (run #'coq-eglot-goto-point)
      (should (position-at-marker-p "definition"))
      ;; up to the error
      (goto-marker "error")
      (run #'coq-eglot-goto-point)
      (should (position-at-marker-p "before error"))
      (run #'coq-eglot-show-goals)
      (should (string-match-p "1 goal" (buffer-text "*goals*")))
      (run #'coq-eglot-retract-buffer)
      (run #'coq-eglot-assert-next-command)
      (should (position-at-marker-p "definition")))))

(ert-deftest coq-eglot-move-back-at-once ()
  "Moving back moves the proof position at once, to the last known
sentence; the server says later where the sentence before is."
  (with-test-file
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (let ((before (coq-eglot-position)))
      (goto-marker "statement")
      (coq-eglot-goto-point)
      ;; at once, before any answer
      (should (< (coq-eglot-position) before))
      (wait-for-coq)
      (should (position-at-marker-p "statement")))))

(ert-deftest coq-eglot-goals-kept-two-sentences ()
  "The goals are kept for the proof position and the sentence before,
the messages for all the sentences."
  (with-test-file
    (dotimes (_ 4) (run #'coq-eglot-assert-next-command))
    (let ((sentences (coq-eglot-session-sentences)))
      (should (= (length sentences) 4))
      (should (equal (mapcar (lambda (sentence)
                               (and (coq-eglot-session-sentence-answer sentence)
                                    t))
                             sentences)
                     '(t t nil nil)))
      ;; the message of the definition, the oldest one
      (should (equal (mapcar #'coq-eglot-lsp-message-text
                             (coq-eglot-session-sentence-messages
                              (car (last sentences))))
                     '("double is defined"))))))

(ert-deftest coq-eglot-position-hook-on-change ()
  "The position hook runs when what the overlays display changes, not
when they are updated again with nothing new."
  (with-test-file
    (run #'coq-eglot-assert-next-command)
    (let ((ran 0))
      (add-hook 'coq-eglot-position-hook (lambda () (cl-incf ran)) nil t)
      (coq-eglot--update-overlays)
      (coq-eglot--update-overlays)
      (should (= ran 0))
      (run #'coq-eglot-assert-next-command)
      (should (> ran 0)))))

(ert-deftest coq-eglot-busy-indicator ()
  "The mode line shows an ellipsis while the buffer waits for the server."
  (with-file "eglot_slow.v"
    (force-new-check)
    (should-not (string-search "…" (coq-eglot--lighter)))
    (coq-eglot-process-buffer)
    (should (string-search "…" (coq-eglot--lighter)))
    (wait-for-coq)
    (should-not (string-search "…" (coq-eglot--lighter)))))

(ert-deftest coq-eglot-move-back-exact-at-once ()
  "After one check of several sentences, moving back goes at once to the
right sentence: the server told the bounds of all the sentences it
executed."
  (with-test-file
    (skip-unless-execinfo)
    (force-new-check)
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    ;; the bounds of each sentence are known, not only of the last one
    (goto-marker "statement")
    (should (= (coq-eglot-sentences-previous-end (point)) (point)))
    (should (coq-eglot-sentences-range-ending-at (point)))
    (coq-eglot-goto-point)
    ;; before any answer
    (should (position-at-marker-p "statement"))))

;; Connecting without waiting

(ert-deftest coq-eglot-connect-without-waiting ()
  "After a restart, a command does not wait for the server to connect:
its requests wait, and are sent once connected."
  (with-test-file
    (coq-eglot-restart-server)
    (goto-marker "split")
    (let ((start (float-time)))
      (coq-eglot-goto-point)
      (should (< (- (float-time) start) 0.5)))
    (should (coq-eglot-busy-p))
    (wait-for-coq)
    (should (position-at-marker-p "split"))))

(ert-deftest coq-eglot-connection-failed ()
  "If the server does not connect in time, the command stops and says so:
the target is forgotten, the buffer is not busy."
  (with-file (expand-file-name "eglot_compile_c.v" compile-directory)
    (unwind-protect
        (progn
          (coq-eglot-lsp-shutdown)
          ;; a server that knows its version, but never answers
          (with-fake-server "[ \"$1\" = --version ] && echo 0.2.5 || sleep 30"
            (let ((messages nil))
              (cl-letf* ((message-fn (symbol-function 'message))
                         ((symbol-function 'message)
                          (lambda (format &rest args)
                            (when format
                              (push (apply #'format-message format args)
                                    messages))
                            (apply message-fn format args))))
                (goto-char (point-max))
                (let ((eglot-connect-timeout 1))
                  (coq-eglot-goto-point)
                  ;; the Eglot of Emacs 29 signals its own timeout
                  ;; from a timer: only a message, unless debugging
                  ;; errors, as ERT does
                  (let ((debug-on-error nil))
                    (should (wait-until (lambda () (not (coq-eglot-busy-p)))
                                        10))))
                (should-not (coq-eglot-checking-p))
                (should (seq-find (lambda (text)
                                    (string-match-p "did not start" text))
                                  messages))))))
      (coq-eglot-lsp-kill-connecting-servers)
      (coq-eglot-lsp-shutdown))))

;; Errors and stops while connecting

(ert-deftest coq-eglot-deferred-send-error ()
  "A request failing to be sent once the server connects gets its error;
the other requests waiting are sent all the same."
  (with-temp-buffer
    (let ((connected nil) (sent nil) (failures nil) (answers nil))
      (cl-letf (((symbol-function 'coq-eglot-lsp-connect)
                 (lambda () (and connected 'server)))
                ((symbol-function 'coq-eglot-lsp-current-server)
                 (lambda () (and connected 'server)))
                ((symbol-function 'coq-eglot-lsp-connecting-servers)
                 (lambda () (and (not connected) '(connecting))))
                ((symbol-function 'eglot--signal-textDocument/didChange)
                 #'ignore)
                ((symbol-function 'jsonrpc--async-request-1)
                 (lambda (_server method _params &rest args)
                   (push method sent)
                   (funcall (plist-get args :success-fn) 'answer)
                   (list (length sent)))))
        (coq-eglot-lsp--async-request
         1 :first (lambda () (error "No parameters"))
         (lambda (answer _context) (push answer answers))
         (lambda (failure) (push failure failures)))
        (coq-eglot-lsp--async-request
         1 :second (lambda () nil)
         (lambda (answer _context) (push answer answers))
         (lambda (failure) (push failure failures)))
        (should (coq-eglot-lsp-connecting-p))
        (should-not sent)
        (setq connected t)
        (should (wait-until (lambda () (and failures answers)) 2))
        (should (equal sent '(:second)))
        (should (equal answers '(answer)))
        (should (= (length failures) 1))
        (should (string-match-p "No parameters"
                                (coq-eglot-lsp-failure-message (car failures))))
        (should-not (coq-eglot-lsp-connecting-p))))))

(ert-deftest coq-eglot-connect-timeout-nil ()
  "Without `eglot-connect-timeout', the requests wait for the server as
long as it connects, as Eglot does; with it, they fail after it."
  (with-temp-buffer
    (let ((connected nil) (sent nil) (failures nil) request-success)
      (cl-letf (((symbol-function 'coq-eglot-lsp-connect)
                 (lambda () (and connected 'server)))
                ((symbol-function 'coq-eglot-lsp-current-server)
                 (lambda () (and connected 'server)))
                ((symbol-function 'coq-eglot-lsp-connecting-servers)
                 (lambda () (and (not connected) '(connecting))))
                ((symbol-function 'eglot--signal-textDocument/didChange)
                 #'ignore)
                ((symbol-function 'jsonrpc--async-request-1)
                 (lambda (_server method _params &rest args)
                   (push method sent)
                   (setq request-success (plist-get args :success-fn))
                   (list 1))))
        (let ((request (lambda (method)
                         (coq-eglot-lsp--async-request
                          1 method #'ignore #'ignore
                          (lambda (failure) (push failure failures)))))
              ;; started long ago
              (start (- (float-time) 1000)))
          (funcall request :first)
          (let ((eglot-connect-timeout nil))
            (coq-eglot-lsp--watch-connection (current-buffer) start)
            (accept-process-output nil 0.1)
            (should (coq-eglot-lsp-connecting-p))
            (should-not failures)
            (setq connected t)
            (coq-eglot-lsp--watch-connection (current-buffer) start)
            (should (equal sent '(:first)))
            (should-not (coq-eglot-lsp-connecting-p))
            ;; The scheduler sends the next interactive request only after
            ;; the first one has answered.  The fake transport must model
            ;; that answer before the second connection scenario.
            (funcall request-success 'answer)
            (should (wait-until
                     (lambda () (not coq-eglot-lsp--active-requests))
                     2)))
          ;; with a timeout
          (setq connected nil)
          (funcall request :second)
          (let ((eglot-connect-timeout 30))
            (coq-eglot-lsp--watch-connection (current-buffer) start)
            (should (wait-until (lambda () failures) 2))
            (should (equal sent '(:first)))))
        (coq-eglot-lsp--forget-waiting)))))

(ert-deftest coq-eglot-deferred-send-error-stops-check ()
  "If the request of a check cannot be sent once the server connects, the
check stops: the buffer is not busy."
  (with-test-file
    (coq-eglot-restart-server)
    (goto-marker "split")
    (coq-eglot-goto-point)
    (should (coq-eglot-lsp-connecting-p))
    (cl-letf (((symbol-function 'eglot--signal-textDocument/didChange)
               (lambda () (error "Cannot send"))))
      (should (wait-until (lambda () (not (coq-eglot-busy-p))) 30)))
    (should-not (coq-eglot-checking-p))))

(defmacro with-connecting-server (&rest body)
  "Run BODY in eglot_compile_c.v, with a server that never connects."
  (declare (indent 0) (debug t))
  `(with-file (expand-file-name "eglot_compile_c.v" compile-directory)
     (unwind-protect
         (progn
           (coq-eglot-lsp-shutdown)
           (with-fake-server "[ \"$1\" = --version ] && echo 0.2.5 || sleep 30"
             (goto-char (point-max))
             (coq-eglot-goto-point)
             (should (coq-eglot-lsp-connecting-servers))
             ,@body))
       (coq-eglot-lsp-kill-connecting-servers)
       (coq-eglot-lsp-shutdown))))

(ert-deftest coq-eglot-exit-while-connecting ()
  "Exiting while the server connects stops it: it never becomes the
server of the buffer."
  (with-connecting-server
    (coq-eglot-exit)
    (should-not (coq-eglot-lsp-connecting-servers))
    (should-not (coq-eglot-busy-p))
    (accept-process-output nil 0.3)
    (should-not (coq-eglot-lsp-current-server))
    (should-not (coq-eglot-lsp-connecting-servers))))

(ert-deftest coq-eglot-restart-while-connecting ()
  "Restarting while the server connects starts another one."
  (with-connecting-server
    (let ((old (coq-eglot-lsp-connecting-servers)))
      (coq-eglot-restart-server)
      (let ((new (coq-eglot-lsp-connecting-servers)))
        (should new)
        (should-not (seq-intersection old new))
        (should-not (seq-some #'jsonrpc-running-p old))))))

(ert-deftest coq-eglot-exit-while-connecting-two-buffers ()
  "Exiting while the server connects stops it for all the buffers of the
project: those waiting for it are not busy anymore, and say nothing."
  (with-connecting-server
    (let ((other (find-file-noselect
                  (expand-file-name "eglot_compile_b.v" compile-directory)))
          (messages nil))
      (unwind-protect
          (progn
            (with-current-buffer other
              (goto-char (point-max))
              (coq-eglot-goto-point)
              (should (coq-eglot-busy-p)))
            (cl-letf* ((message-fn (symbol-function 'message))
                       ((symbol-function 'message)
                        (lambda (format &rest args)
                          (when format
                            (push (apply #'format-message format args)
                                  messages))
                          (apply message-fn format args))))
              (coq-eglot-exit)
              (accept-process-output nil 0.3))
            (with-current-buffer other
              (should-not (coq-eglot-busy-p))
              (should-not (coq-eglot-checking-p)))
            (should-not (seq-find (lambda (text)
                                    (string-match-p "did not start" text))
                                  messages)))
        (with-current-buffer other (set-buffer-modified-p nil))
        (kill-buffer other)))))

;; The session, with the server

(ert-deftest coq-eglot-session-error-sentence ()
  "The diagnostic of an error gives the range of its sentence."
  (with-test-file
    (goto-marker "error")
    (run #'coq-eglot-goto-point)
    (let ((diag (seq-find (lambda (diag)
                            (eq (coq-eglot-lsp-diagnostic-severity diag) 'error))
                          (mapcar #'cdr coq-eglot-session--diagnostics))))
      (should diag)
      (let ((sentence (coq-eglot-lsp-diagnostic-sentence diag)))
        (should sentence)
        (should (equal (buffer-substring (car sentence) (cdr sentence))
                       "rewrite unknown_lemma."))))))

;; The session, without server

(defvar test-version 0
  "The version of the document the fake server knows, see `with-session'.")

(defmacro with-session (text &rest body)
  "Run BODY in a temporary buffer containing TEXT, with a session.
The version the server knows is `test-version', starting at 1: BODY
increments it to send the changes."
  (declare (indent 1) (debug t))
  `(with-temp-buffer
     (insert ,text)
     (let ((test-version 1))
       (coq-eglot-session-start (lambda () test-version))
       ,@body)))

(defun edit-at (pos)
  "Insert a space at POS."
  (save-excursion (goto-char pos) (insert " ")))

(ert-deftest coq-eglot-session-validity ()
  "What the server said about a version is valid before the first
position edited since, the smallest one if several editions."
  (with-session (make-string 100 ?a)
    ;; not edited since version 1
    (should (coq-eglot-session-valid-p 1 90))
    (edit-at 30)
    (should (coq-eglot-session-valid-p 1 29))
    (should-not (coq-eglot-session-valid-p 1 30))
    ;; the changes are sent: version 2
    (setq test-version 2)
    (should (coq-eglot-session-valid-p 2 90))
    ;; an edition after, then one before: the smallest counts
    (edit-at 50)
    (edit-at 10)
    (should (coq-eglot-session-valid-p 2 9))
    (should-not (coq-eglot-session-valid-p 2 20))
    (should-not (coq-eglot-session-valid-p 1 20))
    (should (coq-eglot-session-valid-p 1 9))
    ;; a version never dated, between two dated ones, gets the date of
    ;; the older one: less valid, never more
    (setq test-version 4)
    (edit-at 60)
    (should-not (coq-eglot-session-valid-p 3 20))
    (should (coq-eglot-session-valid-p 3 9))
    (should (coq-eglot-session-valid-p 4 59))
    (should-not (coq-eglot-session-valid-p 4 60))
    ;; a version newer than all the dated ones was not edited since
    (should (coq-eglot-session-valid-p 5 90))
    (should (coq-eglot-session-valid-p 4 59))
    (should-not (coq-eglot-session-valid-p 4 60))
    ;; no version: nothing valid
    (should-not (coq-eglot-session-valid-p nil 1))))

(ert-deftest coq-eglot-session-edition-at-beginning ()
  "An edition at the beginning makes nothing valid about the versions
before it, even what was before other editions."
  (with-session (make-string 100 ?a)
    (edit-at 30)
    (setq test-version 2)
    (edit-at (point-min))
    (setq test-version 3)
    (edit-at 50)
    (should-not (coq-eglot-session-valid-p 1 1))
    (should-not (coq-eglot-session-valid-p 2 1))
    (should (coq-eglot-session-valid-p 3 49))
    (should-not (coq-eglot-session-valid-p 3 50))
    ;; an edition at the beginning covers all the points after it
    (should (= (length coq-eglot-session--points) 2))
    ;; the server opens the document again: versions from 0
    (coq-eglot-session-reset)
    (setq test-version 0)
    (should (coq-eglot-session-valid-p 0 90))))

(ert-deftest coq-eglot-session-merged-editions ()
  "The editions in the same sentence are one point, the latest date wins:
typing a sentence does not make one point per character.  Exact at the
ends of sentences."
  (with-session "Lemma a : True. Proof. idtac. Qed."
    (setq coq-eglot-session-sentence-end-function
          (lambda (pos)
            (save-excursion (goto-char pos)
                            (if (search-forward "." nil t) (point)
                              (point-max)))))
    (let ((proof-end (save-excursion (goto-char (point-min))
                                     (search-forward "Proof.")
                                     (point))))
      ;; typing in "idtac."
      (dolist (offset '(1 2 3 4))
        (edit-at (+ proof-end offset)))
      (should (= (length coq-eglot-session--points) 1))
      ;; the sentences before are still valid, not the edited one
      (should (coq-eglot-session-valid-p 1 proof-end))
      (should-not (coq-eglot-session-valid-p 1 (+ proof-end 10)))
      ;; after the merge, still valid up to the end of Proof.
      (setq test-version 2)
      (edit-at (+ proof-end 8))
      (should (= (length coq-eglot-session--points) 1))
      (should (coq-eglot-session-valid-p 2 proof-end))
      (should-not (coq-eglot-session-valid-p 2 (+ proof-end 10)))
      ;; an edition in another sentence is another point
      (edit-at 3)
      (should (= (length coq-eglot-session--points) 1))
      (setq test-version 3)
      (let ((last (- (point-max) 1)))
        (edit-at last)
        (should (= (length coq-eglot-session--points) 2))
        (should (coq-eglot-session-valid-p 3 (1- last)))
        (should-not (coq-eglot-session-valid-p 3 last))))))

(defun diagnostic (start end &optional severity)
  "A diagnostic from START to END, an error by default."
  (coq-eglot-lsp--make-diagnostic start end (or severity 'error) "msg" nil))

(ert-deftest coq-eglot-session-diagnostics ()
  "The diagnostics are a snapshot, kept where still valid.
The first error between two positions, warnings do not count."
  (with-session (make-string 100 ?a)
    (should (coq-eglot-session-receive-diagnostics
             (coq-eglot-lsp--make-diagnostics
              1 (list (diagnostic 41 44) (diagnostic 30 33)
                      (diagnostic 1 6 'warning)))))
    (should (equal (coq-eglot-session-error-range 1 100) '(30 . 33)))
    (should (equal (coq-eglot-session-error-range 31 100) '(41 . 44)))
    (should-not (coq-eglot-session-error-range 1 30))
    ;; an edition forgets those after it
    (edit-at 40)
    (should-not (coq-eglot-session-error-range 31 100))
    (should (equal (coq-eglot-session-error-range 1 100) '(30 . 33)))
    ;; a late snapshot of version 1 is kept only before the edition
    (should (coq-eglot-session-receive-diagnostics
             (coq-eglot-lsp--make-diagnostics
              1 (list (diagnostic 20 22) (diagnostic 60 62)))))
    (should (equal (coq-eglot-session-error-range 1 100) '(20 . 22)))
    (should-not (coq-eglot-session-error-range 21 100))
    ;; a snapshot of version 2 replaces it, even empty
    (setq test-version 2)
    (should (coq-eglot-session-receive-diagnostics
             (coq-eglot-lsp--make-diagnostics 2 nil)))
    (should-not (coq-eglot-session-error-range 1 100))
    ;; an older one is ignored
    (should-not (coq-eglot-session-receive-diagnostics
                 (coq-eglot-lsp--make-diagnostics
                  1 (list (diagnostic 20 22)))))
    (should-not (coq-eglot-session-error-range 1 100))))

(ert-deftest coq-eglot-diagnostic-stops-running-check ()
  "The first error is found from the fixed start, behind current progress."
  (with-session "A. B. C."
    (setq coq-eglot-session-sentence-end-function
          (lambda (_pos) (point-max)))
    (let* ((work (coq-eglot-session-start-work))
           (context (coq-eglot-lsp--make-context
                     :petanque/get_state_at_pos 8))
           cancelled failed traced)
      (coq-eglot-session-set-target (point-max))
      (setq coq-eglot--work-context context
            coq-eglot--work-start 1)
      (let ((event
             (coq-eglot-lsp--make-diagnostics
              1 (list (coq-eglot-lsp--make-diagnostic
                       5 5 'error "bad B" '(4 . 6))))))
        (cl-letf (((symbol-function 'coq-eglot-lsp-cancel-request)
                   (lambda (request) (setq cancelled request)))
                  ((symbol-function 'coq-eglot--update-overlays) #'ignore)
                  ((symbol-function 'coq-eglot--trace-check)
                   (lambda (start end answer)
                     (setq traced (list start end answer))))
                  ((symbol-function 'coq-eglot-position) (lambda () 7))
                  ((symbol-function 'coq-eglot--fail)
                   (lambda (start end text &optional _answer)
                     (setq failed (list start end text)))))
          ;; The real hook has this order: the session, then the interface.
          (coq-eglot-session-observe event)
          (coq-eglot--observe event))
        (should (eq cancelled context))
        (should (equal traced '(1 4 nil)))
        (should (equal failed '(4 6 "bad B")))
        (should-not (coq-eglot-session-work-p work))
        (should-not (coq-eglot-session-target))
        (should-not coq-eglot--work-context)
        (should-not coq-eglot--work-start)))))

(ert-deftest coq-eglot-known-error-sends-no-operation ()
  "The planner stops at a valid recorded error without asking the server."
  (with-session "A. B. C."
    (setq coq-eglot-session-sentence-start-function
          (lambda (pos) (and (< pos (point-max)) pos)))
    (setq coq-eglot-session-sentence-end-function
          (lambda (_pos) (point-max)))
    (coq-eglot-session-receive-diagnostics
     (coq-eglot-lsp--make-diagnostics
      1 (list (coq-eglot-lsp--make-diagnostic
               5 5 'error "known bad B" '(4 . 6)))))
    (coq-eglot-session-set-target (point-max))
    (let (sent failed)
      (cl-letf (((symbol-function 'coq-eglot--step)
                 (lambda (&rest _) (setq sent t)))
                ((symbol-function 'coq-eglot--advance)
                 (lambda (&rest _) (setq sent t)))
                ((symbol-function 'coq-eglot--update-overlays) #'ignore)
                ((symbol-function 'coq-eglot--trace-check) #'ignore)
                ((symbol-function 'coq-eglot--fail)
                 (lambda (start end text &optional _answer)
                   (setq failed (list start end text)))))
        (coq-eglot--plan))
      (should-not sent)
      (should (equal failed '(4 6 "known bad B")))
      (should-not (coq-eglot-session-target)))))

(ert-deftest coq-eglot-document-error-stops-running-check ()
  "An error without a sentence range also stops a pending target request."
  (with-session "A. B. C."
    (setq coq-eglot-session-sentence-end-function
          (lambda (_pos) (point-max)))
    (let* ((work (coq-eglot-session-start-work))
           (context (coq-eglot-lsp--make-context
                     :petanque/get_state_at_pos 8))
           cancelled shown highlighted)
      (coq-eglot-session-set-target (point-max))
      (setq coq-eglot--work-context context
            coq-eglot--work-start 1)
      (let ((event
             (coq-eglot-lsp--make-diagnostics
              1 (list (coq-eglot-lsp--make-diagnostic
                       1 3 'error "bad document" nil)))))
        (cl-letf (((symbol-function 'coq-eglot-lsp-cancel-request)
                   (lambda (request) (setq cancelled request)))
                  ((symbol-function 'coq-eglot--update-overlays) #'ignore)
                  ((symbol-function 'coq-eglot--show-error)
                   (lambda (text) (setq shown text)))
                  ((symbol-function 'coq-eglot--highlight-error)
                   (lambda (start end) (setq highlighted (cons start end)))))
          (coq-eglot-session-observe event)
          (coq-eglot--observe event))
        (should (eq cancelled context))
        (should (equal shown "bad document"))
        (should (equal highlighted '(1 . 3)))
        (should-not (coq-eglot-session-work-p work))
        (should-not (coq-eglot-session-target))))))

(defmacro with-planner (text &rest body)
  "Run BODY with a session on TEXT, sentences ending with a dot."
  (declare (indent 1) (debug t))
  `(with-session ,text
     (setq coq-eglot-session-sentence-start-function
           (lambda (pos)
             (save-excursion
               (goto-char pos)
               (skip-chars-forward " \n")
               (and (< (point) (point-max)) (point)))))
     (setq coq-eglot-session-sentence-end-function
           (lambda (pos)
             (save-excursion
               (goto-char pos)
               (if (search-forward "." nil t) (point) (point-max)))))
     ,@body))

(ert-deftest coq-eglot-step-separates-check-from-final-goals ()
  "A one-sentence step starts with the same resumable check as a distant one."
  (with-planner "A."
    (let (checked)
      (cl-letf (((symbol-function 'coq-eglot-position) (lambda () 1))
                ((symbol-function 'coq-eglot--update-overlays) #'ignore)
                ((symbol-function 'coq-eglot--compile-then)
                 (lambda (_work _start _end continue) (funcall continue nil)))
                ((symbol-function 'coq-eglot--check)
                 (lambda (work before start last failed)
                   (setq checked (list work before start last failed)))))
        (coq-eglot--step 1))
      (should (coq-eglot-session-work-p (car checked)))
      (should (equal (cdr checked) '(1 1 2 nil))))))

(ert-deftest coq-eglot-session-planner ()
  "The planner starts one operation at a time toward the target: one
sentence, or a check of several, and forgets the target once reached."
  (with-planner "A. B. C."
    ;; nothing asked
    (should-not (coq-eglot-session-next-action))
    ;; inside the first sentence: one step
    (coq-eglot-session-set-target 2)
    (should (equal (coq-eglot-session-target-end) 3))
    (should (equal (coq-eglot-session-next-action) '(step 1)))
    ;; further: a check
    (coq-eglot-session-set-target 9)
    (should (equal (coq-eglot-session-next-action) '(check 1 9)))
    ;; nothing while an operation runs
    (let ((work (coq-eglot-session-start-work)))
      (should (coq-eglot-session-working-p))
      (should-not (coq-eglot-session-next-action))
      (coq-eglot-session-finish-work work))
    ;; the first two sentences processed: one step left
    (coq-eglot-session-add-sentence 6 nil)
    (should (equal (coq-eglot-session-next-action) '(step 7)))
    ;; reached: the target is forgotten
    (coq-eglot-session-add-sentence 9 nil)
    (should-not (coq-eglot-session-next-action))
    (should-not (coq-eglot-session-target))))

(ert-deftest coq-eglot-session-stale-work ()
  "An operation stopped, or replaced by another, is no longer running:
what arrives for it is ignored."
  (with-planner "A. B."
    (let ((work (coq-eglot-session-start-work)))
      (coq-eglot-session-stop-work)
      (should-not (coq-eglot-session-work-p work))
      (let ((other (coq-eglot-session-start-work)))
        (should-not (coq-eglot-session-work-p work))
        (should (coq-eglot-session-work-p other))
        ;; finishing a stale operation does not finish the running one
        (coq-eglot-session-finish-work work)
        (should (coq-eglot-session-working-p))))))

(ert-deftest coq-eglot-goals-asked-again-after-edition ()
  "Goals asked again after an edition are asked to the server again: the
answer of the request sent before would not be valid."
  (with-session "Lemma a : True. Proof. idtac. Qed."
    (let ((sent 0))
      (cl-letf (((symbol-function 'coq-eglot-lsp-goals-options) #'ignore)
                ((symbol-function 'coq-eglot-lsp-goals-async)
                 (lambda (&rest _) (cl-incf sent))))
        (coq-eglot--ask-goals 10 #'ignore)
        ;; the same question: the same request
        (coq-eglot--ask-goals 10 #'ignore)
        (should (= sent 1))
        ;; after an edition, even after the position: a new request
        (edit-at 12)
        (coq-eglot--ask-goals 10 #'ignore)
        (should (= sent 2))))))

(ert-deftest coq-eglot-query-latest-wins ()
  "Only the answer of the last query sent is displayed, even if an older
one comes after it.  The queries make the buffer busy."
  (with-test-file
    (run #'coq-eglot-assert-next-command)
    (let ((answers nil))
      (cl-letf (((symbol-function 'coq-eglot-lsp-query-async)
                 (lambda (_pos _command on-success _on-error)
                   (push on-success answers))))
        (coq-eglot-run-query "Check 1")
        (coq-eglot-run-query "Check 2")
        (should (coq-eglot-busy-p))
        ;; the second answers first, then the first
        (funcall (car answers) '("second"))
        (funcall (cadr answers) '("first"))
        (should (equal (buffer-text "*response*") "second"))
        (should-not (coq-eglot-busy-p))))))

;; The bounds of the sentences, without server

(defmacro with-sentences (text &rest body)
  "Run BODY with a session on TEXT, sentences ending with a dot."
  (declare (indent 1) (debug t))
  `(with-planner ,text
     (setq coq-eglot-sentences-start-function
           coq-eglot-session-sentence-start-function)
     ,@body))

(defun execution (start end &optional version)
  "The event of the execution of the sentence from START to END."
  (coq-eglot-lsp--make-execution (or version test-version) start end))

(ert-deftest coq-eglot-sentences-learned ()
  "The bounds learned from the executions, the answers and the errors,
kept in order; an overlapping range replaces the old one."
  (with-sentences "A. B. C. D."
    (let ((changes 0))
      (add-hook 'coq-eglot-sentences-change-hook (lambda () (cl-incf changes))
                nil t)
      (coq-eglot-sentences-observe (execution 1 3))
      (coq-eglot-sentences-observe (execution 4 6))
      ;; the same again changes nothing
      (coq-eglot-sentences-observe (execution 4 6))
      (should (= changes 2))
      ;; an answer for a later sentence, an error for an earlier one
      (coq-eglot-sentences-observe
       (coq-eglot-lsp-make-answer :version 1 :sentence '(10 . 12)))
      (coq-eglot-sentences-observe
       (coq-eglot-lsp--make-diagnostics
        1 (list (coq-eglot-lsp--make-diagnostic 7 8 'error "e" '(7 . 9)))))
      (should (equal (coq-eglot-sentences--ranges)
                     '((10 . 12) (7 . 9) (4 . 6) (1 . 3))))
      ;; an overlapping range replaces
      (coq-eglot-sentences-observe (execution 4 9))
      (should (equal (coq-eglot-sentences--ranges)
                     '((10 . 12) (4 . 9) (1 . 3)))))))

(ert-deftest coq-eglot-sentences-edition ()
  "An edition forgets the sentences ending at it or after, a late event
about the text before it is still learned, not about the text after."
  (with-sentences "A. B. C."
    (coq-eglot-sentences-observe (execution 1 3))
    (coq-eglot-sentences-observe (execution 4 6))
    (coq-eglot-sentences-observe (execution 7 9))
    ;; right at the end of B.: B. is edited too
    (edit-at 6)
    (should (equal (coq-eglot-sentences--ranges) '((1 . 3))))
    ;; late: about version 1, before the edition, and after it
    (coq-eglot-sentences-observe (execution 4 5 1))
    (coq-eglot-sentences-observe (execution 8 10 1))
    (should (equal (coq-eglot-sentences--ranges) '((4 . 5) (1 . 3))))))

(ert-deftest coq-eglot-sentences-previous-end ()
  "The end of the sentence before a position, if surely known: no
sentence the server did not tell of between."
  (with-sentences "A. B. C. D."
    ;; nothing known: sure only before the first sentence
    (should (= (coq-eglot-sentences-previous-end 1) 1))
    (should-not (coq-eglot-sentences-previous-end 5))
    (coq-eglot-sentences-observe (execution 1 3))
    (coq-eglot-sentences-observe (execution 4 6))
    ;; inside B., or right after it, or before C.
    (should (= (coq-eglot-sentences-previous-end 5) 3))
    (should (= (coq-eglot-sentences-previous-end 6) 6))
    (should (= (coq-eglot-sentences-previous-end 7) 6))
    ;; inside C., not known: it may end before
    (should-not (coq-eglot-sentences-previous-end 8))
    (should-not (coq-eglot-sentences-previous-end 11))
    (coq-eglot-sentences-observe (execution 10 12))
    ;; C. is not known, D. is: C. may end before D.
    (should-not (coq-eglot-sentences-previous-end 11))))

(ert-deftest coq-eglot-session-diagnostics-whole-sentence ()
  "An error depends on all its sentence: an edition after its message but
in its sentence forgets it.  A warning, without sentence range, up to
the end of its message."
  (with-sentences "Lemma a : True. Proof. exact foo. Qed."
    (let* ((exact (save-excursion (goto-char (point-min))
                                  (search-forward "exact") (match-beginning 0)))
           (foo (+ exact 6))
           (end (+ exact 10)))
      ;; an error with its sentence, a warning in a known sentence
      (coq-eglot-sentences-observe (execution 1 16))
      (should (coq-eglot-session-receive-diagnostics
               (coq-eglot-lsp--make-diagnostics
                1 (list (coq-eglot-lsp--make-diagnostic
                         foo (+ foo 3) 'error "foo" (cons exact end))
                        (coq-eglot-lsp--make-diagnostic 1 6 'warning "w" nil)))))
      (should (coq-eglot-session-error-range 1 100))
      ;; after the message, in the sentence
      (edit-at (+ foo 3))
      (should-not (coq-eglot-session-error-range 1 100))
      (should (= (length coq-eglot-session--diagnostics) 1))
      ;; a warning has no sentence range: kept up to the end of its
      ;; message, nothing decides on it
      (edit-at 10)
      (should (= (length coq-eglot-session--diagnostics) 1))
      (edit-at 5)
      (should-not coq-eglot-session--diagnostics))))

(ert-deftest coq-eglot-session-diagnostics-late ()
  "An error of an older version, arriving after an edition after its
message but in its sentence, is not kept."
  (with-sentences "Lemma a : True. Proof. exact foo. Qed."
    (let* ((exact (save-excursion (goto-char (point-min))
                                  (search-forward "exact") (match-beginning 0)))
           (foo (+ exact 6))
           (end (+ exact 10))
           (version test-version))
      (edit-at (+ foo 3))
      (coq-eglot-session-receive-diagnostics
       (coq-eglot-lsp--make-diagnostics
        version (list (coq-eglot-lsp--make-diagnostic
                       foo (+ foo 3) 'error "foo" (cons exact end)))))
      (should-not (coq-eglot-session-error-range 1 100))
      (should-not coq-eglot-session--diagnostics)
      (should-not (coq-eglot-sentences-range-ending-at end)))))

;;; The events buffer

(defun event-json (line)
  "Text shown by `coq-eglot-lsp-show-event-json' on LINE."
  (with-temp-buffer
    (insert line)
    (goto-char (point-min))
    (let ((display-buffer-overriding-action '(display-buffer-no-window
                                              (allow-no-window . t))))
      (coq-eglot-lsp-show-event-json))
    (buffer-text coq-eglot-lsp-event-json-buffer-name)))

(ert-deftest coq-eglot-show-event-json ()
  "The JSON message of a line of the events buffer, indented."
  (let ((text (event-json
               (concat "[jsonrpc] e[12:00:00.000] <-- proof/goals[3] "
                       "{\"id\":3,\"result\":{\"goals\":null,"
                       "\"messages\":[]}}"))))
    (should (string-prefix-p "{" text))
    (should (string-match-p "\n *\"goals\": null" text))
    (should (string-match-p "\n *\"messages\": \\[\\]" text)))
  (with-current-buffer coq-eglot-lsp-event-json-buffer-name
    (should (derived-mode-p 'js-json-mode)))
  (should-error (event-json "[jsonrpc] i[12:00:00.000] Running language server")
                :type 'user-error)
  ;; cut by the size limit of the events buffer
  (should-error (event-json "[jsonrpc] e[12:00:00.000] <-- x {\"id\":3,\"res")
                :type 'user-error))

(ert-deftest coq-eglot-events-keys ()
  "The events buffer of the server shows its messages as JSON.
Not with the jsonrpc of Emacs 29, which pretty-prints them as Lisp."
  (with-test-file
    (run #'coq-eglot-assert-next-command)
    (should (wait-until #'coq-eglot-lsp-current-server 10))
    (let ((server (coq-eglot-lsp-current-server)))
      (with-current-buffer (jsonrpc-events-buffer server)
        (unless (coq-eglot-lsp--events-json-p server)
          (should-not (current-local-map))
          (ert-skip "The events buffer has no JSON"))
        (should (eq (lookup-key (current-local-map) "j")
                    #'coq-eglot-lsp-show-event-json))
        ;; the answer to initialize, on one line
        (goto-char (point-min))
        (should (re-search-forward "<-- initialize\\[[0-9]+\\] {" nil t))
        (let ((display-buffer-overriding-action '(display-buffer-no-window
                                                  (allow-no-window . t))))
          (coq-eglot-lsp-show-event-json))
        (should (string-match-p "\n *\"capabilities\": {"
                                (buffer-text
                                 coq-eglot-lsp-event-json-buffer-name)))))))

;;; The other goals, detailed

(defun test-goal (ty &optional evar hyps)
  "A goal of the server, of conclusion TY, existential variable EVAR.
HYPS is a list of (NAME . TYPE)."
  (list :info (list :evar (vector "Ser_Evar" (or evar 1)) :name nil)
        :hyps (vconcat (mapcar (lambda (hyp)
                                 (list :names (vector (car hyp)) :def nil
                                       :ty (cdr hyp)))
                               hyps))
        :ty ty))

(ert-deftest coq-eglot-goals-bullet-hint ()
  "The next bullet, from the suggestion of Coq, for the innermost level
with goals."
  (let* ((stack (vector (vector [] []) (vector [] (vector (test-goal "A")))))
         (hint (lambda (bullet)
                 (let ((goals (list :goals [] :stack stack :bullet bullet)))
                   (coq-eglot-goals--bullet-hint
                    goals (coq-eglot-goals--levels goals))))))
    (should (equal (coq-eglot-goals--levels (list :stack stack))
                   (list (list 2 (test-goal "A")))))
    (should (equal (funcall hint "Focus next goal with bullet +.")
                   '(2 . "next bullet: +")))
    (should (equal (funcall hint "Try unfocusing with \"}\".")
                   '(2 . "after }")))
    ;; the current bullet focuses the goals of the innermost level only
    (should-not (funcall hint "The current bullet - is unfinished."))
    (should-not (funcall hint nil))
    (setq stack (vector (vector [] (vector (test-goal "A")))))
    (should (equal (funcall hint "The current bullet - is unfinished.")
                   '(1 . "next bullet: -")))
    (should (equal (coq-eglot-goals-bullet-line
                    (list :bullet "Focus next goal with bullet -."))
                   "Focus next goal with bullet -.\n"))
    (should (equal (coq-eglot-goals-bullet-line (list :bullet nil)) ""))))

(defun goal-button ()
  "After string of the button of the goal title at point."
  (let ((ov (seq-find (lambda (ov) (overlay-get ov 'coq-eglot-goal-button))
                      (overlays-at (point)))))
    (and ov (substring-no-properties (overlay-get ov 'after-string)))))

(ert-deftest coq-eglot-detailed-goals ()
  "The other goals with their hypotheses, folded under their title, and
the unfocused goals by level, with the next bullet."
  (with-test-file
    (unwind-protect
        (progn
          (setq coq-fold-other-goals nil)
          ;; like Coq: only the conclusions, and the next bullet
          (goto-marker "subproof")
          (search-backward "-")
          (run #'coq-eglot-goto-point)
          (should (string-match-p
                   (concat "\\`This subproof is complete, but there are some "
                           "unfocused goals.\nFocus next goal with bullet -.\n\n"
                           "1 goal\n\ngoal 1 is:\n True\\'")
                   (buffer-text "*goals*")))
          (goto-marker "split")
          (run #'coq-eglot-goto-point)
          (should (string-match-p "\n\ngoal 2 is:\n True\\'"
                                  (buffer-text "*goals*")))
          ;; detailed, without asking the server again
          (coq-eglot-toggle-detailed-goals)
          (should coq-eglot-detailed-goals)
          (with-current-buffer "*goals*"
            (should (string-match-p
                     "\n\ngoal 2 is:\n  n : nat\n  =+\n True\\'"
                     (buffer-text "*goals*")))
            (goto-char (point-min))
            (search-forward "goal 2 is:")
            (goto-char (match-beginning 0))
            (should (= (point) (coq-goals--other-goals-start)))
            (should (equal (goal-button) "  ▸ 1 hypothesis"))
            (let ((hyp (save-excursion (search-forward "n : nat"))))
              (should (invisible-p hyp))
              ;; above the keymap of the other goals
              (should (eq (key-binding (kbd "RET"))
                          #'coq-eglot-toggle-goal-hyps))
              (call-interactively (key-binding (kbd "RET")))
              (should-not (invisible-p hyp))
              (should (equal (goal-button) "  ▾"))
              ;; a click folds them again
              (let ((window (get-buffer-window "*goals*")))
                (when window
                  (coq-eglot-toggle-goal-hyps
                   (list 'mouse-1 (list window (point) '(0 . 0) 0)))
                  (should (invisible-p hyp))
                  (call-interactively (key-binding (kbd "RET")))))))
          ;; unfolded in the next goals
          (run #'coq-eglot-goto-point)
          (with-current-buffer "*goals*"
            (goto-char (point-min))
            (should-not (invisible-p (search-forward "goal 2 is:\n  n"))))
          ;; in a bullet, the other goal is unfocused, at level 1
          (goto-marker "hello")
          (run #'coq-eglot-goto-point)
          (should (string-match-p
                   (concat "\\*\\*\\* Unfocused goals:\n\n"
                           "── level 1, next bullet: -\ngoal 2 is:\n  n : nat\n")
                   (buffer-text "*goals*")))
          ;; no goal focused: the folding starts at the level
          (goto-marker "subproof")
          (search-backward "-")
          (run #'coq-eglot-goto-point)
          (with-current-buffer "*goals*"
            (should (string-match-p
                     (concat "\\`This subproof is complete, but there are some "
                             "unfocused goals.\nFocus next goal with bullet -.\n\n"
                             "1 goal\n\n── level 1, next bullet: -\ngoal 1 is:\n")
                     (buffer-text "*goals*")))
            (goto-char (point-min))
            (search-forward "── level")
            (should (= (match-beginning 0) (coq-goals--other-goals-start)))
            (coq-toggle-other-goals)
            (should (equal (substring-no-properties
                            (overlay-get (other-goals-overlay) 'display))
                           "▸ 1 unfocused goal")))
          (coq-eglot-toggle-detailed-goals)
          (should-not coq-eglot-detailed-goals)
          (should (string-match-p "\n\ngoal 1 is:\n True\\'"
                                  (buffer-text "*goals*"))))
      (setq coq-eglot-detailed-goals nil)
      (setq coq-fold-other-goals t)
      (setq coq-eglot-goals--unfolded nil))))

(provide 'coq-eglot-test-basic)

;;; coq-eglot-test-basic.el ends here
