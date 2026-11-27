;;; coq-eglot-test-basic.el --- Basic tests of the Eglot backend for Coq  -*- lexical-binding: t -*-
;;
;; This file is part of Proof General.
;;
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Test the proof position, the goals and response buffers, errors and
;; edition before the proof position, with the Eglot backend.
;; See coq-eglot-test-common.el for the settings and the utilities.

;;; Code:

(require 'coq-eglot-test-common
         (expand-file-name "coq-eglot-test-common"
                           (file-name-directory
                            (or load-file-name buffer-file-name))))

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

(ert-deftest coq-eglot-error-stops ()
  "Processing stops before the sentence that fails.
Like Proof General, the sentence is highlighted with `proof-boring-face',
the error location with `proof-warning-face', and point moves there."
  (with-test-file
    (run #'coq-eglot-process-buffer)
    (should (position-at-marker-p "before error"))
    (should (string-match-p "\\`Error: .*unknown_lemma" (buffer-text "*response*")))
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
    ;; errors are displayed as such: only "Error:" in the error face
    (should (string-match-p "\\`Error: .*was not found"
                            (query #'coq-run-query "Check l")))
    (with-current-buffer "*response*"
      (should (eq (get-text-property (point-min) 'font-lock-face)
                  'proof-error-face))
      (should-not (get-text-property (search-forward "was not found")
                                     'font-lock-face)))
    ;; the proof position does not move
    (should (position-at-marker-p "definition"))))

(ert-deftest coq-eglot-message-levels ()
  "Errors and warnings come after \"Error: \" and \"Warning: \", like in
Proof General, the other messages alone."
  (with-test-file
    (goto-marker "split")
    (run #'coq-eglot-goto-point)
    (should (string-prefix-p
             "Warning: Could not enable unknown warning"
             (query #'coq-eglot-run-query "Set Warnings \"+nonexistent-xyz\".")))
    (let ((text (query #'coq-eglot-run-query "Check (1 + true).")))
      (should (string-prefix-p "Error: " text))
      (should-not (string-match-p "Coq: " text)))
    (should (string-prefix-p "double\n" (query #'coq-eglot-run-query "Check double.")))))

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
    ;; only "Error:" in the error face, the rest like the other messages
    (should (eq (face-of "*response*" "Error:") 'proof-error-face))
    (should-not (face-of "*response*" "The reference"))
    ;; the quoted terms like the goals, the rest not
    (query #'coq-run-query "Check (0 (fun n : nat => n))")
    (should (eq (face-of "*response*" "fun n") 'font-lock-type-face))
    (should-not (face-of "*response*" "cannot be applied"))))

(ert-deftest coq-eglot-split-goals ()
  "The conclusion can be displayed apart from the hypotheses."
  (with-test-file
    ;; the other goals like Coq, until the cleanup below
    (setq coq-eglot-detailed-goals nil)
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
        (setq coq-eglot-split-goals nil)
        (setq coq-eglot-detailed-goals t)))))

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
          ;; the other goals like Coq
          (setq coq-eglot-detailed-goals nil)
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
      (setq coq-eglot-detailed-goals t)
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
  "The overlay of the button after the goal title at point."
  (seq-find (lambda (ov) (overlay-get ov 'coq-eglot-goal-button))
            (overlays-at (line-end-position))))

(defun goal-button-text ()
  "Text of the button after the goal title at point."
  (let ((ov (goal-button)))
    (and ov (string-remove-suffix
             "\n" (substring-no-properties (overlay-get ov 'display))))))

(ert-deftest coq-eglot-detailed-goals ()
  "The other goals with their hypotheses, folded under their title, and
the unfocused goals by level, with the next bullet."
  (with-test-file
    (unwind-protect
        (progn
          (setq coq-fold-other-goals nil)
          (setq coq-eglot-detailed-goals nil)
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
                     "\n\ngoal 2:\n  n : nat\n  =+\n True\\'"
                     (buffer-text "*goals*")))
            (goto-char (point-min))
            (search-forward "goal 2:")
            (goto-char (match-beginning 0))
            (should (= (point) (coq-goals--other-goals-start)))
            (should (equal (goal-button-text) "  ▸ 1 hypothesis"))
            (let ((hyp (save-excursion (search-forward "n : nat"))))
              (should (invisible-p hyp))
              ;; no empty line between the button and the conclusion
              (should (invisible-p (save-excursion
                                     (search-forward "\n True")
                                     (match-beginning 0))))
              ;; above the keymap of the other goals
              (should (eq (key-binding (kbd "RET"))
                          #'coq-eglot-toggle-goal-hyps))
              (call-interactively (key-binding (kbd "RET")))
              (should-not (invisible-p hyp))
              (should (equal (goal-button-text) "  ▾"))
              ;; a click folds them again
              (let ((window (get-buffer-window "*goals*")))
                (when window
                  (coq-eglot-toggle-goal-hyps
                   (list 'mouse-1 (list window (point) '(0 . 0) 0)))
                  (should (invisible-p hyp))
                  ;; a click on the button too, not on the other goals
                  (let ((end (line-end-position)))
                    (should (eq (overlay-start (goal-button)) end))
                    (should (eq (key-binding [mouse-1] nil nil end)
                                #'coq-eglot-toggle-goal-hyps))
                    ;; elsewhere, the folding of all the other goals
                    (should (eq (key-binding [mouse-1] nil nil (+ end 3))
                                #'coq-toggle-other-goals))
                    (coq-eglot-toggle-goal-hyps
                     (list 'mouse-1 (list window end '(0 . 0) 0))))
                  (should-not (invisible-p hyp))))))
          ;; unfolded in the next goals
          (run #'coq-eglot-goto-point)
          (with-current-buffer "*goals*"
            (goto-char (point-min))
            (should-not (invisible-p (search-forward "goal 2:\n  n"))))
          ;; in a bullet, the other goal is unfocused, at level 1
          (goto-marker "hello")
          (run #'coq-eglot-goto-point)
          (should (string-match-p
                   (concat "\\*\\*\\* Unfocused goals:\n\n"
                           "── level 1, next bullet: -\ngoal 2:\n  n : nat\n")
                   (buffer-text "*goals*")))
          ;; no goal focused: the folding starts at the level
          (goto-marker "subproof")
          (search-backward "-")
          (run #'coq-eglot-goto-point)
          (with-current-buffer "*goals*"
            (should (string-match-p
                     (concat "\\`This subproof is complete, but there are some "
                             "unfocused goals.\nFocus next goal with bullet -.\n\n"
                             "1 goal\n\n── level 1, next bullet: -\ngoal 1:\n")
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
      (setq coq-eglot-detailed-goals t)
      (setq coq-fold-other-goals t)
      (setq coq-eglot-goals--unfolded nil))))

(ert-deftest coq-eglot-window-need-other-goals ()
  "The goals after the first one count for one line in the height the
goals window needs: they are displayed only if the response leaves room."
  (with-test-file
    (with-layout t 'hybrid
      (unwind-protect
          (progn
            (setq coq-fold-other-goals nil)
            (setq coq-eglot-detailed-goals t)
            (goto-marker "split")
            (run #'coq-eglot-goto-point)
            (let ((goals (get-buffer-window "*goals*")))
              (should goals)
              (with-current-buffer "*goals*"
                (let ((start (coq-goals--other-goals-start))
                      (mode-line (- (window-total-height goals)
                                    (window-body-height goals))))
                  (should start)
                  (should (= (proof-window-need goals)
                             (+ mode-line 1
                                (count-screen-lines (point-min) start nil
                                                    goals))))
                  (should (< (proof-window-need goals)
                             (+ mode-line
                                (count-screen-lines (point-min) (point-max)
                                                    nil goals))))))))
        (setq coq-eglot-detailed-goals t)
        (setq coq-fold-other-goals t)))))

(provide 'coq-eglot-test-basic)

;;; coq-eglot-test-basic.el ends here
