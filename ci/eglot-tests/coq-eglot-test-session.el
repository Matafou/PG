;;; coq-eglot-test-session.el --- Tests of the Eglot backend: the session  -*- lexical-binding: t -*-
;;
;; This file is part of Proof General.
;;
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Test the session, the planner and the sentences, with the Eglot backend.
;; See coq-eglot-test-common.el for the settings and the utilities.

;;; Code:

(require 'coq-eglot-test-common
         (expand-file-name "coq-eglot-test-common"
                           (file-name-directory
                            (or load-file-name buffer-file-name))))

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

;;; coq-eglot-test-session.el ends here
