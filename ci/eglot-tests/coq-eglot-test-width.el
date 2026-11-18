;;; coq-eglot-test-width.el --- Tests of the Eglot backend: the printing width  -*- lexical-binding: t -*-
;;
;; This file is part of Proof General.
;;
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Test the printing width and the printing flags, with the Eglot backend.
;; See coq-eglot-test-common.el for the settings and the utilities.

;;; Code:

(require 'coq-eglot-test-common
         (expand-file-name "coq-eglot-test-common"
                           (file-name-directory
                            (or load-file-name buffer-file-name))))

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

;;; coq-eglot-test-width.el ends here
