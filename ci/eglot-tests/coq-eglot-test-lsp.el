;;; coq-eglot-test-lsp.el --- Tests of the Eglot backend: the connection to the server  -*- lexical-binding: t -*-
;;
;; This file is part of Proof General.
;;
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Test the connection to the server, with the Eglot backend.
;; See coq-eglot-test-common.el for the settings and the utilities.

;;; Code:

(require 'coq-eglot-test-common
         (expand-file-name "coq-eglot-test-common"
                           (file-name-directory
                            (or load-file-name buffer-file-name))))

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
  "Run BODY with the server `fake-server', printing OUTPUT with --version.
The coq-lsp next to the Rocq found in `exec-path'."
  (declare (indent 1) (debug t))
  `(with-installation '("rocq")
     (without-user-rocq
       (let* ((fake-server (expand-file-name "coq-lsp" bin))
              (exec-path (list bin))
              (coq-eglot-lsp--server-versions (make-hash-table :test #'equal)))
         (with-temp-file fake-server
           (insert "#!/bin/sh\n" ,output))
         (set-file-modes fake-server #o755)
         ,@body))))

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

(ert-deftest coq-eglot-load-path-server-args ()
  "The -R and -Q of `coq-eglot-server-args' are not compared with the
load path of the buffer."
  (let ((process (make-process :name "fake-coq-lsp" :noquery t
                               :command '("sleep" "30" "-R" "a,A"
                                          "-Q" "b,B" "-R" "c,C")))
        (coq-eglot-server-args '("-R" "a,A" "-Q" "b,B")))
    (unwind-protect
        (cl-letf (((symbol-function 'jsonrpc--process) (lambda (_) process)))
          (should (equal (coq-eglot-lsp--server-load-path-args nil)
                         '("-R" "c,C")))
          (let ((coq-eglot-server-args nil))
            (should (equal (coq-eglot-lsp--server-load-path-args nil)
                           '("-R" "a,A" "-Q" "b,B" "-R" "c,C")))))
      (delete-process process))))

(ert-deftest coq-eglot-load-path-same ()
  "Without `coq-eglot-server-args', a server with the load path of the
buffer has the same load path: no warning."
  (let* ((dir (file-name-as-directory (make-temp-file "coq-eglot-lp-" t)))
         (coq-load-path (list (list 'rec dir "Lib")))
         (coq-eglot-server-args nil)
         (args (coq-eglot-lsp-load-path-args))
         (process (make-process :name "fake-coq-lsp" :noquery t
                                :command (append '("sleep" "30") args))))
    (unwind-protect
        (cl-letf (((symbol-function 'jsonrpc--process) (lambda (_) process)))
          (should args)
          (should (equal (coq-eglot-lsp--server-load-path-args nil) args)))
      (delete-process process)
      (delete-directory dir t))))

(ert-deftest coq-eglot-load-path-invalid ()
  "An invalid `coq-load-path' is a user error naming it."
  (with-fake-server ""
    (let ((coq-load-path '(42)))
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

;;; Admission of automatic requests

(ert-deftest coq-eglot-lsp-debounce-keeps-latest ()
  "Only the last automatic request with an equal key is run."
  (with-temp-buffer
    (let (ran cancelled)
      (coq-eglot-lsp--debounce
       'refresh 0.05 (lambda () (push 'old ran))
       :on-cancel (lambda () (setq cancelled t)))
      (coq-eglot-lsp--debounce
       'refresh 0.01 (lambda () (push 'new ran)))
      (should cancelled)
      (should (wait-until (lambda () ran) 1))
      (accept-process-output nil 0.08)
      (should (equal ran '(new)))
      (should-not (gethash 'refresh coq-eglot-lsp--debounces)))))

(ert-deftest coq-eglot-lsp-debounce-keys-are-independent ()
  "Automatic requests with different keys do not replace one another."
  (with-temp-buffer
    (let (ran)
      (coq-eglot-lsp--debounce 'left 0 (lambda () (push 'left ran)))
      (coq-eglot-lsp--debounce 'right 0 (lambda () (push 'right ran)))
      (should (wait-until (lambda () (= (length ran) 2)) 1))
      (should (equal (sort ran #'string-lessp) '(left right))))))

(ert-deftest coq-eglot-lsp-debounce-can-be-cancelled ()
  "Cancelling a debounce prevents it from creating its request."
  (with-temp-buffer
    (let (ran cancelled debounce)
      (setq debounce
            (coq-eglot-lsp--debounce
             'refresh 0.02 (lambda () (setq ran t))
             :on-cancel (lambda () (setq cancelled t))))
      (should (coq-eglot-lsp--cancel-debounce debounce))
      (should-not (coq-eglot-lsp--cancel-debounce debounce))
      (accept-process-output nil 0.05)
      (should-not ran)
      (should cancelled))))

(ert-deftest coq-eglot-lsp-reset-cancels-debounces ()
  "Resetting the scheduler cancels automatic requests not sent yet."
  (with-temp-buffer
    (let (ran)
      (coq-eglot-lsp--debounce 'refresh 0.02 (lambda () (setq ran t)))
      (coq-eglot-lsp--reset-scheduler)
      (accept-process-output nil 0.05)
      (should-not ran)
      (should (hash-table-empty-p coq-eglot-lsp--debounces)))))

(ert-deftest coq-eglot-lsp-debounce-cleaned-up-with-buffer ()
  "Killing a buffer cancels its delayed automatic requests."
  (let ((buffer (generate-new-buffer " *coq-eglot-debounce-test*"))
        timer ran)
    (with-current-buffer buffer
      (setq timer
            (coq-eglot-lsp-debounce-timer
             (coq-eglot-lsp--debounce
              'refresh 10 (lambda () (setq ran t))))))
    (should (memq timer timer-list))
    (kill-buffer buffer)
    (should-not (memq timer timer-list))
    (should-not ran)))

;;; Scheduling policies

(ert-deftest coq-eglot-lsp-policy-combinations-validated ()
  "Only combinations with an implemented scheduler semantics are accepted."
  (dolist (combination coq-eglot-lsp--supported-policy-combinations)
    (should
     (coq-eglot-lsp--make-policy
      'test (car combination) 1 (cadr combination))))
  (dolist (combination '((protected latest)
                         (protected drop)
                         (resumable fifo)
                         (resumable drop)
                         (discardable fifo)))
    (should-error
     (coq-eglot-lsp--make-policy
      'test (car combination) 1 (cadr combination))))
  (should-error (coq-eglot-lsp--make-policy 'test 'unknown 1 'fifo))
  (should-error (coq-eglot-lsp--make-policy 'test 'protected 1 'unknown))
  (should (coq-eglot-lsp--make-policy
           'settled 'discardable 1 'latest 0.05))
  (should (coq-eglot-lsp--make-policy
           'settled 'discardable 1 'drop 0.05))
  (should-error
   (coq-eglot-lsp--make-policy 'settled 'protected 1 'fifo 0.05))
  (should-error
   (coq-eglot-lsp--make-policy 'settled 'discardable 1 'latest -1))
  (should (= (coq-eglot-lsp-policy-settle-delay
              coq-eglot-lsp-hover-policy)
             0.05)))

(ert-deftest coq-eglot-lsp-policy-debounces-before-scheduling ()
  "A settled policy admits only the last equivalent request."
  (with-temp-buffer
    (let ((policy (coq-eglot-lsp--make-policy
                   'refresh 'discardable 1 'latest 0.02))
          sent first second success)
      (cl-letf (((symbol-function 'coq-eglot-lsp-connect)
                 (lambda () 'server))
                ((symbol-function 'coq-eglot-lsp-current-server)
                 (lambda () 'server))
                ((symbol-function 'coq-eglot-lsp--flush-document)
                 (lambda () 1))
                ((symbol-function 'jsonrpc--async-request-1)
                 (lambda (_server method _params &rest args)
                   (push method sent)
                   (setq success (plist-get args :success-fn))
                   '(42))))
        (setq first
              (coq-eglot-lsp--async-request
               1 :old #'ignore #'ignore #'ignore policy 'refresh)
              second
              (coq-eglot-lsp--async-request
               1 :new #'ignore #'ignore #'ignore policy 'refresh))
        (should (coq-eglot-lsp-context-cancelled first))
        (should-not (coq-eglot-lsp-context-cancelled second))
        (should-not sent)
        (should (wait-until (lambda () sent) 1))
        (should (equal sent '(:new)))
        (funcall success 'answer)
        (should (wait-until
                 (lambda () (null coq-eglot-lsp--active-requests)) 1))))))

(ert-deftest coq-eglot-lsp-settled-policy-needs-key ()
  "A settled request must identify the equivalent events it replaces."
  (let ((policy (coq-eglot-lsp--make-policy
                 'refresh 'discardable 1 'latest 0.02)))
    (should-error
     (coq-eglot-lsp--async-request
      1 :refresh #'ignore #'ignore #'ignore policy nil))))

(ert-deftest coq-eglot-lsp-settled-request-can-be-cancelled ()
  "Cancelling during settlement prevents admission to the scheduler."
  (with-temp-buffer
    (let ((policy (coq-eglot-lsp--make-policy
                   'refresh 'discardable 1 'latest 10))
          sent context)
      (cl-letf (((symbol-function 'coq-eglot-lsp-current-server)
                 (lambda () nil)))
        (setq context
              (coq-eglot-lsp--async-request
               1 :refresh (lambda () (setq sent t))
               #'ignore #'ignore policy 'refresh))
        (should (coq-eglot-lsp-context-debounce context))
        (coq-eglot-lsp-cancel-request context)
        (should (coq-eglot-lsp-context-cancelled context))
        (should-not (coq-eglot-lsp-context-debounce context))
        (should-not coq-eglot-lsp--request-queue)
        (should-not coq-eglot-lsp--active-requests)
        (should-not sent)))))

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
                     "printed\nWarning: careful\nplain"))
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

;;; coq-eglot-test-lsp.el ends here
