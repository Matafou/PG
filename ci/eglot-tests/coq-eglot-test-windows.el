;;; coq-eglot-test-windows.el --- Tests of the Eglot backend: the windows  -*- lexical-binding: t -*-
;;
;; This file is part of Proof General.
;;
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Test the windows of the goals and messages, with the Eglot backend.
;; See coq-eglot-test-common.el for the settings and the utilities.

;;; Code:

(require 'coq-eglot-test-common
         (expand-file-name "coq-eglot-test-common"
                           (file-name-directory
                            (or load-file-name buffer-file-name))))

(ert-deftest coq-eglot-resize-windows ()
  "The response window gets the height it needs, the goals window above
it the rest, like in Proof General, see `proof-fit-output-windows'."
  (with-test-file
    (with-layout t 'hybrid
      (goto-marker "split")
      (run #'coq-eglot-goto-point)
      (query #'coq-eglot-run-query "Check double")
      (let ((goals (get-buffer-window "*goals*"))
            (response (get-buffer-window "*response*")))
        (should (and goals response))
        (should (= (window-total-height response)
                   (max window-min-height (proof-window-need response))))
        (should (> (window-total-height goals) (proof-window-need goals)))))))

(ert-deftest coq-eglot-resize-windows-off ()
  "Without `proof-shrink-windows-tofit', the heights of the windows do
not change."
  (with-test-file
    (with-layout t 'hybrid
      (let ((proof-shrink-windows-tofit nil)
            (calls 0))
        (cl-letf (((symbol-function 'proof-resize-output-column)
                   (lambda (&rest _) (setq calls (1+ calls)))))
          (goto-marker "split")
          (run #'coq-eglot-goto-point)
          (query #'coq-eglot-run-query "Check double"))
        (should (= calls 0))))))

(ert-deftest coq-eglot-resize-windows-split ()
  "With split goals, the hypotheses, the conclusion and the response
windows share their height, each one getting what it needs if they fit.
The conclusion gets the lines left, not the hypotheses above it: they
have a lower weight by default, see `proof-output-windows-weights'."
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
                        (proof-window-need conclusion)))
            (should (= (window-total-height goals)
                       (max window-min-height (proof-window-need goals))))
            (should (= (window-total-height response)
                       (max window-min-height (proof-window-need response))))
            ;; with equal weights, the upper window gets them
            (let ((proof-output-windows-weights '((hypotheses . 1))))
              (coq-eglot--resize-windows))
            (should (> (window-total-height goals)
                       (max window-min-height (proof-window-need goals))))))
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
      (let ((proof-shrink-windows-tofit nil))
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
      ;; a presentation of the goals, like in the OPTIONS menu
      (let ((compact (assoc "Compact Contexts"
                            (mapcar (lambda (item)
                                      (and (vectorp item) (append item nil)))
                                    (cdr (assoc "Windows"
                                                (cdr coq-eglot--menu-spec)))))))
        (should (eq (nth 1 compact) 'coq-eglot-toggle-compact-contexts))
        (should (eq (plist-get (nthcdr 2 compact) :style) 'toggle)))
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
  "With `proof-shrink-windows-tofit', the script window keeps its height,
the goals and response windows below it share theirs."
  (with-test-file
    (with-layout t 'vertical
      (let ((proof-shrink-windows-tofit t)
            (script (selected-window)))
        (goto-marker "split")
        (run #'coq-eglot-goto-point)
        (pcase-let* ((`(,goals ,response) (windows-of "*goals*" "*response*"))
                     (height (window-total-height script))
                     (outputs (+ (window-total-height goals)
                                 (window-total-height response))))
          (query #'coq-eglot-run-query "Check double")
          (should (= (window-total-height script) height))
          (should (= (+ (window-total-height goals)
                        (window-total-height response))
                     outputs))
          (should (= (window-total-height response)
                     (max window-min-height (proof-window-need response)))))))))

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
                  ((symbol-function 'proof-resize-output-column)
                   (lambda (&rest _) (setq resized (1+ resized))))
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

(ert-deftest coq-eglot-fold-error-environment ()
  "The environments of the error messages are folded in the response
buffer.  `coq-toggle-error-environment' unfolds them and fits the
output windows again, see `proof-output-windows-function'."
  (with-test-file
    (with-layout t 'vertical
      (let ((coq-fold-error-environment t)
            (folded (lambda ()
                      (with-current-buffer "*response*"
                        (seq-some (lambda (ov)
                                    (and (overlay-get ov 'coq-error-environment)
                                         (overlay-get ov 'display)))
                                  (overlays-in (point-min) (point-max))))))
            (resized 0))
        (goto-marker "split")
        (run #'coq-eglot-goto-point)
        (coq-eglot--show-response
         (concat "In environment\nn : nat\nm : nat\n"
                 "The term \"n\" has type \"nat\" while it is expected"
                 " to have type \"bool\"."))
        (should (funcall folded))
        (cl-letf (((symbol-function 'proof-resize-output-column)
                   (lambda (&rest _) (setq resized (1+ resized)))))
          (with-current-buffer "*response*"
            (coq-toggle-error-environment)))
        (should-not (funcall folded))
        (should (> resized 0))))))

;;; coq-eglot-test-windows.el ends here
