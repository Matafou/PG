;;; coq-eglot-test-twin.el --- Tests of the Eglot backend: the two Rocq mode  -*- lexical-binding: t -*-
;;
;; This file is part of Proof General.
;;
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Test the two Rocq mode, with the Eglot backend.
;; See coq-eglot-test-common.el for the settings and the utilities.

;;; Code:

(require 'coq-eglot-test-common
         (expand-file-name "coq-eglot-test-common"
                           (file-name-directory
                            (or load-file-name buffer-file-name))))

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
      (setq coq-eglot-twin--sentences-dirty-start (point))
      (insert "\nCheck s.")
      (let ((new (coq-eglot-twin--sentences)))
        ;; The unchanged prefix, including a locked prefix in a real script,
        ;; keeps the same sentence objects.
        (should (eq (aref new 0) (aref sentences 0)))
        (should (equal (coq-eglot-twin--sentence-text
                        (aref new (1- (length new))))
                       "Check s."))))))

(ert-deftest coq-eglot-twin-sentences-reuse-suffix ()
  "A local edit reparses its sentence and reuses the unchanged suffix."
  (with-twin-texts "Check 1. Check 2. Check 3. Check 4." ""
    (let* ((sentences (coq-eglot-twin--sentences))
           (first (aref sentences 0))
           (third (aref sentences 2))
           (fourth (aref sentences 3))
           (old-third-start (coq-eglot-twin--sentence-start third)))
      (add-hook 'after-change-functions #'coq-eglot-twin--after-change nil t)
      (goto-char (search-position "Check 2"))
      (insert "0")
      (let ((new (coq-eglot-twin--sentences)))
        (should (equal (sentence-texts)
                       '("Check 1." "Check 20." "Check 3." "Check 4.")))
        (should (eq (aref new 0) first))
        (should (eq (aref new 2) third))
        (should (eq (aref new 3) fourth))
        (should (= (coq-eglot-twin--sentence-start (aref new 2))
                   (1+ old-third-start))))
      ;; Changing a command boundary prevents a premature rejoin: parsing
      ;; continues through the merged command, then reuses the next sentence.
      (goto-char (search-position "Check 20."))
      (backward-char)
      (delete-char 1)
      (let ((new (coq-eglot-twin--sentences)))
        (should (equal (sentence-texts)
                       '("Check 1." "Check 20 Check 3." "Check 4.")))
        (should (eq (aref new 2) fourth))))))

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
      ;; A later edition restarts the debounce instead of keeping the timer
      ;; scheduled by the first one.
      (let ((first (coq-eglot-twin--twins-highlight-timer
                    coq-eglot-twin--twins)))
        (with-current-buffer twin
          (coq-eglot-twin--after-change (point-max)))
        (should-not
         (eq first (coq-eglot-twin--twins-highlight-timer
                    coq-eglot-twin--twins))))
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

(ert-deftest coq-eglot-twin-refine-size-limit ()
  "Large zones keep sentence highlighting without word refinement."
  (with-twin-texts "Check 1." "Check 2."
    (let ((coq-eglot-twin-max-refine-characters 0))
      (coq-eglot-twin--highlight)
      (should (seq-some (lambda (overlay)
                          (overlay-get overlay 'coq-eglot-twin))
                        coq-eglot-twin--overlays))
      (should-not
       (seq-some (lambda (overlay)
                   (overlay-get overlay 'coq-eglot-twin-refine))
                 coq-eglot-twin--overlays))
      (with-current-buffer twin
        (should (seq-some (lambda (overlay)
                            (overlay-get overlay 'coq-eglot-twin))
                          coq-eglot-twin--overlays))
        (should-not
         (seq-some (lambda (overlay)
                     (overlay-get overlay 'coq-eglot-twin-refine))
                   coq-eglot-twin--overlays))))))

(ert-deftest coq-eglot-twin-blend ()
  "Over the processed part, the diverging zones have a background
blending theirs with the one of the processed part."
  (should (equal (coq-eglot-twin--background '((:foreground "red")
                                               (:background "#000000")))
                 "#000000"))
  (should-not (coq-eglot-twin--blend '(:background "#000000") 'default))
  (should (equal (coq-eglot-twin--blend '(:background "#000000")
                                        '(:background "#ffffff") 0.65)
                 "#a5a5a5"))
  (with-twin-texts "Check 1. Check 2. Check 3. Check 4." "Check 1. Check 4."
    (cl-letf (((symbol-function 'coq-eglot-twin--blend)
               (lambda (face1 face2 &optional face2-weight)
                 (and (eq face1 'coq-eglot-twin-added)
                      (eq face2 'proof-locked-face)
                      (= face2-weight 0.65)
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
      (let ((response (get-buffer (coq-eglot--response-name)))
            (twin-response
             (with-current-buffer twin
               (get-buffer (coq-eglot--response-name)))))
        ;; Responses produced by scripting on both sides are compared.
        (coq-eglot--show-response "left response" t)
        (with-current-buffer twin
          (coq-eglot--show-response "right response" t))
        (wait-for-twins)
        (should (twin-differences response))
        (should (twin-differences twin-response))
        ;; An explicit query belongs to this side only: its response is not
        ;; compared with the scripting response left on the other side.  The
        ;; comparison of the goals remains active.
        (should (string-match-p
                 "nat" (query #'coq-eglot-run-query "About nat")))
        (wait-for-twins)
        (should-not (twin-differences response))
        (should-not (twin-differences twin-response)))
      (should (member '("1" . coq-eglot-twin-refine-added)
                      (twin-differences goals)))
      ;; not compared when the positions do not correspond
      (let ((coq-eglot-twin-synchronize nil))
        (run #'coq-eglot-retract-buffer)
        (wait-for-twins)
        (should-not (twin-differences goals))
        (should-not (twin-differences twin-goals))))))

(ert-deftest coq-eglot-twin-synchronize-error ()
  "An error on either side stops both; off, it does not move the twin."
  (with-sync-twins (string-replace "idtac." "exact 0." sync-twin-text)
    (goto-char (point-max))
    (run #'coq-eglot-process-buffer)
    (wait-for-twins)
    ;; The follower's error stops the leader too, and brings it back if a
    ;; progress notification had already moved it past the corresponding
    ;; sentence.
    (should-not (coq-eglot-checking-p))
    (should (= (coq-eglot-position)
               (coq-eglot-twin-position
                (with-current-buffer twin (coq-eglot-position)) twin)))
    (should-not (position-at-marker-p "l3"))
    (with-current-buffer twin
      ;; stopped before the error
      (should-not (coq-eglot-checking-p))
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

(ert-deftest coq-eglot-twin-synchronize-leader-error ()
  "An error of the leader retargets its follower exactly before the error."
  (with-sync-twins sync-twin-text
    (goto-char (point-min))
    (search-forward "reflexivity.")
    (replace-match "exact 0." t t)
    (goto-char (point-max))
    (run #'coq-eglot-process-buffer)
    (wait-for-twins)
    (should-not (coq-eglot-checking-p))
    (should (cl-some (lambda (overlay)
                       (equal (buffer-substring (overlay-start overlay)
                                                (overlay-end overlay))
                              "exact 0."))
                     coq-eglot--error-overlays))
    (should-not (with-current-buffer twin (coq-eglot-checking-p)))
    (should (= (with-current-buffer twin (coq-eglot-position))
               (coq-eglot-twin-position (coq-eglot-position))))))

(ert-deftest coq-eglot-twin-synchronize-earliest-error ()
  "Of errors on both sides, the earliest one becomes their common target."
  (with-sync-twins (string-replace "idtac." "exact 0." sync-twin-text)
    ;; The leader fails in l1, before the follower's error in l2.
    (goto-char (point-min))
    (search-forward "exact I.")
    (replace-match "exact 0." t t)
    (goto-char (point-max))
    (run #'coq-eglot-process-buffer)
    (wait-for-twins)
    (let ((before-first-error (search-position "Lemma l1 : True.\nProof.")))
      (should (= (coq-eglot-position) before-first-error))
      (should (= (with-current-buffer twin (coq-eglot-position))
                 (coq-eglot-twin-position before-first-error))))
    (should (cl-some (lambda (overlay)
                       (equal (buffer-substring (overlay-start overlay)
                                                (overlay-end overlay))
                              "exact 0."))
                     coq-eglot--error-overlays))))

(ert-deftest coq-eglot-twin-pair-errors ()
  "A buffer has at most one twin, and it is not itself."
  (with-twin
    (should-error (coq-eglot-twin-pair (current-buffer)) :type 'user-error)
    (should-error (coq-eglot-twin-pair twin) :type 'user-error)))

;;; coq-eglot-test-twin.el ends here
