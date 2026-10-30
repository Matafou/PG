;;; coq-eglot-compile.el --- Compile the libraries required by the script  -*- lexical-binding:t -*-

;; This file is part of Proof General.

;; Portions © Copyright 2026  Pierre Courtieu

;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;;
;; Like Proof General with `coq-compile-before-require', compile the
;; libraries required by the part of the script to check, before the
;; server checks it.  The parallel background compilation of Proof
;; General (coq-par-compile.el) does all the work: dependency analysis
;; with coqdep, compilation with coqc, quick or vos compilation...  It
;; is given one queue item per Require sentence, whose span is an
;; overlay on the sentence.  When the compilation for a Require is
;; finished, the item comes back through
;; `coq-par-release-items-function' instead of going to
;; `proof-action-list'.
;;
;; The compiler and coqdep are taken next to the language server, to
;; produce .vo files the server can load.
;;
;; The overlay of a compiled Require sentence is kept: it records the
;; libraries the sentence loaded, with the dates of their .vo files.
;; When one of them changes afterwards (edited in a buffer, source or
;; .vo file changed), the processed Require sentence is marked as
;; outdated, and so is the mode line.  The user decides when to go back
;; before it.

;;; Code:

(require 'cl-lib)
(require 'seq)
(require 'coq-par-compile)
(require 'coq-indent)
(require 'coq-eglot-lsp)

(declare-function coq-eglot-position "coq-eglot")

;; Settings of the Proof General backend (coq.el, pg-custom.el), used
;; by coq-system.el
(defvar coq-prog-args nil
  "Arguments given to the compiler, on top of the load path.
Set from _CoqProject by `coq-load-project-file'.")
(defvar coq-debug nil
  "Non-nil to display debugging messages of the Coq settings.")

(defface coq-eglot-outdated-require '((t :inherit flymake-warning))
  "Face of a processed Require sentence whose libraries changed since."
  :group 'coq-eglot)

(defvar-local coq-eglot-compile--state nil
  "The compilation running for the current buffer, or nil.
A plist with :pending, the overlays of the Require sentences whose
compilation is not finished, in the order of the buffer, and :on-done,
the function to call at the end.")

;;; Programs

(defun coq-eglot-compile--set-programs ()
  "Use the Rocq or Coq programs next to the language server.
Set buffer locally the programs used by the compilation.  Keep the
global values if they are not found there."
  (let* ((server (car (ignore-errors (coq-eglot-lsp-server-command))))
         (server-path (and server (executable-find server)))
         (exec-path (and server-path
                         (list (file-name-directory server-path))))
         (rocq (and exec-path (executable-find "rocq")))
         (coqc (and exec-path (executable-find "coqc"))))
    (cond
     (rocq
      (setq-local proof-prog-name rocq)
      (setq-local coq-compiler rocq)
      (setq-local coq-dependency-analyzer rocq))
     (coqc
      (setq-local proof-prog-name (executable-find "coqtop"))
      (setq-local coq-compiler coqc)
      (setq-local coq-dependency-analyzer (executable-find "coqdep"))))))

;;; Require sentences

(defun coq-eglot-compile--require-sentences (start end)
  "Return the bounds (BEG . END) of the Require sentences in START..END.
Only the sentences starting before END count.  Sentences are
delimited locally: the server did not check them yet."
  (let (requires)
    (save-excursion
      (goto-char start)
      (forward-comment (buffer-size))
      (while (and (< (point) end)
                  (let ((beg (point)))
                    (when (eq (coq-script-parse-cmdend-forward) 'cmd)
                      (when (string-match-p coq-require-command-regexp
                                            (buffer-substring-no-properties
                                             beg (point)))
                        (push (cons beg (point)) requires))
                      t)))
        (forward-comment (buffer-size))))
    (nreverse requires)))

;;; Compilation

(defun coq-eglot-compile--item (bounds)
  "Return the queue item of the Require sentence with BOUNDS."
  (let ((overlay (make-overlay (car bounds) (cdr bounds))))
    (list overlay
          (list (buffer-substring-no-properties (car bounds) (cdr bounds)))
          nil)))

(defun coq-eglot-compile--recompiled-p ()
  "Non-nil if the last compilation compiled some library."
  (and coq--compilation-object-hash
       (catch 'found
         (maphash (lambda (_ job)
                    (when (eq (get job 'youngest-coqc-dependency)
                              'just-compiled)
                      (throw 'found t)))
                  coq--compilation-object-hash)
         nil)))

(defun coq-eglot-compile--finish (failed)
  "End the compilation of the current buffer.
FAILED is non-nil if some compilation failed: the start of the first
Require sentence whose compilation did not finish is passed to the
:on-done function, otherwise nil.  If a library was compiled, the
server may have loaded the previous version: tell it to load the
libraries again."
  (when-let* ((state coq-eglot-compile--state))
    (let* ((pending (plist-get state :pending))
           (limit (and failed pending (overlay-start (car pending)))))
      (setq coq-eglot-compile--state nil)
      (mapc #'delete-overlay pending)
      (when (coq-eglot-compile--recompiled-p)
        (coq-eglot-lsp-workspace-update)
        ;; the libraries of other buffers may have changed
        (coq-eglot-compile-check-all-outdated))
      (funcall (plist-get state :on-done) limit))))

(defun coq-eglot-compile--release (items job)
  "The compilation for the Require sentences of ITEMS is finished.
JOB is their require job.  `coq-par-release-items-function' of the
script buffers.  The overlays of the sentences are kept, with the
libraries they load."
  (when coq-eglot-compile--state
    (dolist (item items)
      (if (overlayp (car item))
          (let ((pending (plist-get coq-eglot-compile--state :pending)))
            (coq-eglot-compile--record (car item) job)
            (plist-put coq-eglot-compile--state :pending
                       (delq (car item) pending)))
        ;; a callback item: there is no queue to wait for
        (funcall (nth 2 item) nil)))
    (unless (plist-get coq-eglot-compile--state :pending)
      (coq-eglot-compile--finish nil))))

(defun coq-eglot-compile--failure ()
  "The last require job failed.  `coq-par-failure-function'."
  (coq-eglot-compile--finish t))

(defun coq-eglot-compile--abort (_buffer)
  "All the jobs were killed after an error.
`coq-par-abort-function'.  The compilations of the other buffers are
gone too."
  (coq-eglot-compile--abort-all))

(defun coq-eglot-compile--abort-all ()
  "End with a failure the compilations of all buffers."
  (dolist (buffer (buffer-list))
    (with-current-buffer buffer
      (when coq-eglot-compile--state
        (coq-eglot-compile--finish t)))))

(defun coq-eglot-compile-requires (start end on-done)
  "Compile the libraries required by the sentences between START and END.
Return nil if there is nothing to compile: no Require sentence there,
or `coq-compile-before-require' is nil.  Otherwise start the
compilation in the background and return non-nil.  ON-DONE is called
later in the current buffer with nil if all the compilations
succeeded, otherwise with the start of the first Require sentence
whose compilation failed.  The errors are displayed by the
compilation."
  (let ((requires (and coq-compile-before-require
                       (coq-eglot-compile--require-sentences start end))))
    ;; the processed Require sentences are after the proof position
    (coq-eglot-compile--forget-from start)
    (when requires
      (coq-eglot-compile--set-programs)
      (setq-local coq-par-release-items-function #'coq-eglot-compile--release)
      (setq-local coq-par-failure-function #'coq-eglot-compile--failure)
      (setq-local coq-par-abort-function #'coq-eglot-compile--abort)
      ;; the locks of Proof General are for the proof shell
      (setq-local coq-lock-ancestors nil)
      (let ((items (mapcar #'coq-eglot-compile--item requires)))
        (setq coq-eglot-compile--state
              (list :pending (mapcar #'car items) :on-done on-done))
        (message "Compiling the required libraries...")
        (unless (coq-par-start-compilation items)
          ;; reported already, ON-DONE called if a job was created
          (coq-eglot-compile--finish t))
        t))))

(defun coq-eglot-compile-running-p ()
  "Non-nil if a compilation is running for the current buffer."
  coq-eglot-compile--state)

(defun coq-eglot-compile-cancel ()
  "Kill the compilation running for the current buffer, if any.
Do not call its :on-done function.  The background jobs are shared,
the compilations of the other buffers fail."
  (when coq-eglot-compile--state
    (mapc #'delete-overlay (plist-get coq-eglot-compile--state :pending))
    (setq coq-eglot-compile--state nil)
    (coq-par-kill-and-cleanup)
    (coq-eglot-compile--abort-all)))

;;; Outdated libraries

(defvar-local coq-eglot-compile--loaded nil
  "Overlays of the compiled Require sentences.
The property `coq-eglot-libraries' of an overlay is the list of
\(SOURCE VO DATE) of the libraries the sentence loads, even indirectly:
SOURCE is the .v file, VO the .vo file, DATE the modification time of
VO when it was loaded.  The property `coq-eglot-outdated' is the list of the
sources that changed since.")

(defvar-local coq-eglot-compile--outdated-p nil
  "Non-nil if a processed Require sentence loads outdated libraries.")

(defun coq-eglot-compile--date (file)
  "Modification time of FILE, nil if it does not exist."
  (file-attribute-modification-time (file-attributes file)))

(defun coq-eglot-compile--libraries (job)
  "Return the (SOURCE VO DATE) of the libraries required by JOB.
They are the file jobs JOB depends on, even indirectly, see
`coq-eglot-compile--loaded'."
  (let (visited libraries)
    (cl-labels ((visit (job)
                  (unless (memq job visited)
                    (push job visited)
                    (when (eq (get job 'type) 'file)
                      (push (list (get job 'src-file) (get job 'vo-file)
                                  (coq-eglot-compile--date (get job 'vo-file)))
                            libraries))
                    (mapc #'visit (get job 'coqc-dependees)))))
      (visit job))
    libraries))

(defun coq-eglot-compile--record (overlay job)
  "Keep OVERLAY on a compiled Require sentence, with the libraries of JOB."
  (overlay-put overlay 'coq-eglot-libraries (coq-eglot-compile--libraries job))
  (push overlay coq-eglot-compile--loaded))

(defun coq-eglot-compile--forget-from (pos)
  "Forget the compiled Require sentences ending after POS."
  (setq coq-eglot-compile--loaded
        (seq-filter (lambda (overlay)
                      (if (and (overlay-buffer overlay)
                               (<= (overlay-end overlay) pos))
                          t
                        (delete-overlay overlay)
                        nil))
                    coq-eglot-compile--loaded))
  (coq-eglot-compile-show-outdated pos))

(defun coq-eglot-compile--outdated-library-p (library)
  "Non-nil if LIBRARY, a (SOURCE VO DATE), changed since it was loaded.
Its source is modified in a buffer, or newer than DATE, or VO changed."
  (pcase-let* ((`(,source ,vo ,date) library)
               (buffer (find-buffer-visiting source))
               (source-date (coq-eglot-compile--date source)))
    (or (and buffer (buffer-modified-p buffer))
        (and date source-date (time-less-p date source-date))
        (not (equal date (coq-eglot-compile--date vo))))))

(defun coq-eglot-compile-check-outdated ()
  "Find the processed Require sentences loading outdated libraries.
Mark them and the mode line."
  (dolist (overlay coq-eglot-compile--loaded)
    (overlay-put overlay 'coq-eglot-outdated
                 (mapcar #'car (seq-filter
                                #'coq-eglot-compile--outdated-library-p
                                (overlay-get overlay 'coq-eglot-libraries)))))
  (coq-eglot-compile-show-outdated (coq-eglot-position)))

(defun coq-eglot-compile-show-outdated (pos)
  "Mark the outdated Require sentences ending before POS, and the mode line."
  (let (any)
    (dolist (overlay coq-eglot-compile--loaded)
      (let ((outdated (and (<= (overlay-end overlay) pos)
                           (overlay-get overlay 'coq-eglot-outdated))))
        (setq any (or any outdated))
        (overlay-put overlay 'face (and outdated 'coq-eglot-outdated-require))
        (overlay-put overlay 'help-echo
                     (and outdated
                          (concat "Changed since loaded: "
                                  (mapconcat #'abbreviate-file-name
                                             outdated ", "))))
        (overlay-put overlay 'before-string
                     (and outdated
                          (propertize "!" 'display
                                      '(left-fringe exclamation-mark
                                                    warning))))))
    (unless (eq (and any t) coq-eglot-compile--outdated-p)
      (setq coq-eglot-compile--outdated-p (and any t))
      (force-mode-line-update))))

(defun coq-eglot-compile-check-all-outdated ()
  "Run `coq-eglot-compile-check-outdated' in all the script buffers."
  (dolist (buffer (buffer-list))
    (with-current-buffer buffer
      (when coq-eglot-compile--loaded
        (coq-eglot-compile-check-outdated)))))

(defun coq-eglot-compile--file-changed ()
  "A file buffer was saved or reverted: it may be a library."
  (when buffer-file-name
    (coq-eglot-compile-check-all-outdated)))

(defun coq-eglot-compile--file-modified ()
  "A file buffer is about to be modified: it may be a library.
Check after the modification, when the buffer is marked as modified."
  (when buffer-file-name
    (run-at-time 0 nil #'coq-eglot-compile-check-all-outdated)))

(add-hook 'first-change-hook #'coq-eglot-compile--file-modified)
(add-hook 'after-save-hook #'coq-eglot-compile--file-changed)
(add-hook 'after-revert-hook #'coq-eglot-compile--file-changed)

(provide 'coq-eglot-compile)

;;; coq-eglot-compile.el ends here
