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

;;; Code:

(require 'coq-par-compile)
(require 'coq-indent)
(require 'coq-eglot-lsp)

;; Settings of the Proof General backend (coq.el, pg-custom.el), used
;; by coq-system.el
(defvar coq-prog-args nil
  "Arguments given to the compiler, on top of the load path.
Set from _CoqProject by `coq-load-project-file'.")
(defvar coq-debug nil
  "Non-nil to display debugging messages of the Coq settings.")

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
        (coq-eglot-lsp-workspace-update))
      (funcall (plist-get state :on-done) limit))))

(defun coq-eglot-compile--release (items)
  "The compilation for the Require sentences of ITEMS is finished.
`coq-par-release-items-function' of the script buffers."
  (when coq-eglot-compile--state
    (dolist (item items)
      (if (overlayp (car item))
          (let ((pending (plist-get coq-eglot-compile--state :pending)))
            (delete-overlay (car item))
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

(provide 'coq-eglot-compile)

;;; coq-eglot-compile.el ends here
