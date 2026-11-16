;;; coq-eglot-sentences.el --- The bounds of the sentences of a Coq script  -*- lexical-binding: t; -*-

;; This file is part of Proof General.

;; Portions © Copyright 2026  Pierre Courtieu

;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;;
;; An observer of the events of the server (coq-eglot-lsp.el) that
;; learns the bounds of the sentences of the script: the range of each
;; sentence the server executes, of the answers of the goals, of the
;; errors.  Only facts: not that the sentences are checked, nothing
;; displayed, no request sent, no decision.  The session and the
;; interface ask it where the sentence before a position ends.
;;
;; The bounds are kept as a list of (START . END), the last one first,
;; in a `coq-eglot-sentences' structure, buffer-local.  Like the points
;; of the dates (coq-eglot-session.el), the positions stay right
;; without markers: an edition at P removes the ranges ending at P or
;; after (a sentence ending at P is edited too), and the text before P
;; does not move.  Whether an event of an older version is still valid
;; is told by the session, see `coq-eglot-sentences-valid-function'.
;;
;; The editions come from the buffer: the session calls
;; `coq-eglot-sentences-observe-edit' before each change, after dating
;; it.  The events come from the server, see
;; `coq-eglot-lsp-event-functions'.

;;; Code:

(require 'cl-lib)
(require 'seq)
(require 'coq-eglot-lsp)                ; the structures of the events

(cl-defstruct (coq-eglot-sentences
               (:constructor coq-eglot-sentences-make ()))
  "The bounds of the sentences the server told.
RANGES is a list of (START . END), not overlapping, the ends
decreasing: the last sentence first."
  ranges)

(defvar-local coq-eglot-sentences nil
  "The bounds of the sentences of the current buffer, or nil.
A `coq-eglot-sentences', made when first needed.")

(defvar-local coq-eglot-sentences-valid-function nil
  "Function telling whether what the server said is still valid.
Called with a version and a position, see `coq-eglot-session-valid-p'.")

(defvar-local coq-eglot-sentences-start-function nil
  "Function returning the start of the first sentence after a position.
Called with the position, it returns nil if there is none.")

(defvar coq-eglot-sentences-change-hook nil
  "Hook run in a script buffer when the known bounds of its sentences change.
Learned from the server, or forgotten by an edition.")

(defun coq-eglot-sentences--index ()
  "The bounds of the sentences of the current buffer."
  (or coq-eglot-sentences
      (setq coq-eglot-sentences (coq-eglot-sentences-make))))

(defun coq-eglot-sentences--ranges ()
  "The known ranges of the current buffer, the last one first."
  (and coq-eglot-sentences (coq-eglot-sentences-ranges coq-eglot-sentences)))

(defun coq-eglot-sentences--changed ()
  "Run `coq-eglot-sentences-change-hook'."
  (run-hooks 'coq-eglot-sentences-change-hook))

;;; Learning

(defun coq-eglot-sentences--insert (ranges start end)
  "RANGES with (START . END), which replaces the ranges it overlaps."
  (if (or (null ranges) (>= start (cdar ranges)))
      ;; after all the others: the server executes in order
      (cons (cons start end) ranges)
    (let ((kept (seq-remove (lambda (range)
                              (and (< (car range) end) (> (cdr range) start)))
                            ranges))
          (after nil))
      (while (and kept (> (cdar kept) end))
        (push (pop kept) after))
      (nconc (nreverse after) (cons (cons start end) kept)))))

(defun coq-eglot-sentences-learn (version start end)
  "Record the sentence from START to END of VERSION, if still valid.
See `coq-eglot-sentences-valid-function'.  Return non-nil if new."
  (when (and version (< start end)
             (funcall coq-eglot-sentences-valid-function version end))
    (let* ((index (coq-eglot-sentences--index))
           (ranges (coq-eglot-sentences-ranges index)))
      (unless (member (cons start end) ranges)
        (setf (coq-eglot-sentences-ranges index)
              (coq-eglot-sentences--insert ranges start end))
        (coq-eglot-sentences--changed)
        t))))

(defun coq-eglot-sentences-observe (event)
  "Learn the bounds of the sentences from EVENT of the server.
A function of `coq-eglot-lsp-event-functions'."
  (cond
   ((coq-eglot-lsp-execution-p event)
    (coq-eglot-sentences-learn (coq-eglot-lsp-execution-version event)
                               (coq-eglot-lsp-execution-start event)
                               (coq-eglot-lsp-execution-end event)))
   ((coq-eglot-lsp-answer-p event)
    (let ((sentence (coq-eglot-lsp-answer-sentence event))
          (context (coq-eglot-lsp-answer-context event)))
      (when sentence
        (coq-eglot-sentences-learn
         (or (coq-eglot-lsp-answer-version event)
             (and context (coq-eglot-lsp-context-version context)))
         (car sentence) (cdr sentence)))))
   ((coq-eglot-lsp-diagnostics-p event)
    (let ((version (coq-eglot-lsp-diagnostics-version event)))
      (dolist (diag (coq-eglot-lsp-diagnostics-diagnostics event))
        (let ((sentence (coq-eglot-lsp-diagnostic-sentence diag)))
          (when sentence
            (coq-eglot-sentences-learn version (car sentence)
                                       (cdr sentence)))))))))

(defun coq-eglot-sentences-observe-edit (beg)
  "Forget the bounds of the sentences ending at BEG or after.
Before an edition at BEG."
  (let ((index coq-eglot-sentences)
        (forgot nil))
    (when index
      (while (and (coq-eglot-sentences-ranges index)
                  (>= (cdar (coq-eglot-sentences-ranges index)) beg))
        (pop (coq-eglot-sentences-ranges index))
        (setq forgot t))
      (when forgot (coq-eglot-sentences--changed)))))

(defun coq-eglot-sentences-clear ()
  "Forget all the bounds of the sentences of the current buffer."
  (when (coq-eglot-sentences--ranges)
    (setf (coq-eglot-sentences-ranges coq-eglot-sentences) nil)
    (coq-eglot-sentences--changed)))

;;; Searching

(defun coq-eglot-sentences-range-before (pos)
  "The range (START . END) of the last known sentence ending at POS or before.
Nil if none is known.  Not necessarily the last sentence before POS:
one the server did not tell of may be between, see
`coq-eglot-sentences-previous-end'."
  (seq-find (lambda (range) (<= (cdr range) pos))
            (coq-eglot-sentences--ranges)))

(defun coq-eglot-sentences-range-ending-at (end)
  "The range (START . END) of the known sentence ending at END, or nil."
  (seq-find (lambda (range) (= (cdr range) end))
            (coq-eglot-sentences--ranges)))

(defun coq-eglot-sentences-previous-end (pos)
  "The end of the last sentence ending at POS or before, if surely known.
`point-min' if there is none.  Nil if a sentence the server did not
tell of may be between the last known one and POS.  Sure when nothing
but blanks and comments follow the end of the last known sentence up to
POS, or up to the next known sentence, which then contains POS.  See
`coq-eglot-sentences-start-function'."
  (let* ((ranges (coq-eglot-sentences--ranges))
         (tail (seq-drop-while (lambda (range) (> (cdr range) pos)) ranges))
         (end (if tail (cdar tail) (point-min)))
         ;; the known sentence after it, maybe containing POS
         (next (car (last (seq-take-while (lambda (range) (> (cdr range) pos))
                                          ranges))))
         (start (funcall coq-eglot-sentences-start-function end)))
    (and (or (null start) (>= start pos)
             (and next (= (car next) start)))
         end)))

(provide 'coq-eglot-sentences)

;;; coq-eglot-sentences.el ends here
