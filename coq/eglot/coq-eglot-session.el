;;; coq-eglot-session.el --- What the Coq server said about a script  -*- lexical-binding: t; -*-

;; This file is part of Proof General.

;; Portions © Copyright 2026  Pierre Courtieu

;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;;
;; The session of a script buffer: what the server said about it and
;; is still valid.  Between the adapter of the protocol,
;; coq-eglot-lsp.el, which gives the events of the server with the
;; version of the document and the positions they are about, and the
;; interface, coq-eglot.el, which displays and runs the commands.
;;
;; - The journal of the versions tells whether an event about an older
;;   version is still valid: the text before the first position edited
;;   since did not change.  coq-lsp applies the same rule, it does not
;;   tell the client what it forgets.
;; - The known sentences: overlays on the processed sentences.
;; - The diagnostics: the last snapshot published by the server, on the
;;   part of the text where it is still valid.
;;
;; No display here, no request: the session only records.

;;; Code:

(require 'cl-lib)
(require 'coq-eglot-lsp)                ; the structures of the events

;;; Versions

(defvar-local coq-eglot-session--diagnostics-version nil
  "The version of the last snapshot of diagnostics accepted, or nil.")

(defvar-local coq-eglot-session-version-function nil
  "Function returning the version of the document the server knows.
Called without argument in the script buffer, see
`coq-eglot-lsp-version'.  A version changes only when the changes of
the buffer are sent, several editions may be in one version.")

(defvar-local coq-eglot-session--journal nil
  "The versions edited since they were sent, the most recent first.
Each element is (VERSION . EDITED): EDITED is the smallest position
edited since the text of VERSION was sent.  A version without element,
more recent than the first one, was not edited since.  See
`coq-eglot-session-valid-p'.")

(defvar-local coq-eglot-session--floor 0
  "The versions before this one are forgotten: nothing about them is valid.")

(defconst coq-eglot-session--journal-size 50
  "Number of versions kept in `coq-eglot-session--journal'.")

(defun coq-eglot-session--version ()
  "The version of the document the server knows."
  (funcall coq-eglot-session-version-function))

(defun coq-eglot-session--before-change (beg _end)
  "Record an edition at BEG in the journal of the versions.
Before the change: the version is still the one of the text before it."
  (let ((version (coq-eglot-session--version)))
    (unless (eql (caar coq-eglot-session--journal) version)
      (push (cons version beg) coq-eglot-session--journal))
    (dolist (entry coq-eglot-session--journal)
      (setcdr entry (min (cdr entry) beg))))
  ;; nothing is valid about these versions any more
  (let ((kept (cl-loop for entry in coq-eglot-session--journal
                       for i from 1
                       while (and (> (cdr entry) (point-min))
                                  (<= i coq-eglot-session--journal-size))
                       collect entry)))
    (when (< (length kept) (length coq-eglot-session--journal))
      (setq coq-eglot-session--floor
            (1+ (car (nth (length kept) coq-eglot-session--journal))))
      (setq coq-eglot-session--journal kept)))
  (coq-eglot-session--forget-diagnostics beg))

(defun coq-eglot-session-edited (version)
  "The smallest position edited since the text of VERSION was sent.
Nil if not edited since, 0 if VERSION is forgotten."
  (cond
   ((< version coq-eglot-session--floor) 0)
   (t
    ;; the oldest version recorded since VERSION: its editions are
    ;; after VERSION
    (let ((edited nil))
      (dolist (entry coq-eglot-session--journal)
        (when (>= (car entry) version)
          (setq edited (cdr entry))))
      edited))))

(defun coq-eglot-session-valid-p (version pos)
  "Non-nil if what the server said about VERSION before POS is still valid.
The text before POS did not change since VERSION: POS is before the
first position edited since.  POS is a position of the current text:
positions of VERSION before the first edition are the same, those
after it stay after it once converted, see coq-eglot-lsp.el."
  (let ((edited (and version (coq-eglot-session-edited version))))
    (and version (or (null edited) (< pos edited)))))

(defun coq-eglot-session-reset ()
  "Forget the journal of the versions: the server opens the document again.
Its versions start again from 0: the diagnostics kept stay, but the
next snapshot replaces them whatever its version."
  (setq coq-eglot-session--journal nil
        coq-eglot-session--floor 0
        coq-eglot-session--diagnostics-version nil))

;;; The known sentences

(defvar-local coq-eglot-session--sentences nil
  "The known processed sentences, the last one first.
Each one is an overlay with a non-nil `coq-eglot-sentence' property,
see `coq-eglot-session-add-sentence'.  The text before its end did not
change since the server checked it, so what it records is still valid:
an edition forgets the sentences it touches, see
`coq-eglot-session-forget-sentences'.  Not every processed sentence has
an overlay.  The proof position is the end of the first one, or the
beginning of the buffer.")

(defun coq-eglot-session-last-sentence ()
  "The overlay of the last known processed sentence, or nil.
Forget the overlays deleted by others, for instance by
`remove-overlays' without properties."
  (while (and coq-eglot-session--sentences
              (null (overlay-buffer (car coq-eglot-session--sentences))))
    (pop coq-eglot-session--sentences))
  (car coq-eglot-session--sentences))

(defun coq-eglot-session-sentences ()
  "The overlays of the known processed sentences, the last one first."
  (coq-eglot-session-last-sentence)
  (seq-filter #'overlay-buffer coq-eglot-session--sentences))

(defun coq-eglot-session-add-sentence (end answer)
  "Record a processed sentence ending at END, with ANSWER, and return it.
ANSWER is a `coq-eglot-lsp-answer' with the goals after the sentence,
or nil, see `coq-eglot-session-set-sentence-answer'."
  (let ((sentence (make-overlay end end nil nil nil)))
    (overlay-put sentence 'coq-eglot-sentence t)
    (coq-eglot-session-set-sentence-answer sentence answer)
    (push sentence coq-eglot-session--sentences)
    sentence))

(defun coq-eglot-session-sentence-start (sentence)
  "The start of SENTENCE, an overlay of the known sentences, or nil."
  (and (< (overlay-start sentence) (overlay-end sentence))
       (overlay-start sentence)))

(defun coq-eglot-session-sentence-answer (sentence)
  "The answer of the server with the goals after SENTENCE, or nil.
SENTENCE is an overlay of the known sentences."
  (overlay-get sentence 'coq-eglot-answer))

(defun coq-eglot-session-set-sentence-answer (sentence answer)
  "Record ANSWER as the answer of the server after SENTENCE.
SENTENCE is an overlay of the known sentences.  The sentence of ANSWER,
if it ends there, gives the start of the overlay: it is empty, at the
end of the sentence, while the start is unknown."
  (let ((end (overlay-end sentence))
        (bounds (and answer (coq-eglot-lsp-answer-sentence answer))))
    (when (and bounds (= (cdr bounds) end) (< (car bounds) end))
      (move-overlay sentence (car bounds) end)))
  (overlay-put sentence 'coq-eglot-answer answer))

(defun coq-eglot-session-sentence-ending-at (end)
  "The overlay of the known processed sentence ending at END, or nil."
  (seq-find (lambda (sentence)
              (and (overlay-buffer sentence) (= (overlay-end sentence) end)))
            coq-eglot-session--sentences))

(defun coq-eglot-session-forget-sentences (pos)
  "Forget the known processed sentences ending after POS."
  (while (and (coq-eglot-session-last-sentence)
              (> (overlay-end (car coq-eglot-session--sentences)) pos))
    (delete-overlay (pop coq-eglot-session--sentences))))

(defun coq-eglot-session-position ()
  "The proof position: the end of the last known processed sentence."
  (let ((last (coq-eglot-session-last-sentence)))
    (if last (overlay-end last) (point-min))))

;;; Diagnostics

(defvar-local coq-eglot-session--diagnostics nil
  "The diagnostics of the server still valid, a list.
Of `coq-eglot-lsp-diagnostic': those of the last snapshot accepted,
before the first position edited since.")

(defun coq-eglot-session-receive-diagnostics (diagnostics)
  "Record DIAGNOSTICS, a `coq-eglot-lsp-diagnostics' snapshot.
It replaces the previous one, on the part of the text where it is still
valid, see `coq-eglot-session-valid-p'.  Ignored if older than the
previous one.  Return non-nil if recorded."
  (let ((version (coq-eglot-lsp-diagnostics-version diagnostics)))
    (when (and version
               (not (and coq-eglot-session--diagnostics-version
                         (< version coq-eglot-session--diagnostics-version)))
               (coq-eglot-session-valid-p version (point-min)))
      (setq coq-eglot-session--diagnostics-version version)
      (setq coq-eglot-session--diagnostics
            (seq-filter (lambda (diag)
                          (coq-eglot-session-valid-p
                           version (coq-eglot-lsp-diagnostic-end diag)))
                        (coq-eglot-lsp-diagnostics-diagnostics diagnostics)))
      t)))

(defun coq-eglot-session--forget-diagnostics (pos)
  "Forget the diagnostics ending at POS or after: an edition at POS."
  (setq coq-eglot-session--diagnostics
        (seq-remove (lambda (diag) (>= (coq-eglot-lsp-diagnostic-end diag) pos))
                    coq-eglot-session--diagnostics)))

(defun coq-eglot-session-error-range (start end)
  "Buffer range (BEG . END) of the first error located between START and END.
Among the valid diagnostics, nil if none."
  (let (first)
    (dolist (diag coq-eglot-session--diagnostics)
      (let ((beg (coq-eglot-lsp-diagnostic-start diag)))
        (when (and (eq (coq-eglot-lsp-diagnostic-severity diag) 'error)
                   (<= start beg) (< beg end)
                   (or (null first) (< beg (car first))))
          (setq first (cons beg (coq-eglot-lsp-diagnostic-end diag))))))
    first))

;;; Start and stop

(defun coq-eglot-session-start (version-function)
  "Start the session of the current buffer.
VERSION-FUNCTION gives the version the server knows, see
`coq-eglot-session-version-function'."
  (setq coq-eglot-session-version-function version-function)
  (coq-eglot-session-reset)
  (add-hook 'before-change-functions #'coq-eglot-session--before-change nil t))

(defun coq-eglot-session-stop ()
  "Stop the session of the current buffer, forget everything."
  (remove-hook 'before-change-functions #'coq-eglot-session--before-change t)
  (coq-eglot-session-forget-sentences (1- (point-min)))
  (setq coq-eglot-session--diagnostics nil
        coq-eglot-session--diagnostics-version nil)
  (coq-eglot-session-reset))

(provide 'coq-eglot-session)

;;; coq-eglot-session.el ends here
