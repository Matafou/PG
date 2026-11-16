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
;; - The dates of the editions tell whether an event about an older
;;   version is still valid: no edition before the end of what it is
;;   about since that version.  coq-lsp applies the same rule, it does
;;   not tell the client what it forgets.
;; - The known sentences: overlays on the processed sentences.
;; - The diagnostics: the last snapshot published by the server, on the
;;   part of the text where it is still valid.
;;
;; No display here, no request: the session only records.

;;; Code:

(require 'cl-lib)
(require 'coq-eglot-lsp)                ; the structures of the events
(require 'coq-eglot-sentences)

;;; Validity: the dates of the editions

;; The question: an answer or a notification of the server is about
;; version V of the document and about a part of it ending at X.  Is
;; it still true of the current text?  It is if no edition was made at
;; X or before since V: a sentence depends on all the text before it,
;; and only on it (coq-lsp keeps the common prefix of two versions and
;; checks again the rest).  An edition right at the end of a sentence
;; counts: it may extend the sentence.
;;
;; A local clock dates the editions and the versions: it advances at
;; each edition.  The date of V is the date of its text, the clock
;; when V was the version of the buffer.  For a position X:
;;
;;   I(X) = date of the last edition at X or before, 0 if none
;;
;; and what was said about V up to X is valid iff I(X) <= date(V).
;;
;; I is constant by intervals and grows with X (the last edition at X
;; or before is also at Y or before, for Y > X): it is kept as its
;; points of change, `coq-eglot-session--points', positions increasing
;; with the dates.  An edition at P, at date D:
;;
;; 1. removes the points at P or after: for X >= P, I(X) is now D, the
;;    latest date, whatever they said;
;; 2. adds the point (P . D).
;;
;; The positions of the points stay right without markers: an edition
;; at P moves only the text after P, where no point is left.  Each
;; point is added once and removed at most once.
;;
;; Merging the editions of a sentence: two points (P1 . D1) and
;; (P2 . D2) in the same sentence, P1 < P2, become (P1 . D2), the
;; latest date wins.  It is safe: only I(X) for X between P1 and P2
;; changes, to a later date, which makes fewer answers valid, never
;; more.  And it is exact at the ends of sentences, where the answers
;; mostly are (no end of sentence between P1 and P2): typing in a
;; sentence makes one point, not one per character.  If the guess of
;; the sentence is wrong, merging stays safe.
;;
;; The versions: Eglot gives a version to the text when it sends the
;; changes, several editions may be in one version (since Emacs 30).
;; The exact time does not matter: before an edition, the version of
;; the buffer is still the one of the text before it, it gets the date
;; of now if it has none yet (`coq-eglot-session--before-change').  A
;; version newer than all those dated was not edited since: valid
;; everywhere.  A version between two dated ones never was the version
;; of the buffer at an edition, it gets the date of the older one,
;; which can only make it less valid.

(defvar-local coq-eglot-session-version-function nil
  "Function returning the version of the document the server knows.
Called without argument in the script buffer, see
`coq-eglot-lsp-version'.  A version changes only when the changes of
the buffer are sent, several editions may be in one version.")

(defvar-local coq-eglot-session--clock 0
  "The local clock: the date of the last edition.")

(defvar-local coq-eglot-session--points nil
  "The points of change of I, the last one first.
Each element is (POS . DATE): the last edition at POS or before has
DATE, until the next point.  The positions and the dates decrease
along the list.  See the comment above.")

(defvar-local coq-eglot-session--dates nil
  "The dates of the versions, the most recent version first.
Each element is (VERSION . DATE).")

(defvar-local coq-eglot-session--diagnostics-version nil
  "The version of the last snapshot of diagnostics accepted, or nil.")


(defvar-local coq-eglot-session-sentence-end-function nil
  "Function guessing the end of the sentence at a position.
Called with a position, it returns the end of the sentence containing
it, or starting at it.  Also used to merge the editions of a sentence,
see the comment above.")

(defun coq-eglot-session--version ()
  "The version of the document the server knows."
  (funcall coq-eglot-session-version-function))

(defun coq-eglot-session--same-sentence-p (pos1 pos2)
  "Non-nil if POS1 and POS2 are in the same sentence, POS1 < POS2.
Guessed: no end of sentence between them.  Nil if there is no way to
guess."
  (and coq-eglot-session-sentence-end-function
       (>= (funcall coq-eglot-session-sentence-end-function pos1) pos2)))

(defun coq-eglot-session--before-change (beg _end)
  "Date the edition at BEG, see the comment above.
Before the change: the version is still the one of the text before it,
and the positions before BEG do not move."
  (let ((version (coq-eglot-session--version)))
    ;; the text of VERSION is the one before this edition
    (unless (assoc version coq-eglot-session--dates)
      (push (cons version coq-eglot-session--clock) coq-eglot-session--dates)))
  (let ((date (cl-incf coq-eglot-session--clock)))
    ;; 1. the points at BEG or after are covered by this edition
    (while (and coq-eglot-session--points
                (>= (caar coq-eglot-session--points) beg))
      (pop coq-eglot-session--points))
    ;; 2. the point of this edition, merged with the previous one if in
    ;; the same sentence: the latest date wins
    (let ((last (car coq-eglot-session--points)))
      (if (and last (coq-eglot-session--same-sentence-p (car last) beg))
          (setcdr last date)
        (push (cons beg date) coq-eglot-session--points))))
  (coq-eglot-session--forget-diagnostics beg)
  ;; the bounds of the sentences, after the date: see
  ;; coq-eglot-sentences.el
  (coq-eglot-sentences-observe-edit beg))

(defun coq-eglot-session-clock ()
  "The local clock, the date of the last edition.
In the key of a request, see `coq-eglot-session-ask': a request asked
after an edition never waits for the answer of one asked before."
  coq-eglot-session--clock)

(defun coq-eglot-session--edited (pos)
  "I(POS): the date of the last edition at POS or before, 0 if none."
  (let ((points coq-eglot-session--points))
    (while (and points (> (caar points) pos))
      (pop points))
    (if points (cdar points) 0)))

(defun coq-eglot-session--date (version)
  "The date of the text of VERSION, see the comment above.
The clock if newer than all the dated versions: not edited since."
  (let ((dates coq-eglot-session--dates))
    (cond
     ((or (null dates) (> version (caar dates))) coq-eglot-session--clock)
     (t
      ;; the most recent dated version not newer than VERSION
      (while (and dates (> (caar dates) version))
        (pop dates))
      ;; older than all the dated ones: nothing is valid
      (if dates (cdar dates) -1)))))

(defun coq-eglot-session-validity (version)
  "A predicate telling if what the server said about VERSION is valid.
Called with a position, see `coq-eglot-session-valid-p'.  The date of
VERSION is computed once: for the many diagnostics of a snapshot."
  (let ((date (and version (coq-eglot-session--date version))))
    (lambda (pos)
      (and date (<= (coq-eglot-session--edited pos) date)))))

(defun coq-eglot-session-valid-p (version pos)
  "Non-nil if what the server said about VERSION up to POS is still valid.
No edition at POS or before since VERSION, see the comment above.  POS
is a position of the current text: the positions of VERSION before the
first edition are the same, those after it stay after it once
converted, see coq-eglot-lsp.el."
  (and version
       (<= (coq-eglot-session--edited pos)
           (coq-eglot-session--date version))))

(defun coq-eglot-session-reset ()
  "Forget the dates of the versions: the server opens the document again.
Its versions start again from 0: the diagnostics kept stay, but the
next snapshot replaces them whatever its version.  The dates of the
editions stay, they are about the text."
  (setq coq-eglot-session--dates nil
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
    ;; the goals are kept for the proof position and the sentence
    ;; before, to move back one sentence at once; the messages for all
    (let ((older (nth 2 coq-eglot-session--sentences)))
      (when older (overlay-put older 'coq-eglot-answer nil)))
    sentence))

(defun coq-eglot-session-sentence-start (sentence)
  "The start of SENTENCE, an overlay of the known sentences, or nil."
  (and (< (overlay-start sentence) (overlay-end sentence))
       (overlay-start sentence)))

(defun coq-eglot-session-sentence-answer (sentence)
  "The answer of the server with the goals after SENTENCE, or nil.
SENTENCE is an overlay of the known sentences.  Kept only for the last
two sentences, see `coq-eglot-session-add-sentence'."
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
  (overlay-put sentence 'coq-eglot-answer answer)
  (when answer
    (overlay-put sentence 'coq-eglot-messages
                 (coq-eglot-lsp-answer-messages answer))))

(defun coq-eglot-session-sentence-messages (sentence)
  "The messages of SENTENCE, a list of `coq-eglot-lsp-message'.
Kept when its goals are not, see `coq-eglot-session-add-sentence'."
  (overlay-get sentence 'coq-eglot-messages))

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
  "The diagnostics of the server still valid, a list of (END . DIAG).
DIAG is a `coq-eglot-lsp-diagnostic' of the last snapshot accepted, END
the end of its sentence, see `coq-eglot-session--sentence-end': a
diagnostic depends on all its sentence, Coq executes it again whole.
Kept while the text did not change before END since its version.")

(defun coq-eglot-session--sentence-end (diag)
  "The end of the sentence of DIAG, a `coq-eglot-lsp-diagnostic'.
Its sentence range, which the server gives for the errors (see
`coq-eglot-lsp--options'), otherwise the end of its message: the
warnings, which nothing uses to decide."
  (max (coq-eglot-lsp-diagnostic-end diag)
       (or (cdr (coq-eglot-lsp-diagnostic-sentence diag)) 0)))

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
      (let ((valid-p (coq-eglot-session-validity version)))
        (setq coq-eglot-session--diagnostics-version version)
        (setq coq-eglot-session--diagnostics
              (seq-filter (lambda (entry) (funcall valid-p (car entry)))
                          (mapcar (lambda (diag)
                                    (cons (coq-eglot-session--sentence-end diag)
                                          diag))
                                  (coq-eglot-lsp-diagnostics-diagnostics
                                   diagnostics)))))
      t)))

(defun coq-eglot-session-observe (event)
  "Observe EVENT of the server: record the snapshots of diagnostics.
A function of `coq-eglot-lsp-event-functions'."
  (when (coq-eglot-lsp-diagnostics-p event)
    (coq-eglot-session-receive-diagnostics event)))

(defun coq-eglot-session--forget-diagnostics (pos)
  "Forget the diagnostics whose sentence ends at POS or after.
An edition at POS: a sentence ending at POS is edited too."
  (setq coq-eglot-session--diagnostics
        (seq-remove (lambda (entry) (>= (car entry) pos))
                    coq-eglot-session--diagnostics)))

(defun coq-eglot-session-error (start end)
  "The first error located between START and END, a diagnostic, or nil.
Among the valid diagnostics, see `coq-eglot-session-error-range'."
  (let (first)
    (dolist (diag (mapcar #'cdr coq-eglot-session--diagnostics))
      (let ((beg (coq-eglot-lsp-diagnostic-start diag)))
        (when (and (eq (coq-eglot-lsp-diagnostic-severity diag) 'error)
                   (<= start beg) (< beg end)
                   (or (null first)
                       (< beg (coq-eglot-lsp-diagnostic-start first))))
          (setq first diag))))
    first))

(defun coq-eglot-session-error-range (start end)
  "Buffer range (BEG . END) of the first error located between START and END.
Among the valid diagnostics, nil if none."
  (let (first)
    (dolist (diag (mapcar #'cdr coq-eglot-session--diagnostics))
      (let ((beg (coq-eglot-lsp-diagnostic-start diag)))
        (when (and (eq (coq-eglot-lsp-diagnostic-severity diag) 'error)
                   (<= start beg) (< beg end)
                   (or (null first) (< beg (car first))))
          (setq first (cons beg (coq-eglot-lsp-diagnostic-end diag))))))
    first))

;;; Changes of the state

(defvar coq-eglot-session-state-hook nil
  "Hook run in a script buffer when its session may stop or start waiting.
A target set or reached, an operation or a request starting or ending:
see `coq-eglot-session-settled-p'.")

(defun coq-eglot-session--changed ()
  "Run `coq-eglot-session-state-hook'."
  (run-hooks 'coq-eglot-session-state-hook))

;;; Target and work

;; The target T is where the user asked to go: the sentences up to the
;; one containing the character before T are to be processed.  The
;; proof position, the anchor A, moves toward it as the server checks,
;; never past it.  The work is the operation running to move A toward
;; T: one at a time, never replaced while it runs (cancelling it could
;; interrupt Coq in the middle of a sentence).  See ASYNC-DESIGN.md.

(defvar-local coq-eglot-session--target nil
  "Marker at the target, or nil if the user asked nothing.")

(defvar-local coq-eglot-session--work nil
  "The operation running to move the proof position, or nil.
An object identifying it: what arrives for another one is ignored.")

(defvar-local coq-eglot-session-sentence-start-function nil
  "Function returning the start of the first sentence after a position.
Called with the position, it returns nil if there is none.")


(defun coq-eglot-session-target ()
  "The target, or nil if the user asked nothing."
  (and coq-eglot-session--target
       (marker-position coq-eglot-session--target)))

(defun coq-eglot-session-set-target (pos)
  "Set the target at POS, or forget it if POS is nil."
  (if (null pos)
      (when coq-eglot-session--target
        (set-marker coq-eglot-session--target nil)
        (setq coq-eglot-session--target nil))
    (if coq-eglot-session--target
        (set-marker coq-eglot-session--target pos)
      (setq coq-eglot-session--target (copy-marker pos))))
  (coq-eglot-session--changed))

(defun coq-eglot-session-target-end ()
  "The end of the part to process: the end of the sentence before the target.
Guessed, for the display.  Nil if the user asked nothing."
  (let ((target (coq-eglot-session-target)))
    (and target
         (let ((last (1- (save-excursion (goto-char target)
                                         (forward-comment (- (point)))
                                         (point)))))
           (max target
                (if (< last (point-min)) target
                  (funcall coq-eglot-session-sentence-end-function last)))))))

(defun coq-eglot-session-start-work ()
  "Note that an operation starts to move the proof position, return it."
  (prog1 (setq coq-eglot-session--work (list 'work))
    (coq-eglot-session--changed)))

(defun coq-eglot-session-work-p (work)
  "Non-nil if WORK, an operation, is still the running one."
  (and work (eq work coq-eglot-session--work)))

(defun coq-eglot-session-working-p ()
  "Non-nil if an operation moving the proof position runs."
  (and coq-eglot-session--work t))

(defun coq-eglot-session-finish-work (work)
  "Note that WORK, an operation, is finished, if still the running one."
  (when (coq-eglot-session-work-p work)
    (setq coq-eglot-session--work nil)
    (coq-eglot-session--changed)))

(defun coq-eglot-session-stop-work ()
  "Forget the target and the running operation: nothing to do any more."
  (coq-eglot-session-set-target nil)
  (setq coq-eglot-session--work nil)
  (coq-eglot-session--changed))

(defun coq-eglot-session-next-action ()
  "The next operation to move the proof position toward the target, or nil.
Nil while an operation runs, or if there is nothing to do: then the
target is forgotten.  Otherwise (step START): process the sentence
starting at START, the only one before the target; or (check START
TARGET): process the sentences from START to the one containing the
character before TARGET."
  (let* ((target (coq-eglot-session-target))
         (start (and target
                     (funcall coq-eglot-session-sentence-start-function
                              (coq-eglot-session-position)))))
    (cond
     (coq-eglot-session--work nil)
     ((null target) nil)
     ((or (null start) (>= start target))
      (coq-eglot-session-set-target nil)
      nil)
     ((>= (funcall coq-eglot-session-sentence-end-function start)
          (coq-eglot-session-target-end))
      (list 'step start))
     (t (list 'check start target)))))

;;; Requests in flight

;; The requests sent and not answered yet, besides the operation that
;; moves the proof position: the goals at a position, for instance.
;; One per key: asking again what is already asked waits for the same
;; answer, see `coq-eglot-session-ask'.  Who asked is not kept, only
;; what to do with the answer.  The key says all what the answer
;; depends on, including the date of the text (`coq-eglot-session-clock'):
;; after an edition, a new request is sent, it does not wait for an
;; answer that will not be valid.  The requests stay until answered,
;; even if their answer will be ignored: the session is at rest only
;; when the server answered everything.

(defvar-local coq-eglot-session--requests nil
  "The requests in flight, a list of (KEY . CALLBACKS).
KEY says what is asked, like (goals . POS).  CALLBACKS are called with
the answer, in the order they asked.")

(defun coq-eglot-session-ask (key callback send)
  "Ask KEY, call CALLBACK with the answer.
If KEY is not asked yet, call SEND with a function to call with the
answer, or with nil if the request failed: SEND sends the request.
Otherwise CALLBACK waits for the same answer."
  (let ((entry (assoc key coq-eglot-session--requests)))
    (if entry
        (setcdr entry (append (cdr entry) (list callback)))
      (push (list key callback) coq-eglot-session--requests)
      (coq-eglot-session--changed)
      (let ((buffer (current-buffer)))
        (condition-case err
            (funcall send
                     (lambda (answer)
                       (when (buffer-live-p buffer)
                         (with-current-buffer buffer
                           (coq-eglot-session--answered key answer)))))
          (error (coq-eglot-session--answered key nil)
                 (signal (car err) (cdr err))))))))

(defun coq-eglot-session--answered (key answer)
  "KEY was answered with ANSWER: call its callbacks, it is no longer asked."
  (let ((entry (assoc key coq-eglot-session--requests)))
    (when entry
      (setq coq-eglot-session--requests
            (delq entry coq-eglot-session--requests))
      (coq-eglot-session--changed)
      (dolist (callback (cdr entry))
        (funcall callback answer)))))

(defun coq-eglot-session-asked-p (&optional key)
  "Non-nil if KEY is asked, or any request if KEY is nil."
  (if key (and (assoc key coq-eglot-session--requests) t)
    (and coq-eglot-session--requests t)))

(defun coq-eglot-session-forget-requests ()
  "Forget the requests in flight: their answers will be ignored.
After a cancellation, or when the server stops."
  (setq coq-eglot-session--requests nil)
  (coq-eglot-session--changed))

(defun coq-eglot-session-settled-p ()
  "Non-nil if the session is at rest: nothing asked, nothing to do.
No target, no operation running, no request in flight."
  (not (or (coq-eglot-session-target)
           coq-eglot-session--work
           coq-eglot-session--requests)))

;;; Start and stop

(defun coq-eglot-session-start (version-function)
  "Start the session of the current buffer.
VERSION-FUNCTION gives the version the server knows, see
`coq-eglot-session-version-function'."
  (setq coq-eglot-session-version-function version-function)
  (setq coq-eglot-sentences-valid-function #'coq-eglot-session-valid-p)
  (coq-eglot-session-reset)
  (add-hook 'coq-eglot-lsp-event-functions #'coq-eglot-sentences-observe nil t)
  (add-hook 'coq-eglot-lsp-event-functions #'coq-eglot-session-observe nil t)
  (add-hook 'before-change-functions #'coq-eglot-session--before-change nil t))

(defun coq-eglot-session-stop ()
  "Stop the session of the current buffer, forget everything."
  (remove-hook 'before-change-functions #'coq-eglot-session--before-change t)
  (remove-hook 'coq-eglot-lsp-event-functions #'coq-eglot-sentences-observe t)
  (remove-hook 'coq-eglot-lsp-event-functions #'coq-eglot-session-observe t)
  (coq-eglot-session-forget-sentences (1- (point-min)))
  (coq-eglot-session-stop-work)
  (coq-eglot-session-forget-requests)
  (setq coq-eglot-session--points nil)
  (coq-eglot-sentences-clear)
  (setq coq-eglot-session--diagnostics nil
        coq-eglot-session--diagnostics-version nil)
  (coq-eglot-session-reset))

(provide 'coq-eglot-session)

;;; coq-eglot-session.el ends here
