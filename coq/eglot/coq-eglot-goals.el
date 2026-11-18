;;; coq-eglot-goals.el --- The text of the goals  -*- lexical-binding:t -*-

;; This file is part of Proof General.

;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;;
;; The text of the goals, from the answers of the server: the first
;; goal like Coq prints it, its compatible hypotheses on the same line
;; with `coq-eglot-compact-contexts', then the goals after it.  Their
;; display, in the goals buffers, is in coq-eglot.el, see
;; `coq-eglot--show-goals'.
;;
;; With `coq-eglot-detailed-goals', the goals after the first one keep
;; their hypotheses, folded under their title, and the unfocused goals
;; are grouped by level, with the bullet that focuses the next one.
;; The server gives all this: the hypotheses of every goal, the levels
;; of the focus stack, and the suggestion of Coq for the next bullet.
;;
;; The structure is in text properties, no backend reads it in the
;; text: `coq-eglot-goal-title' on the title of a goal with hypotheses,
;; its key, and `invisible' with the same key on its hypotheses.  And
;; `coq-other-goals-start' where the folding of coq-goals.el starts.

;;; Code:

(require 'cl-lib)
(require 'subr-x)
(require 'coq-goals)                    ; coq-other-goals-face

(declare-function coq-eglot--hyps-width "coq-eglot" ())
(declare-function coq-eglot--compact-contexts-p "coq-eglot" ())

(defcustom coq-eglot-detailed-goals t
  "Non-nil: the goals after the first one with their hypotheses.
Their hypotheses are folded under their title, RET or mouse-1 there
unfolds them: folded, they take no room.  The unfocused goals are
grouped by level, the innermost first, with the bullet that focuses the
next goal.  Nil: only their conclusion, like Coq."
  :type 'boolean
  :safe #'booleanp
  :group 'coq-eglot)

(defface coq-eglot-goals-level
  '((t :inherit shadow))
  "Face of the lines giving the levels of the unfocused goals."
  :group 'coq-eglot)

(defvar coq-eglot-goals--unfolded nil
  "Keys of the goals whose hypotheses are unfolded, see `coq-eglot-goals--key'.")

;;; The first goal

(defun coq-eglot--trim-lines (text)
  "TEXT without blanks at the end of its lines.
Coq leaves a space before some line breaks: in a line as wide as the
window, it would wrap."
  (replace-regexp-in-string "[ \t]+$" "" text))

(defun coq-eglot--indent (text indentation)
  "TEXT with INDENTATION, a string, at the beginning of its lines but the first.
Without blanks at the end of its lines, see `coq-eglot--trim-lines'."
  (string-replace "\n" (concat "\n" indentation)
                  (coq-eglot--trim-lines text)))

(defun coq-eglot--fill-names (names width)
  "Join NAMES with commas, in lines of at most WIDTH characters.
The lines after the first one are indented by 2, like Coq does.  Room
is left for the comma or the colon after them."
  (let ((lines nil) (line nil))
    (dolist (name names)
      (let ((candidate (if line (concat line ", " name) name)))
        (if (or (null line) (<= (+ 2 (length candidate)) width))
            (setq line candidate)
          (push (concat line ",") lines)
          (setq line name))))
    (mapconcat #'identity (nreverse (cons line lines)) "\n  ")))

(defun coq-eglot--format-hyp (hyp)
  "Format hypothesis HYP of a goal.
Like Coq does: if it does not fit on one line, its names are on several
lines, and its type goes below them, indented.  The text has the
property `coq-hyp', the list of its names, and the part after the
names the property `coq-hyp-body', to highlight and fold it, see
`coq-hyps-decorate'."
  (let* ((names (append (plist-get hyp :names) nil))
         (width (coq-eglot--hyps-width))
         (names-text (coq-eglot--fill-names names (- width 2)))
         (last-line (car (last (split-string names-text "\n"))))
         (def (and (plist-get hyp :def)
                   (coq-eglot--trim-lines (plist-get hyp :def))))
         (ty (coq-eglot--trim-lines (plist-get hyp :ty)))
         (one-line (concat (if def (concat " := " def) "") " : " ty))
         (body
          ;; the server printed TY alone, without the names
          (if (and (not (string-search "\n" one-line))
                   (<= (+ 2 (length last-line) (length one-line)) width))
              one-line
            (concat (if def
                        (concat " :=\n    " (coq-eglot--indent def "    ")
                                "\n    : " (coq-eglot--indent ty "      "))
                      (concat " :\n    " (coq-eglot--indent ty "    ")))))))
    (propertize
     (concat "  " names-text (propertize body 'coq-hyp-body t))
     'coq-hyp names)))

(defun coq-eglot--simple-hyp-p (hyp text sorts)
  "Non-nil if HYP, formatted as TEXT, can share its line with others.
An assumption, not a definition, whose type is in Type, neither in Prop
nor in SProp, see SORTS, the alist of
`coq-eglot-lsp--parse-hyp-sorts'.  And TEXT is on one line."
  (and (not (plist-get hyp :def))
       (not (string-search "\n" text))
       (seq-every-p (lambda (name)
                      (let ((sort (cdr (assoc name sorts))))
                        (and sort (not (member sort '("Prop" "SProp"))))))
                    (plist-get hyp :names))))

(defun coq-eglot--format-hyps (goal)
  "Format the hypotheses of GOAL, one per line.
With `coq-eglot-compact-contexts', put compatible hypotheses on the
same line, three spaces apart, as many as fit in the width.  GOAL must
have their sorts, see `coq-eglot--simple-hyp-p'."
  (let ((sorts (and (coq-eglot--compact-contexts-p)
                    (plist-get goal :hyp-sorts)))
        (width (coq-eglot--hyps-width))
        (lines nil)
        (line nil))                     ; the current line of simple hyps
    (dolist (hyp (append (plist-get goal :hyps) nil))
      (let ((text (coq-eglot--format-hyp hyp)))
        (cond
         ((not (and sorts (coq-eglot--simple-hyp-p hyp text sorts)))
          (when line (push line lines) (setq line nil))
          (push text lines))
         ;; each hyp keeps its indentation of 2, for its folding button
         ((and line (<= (+ (length line) 1 (length text)) width))
          (setq line (concat line " " text)))
         (t
          (when line (push line lines))
          (setq line text)))))
    (when line (push line lines))
    (mapconcat (lambda (text) (concat text "\n")) (nreverse lines) "")))

(defun coq-eglot--first-goal (goals)
  "The first focused goal of GOALS, or nil."
  (let ((focused (and goals (plist-get goals :goals))))
    (and (> (length focused) 0) (aref focused 0))))

(defun coq-eglot--format-conclusion (goal &optional no-separator)
  "Format the conclusion of GOAL, below the separator unless NO-SEPARATOR."
  (concat (if no-separator "" "  ============================\n")
          "  " (coq-eglot--indent (plist-get goal :ty) "  ") "\n"))

;;; The goals, like Coq

(defun coq-eglot--unfocused-p (goals)
  "Non-nil if GOALS has unfocused goals."
  (seq-some (lambda (level)
              (seq-some (lambda (side) (> (length side) 0)) level))
            (plist-get goals :stack)))

(defun coq-eglot--unfocused-count (goals)
  "Number of unfocused goals of GOALS."
  (seq-reduce (lambda (count level)
                (seq-reduce (lambda (count side) (+ count (length side)))
                            level count))
              (plist-get goals :stack) 0))

(defun coq-eglot--unfocused-goals (goals)
  "The unfocused goals of GOALS, the innermost level first."
  (seq-mapcat (lambda (level) (seq-mapcat #'identity level 'list))
              (plist-get goals :stack) 'list))

(defun coq-eglot--format-goal-list (goals first)
  "Format GOALS, numbered from FIRST, like Coq does for the other goals."
  (let ((i (1- first)))
    (mapconcat (lambda (goal)
                 (setq i (1+ i))
                 (format "\ngoal %d is:\n %s\n" i
                         (coq-eglot--indent (plist-get goal :ty) " ")))
               goals "")))

(defun coq-eglot--format-other-goals (goals)
  "Format the goals of GOALS after the first one.
Like Coq with Set Printing Unfocused: the unfocused goals come after a
line \"*** Unfocused goals:\".  coq-goals.el folds them, see
`coq-fold-other-goals'.  With their hypotheses and levels if
`coq-eglot-detailed-goals'."
  (if coq-eglot-detailed-goals
      (coq-eglot-goals-format-other goals)
    (let ((others (cdr (append (plist-get goals :goals) nil)))
          (unfocused (coq-eglot--unfocused-goals goals)))
      (concat (coq-eglot--format-goal-list others 2)
              (when unfocused
                (concat "\n*** Unfocused goals:\n"
                        (coq-eglot--format-goal-list unfocused
                                                     (+ 2 (length others)))))))))

(defun coq-eglot--format-goals-parts (goals &optional no-separator)
  "Format GOALS, as returned by the server, like Coq does.
Return (HYPOTHESES . REST): the number of goals and the hypotheses of
the first one, then its conclusion and the other goals.  Both are empty
if GOALS is nil (outside of proofs).  Without the separator line before
the conclusion if NO-SEPARATOR."
  (if (null goals)
      (cons "" "")
    (let* ((focused (plist-get goals :goals))
           (n (length focused)))
      (cond
       ((> n 0)
        (cons
         (concat (format "%d goal%s\n\n" n (if (= n 1) "" "s"))
                 (coq-eglot--format-hyps (aref focused 0)))
         (concat
          (coq-eglot--format-conclusion (aref focused 0) no-separator)
          (coq-eglot--format-other-goals goals))))
       ((coq-eglot--unfocused-p goals)
        (let ((unfocused (coq-eglot--unfocused-goals goals)))
          (cons ""
                (concat "This subproof is complete, but there are some unfocused goals.\n"
                        ;; like Coq: "Focus next goal with bullet -."
                        (coq-eglot-goals-bullet-line goals)
                        (format "\n%d goal%s\n" (length unfocused)
                                (if (cdr unfocused) "s" ""))
                        (if coq-eglot-detailed-goals
                            (coq-eglot-goals-format-unfocused goals)
                          (coq-eglot--format-goal-list unfocused 1))))))
       ((> (length (plist-get goals :given_up)) 0)
        (cons "" "No more goals, but there are some goals you gave up.\n"))
       ((> (length (plist-get goals :shelf)) 0)
        (cons "" "All the remaining goals are on the shelf.\n"))
       (t (cons "" "No more goals.\n"))))))

(defun coq-eglot--format-goals (goals)
  "Format GOALS, as returned by the server, like Coq does.
Return the empty string if GOALS is nil (outside of proofs)."
  (let ((parts (coq-eglot--format-goals-parts goals)))
    (concat (car parts) (cdr parts))))

;;; The next bullet

(defun coq-eglot-goals-bullet-line (goals)
  "The suggestion of Coq for the next bullet in GOALS, as a line, or \"\".
Like \"Focus next goal with bullet -.\", which Coq prints after
\"This subproof is complete\"."
  (let ((bullet (plist-get goals :bullet)))
    (if (and (stringp bullet) (not (string-empty-p bullet)))
        (concat bullet "\n")
      "")))

(defun coq-eglot-goals--levels (goals)
  "The unfocused goals of GOALS by level, as a list of (DEPTH . GOALS).
The innermost level first, at depth 1.  Without the empty levels."
  (let ((depth 0)
        levels)
    (seq-doseq (level (plist-get goals :stack))
      (setq depth (1+ depth))
      (let ((goals (seq-mapcat #'identity level 'list)))
        (when goals
          (push (cons depth goals) levels))))
    (nreverse levels)))

(defun coq-eglot-goals--bullet-hint (goals levels)
  "The next bullet of GOALS for one of its LEVELS, as (DEPTH . TEXT), or nil.
From the suggestion of Coq, see `coq-eglot-goals-bullet-line'.  It is
for the innermost level that has goals.  If the current bullet is
unfinished, the same bullet focuses the goals of the innermost level,
if it has some."
  (let ((bullet (plist-get goals :bullet))
        (first (car levels)))
    (when (and (stringp bullet) first)
      (cond
       ((string-match "\\`Focus next goal with bullet \\(.+\\)\\.\\'" bullet)
        (cons (car first) (concat "next bullet: " (match-string 1 bullet))))
       ((and (string-match "\\`The current bullet \\(.+\\) is unfinished\\.\\'"
                           bullet)
             (= (car first) 1))
        (cons 1 (concat "next bullet: " (match-string 1 bullet))))
       ((string-match-p "\\`Try unfocusing with \"}\"\\.\\'" bullet)
        (cons (car first) "after }"))))))

;;; The other goals, detailed

(defun coq-eglot-goals--key (goal number)
  "Key of GOAL, numbered NUMBER: a symbol, the same in the next goals.
From its existential variable, from NUMBER if the server does not give
it."
  (let* ((evar (plist-get (plist-get goal :info) :evar))
         (id (cond ((and (vectorp evar) (= (length evar) 2)) (aref evar 1))
                   (evar evar)
                   (t (format "n%d" number))))
         (key (intern (format "coq-eglot-goal-%s" id))))
    (put key 'coq-eglot-goal t)
    key))

(defun coq-eglot-goals--hyps-text (goal)
  "The hypotheses of GOAL, without the properties of the first goal's.
Folding or highlighting a hypothesis of the first goal, see
`coq-hyps-decorate', works by names: it must not apply to the other
goals."
  (let ((text (copy-sequence (coq-eglot--format-hyps goal))))
    (remove-list-of-text-properties 0 (length text)
                                    '(coq-hyp coq-hyp-body) text)
    text))

(defun coq-eglot-goals--hyps-count (goal)
  "Number of hypotheses of GOAL, a hypothesis may have several names."
  (seq-reduce (lambda (count hyp) (+ count (length (plist-get hyp :names))))
              (plist-get goal :hyps) 0))

(defun coq-eglot-goals--format-goal (goal number)
  "Format GOAL, numbered NUMBER, its hypotheses folded under its title."
  (let ((title (format "goal %d:" number))
        (hyps (coq-eglot-goals--hyps-text goal)))
    (concat "\n"
            (if (string-empty-p hyps)
                (concat title "\n")
              (let ((key (coq-eglot-goals--key goal number)))
                ;; the newline after the separator is folded too: the
                ;; button displays the one after the title
                (concat (propertize title
                                    'coq-eglot-goal-title key
                                    'coq-eglot-goal-hyps
                                    (coq-eglot-goals--hyps-count goal))
                        "\n"
                        (propertize
                         (concat (string-remove-suffix "\n" hyps)
                                 "\n  ============================\n")
                         'invisible key))))
            " " (coq-eglot--indent (plist-get goal :ty) " ") "\n")))

(defun coq-eglot-goals--format-list (goals first)
  "Format GOALS, numbered from FIRST, see `coq-eglot-goals--format-goal'."
  (let ((number (1- first)))
    (mapconcat (lambda (goal)
                 (coq-eglot-goals--format-goal goal (cl-incf number)))
               goals "")))

(defun coq-eglot-goals--format-levels (goals first)
  "Format the unfocused goals of GOALS by level, numbered from FIRST.
Each level after a line giving its depth, and the next bullet for one of
them, see `coq-eglot-goals--bullet-hint'."
  (let* ((levels (coq-eglot-goals--levels goals))
         (hint (coq-eglot-goals--bullet-hint goals levels))
         (number first))
    (mapconcat
     (lambda (level)
       (let ((line (concat (format "── level %d" (car level))
                           (and (eql (car hint) (car level))
                                (concat ", " (cdr hint))))))
         (prog1
             (concat "\n"
                     (propertize line 'face 'coq-eglot-goals-level
                                 'font-lock-face 'coq-eglot-goals-level)
                     (coq-eglot-goals--format-list (cdr level) number))
           (setq number (+ number (length (cdr level)))))))
     levels "")))

(defun coq-eglot-goals--mark-start (text)
  "TEXT, where the folding of the other goals starts after its newlines.
See `coq-goals--other-goals-start'."
  (let ((start (string-match "[^\n]" text)))
    (when start
      (put-text-property start (1+ start) 'coq-other-goals-start t text))
    text))

(defun coq-eglot-goals-format-other (goals)
  "Format the goals of GOALS after the first one, detailed.
The other focused goals, then the unfocused ones by level after a line
\"*** Unfocused goals:\", like Coq with Set Printing Unfocused."
  (let ((others (cdr (append (plist-get goals :goals) nil))))
    (coq-eglot-goals--mark-start
     (concat (coq-eglot-goals--format-list others 2)
             (when (coq-eglot-goals--levels goals)
               (concat "\n*** Unfocused goals:\n"
                       (coq-eglot-goals--format-levels
                        goals (+ 2 (length others)))))))))

(defun coq-eglot-goals-format-unfocused (goals)
  "Format the unfocused goals of GOALS by level, detailed, numbered from 1.
When no goal is focused."
  (coq-eglot-goals--mark-start (coq-eglot-goals--format-levels goals 1)))

;;; Folding the hypotheses of a goal

(defvar coq-eglot-goals-title-map
  (let ((map (make-sparse-keymap)))
    (define-key map [mouse-1] #'coq-eglot-toggle-goal-hyps)
    (define-key map (kbd "RET") #'coq-eglot-toggle-goal-hyps)
    map)
  "Keymap of the titles of the goals with hypotheses.")

(defun coq-eglot-goals--overlay (start end key &rest properties)
  "Make an overlay from START to END toggling the hypotheses of goal KEY.
With PROPERTIES.  Above the folding of the other goals, whose keymap
it hides."
  (let ((ov (make-overlay start end)))
    (overlay-put ov 'coq-eglot-goal-overlay t)
    (overlay-put ov 'coq-eglot-goal-title key)
    (overlay-put ov 'evaporate t)
    (overlay-put ov 'priority 10)
    (overlay-put ov 'keymap coq-eglot-goals-title-map)
    (overlay-put ov 'mouse-face 'highlight)
    (overlay-put ov 'help-echo "mouse-1, RET: show or hide the hypotheses")
    (while properties
      (overlay-put ov (pop properties) (pop properties)))
    ov))

(defun coq-eglot-goals-decorate ()
  "Fold the hypotheses of the goals of the current buffer, but the unfolded.
See `coq-eglot-goals--unfolded'.  The title of each goal and the button
after it, giving the number of its hypotheses, show or hide them."
  (remove-overlays (point-min) (point-max) 'coq-eglot-goal-overlay t)
  (when (listp buffer-invisibility-spec)
    (setq buffer-invisibility-spec
          (seq-remove (lambda (elt)
                        (let ((atom (if (consp elt) (car elt) elt)))
                          (and (symbolp atom) (get atom 'coq-eglot-goal))))
                      buffer-invisibility-spec)))
  (let ((pos (point-min))
        keys)
    (while (setq pos (text-property-not-all pos (point-max)
                                            'coq-eglot-goal-title nil))
      (let* ((end (next-single-property-change pos 'coq-eglot-goal-title
                                               nil (point-max)))
             (key (get-text-property pos 'coq-eglot-goal-title))
             (count (get-text-property pos 'coq-eglot-goal-hyps))
             (folded (not (memq key coq-eglot-goals--unfolded))))
        (push key keys)
        (when folded
          (add-to-invisibility-spec key))
        (coq-eglot-goals--overlay pos end key)
        ;; the button displays the newline after the title: a click on it
        ;; is at a position of the buffer, where the keymap applies
        (when (eq (char-after end) ?\n)
          (coq-eglot-goals--overlay
           end (1+ end) key
           'coq-eglot-goal-button t
           'display (concat "  "
                            (propertize (if folded
                                            (format "▸ %d hypothes%s" count
                                                    (if (= count 1) "is" "es"))
                                          "▾")
                                        'face 'coq-other-goals-face)
                            "\n")))
        (setq pos end)))
    ;; the buffer of the other goals: forget the goals that are gone
    (when keys
      (setq coq-eglot-goals--unfolded
            (seq-filter (lambda (key) (memq key keys))
                        coq-eglot-goals--unfolded)))))

(defun coq-eglot-goals--title-at (event)
  "Buffer and key of the goal title at EVENT, or at point if not a mouse event.
On the title or on its button, see `coq-eglot-goals-decorate'."
  (if (mouse-event-p event)
      (let ((posn (event-start event)))
        (with-current-buffer (window-buffer (posn-window posn))
          (cons (current-buffer)
                (and (posn-point posn)
                     (get-char-property (posn-point posn)
                                        'coq-eglot-goal-title)))))
    (cons (current-buffer) (get-char-property (point) 'coq-eglot-goal-title))))

(defun coq-eglot-toggle-goal-hyps (&optional event)
  "Show or hide the hypotheses of the goal whose title is at EVENT or point.
See `coq-eglot-detailed-goals'."
  (interactive (list last-nonmenu-event))
  (pcase-let ((`(,buffer . ,key) (coq-eglot-goals--title-at event)))
    (unless key
      (user-error "Coq: no goal title here"))
    (setq coq-eglot-goals--unfolded
          (if (memq key coq-eglot-goals--unfolded)
              (delq key coq-eglot-goals--unfolded)
            (cons key coq-eglot-goals--unfolded)))
    (with-current-buffer buffer
      (coq-eglot-goals-decorate))))

(provide 'coq-eglot-goals)

;;; coq-eglot-goals.el ends here
