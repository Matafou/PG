;;; coq-eglot-ui.el --- Faces, mode line and menu of the Eglot backend  -*- lexical-binding:t -*-

;; This file is part of Proof General.

;; Portions © Copyright 2026  Pierre Courtieu

;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;;
;; How the Eglot backend looks: its faces, its indicator in the mode
;; line, its menu.  Nothing here decides what the backend does:
;; coq-eglot.el only uses these names.

;;; Code:

(require 'color)
(require 'coq-queries)                  ; coq-options-menu
(require 'coq-templates)                ; coq-insert-menu
(require 'coq-goals)                    ; coq-hyps-menu
(require 'coq-compile-common)           ; coq-compile-menu
(require 'coq-eglot-lsp)                ; coq-eglot-lsp-connecting-p
(require 'coq-eglot-compile)            ; coq-eglot-compile--outdated-p

(defvar coq-eglot--twin)
(defvar coq-eglot--twin-label)
(declare-function coq-eglot-busy-p "coq-eglot")

;;; Faces

(defface coq-eglot-goals-separator '((t :inherit shadow))
  "Face of the line between the hypotheses and the conclusion.
See `coq-eglot-split-goals'.  The default inherits from `shadow', which
themes make visible on their background."
  :group 'coq-eglot)

(defface coq-eglot-inactive-locked-face '((t :extend t))
  "Face of the processed part of the script buffers that are not active.
Only the active script buffer displays its goals and messages, see
`coq-eglot--active-buffer'.  If this face has no background, the
background is the one of `proof-locked-face', grayed: see
`coq-eglot-inactive-saturation'."
  :group 'coq-eglot)

(defcustom coq-eglot-inactive-saturation 0.5
  "Saturation of the processed part of inactive script buffers.
A factor between 0 (gray) and 1 (same color), applied to the background
of `proof-locked-face' when `coq-eglot-inactive-locked-face' has no
background."
  :type 'number
  :group 'coq-eglot)

(defun coq-eglot--desaturate-rgb (rgb factor)
  "Return color RGB, a list of 3 numbers in [0,1], with saturation times FACTOR.
The result is a hexadecimal color string."
  (pcase-let ((`(,h ,s ,l) (apply #'color-rgb-to-hsl rgb)))
    (apply #'color-rgb-to-hex
           (append (color-hsl-to-rgb h (* s factor) l) '(2)))))

(defun coq-eglot--inactive-locked-face ()
  "Face of the processed part of an inactive script buffer.
See `coq-eglot-inactive-locked-face'."
  (let ((locked (face-background 'proof-locked-face nil t)))
    (if (or (face-background 'coq-eglot-inactive-locked-face nil t)
            (not (stringp locked))
            (not (color-defined-p locked)))
        'coq-eglot-inactive-locked-face
      (list (list :background (coq-eglot--desaturate-rgb
                               (color-name-to-rgb locked)
                               coq-eglot-inactive-saturation))
            'coq-eglot-inactive-locked-face))))

;;; Mode line

(defun coq-eglot--lighter ()
  "Mode line indicator of `coq-eglot-mode'.
Warn if processed Require sentences load outdated libraries.  An
ellipsis while the buffer waits for the server, see `coq-eglot-busy-p'."
  (concat
   (if coq-eglot-compile--outdated-p
       (propertize " Coq-LSP!" 'face 'warning
                   'help-echo "Some required libraries changed since loaded")
     " Coq-LSP")
   ;; which server, for twins
   (and coq-eglot--twin coq-eglot--twin-label
        (format "[%s]" coq-eglot--twin-label))
   ;; waiting for the server
   (and (coq-eglot-busy-p)
        (propertize "…" 'help-echo
                    (if (coq-eglot-lsp-connecting-p)
                        "Starting the Coq server"
                      "Waiting for the Coq server")))))

;;; Menu

(defun coq-eglot--warn-no-effect (what reason)
  "Warn that WHAT, a menu entry or a command, has no effect, for REASON."
  (display-warning 'coq-eglot
                   (format "%s has no effect with the Eglot backend: %s"
                           what reason)))

(defconst coq-eglot--no-effect-entries
  '((coq-compile-parallel-in-background-toggle
     . "the compilation is always parallel and in the background")
    (coq-lock-ancestors-toggle
     . "the files of the imported libraries are not locked")
    (coq-compile-quick
     . "it is for Coq < 8.11, older than what coq-lsp supports")
    (coq-compile-vos
     . "coq-lsp loads the .vo files only, \"ensure vo\" is set again"))
  "Entries of the shared menus without effect in the Eglot backend.
Their commands, or the variables that they set, with the reason.  See
`coq-eglot--menu-with-warnings'.")

(defun coq-eglot--no-effect-reason (callback)
  "Why the menu entry with CALLBACK has no effect, or nil.
CALLBACK is a command or a form (customize-set-variable \='VAR VALUE).
See `coq-eglot--no-effect-entries'."
  (cdr (assq (if (and (eq (car-safe callback) 'customize-set-variable)
                      (eq (car-safe (nth 1 callback)) 'quote))
                 (nth 1 (nth 1 callback))
               callback)
             coq-eglot--no-effect-entries)))

(defun coq-eglot--run-no-effect (name callback reason)
  "Run CALLBACK of the menu entry NAME, warn that it has no effect, REASON."
  (if (commandp callback)
      (call-interactively callback)
    (eval callback t))
  (coq-eglot--warn-no-effect (format "The menu entry \"%s\"" name) reason))

(defun coq-eglot--menu-with-warnings (menu)
  "MENU, a shared menu, with a warning on its entries without effect.
They do what they do, then warn, see `coq-eglot--no-effect-entries'."
  (mapcar (lambda (item)
            (cond
             ((and (vectorp item) (coq-eglot--no-effect-reason (aref item 1)))
              (let ((new (copy-sequence item)))
                (aset new 1 `(coq-eglot--run-no-effect
                              ,(aref item 0) ',(aref item 1)
                              ,(coq-eglot--no-effect-reason (aref item 1))))
                new))
             ((consp item) (coq-eglot--menu-with-warnings item))
             (t item)))
          menu))

(defconst coq-eglot--options-menu
  (cons
   (car coq-options-menu)
   (mapcan
    (lambda (item)
      (pcase (and (vectorp item) (aref item 1))
        ('coq-set-printing-compact-contexts
         (list ["Compact Contexts" coq-eglot-toggle-compact-contexts
                :style toggle :selected coq-eglot-compact-contexts
                :help "Put compatible hypotheses on the same line"]))
        ('coq-unset-printing-compact-contexts nil)
        (_ (list item))))
    (cdr coq-options-menu)))
  "Printing options menu of the Eglot backend.
Compact contexts are a presentation option, not a command sent to Rocq.")

(defvar coq-eglot--menu-spec
  `("Coq"
    ["Next Step" coq-eglot-assert-next-command]
    ["Undo Step" coq-eglot-undo-last-command]
    ["Goto Point" coq-eglot-goto-point]
    ["Process Buffer" coq-eglot-process-buffer]
    ["Retract Buffer" coq-eglot-retract-buffer]
    ["Goto End of Locked" coq-eglot-goto-end-of-locked]
    "---"
    ["Show Goals" coq-eglot-show-goals]
    ["Show Trace" coq-eglot-show-trace]
    ["Set Printing Width..." coq-ask-printing-width]
    ("Windows"
     ["Layout Windows" coq-eglot-layout-windows]
     ["Three Windows"
      (coq-eglot-set-layout-option 'proof-three-window-enable
                                   (not proof-three-window-enable))
      :style toggle :selected proof-three-window-enable
      :help "Goals and messages in windows of their own"]
     ["Conclusion Apart" coq-eglot-toggle-split-goals
      :style toggle :selected coq-eglot-split-goals
      :help "The conclusion in a window of its own, below the hypotheses"]
     ["Detailed Other Goals" coq-eglot-toggle-detailed-goals
      :style toggle :selected coq-eglot-detailed-goals
      :help "The other goals with their hypotheses, by level"]
     ;; also in the OPTIONS menu, see `coq-eglot--options-menu'
     ["Compact Contexts" coq-eglot-toggle-compact-contexts
      :style toggle :selected coq-eglot-compact-contexts
      :help "Put compatible hypotheses on the same line"]
     ("3 Windows mode layout"
      ["smart"
       (coq-eglot-set-layout-option 'proof-three-window-mode-policy 'smart)
       :style radio :selected (eq proof-three-window-mode-policy 'smart)
       :active proof-three-window-enable
       :help "Adapt to frame width (C-c C-l to refresh)"]
      ["hybrid"
       (coq-eglot-set-layout-option 'proof-three-window-mode-policy 'hybrid)
       :style radio :selected (eq proof-three-window-mode-policy 'hybrid)
       :active proof-three-window-enable
       :help "Two column mode"]
      ["horizontal"
       (coq-eglot-set-layout-option 'proof-three-window-mode-policy
                                    'horizontal)
       :style radio :selected (eq proof-three-window-mode-policy 'horizontal)
       :active proof-three-window-enable
       :help "Three column mode"]
      ["vertical"
       (coq-eglot-set-layout-option 'proof-three-window-mode-policy 'vertical)
       :style radio :selected (eq proof-three-window-mode-policy 'vertical)
       :active proof-three-window-enable
       :help "One column mode"])
     ["Rotate Output Buffers" coq-eglot-display-some-buffers
      :help "Display the messages, the trace or the goals"]
     "---"
     ["Multiple Frames"
      (coq-eglot-set-layout-option 'proof-multiple-frames-enable
                                   (not proof-multiple-frames-enable))
      :style toggle :selected proof-multiple-frames-enable
      :active (display-graphic-p)
      :help "The goals and the messages in frames of their own"]
     ["Auto Raise"
      (customize-set-variable 'proof-auto-raise-buffers
                              (not proof-auto-raise-buffers))
      :style toggle :selected proof-auto-raise-buffers
      :help "Display the goals and the messages when they change"]
     ["Layout Eagerly"
      (customize-set-variable 'proof-layout-windows-on-visit-file
                              (not proof-layout-windows-on-visit-file))
      :style toggle :selected proof-layout-windows-on-visit-file
      :help "Display the goals and messages windows when visiting a file"]
     ["Delete Empty Windows"
      (customize-set-variable 'proof-delete-empty-windows
                              (not proof-delete-empty-windows))
      :style toggle :selected proof-delete-empty-windows
      :active (not proof-multiple-frames-enable)
      :help "Delete the windows of the goals or messages when empty"]
     ["Shrink to Fit"
      (customize-set-variable 'proof-shrink-windows-tofit
                              (not proof-shrink-windows-tofit))
      :style toggle :selected proof-shrink-windows-tofit
      :active (not proof-multiple-frames-enable)
      :help "The goals and messages windows one above the other share their height"])
    ["Fold Other Goals" coq-toggle-other-goals
     :style toggle :selected coq-fold-other-goals]
    ["Fold Error Environments" coq-toggle-error-environment
     :style toggle :selected coq-fold-error-environment]
    ,(coq-eglot--menu-with-warnings coq-compile-menu)
    ["Double Hit Electric Terminator" proof-double-hit-toggle
     :style toggle :selected proof-double-hit-enable]
    ["Trace" coq-eglot-toggle-trace
     :style toggle :selected coq-eglot-trace
     :help "Transcript of the session in buffer *coq-trace*"]
    ,coq-hyps-menu
    ("Queries"
     ["About..." coq-About]
     ["Check..." coq-Check]
     ["Print..." coq-Print]
     ["Search..." coq-Search]
     ["SearchPattern..." coq-SearchIsos]
     ["Search Blacklist..." coq-change-search-blacklist-interactive]
     ["Locate..." coq-LocateConstant]
     ["Locate Notation..." coq-LocateNotation]
     ["Print Hint" coq-PrintHint]
     ["Query..." coq-query]
     ["Other Command..." coq-eglot-query]
     "---"
     ["About with Printing All..." coq-About-with-all]
     ["Check with Printing All..." coq-Check-show-all]
     ["Print with Printing All..." coq-Print-with-all])
    ,coq-eglot--options-menu
    ,(append coq-insert-menu
             '(["Named Goal Selectors" coq-insert-named-goal-selectors]))
    "---"
    ["Interrupt" coq-eglot-interrupt]
    ["Restart Server" coq-eglot-restart-server]
    ["Exit Server" coq-eglot-exit]
    ("Rocq Version" :filter coq-eglot-servers-menu
     :help "The Rocq checking the files of the project, for this session")
    "---"
    ("Two Rocq"
     ["Pair With..." coq-eglot-twin-pair
      :active (not coq-eglot--twin)
      :help "Check another script buffer side by side, a twin"]
     ["Layout Side by Side" coq-eglot-twin-layout
      :active coq-eglot--twin]
     ["Go to Twin Position" coq-eglot-twin-goto-twin-position
      :active coq-eglot--twin
      :help "The same place in the twin, after aligning their sentences"]
     ["Swap Reference" coq-eglot-twin-swap-reference
      :active coq-eglot--twin
      :help "The differences of the other twin are shown as removed"]
     ["Synchronize Proof Positions" coq-eglot-twin-toggle-synchronize
      :style toggle :selected (bound-and-true-p coq-eglot-twin-synchronize)
      :help "The proof position of a twin follows the one of the other"]
     ("Rocq of the Twin" :filter coq-eglot-twin--rocq-menu
      :active coq-eglot--twin
      :help "The Rocq checking the twin, the buffer with its own goals")
     ["Two Servers" coq-eglot-twin-toggle-two-servers
      :style toggle
      :selected (and (fboundp 'coq-eglot-twin-two-servers-p)
                     (coq-eglot-twin-two-servers-p))
      :active (and coq-eglot--twin (fboundp 'coq-eglot-twin--same-project-p)
                   (coq-eglot-twin--same-project-p (current-buffer)
                                                   coq-eglot--twin))
      :help "Twins of one project checked at the same time, using more memory"]
     ["Unpair" coq-eglot-twin-unpair
      :active coq-eglot--twin]))
  "Menu of the Eglot backend of Coq, see `easy-menu-define'.")

(provide 'coq-eglot-ui)

;;; coq-eglot-ui.el ends here
