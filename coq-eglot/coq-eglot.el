;;; coq-eglot.el --- Coq backend using a language server through Eglot  -*- lexical-binding:t -*-

;; This file is part of Proof General.

;; Portions © Copyright 2026  Pierre Courtieu

;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;;
;; Experimental backend for `coq-mode', using a language server
;; (coq-lsp) through Eglot instead of running Coq in a shell.  It is
;; selected by setting `coq-backend' to `eglot' before `coq-mode' is
;; loaded.  Requires Emacs 29 or later.
;;
;; Files in this directory may require files from coq/ (coq-mode,
;; coq-syntax...), but files from coq/ never require files from here,
;; except coq-mode.el which loads this file when the backend is
;; selected.

;;; Code:

(require 'eglot)
(require 'coq-mode)

(defgroup coq-eglot nil
  "Coq backend using a language server through Eglot."
  :group 'coq-mode)

(defun coq-eglot-setup ()
  "Set up the current `coq-mode' buffer for the Eglot backend."
  (message "coq-eglot: the Eglot backend is not implemented yet."))

(provide 'coq-eglot)

;;; coq-eglot.el ends here
