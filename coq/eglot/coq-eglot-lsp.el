;;; coq-eglot-lsp.el --- Communication with the Coq language server  -*- lexical-binding:t -*-

;; This file is part of Proof General.

;; Portions © Copyright 2026  Pierre Courtieu

;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; SPDX-License-Identifier: GPL-3.0-or-later

;;; Commentary:
;;
;; Connection to coq-lsp through Eglot, and the requests specific to
;; Coq.  This is the only file of the Eglot backend that knows about
;; Eglot and the protocol: it uses a few internal functions of Eglot,
;; keep them here.

;;; Code:

(require 'eglot)
(require 'jsonrpc)
(require 'subr-x)                       ; hash-table-keys
(require 'coq-system)                   ; coq-project-filename
(require 'coq-project)                  ; coq-include-options

;; Private symbols of Eglot and jsonrpc used in this file.  When Eglot
;; changes (new Emacs, new Eglot from ELPA), check that each one still
;; exists with the same meaning: run the test
;; `coq-eglot-lsp-internals-exist', then read the new definitions of
;; these symbols.  Each element is (KIND SYMBOL...) with KIND `function'
;; or `variable': one of the SYMBOLs must exist, they are the
;; alternatives of different versions.
(defconst coq-eglot-lsp--internals
  '((function jsonrpc--process)
    (function jsonrpc--async-request-1)
    ;; an alist since jsonrpc 1.0.24 (Emacs 30), a hash table before
    (function jsonrpc--continuations jsonrpc--request-continuations)
    (function eglot--project)
    (function eglot--current-project)
    (function eglot--guess-contact)
    (function eglot--managed-buffers)
    (function eglot--pos-to-lsp-position)
    (function eglot--lsp-position-to-point)
    (function eglot--signal-textDocument/didChange)
    (function eglot--VersionedTextDocumentIdentifier)
    (function eglot--TextDocumentIdentifier)
    (function eglot-uri-to-path eglot--uri-to-path)
    (variable eglot--servers-by-project)
    (variable eglot--managed-mode)
    (variable eglot--versioned-identifier))
  "Internal functions and variables of Eglot and jsonrpc that we use.
See the comment above for what to check when Eglot changes.")

(defgroup coq-eglot nil
  "Coq backend using a language server through Eglot."
  :group 'coq-mode)

(defcustom coq-eglot-server-program nil
  "Command line running the Coq language server.
A list of strings: the program and its arguments.  If nil, use the
first of rocq-lsp and coq-lsp found in `exec-path'.  Only coq-lsp
(renamed rocq-lsp) is supported.  Use an absolute file name to use the
server of a given opam switch."
  :type '(choice (const :tag "rocq-lsp or coq-lsp, found in exec-path" nil)
                 (repeat :tag "Command line" string)))

(defconst coq-eglot-lsp--program-names '("rocq-lsp" "coq-lsp")
  "Names of the server program, tried in this order.")

(defun coq-eglot-lsp-server-command ()
  "Command line of the server, a list of strings.
See `coq-eglot-server-program'.  Signal an error if the program is not
found."
  (let ((command (or coq-eglot-server-program
                     (list (or (seq-find #'executable-find
                                         coq-eglot-lsp--program-names)
                               (user-error "Coq language server not found \
in exec-path: install coq-lsp (opam install coq-lsp), or set \
`coq-eglot-server-program'"))))))
    (unless (executable-find (car command))
      (user-error "Coq language server %s not found, see \
`coq-eglot-server-program'" (car command)))
    command))

(defcustom coq-eglot-server-idle-delay 0.01
  "Seconds the server waits when idle before looking for requests.
Every request waits up to this delay: coq-lsp defaults to 0.1, which
makes processing sentences one by one slow.  Shorter delays use a bit
more CPU while idle.  If nil, use the default of the server."
  :type '(choice (number :tag "Seconds")
                 (const :tag "Default of the server" nil)))

(defcustom coq-eglot-strong-interrupt 'auto
  "Whether the server can interrupt any computation of Coq.
By default, coq-lsp interrupts Coq only where Coq checks for
interruptions: a long reduction like `cbn' runs until its end.  With
memprof-limits (option --int_backend=Mp), it interrupts almost
anywhere.  This needs a server built with OCaml 4.x or OCaml >= 5.3,
otherwise memprof-limits is a fake and nothing can be interrupted.
- `auto': use memprof-limits if the OCaml version of the server
  supports it.  The version is the one of the ocamlc installed next to
  the server, like in an opam switch.  If not found, do not use it.
- t: always use memprof-limits.
- nil: never use it.
coq-lsp considers released versions of Rocq not safe for it (Rocq PR
#19177): an interruption may leave Rocq in an inconsistent state, then
restart the server (\\[coq-eglot-interrupt] twice, or
\\[coq-eglot-exit])."
  :type '(choice (const :tag "If supported by OCaml" auto)
                 (const :tag "Always" t)
                 (const :tag "Never" nil)))

(defvar coq-eglot-lsp--ocaml-versions (make-hash-table :test #'equal)
  "Cache of the OCaml versions of the servers, by file name.")

(defun coq-eglot-lsp--ocaml-version (program)
  "OCaml version of the server PROGRAM, as a string, or nil if unknown.
Ask the ocamlc installed next to it, like in an opam switch."
  (let ((exe (executable-find program)))
    (when exe
      (setq exe (file-truename exe))
      (let ((cached (gethash exe coq-eglot-lsp--ocaml-versions 'unknown)))
        (if (not (eq cached 'unknown))
            cached
          (puthash exe
                   (let ((ocamlc (expand-file-name "ocamlc"
                                                   (file-name-directory exe))))
                     (and (file-executable-p ocamlc)
                          (ignore-errors (car (process-lines ocamlc "-version")))))
                   coq-eglot-lsp--ocaml-versions))))))

;; the output of --version is the number alone, like "0.2.5": keep the
;; first dotted number of the first line to be robust
(defvar coq-eglot-lsp--server-versions (make-hash-table :test #'equal)
  "Cache of the versions of the servers, by file name.")

(defun coq-eglot-lsp--server-version (program)
  "Version of the server PROGRAM, as a string, or nil if unknown.
Run it once with --version, and keep the answer by file name."
  (let ((exe (executable-find program)))
    (when exe
      (setq exe (file-truename exe))
      (let ((cached (gethash exe coq-eglot-lsp--server-versions 'unknown)))
        (if (not (eq cached 'unknown))
            cached
          (puthash exe
                   (ignore-errors
                     (let ((line (car (process-lines exe "--version"))))
                       (and line
                            (string-match "[0-9]+\\(?:\\.[0-9]+\\)+" line)
                            (match-string 0 line))))
                   coq-eglot-lsp--server-versions))))))

(defconst coq-eglot-lsp-minimal-version "0.2.3"
  "Oldest version of coq-lsp supported.
It added the range of the sentence to the answer of proof/goals, and
the request petanque/get_state_at_pos.")

(defun coq-eglot-lsp--check-server-version (program)
  "Signal a user error if the server PROGRAM is too old.
Do nothing if its version is unknown: the server may still work."
  (let ((version (coq-eglot-lsp--server-version program)))
    (when (and version (version< version coq-eglot-lsp-minimal-version))
      (user-error "coq-lsp %s is too old for the Eglot backend of Coq, \
version %s or later is needed (%s)"
                  version coq-eglot-lsp-minimal-version program))))

(defun coq-eglot-lsp--memprof-p (version)
  "Non-nil if OCaml VERSION supports memprof-limits: 4.x or >= 5.3."
  (and version
       (string-match "\\`\\([0-9]+\\)\\.\\([0-9]+\\)" version)
       (let ((major (string-to-number (match-string 1 version)))
             (minor (string-to-number (match-string 2 version))))
         (or (= major 4) (and (= major 5) (>= minor 3)) (> major 5)))))

(defun coq-eglot-lsp--strong-interrupt-p (program)
  "Non-nil if the server PROGRAM should use memprof-limits.
See `coq-eglot-strong-interrupt'."
  (if (eq coq-eglot-strong-interrupt 'auto)
      (coq-eglot-lsp--memprof-p (coq-eglot-lsp--ocaml-version program))
    coq-eglot-strong-interrupt))

(defclass coq-eglot-lsp-server (eglot-lsp-server) ()
  :documentation "Coq language server (coq-lsp).")

(defun coq-eglot-lsp--options ()
  "Options of coq-lsp, as a plist."
  (list
   ;; Check the document only up to the requested positions
   :check_only_on_request t
   ;; Goals after the sentence at the requested position
   :goal_after_tactic t
   ;; Messages of the sentence used for goals
   :messages_follow_goal t
   ;; Diagnostics after each sentence, to stop at the first error
   :eager_diagnostics t
   ;; Pretty print as strings
   :pp_type 0
   ;; The range of the sentence of an error, in its diagnostic
   :send_diags_extra_data t))

(cl-defmethod eglot-initialization-options ((_server coq-eglot-lsp-server))
  (coq-eglot-lsp--options))

(defun coq-eglot-lsp--send-options (server)
  "Send our options to SERVER, if it is a Coq server.
Eglot sends the workspace configuration when connecting, which would
reset the options given at initialization."
  (when (cl-typep server 'coq-eglot-lsp-server)
    (jsonrpc-notify server :workspace/didChangeConfiguration
                    (list :settings (coq-eglot-lsp--options)))))

;; Must run after `eglot-signal-didChangeConfiguration'
(add-hook 'eglot-connect-hook #'coq-eglot-lsp--send-options t)

(defun coq-eglot-lsp--logical-binding (dir path)
  "Argument DIR,PATH of -R and -Q.
Signal a user error if DIR has a comma: coq-lsp splits the argument at
the comma, and there is no way to escape it."
  (when (string-search "," dir)
    (user-error "Directory %s has a comma, which coq-lsp cannot bind \
(-R DIR,LP): rename it" dir))
  (concat (directory-file-name dir) "," path))

(defun coq-eglot-lsp-load-path-args (&optional command)
  "Options -R and -Q of the server, from `coq-load-path'.
The load path of the current buffer, like the compilation uses it, see
`coq-include-options', relative to the directory of the file.  With
COMMAND, a command line, the options -R and -Q of COMMAND instead.  The
entries ocamlimport and package are ignored: coq-lsp has no such
options."
  (let ((options (or command
                     (let ((default-directory
                            (if buffer-file-name
                                (file-name-directory buffer-file-name)
                              default-directory)))
                       (coq-include-options coq-load-path))))
        args)
    (while options
      (let ((option (pop options)))
        (pcase option
          ((or "-R" "-Q")
           (if command
               ;; DIR,LP
               (push (list option (pop options)) args)
             (let* ((dir (pop options))
                    (path (pop options)))
               (push (list option (coq-eglot-lsp--logical-binding dir path))
                     args))))
          ((or "-I" "-package") (unless command (pop options))))))
    (apply #'append (nreverse args))))

(defun coq-eglot-lsp--server-load-path-args (server)
  "Options -R and -Q of the command line of SERVER.
Without those of `coq-eglot-server-program', which come first: they are
the same for all the files."
  (let ((process (jsonrpc--process server)))
    (and (processp process)
         (let* ((args (coq-eglot-lsp-load-path-args
                       (cdr (process-command process))))
                (own (coq-eglot-lsp-load-path-args
                      (cdr coq-eglot-server-program))))
           (if (equal (seq-take args (length own)) own)
               (nthcdr (length own) args)
             args)))))

(defun coq-eglot-lsp-check-load-path ()
  "Warn if the server of the current buffer has another load path.
The server is shared by the files of a project, with the load path of
the file that started it, see `coq-eglot-lsp--contact'.  Warn too if
`coq-use-project-file' is nil but the server reads a project file.  Run
when Eglot starts managing the buffer."
  (let ((server (and (bound-and-true-p eglot--managed-mode)
                     (eglot-current-server))))
    (when (cl-typep server 'coq-eglot-lsp-server)
      (let ((args (append (coq-eglot-lsp--root-load-path-args
                           (project-root (eglot--project server)))
                          (ignore-errors (coq-eglot-lsp-load-path-args)))))
        (unless (equal args (coq-eglot-lsp--server-load-path-args server))
          (display-warning
           'coq-eglot
           (format "The language server of %s was started by another file, \
with another load path (coq-load-path).  C-c C-x stops it, the next \
command starts it with the load path of %s."
                   (buffer-name) (buffer-name)))))
      (let ((root (project-root (eglot--project server))))
        (when (and (not coq-use-project-file)
                   (seq-some (lambda (name)
                               (file-exists-p (expand-file-name name root)))
                             '("_CoqProject" "_RocqProject")))
          (display-warning
           'coq-eglot
           (format "coq-use-project-file is nil, but the language server \
reads the project file of %s anyway." root)))))))

(defun coq-eglot-lsp--root-load-path-args (root)
  "Option -R of ROOT, the root of the server, if it has no project file.
Like coqtop, which binds its current directory to the empty logical
path, so that a file can require the files next to it: coq-lsp binds
nothing without a project file.  -R, not -Q: coq-lsp puts all the -R
before all the -Q, and the last binding of a directory wins, so a -Q
of ROOT would hide the -R of its subdirectories in the load path of
the buffer."
  (unless (seq-some (lambda (name) (file-exists-p (expand-file-name name root)))
                    '("_CoqProject" "_RocqProject"))
    (list "-R" (coq-eglot-lsp--logical-binding (expand-file-name root) ""))))

(defun coq-eglot-lsp--contact (&optional _interactive project)
  "Eglot contact for Coq: our server class and its command line.
With the load path of the current buffer, see
`coq-eglot-lsp-load-path-args': coq-lsp adds it to the one of the
project file it finds in its root directory, if any.  Without a project
file, the root directory of PROJECT is bound to the empty logical path,
see `coq-eglot-lsp--root-load-path-args'.  The Eglot of Emacs 29 gives
no PROJECT: the one of the current buffer, like Eglot."
  (let* ((command (coq-eglot-lsp-server-command))
         (root (project-root (or project (eglot--current-project))))
         (root-args (coq-eglot-lsp--root-load-path-args root))
         (buffer-args
          (condition-case err
              (coq-eglot-lsp-load-path-args)
            (user-error (signal (car err) (cdr err)))
            (error (user-error "Invalid `coq-load-path': %s"
                               (error-message-string err))))))
    (coq-eglot-lsp--check-server-version (car command))
    (when root-args
      (message "Coq: no project file found in %s, assuming -R . \"\""
               (abbreviate-file-name root)))
    (cons 'coq-eglot-lsp-server
          (append command
                  root-args
                  buffer-args
                  (when coq-eglot-server-idle-delay
                    (list (format "--idle-delay=%s"
                                  coq-eglot-server-idle-delay)))
                  (when (and (not (seq-some
                                   (lambda (arg) (string-prefix-p "--int_backend" arg))
                                   command))
                             (coq-eglot-lsp--strong-interrupt-p (car command)))
                    (list "--int_backend=Mp"))))))

(add-to-list 'eglot-server-programs '(coq-mode . coq-eglot-lsp--contact))

(defun coq-eglot-lsp-project (dir)
  "Return the project of a Coq file in DIR, for `project-find-functions'.
It is the directory of the dominating Coq project file (_CoqProject),
if any.  The server is started there, where it reads the project file,
and is shared by the files of this directory and its subdirectories.
If `coq-use-project-file' is nil, it is DIR: the server reads no project
file, unless DIR has one, see `coq-eglot-lsp-check-load-path'."
  (if (not coq-use-project-file)
      (cons 'transient (expand-file-name dir))
    (when-let* ((root (locate-dominating-file
                       dir (lambda (d) (funcall coq-project-filename d)))))
      (cons 'transient root))))

;;; Positions and requests

(defun coq-eglot-lsp-position (pos)
  "LSP position of buffer position POS."
  (save-excursion (eglot--pos-to-lsp-position pos)))

(defun coq-eglot-lsp-point (lsp-pos)
  "Buffer position of LSP position LSP-POS."
  (save-excursion (eglot--lsp-position-to-point lsp-pos)))

(defun coq-eglot-lsp-range (range)
  "Buffer positions (START . END) of LSP range RANGE."
  (cons (coq-eglot-lsp-point (plist-get range :start))
        (coq-eglot-lsp-point (plist-get range :end))))

(defun coq-eglot-lsp-current-server ()
  "The Coq server managing the current buffer, or nil."
  (let ((server (eglot-current-server)))
    (and (cl-typep server 'coq-eglot-lsp-server) server)))

(defun coq-eglot-lsp-ensure-server (&optional no-wait)
  "Return the Coq server of the current buffer, starting it if needed.
Unlike `eglot-ensure', start it now, not after the current command.  If
it is still connecting, started by another command or by Eglot, wait
for it, at most `eglot-connect-timeout' seconds: do not start another
one.  If NO-WAIT is non-nil, do not wait: return nil if it is not
connected yet."
  (or (coq-eglot-lsp-current-server)
      (progn
        (unless (coq-eglot-lsp-connecting-servers)
          ;; with a prefix argument, like the one of the command that
          ;; starts the server, Eglot ignores the class of the contact:
          ;; the server would not be a `coq-eglot-lsp-server'
          (let ((current-prefix-arg nil)
                (eglot-sync-connect (and (not no-wait) eglot-sync-connect)))
            (apply #'eglot (eglot--guess-contact))))
        (unless no-wait
          ;; Eglot waits at most `eglot-sync-connect' seconds
          (with-timeout ((or eglot-connect-timeout 30))
            (while (and (not (coq-eglot-lsp-current-server))
                        (coq-eglot-lsp-connecting-servers))
              (accept-process-output nil 0.05))))
        (coq-eglot-lsp-current-server))))

(defun coq-eglot-lsp-connecting-servers ()
  "Servers of the project of the current buffer still connecting.
Eglot registers a server in its project once connected only: until
then, `eglot-current-server' does not find it."
  (let* ((project (eglot--current-project))
         (connected (gethash project eglot--servers-by-project)))
    (seq-filter (lambda (server)
                  (and (cl-typep server 'coq-eglot-lsp-server)
                       (equal (eglot--project server) project)
                       (not (memq server connected))
                       (jsonrpc-running-p server)))
                (delete-dups
                 (delq nil (mapcar (lambda (process)
                                     (process-get process 'jsonrpc-connection))
                                   (process-list)))))))

(defun coq-eglot-lsp-kill-connecting-servers ()
  "Kill the servers of the current buffer still connecting.
See `coq-eglot-lsp-connecting-servers'.  The Eglot of Emacs 29 reports
their aborted initialization as an error: ignored."
  (dolist (server (coq-eglot-lsp-connecting-servers))
    (ignore-errors (jsonrpc-shutdown server))))

(defun coq-eglot-lsp-shutdown ()
  "Stop the server of the current buffer, even if it is busy.
Return the buffers it managed."
  (let ((server (coq-eglot-lsp-current-server)))
    (when server
      (let ((buffers (eglot--managed-buffers server)))
        ;; a busy server does not answer the shutdown request: it is
        ;; killed after the timeout, which signals an error
        (ignore-errors (eglot-shutdown server nil 0.3 t))
        buffers))))

(defun coq-eglot-lsp-restart ()
  "Restart the server of the current buffer, even if it is busy.
The new server knows nothing: it checks again on demand."
  (coq-eglot-lsp-shutdown)
  (coq-eglot-lsp-ensure-server))

;;; Events

;; The answers and notifications of the server, normalized: the rest of
;; the backend does not see the JSON of coq-lsp.  Each one comes with
;; its objective context, the version of the document and the positions
;; it is about, converted to positions of the current text.  Whether it
;; is still valid after editions is not decided here: before the first
;; position edited since its version, the text did not change and the
;; positions are exact; a position after it stays after it once
;; converted.

(cl-defstruct (coq-eglot-lsp-context
               (:constructor coq-eglot-lsp--make-context (method position)))
  "What a request was about, kept from its sending.
METHOD is its LSP method, a keyword.  POSITION is the buffer position it
was sent at.  VERSION is the version of the document sent with it.  ID
is its jsonrpc id, for `$/cancelRequest'."
  method position version id)

(cl-defstruct (coq-eglot-lsp-message
               (:constructor coq-eglot-lsp--make-message (severity text)))
  "A message of Coq.
SEVERITY is `error', `warning', `notice', `info', or nil if unknown.
TEXT is a string."
  severity text)

(cl-defstruct (coq-eglot-lsp-answer
               (:constructor coq-eglot-lsp-make-answer
                             (&key context version sentence goals messages
                                   error printing-width printing-flags)))
  "The answer of the server with the goals after a sentence.
CONTEXT is the `coq-eglot-lsp-context' of the request, or nil.  VERSION
is the version of the document the answer is about.  SENTENCE is
\(START . END), the buffer positions of the sentence, or nil if the
server did not say.  GOALS is the goal configuration of coq-lsp, the
data displayed (the first goal may have the sorts of its hypotheses
with the key :hyp-sorts, see `coq-eglot-lsp-hyp-sorts-function'), or
nil outside of a proof.  MESSAGES is a list of `coq-eglot-lsp-message'.
ERROR is the text of the error of the sentence, or nil.  PRINTING-WIDTH
and PRINTING-FLAGS are those the goals were printed with, see
`coq-eglot-lsp-printing-width-function' and
`coq-eglot-lsp-printing-flags-function'."
  context version sentence goals messages error printing-width
  printing-flags)

(cl-defstruct (coq-eglot-lsp-checked
               (:constructor coq-eglot-lsp--make-checked (context)))
  "The server checked up to the sentence at the position of CONTEXT.
The answer of `petanque/get_state_at_pos' says nothing else: the version
and the position are those of the request."
  context)

(cl-defstruct (coq-eglot-lsp-progress
               (:constructor coq-eglot-lsp--make-progress (version start)))
  "The server is checking VERSION of the document, up to START.
START is the end of the last sentence checked: the server reports the
rest of the document as still to check, from START."
  version start)

(cl-defstruct (coq-eglot-lsp-diagnostic
               (:constructor coq-eglot-lsp--make-diagnostic
                             (start end severity message sentence)))
  "A diagnostic of the server.
START and END are the buffer positions of the message, not necessarily
of its sentence.  SEVERITY is like in `coq-eglot-lsp-message'.  MESSAGE
is a string.  SENTENCE is (START . END) of its sentence, for errors
only, or nil if the server did not say."
  start end severity message sentence)

(cl-defstruct (coq-eglot-lsp-diagnostics
               (:constructor coq-eglot-lsp--make-diagnostics
                             (version diagnostics)))
  "All the diagnostics of VERSION of the document.
A snapshot: it replaces the previous one, even when DIAGNOSTICS, a list
of `coq-eglot-lsp-diagnostic', is empty."
  version diagnostics)

(cl-defstruct (coq-eglot-lsp-failure
               (:constructor coq-eglot-lsp--make-failure
                             (context code message cancelled)))
  "A request failed.
CONTEXT is its `coq-eglot-lsp-context'.  CODE is the JSON-RPC error
code, MESSAGE its text.  CANCELLED is non-nil if the request was
cancelled, see `coq-eglot-lsp-cancel-all': RequestCancelled of LSP for a
request not started, Interrupted of coq-lsp for a running one."
  context code message cancelled)

(defun coq-eglot-lsp--severity (level)
  "The severity of LSP LEVEL, a number, see `coq-eglot-lsp-message'."
  ;; coq-lsp: Error 1, Warning 2, Notice 3, Info and Debug 4
  (pcase level (1 'error) (2 'warning) (3 'notice) (4 'info)))

(defun coq-eglot-lsp--message (message)
  "MESSAGE of the server as a `coq-eglot-lsp-message'.
MESSAGE is a plist with the keys :level and :text, or a string."
  (if (stringp message)
      (coq-eglot-lsp--make-message nil message)
    (coq-eglot-lsp--make-message
     (coq-eglot-lsp--severity (plist-get message :level))
     (plist-get message :text))))

(defun coq-eglot-lsp--answer (answer context width flags)
  "ANSWER of a goals request with CONTEXT, as a `coq-eglot-lsp-answer'.
Printed at WIDTH with FLAGS.  Nil if ANSWER is nil."
  (when answer
    (let ((range (plist-get answer :range)))
      (coq-eglot-lsp-make-answer
       :context context
       :version (plist-get (plist-get answer :textDocument) :version)
       :sentence (and range (coq-eglot-lsp-range range))
       :goals (plist-get answer :goals)
       :messages (mapcar #'coq-eglot-lsp--message
                         (plist-get answer :messages))
       :error (plist-get answer :error)
       :printing-width width
       :printing-flags flags))))

(defun coq-eglot-lsp--failure (err context)
  "ERR, the error object of a request with CONTEXT, as a failure.
See `coq-eglot-lsp-failure'."
  (let ((code (plist-get err :code)))
    (coq-eglot-lsp--make-failure
     context code (or (plist-get err :message) (format "%S" err))
     (and (memql code '(-32800 -32001)) t))))

(defun coq-eglot-lsp-version ()
  "The version of the current buffer last sent to the server."
  eglot--versioned-identifier)

(defun coq-eglot-lsp--server-for-request ()
  "Return the server of the current buffer, after sending pending changes."
  (let ((server (or (coq-eglot-lsp-ensure-server)
                    (user-error "No Coq language server for this buffer"))))
    (eglot--signal-textDocument/didChange)
    server))

(defvar coq-eglot-lsp--in-request nil
  "Non-nil while waiting for the answer to a synchronous request.
See `coq-eglot-lsp-request'.")

(defun coq-eglot-lsp-request (method params)
  "Send request METHOD with PARAMS to the server of the current buffer.
Pending changes of the buffer are sent first.  Return the answer, or
signal an error.  No timeout: checking may be long, \\[keyboard-quit]
stops waiting."
  (let ((coq-eglot-lsp--in-request t))
    (jsonrpc-request (coq-eglot-lsp--server-for-request) method params
                     :timeout nil)))

(defun coq-eglot-lsp--async-request (pos method params on-success on-error)
  "Send request METHOD at POS with PARAMS to the server of the buffer.
Pending changes of the buffer are sent first.  Return immediately its
`coq-eglot-lsp-context'.  ON-SUCCESS is called with the answer and the
context, ON-ERROR with a `coq-eglot-lsp-failure', in the current buffer
if still live.  PARAMS is a function returning the parameters, called
after the changes are sent.  ON-SUCCESS and ON-ERROR are called from a
timer, not from the process filter, so that they can send synchronous
requests.  Not while waiting for the
answer to a synchronous request, maybe to another server: when it
comes, `jsonrpc-request' would leave theirs, and them, unfinished."
  (let* ((server (coq-eglot-lsp--server-for-request))
         (buffer (current-buffer))
         (context (coq-eglot-lsp--make-context method pos)))
    (setf (coq-eglot-lsp-context-version context) eglot--versioned-identifier)
    (cl-labels ((run (fn arg)
                  (cond
                   ((not (buffer-live-p buffer)))
                   (coq-eglot-lsp--in-request
                    (run-at-time 0.01 nil #'run fn arg))
                   (t (with-current-buffer buffer (funcall fn arg)))))
                (later (fn)
                  (lambda (arg) (run-at-time 0 nil #'run fn arg))))
      (setf (coq-eglot-lsp-context-id context)
            ;; Internal, but `jsonrpc-async-request' does not return the id
            (car (jsonrpc--async-request-1
                  server method (funcall params)
                  :success-fn (later (lambda (answer)
                                       (funcall on-success answer context)))
                  :error-fn (later (lambda (err)
                                     (funcall on-error
                                              (coq-eglot-lsp--failure
                                               err context))))
                  :timeout nil)))
      context)))

(defun coq-eglot-lsp--pending-ids (server)
  "Ids of the requests sent to SERVER and not answered yet."
  ;; internal: an alist since jsonrpc 1.0.24 (Emacs 30), a hash table
  ;; before
  (cond
   ((fboundp 'jsonrpc--continuations)
    (mapcar #'car (jsonrpc--continuations server)))
   ((fboundp 'jsonrpc--request-continuations)
    (hash-table-keys (jsonrpc--request-continuations server)))))

(defun coq-eglot-lsp-cancel-all ()
  "Ask the server of the current buffer to cancel all pending requests.
Including those sent by Eglot on its own, like hover.  Their answers,
errors for cancelled requests, still come later."
  (let ((server (coq-eglot-lsp-current-server)))
    (when server
      (dolist (id (coq-eglot-lsp--pending-ids server))
        (jsonrpc-notify server :$/cancelRequest (list :id id))))))

(defun coq-eglot-lsp-send-changes ()
  "Send now the pending changes of the current buffer to the server.
Eglot sends them only after a short idle time otherwise.  Must not be
called from `after-change-functions'."
  (when (coq-eglot-lsp-current-server)
    (eglot--signal-textDocument/didChange)))

(defun coq-eglot-lsp--servers ()
  "All the running Coq servers."
  (let (servers)
    (maphash (lambda (_project project-servers)
               (dolist (server project-servers)
                 (when (cl-typep server 'coq-eglot-lsp-server)
                   (push server servers))))
             eglot--servers-by-project)
    servers))

(defun coq-eglot-lsp-workspace-update ()
  "Tell all the Coq servers that .vo files changed.
Each one checks again the Require sentences of its documents, and
cancels their pending requests.  All of them, because the projects of
different servers may share libraries.  Ignored before coq-lsp 0.2.5."
  (dolist (server (coq-eglot-lsp--servers))
    (jsonrpc-notify server :coq/workspace_update (make-hash-table))))

(defvar coq-eglot-lsp-printing-width-function nil
  "Function giving the printing width of the goals, or nil.
Called without argument in the script buffer before each goals request.
If it returns a number N, the goals are printed with Set Printing Width
N, otherwise with Coq's default width.  The answer gives the width, see
`coq-eglot-lsp-answer'.")

(defun coq-eglot-lsp--printing-width ()
  "Printing width of the next goals request, or nil.
See `coq-eglot-lsp-printing-width-function'."
  (and coq-eglot-lsp-printing-width-function
       (funcall coq-eglot-lsp-printing-width-function)))

(defvar coq-eglot-lsp-printing-flags-function nil
  "Function giving the printing flags of the goals, or nil.
Called without argument in the script buffer before each goals request.
It returns a list of Coq commands without their final dot, like \"Set
Printing Parentheses\", run before the goals are printed.  The answer
gives them, see `coq-eglot-lsp-answer'.")

(defun coq-eglot-lsp--printing-flags ()
  "Printing flags of the next goals request.
See `coq-eglot-lsp-printing-flags-function'."
  (and coq-eglot-lsp-printing-flags-function
       (funcall coq-eglot-lsp-printing-flags-function)))

(defvar coq-eglot-lsp-hyp-sorts-function nil
  "Function telling whether the goals need the sorts of the hypotheses.
Called without argument in the script buffer before each goals request.
If it returns non-nil, a second request asks the sort of the type of
each hypothesis of the first goal, see `coq-eglot-lsp--hyp-sorts-command':
the first goal of the answer has them with the key :hyp-sorts.  Both
requests are sent together: most of the cost of a request is its
latency, the sorts add almost nothing to the time of the goals.")

(defconst coq-eglot-lsp--hyp-sorts-command
  "1: try (match reverse goal with H : ?T |- _ => \
let s := type of T in idtac \"COQ-EGLOT-SORT\" H s; fail end)."
  "Coq command printing the sort of the type of each hypothesis.
Of the first goal, one message \"COQ-EGLOT-SORT name sort\" each.  The
failure after each message makes `match' try the next hypothesis.")

(defun coq-eglot-lsp--hyp-sorts-p ()
  "Non-nil if the goals need the sorts of the hypotheses.
See `coq-eglot-lsp-hyp-sorts-function'."
  (and coq-eglot-lsp-hyp-sorts-function
       (funcall coq-eglot-lsp-hyp-sorts-function)))

(defun coq-eglot-lsp--parse-hyp-sorts (messages)
  "The sorts in MESSAGES, of `coq-eglot-lsp--hyp-sorts-command'.
An alist from the names of the hypotheses to their sorts, like \"Prop\",
without universes."
  (let (sorts)
    (dolist (message messages)
      (when (string-match
             "\\`COQ-EGLOT-SORT \\([^ \n]+\\) \\([[:alpha:]]+\\)" message)
        (push (cons (match-string 1 message) (match-string 2 message))
              sorts)))
    (nreverse sorts)))

(defun coq-eglot-lsp--with-hyp-sorts (answer messages)
  "ANSWER of a goals request, its first goal with the sorts in MESSAGES.
See `coq-eglot-lsp--parse-hyp-sorts'.  ANSWER unchanged without goals."
  (let ((goals (plist-get (plist-get answer :goals) :goals)))
    (when (> (length goals) 0)
      (plist-put (aref goals 0) :hyp-sorts
                 (coq-eglot-lsp--parse-hyp-sorts messages))))
  answer)

(defun coq-eglot-lsp--goals-params (pos &optional width flags)
  "Parameters of a goals request at buffer position POS.
With Set Printing Width WIDTH if non-nil, and the commands FLAGS: the
server runs them on a copy of the state after the sentence, they change
nothing else."
  (let ((commands (append (and width
                               (list (format "Set Printing Width %d" width)))
                          flags)))
    (append (list :textDocument (eglot--VersionedTextDocumentIdentifier)
                  :position (coq-eglot-lsp-position pos)
                  :pp_format "Str")
            (and commands
                 (list :command (mapconcat (lambda (command)
                                             (concat command "."))
                                           commands " "))))))

(defun coq-eglot-lsp--with-hyp-sorts-answer (answer messages)
  "ANSWER, a `coq-eglot-lsp-answer', with the sorts in MESSAGES.
See `coq-eglot-lsp--with-hyp-sorts'."
  (when answer
    (coq-eglot-lsp--with-hyp-sorts
     (list :goals (coq-eglot-lsp-answer-goals answer)) messages))
  answer)

(defun coq-eglot-lsp-goals-options ()
  "What the next goals request depends on, besides the position.
A list: the printing width, the printing flags, and whether the sorts
of the hypotheses are asked.  For the key of a request."
  (list (coq-eglot-lsp--printing-width)
        (coq-eglot-lsp--printing-flags)
        (and (coq-eglot-lsp--hyp-sorts-p) t)))

(defun coq-eglot-lsp-goals-async (pos on-success on-error)
  "Ask asynchronously the goals after the sentence at POS.
ON-SUCCESS is called with a `coq-eglot-lsp-answer', or nil if the
server answered nothing, ON-ERROR with a `coq-eglot-lsp-failure'.  The
first goal has the sorts of its hypotheses if needed, see
`coq-eglot-lsp-hyp-sorts-function'.  See `coq-eglot-lsp--async-request'.
Return the context of the request."
  (let* ((width (coq-eglot-lsp--printing-width))
         (flags (coq-eglot-lsp--printing-flags))
         ;; with the sorts: the answer of the goals and the messages of
         ;; the sorts, `none' until they arrive
         (answer 'none)
         (messages (if (coq-eglot-lsp--hyp-sorts-p) 'none nil))
         (done (lambda ()
                 (unless (or (eq answer 'none) (eq messages 'none))
                   (funcall on-success
                            (coq-eglot-lsp--with-hyp-sorts-answer
                             answer messages))))))
    (when (eq messages 'none)
      (coq-eglot-lsp-query-async
       pos coq-eglot-lsp--hyp-sorts-command
       (lambda (result) (setq messages result) (funcall done))
       ;; outside of a proof for instance: no sorts
       (lambda (_failure) (setq messages nil) (funcall done))))
    (coq-eglot-lsp--async-request
     pos :proof/goals
     (lambda () (coq-eglot-lsp--goals-params pos width flags))
     (lambda (result context)
       (setq answer (coq-eglot-lsp--answer result context width flags))
       (funcall done))
     on-error)))

(defun coq-eglot-lsp-ping (on-answer)
  "Send a cheap request, call ON-ANSWER without argument when it is answered.
Its answer tells that the server is ready again after an interruption."
  (coq-eglot-lsp--async-request
   (point-min) :proof/goals
   (lambda () (coq-eglot-lsp--goals-params (point-min)))
   (lambda (_answer _context) (funcall on-answer))
   (lambda (_failure) (funcall on-answer))))

(defun coq-eglot-lsp-check-async (pos on-success on-error)
  "Ask asynchronously the server to check up to the sentence at POS.
No goals are computed.  ON-SUCCESS is called with a
`coq-eglot-lsp-checked', ON-ERROR with a `coq-eglot-lsp-failure'.  See
`coq-eglot-lsp--async-request'.  Return the context of the request."
  (coq-eglot-lsp--async-request
   pos :petanque/get_state_at_pos
   (lambda ()
     (list :uri (plist-get (eglot--TextDocumentIdentifier) :uri)
           :position (coq-eglot-lsp-position pos)
           :opts (list :memo t :hash :json-false)))
   (lambda (_answer context)
     (funcall on-success (coq-eglot-lsp--make-checked context)))
   on-error))

(defun coq-eglot-lsp-query-async (pos command on-success on-error)
  "Run Coq COMMAND asynchronously in the state at POS.
The state is the one after the sentences ending before POS.  The
document does not change.  ON-SUCCESS is called with the messages of
COMMAND, a list of strings, ON-ERROR with a `coq-eglot-lsp-failure'.
See `coq-eglot-lsp--async-request'.  Return the context of the
request."
  (coq-eglot-lsp--async-request
   pos :petanque/run_at_point
   (lambda ()
     (list :textDocument (eglot--VersionedTextDocumentIdentifier)
           :position (coq-eglot-lsp-position pos)
           :command command))
   (lambda (answer _context)
     ;; each feedback is [LEVEL TEXT]
     (funcall on-success
              (mapcar (lambda (feedback) (aref feedback 1))
                      (plist-get answer :feedback))))
   on-error))

(defun coq-eglot-lsp-query (pos command)
  "Run Coq COMMAND in the state at POS and return its messages.
Like `coq-eglot-lsp-query-async', but wait for the answer.  Return a
list of strings, or signal an error if COMMAND fails."
  (mapcar (lambda (feedback) (aref feedback 1))
          (plist-get (coq-eglot-lsp-request
                      :petanque/run_at_point
                      (list :textDocument (eglot--VersionedTextDocumentIdentifier)
                            :position (coq-eglot-lsp-position pos)
                            :command command))
                     :feedback)))

;;; Notifications

(defun coq-eglot-lsp--uri-to-path (uri)
  "File name of URI."
  (if (fboundp 'eglot-uri-to-path)
      (eglot-uri-to-path uri)
    (with-no-warnings (eglot--uri-to-path uri))))

(defun coq-eglot-lsp--buffer (uri)
  "The live buffer visiting URI, or nil."
  (find-buffer-visiting (coq-eglot-lsp--uri-to-path uri)))

(cl-defmethod eglot-handle-notification
  ((_server coq-eglot-lsp-server) (_method (eql $/coq/serverVersion))
   &key coq_lsp &allow-other-keys)
  "Warn if the version COQ_LSP of the server is too old."
  (when (and (stringp coq_lsp)
             (version< coq_lsp coq-eglot-lsp-minimal-version))
    (display-warning
     'coq-eglot
     (format "coq-lsp %s is too old for the Eglot backend of Coq, \
version %s or later is needed."
             coq_lsp coq-eglot-lsp-minimal-version))))

(cl-defmethod eglot-handle-notification :after
  ((_server coq-eglot-lsp-server) (_method (eql window/logMessage))
   &key message &allow-other-keys)
  "Warn if the server cannot interrupt Coq although asked to."
  (when (and (stringp message)
             (string-match-p "int_backend: memprof-limits (fake)" message))
    (display-warning
     'coq-eglot
     "The Coq server cannot interrupt computations: its OCaml does not \
support memprof-limits.  Set `coq-eglot-strong-interrupt' to nil.")))

(defvar-local coq-eglot-lsp-progress-function nil
  "Function called while the server checks the current buffer.
It is called with a `coq-eglot-lsp-progress', maybe about an older
version of the buffer.")

(cl-defmethod eglot-handle-notification
  ((_server coq-eglot-lsp-server) (_method (eql $/coq/fileProgress))
   &key textDocument processing &allow-other-keys)
  "Call `coq-eglot-lsp-progress-function' of the buffer being checked.
PROCESSING is the part of the document still to check: coq-lsp 0.2
sends one range, from the end of the last sentence checked to the end
of the document, even when the check is finished."
  (let ((buffer (coq-eglot-lsp--buffer (plist-get textDocument :uri))))
    (when (and buffer (> (length processing) 0))
      (with-current-buffer buffer
        (when coq-eglot-lsp-progress-function
          (funcall coq-eglot-lsp-progress-function
                   (coq-eglot-lsp--make-progress
                    (plist-get textDocument :version)
                    (car (coq-eglot-lsp-range
                          (plist-get (aref processing 0) :range))))))))))

;;; Diagnostics

(defvar-local coq-eglot-lsp-diagnostics-function nil
  "Function called with the diagnostics of the current buffer.
It is called with a `coq-eglot-lsp-diagnostics', maybe about an older
version of the buffer.")

(defun coq-eglot-lsp--diagnostic (diag)
  "DIAG, a diagnostic of the server, as a `coq-eglot-lsp-diagnostic'."
  (let ((range (coq-eglot-lsp-range (plist-get diag :range)))
        (sentence (plist-get (plist-get diag :data) :sentenceRange)))
    (coq-eglot-lsp--make-diagnostic
     (car range) (cdr range)
     (coq-eglot-lsp--severity (plist-get diag :severity))
     (plist-get diag :message)
     (and sentence (coq-eglot-lsp-range sentence)))))

;; Eglot still gives the diagnostics to flymake
(cl-defmethod eglot-handle-notification :after
  ((_server coq-eglot-lsp-server)
   (_method (eql textDocument/publishDiagnostics))
   &key uri diagnostics version &allow-other-keys)
  "Call `coq-eglot-lsp-diagnostics-function' of the buffer of URI.
With its DIAGNOSTICS for VERSION, or the current version if not given."
  (let ((buffer (coq-eglot-lsp--buffer uri)))
    (when buffer
      (with-current-buffer buffer
        (when coq-eglot-lsp-diagnostics-function
          (funcall coq-eglot-lsp-diagnostics-function
                   (coq-eglot-lsp--make-diagnostics
                    (or version eglot--versioned-identifier)
                    (mapcar #'coq-eglot-lsp--diagnostic diagnostics))))))))

(provide 'coq-eglot-lsp)

;;; coq-eglot-lsp.el ends here
