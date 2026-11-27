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
    (function eglot--hover-info)
    (function eglot-server-capable eglot--server-capable)
    (function eglot-uri-to-path eglot--uri-to-path)
    (variable eglot--servers-by-project)
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
the request petanque/get_state_at_pos.  Before 0.2.4, the server does
not tell the range of each sentence it executes, see
`coq-eglot-lsp-execution': going back to a sentence the server checked
in a row with others may take two steps, the first one too far back.")

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
   :send_diags_extra_data t
   ;; The range of each sentence before it is executed, see
   ;; `coq-eglot-lsp-execution' (coq-lsp >= 0.2.4)
   :send_execinfo t))

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
  (let ((server (and (eglot-managed-p)
                     (eglot-current-server))))
    (when (cl-typep server 'coq-eglot-lsp-server)
      (let ((args (ignore-errors (coq-eglot-lsp-load-path-args))))
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

(defun coq-eglot-lsp--contact (&optional _interactive _project)
  "Eglot contact for Coq: our server class and its command line.
With the load path of the current buffer, see
`coq-eglot-lsp-load-path-args': coq-lsp adds it to the one of the
project file it finds in its root directory, if any.  The project
argument is unused here: Eglot starts the server in its root, where
coq-lsp finds the project file.  Without one, no recursive load path is
guessed: an implicit -R of the root may scan an arbitrarily large tree."
  (let* ((command (coq-eglot-lsp-server-command))
         (buffer-args
          (condition-case err
              (coq-eglot-lsp-load-path-args)
            (user-error (signal (car err) (cdr err)))
            (error (user-error "Invalid `coq-load-path': %s"
                               (error-message-string err))))))
    (coq-eglot-lsp--check-server-version (car command))
    (cons 'coq-eglot-lsp-server
          (append command
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

(defun coq-eglot-lsp--connect-timed-out-p (start)
  "Non-nil if a connection started at time START waited too long.
More than `eglot-connect-timeout' seconds; never if it is nil, as for
Eglot."
  (and (numberp eglot-connect-timeout)
       (>= (- (float-time) start) eglot-connect-timeout)))

(defun coq-eglot-lsp-ensure-server (&optional no-wait)
  "Return the Coq server of the current buffer, starting it if needed.
Unlike `eglot-ensure', start it now, not after the current command.  If
it is still connecting, started by another command or by Eglot, wait
for it, at most `eglot-connect-timeout' seconds, without limit if
nil: do not start another one.  If NO-WAIT is non-nil, do not wait:
return nil if it is not connected yet."
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
          (let ((start (float-time)))
            (while (and (not (coq-eglot-lsp-current-server))
                        (coq-eglot-lsp-connecting-servers)
                        (not (coq-eglot-lsp--connect-timed-out-p start)))
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

(defun coq-eglot-lsp--abandon-requests (server)
  "Forget the requests sent to SERVER and not answered, with their timeouts.
When it dies, their error functions are not called."
  ;; internal: an alist of (ID METHOD SUCCESS ERROR TIMER) since jsonrpc
  ;; 1.0.24 (Emacs 30), a hash table of (SUCCESS ERROR TIMER) before
  (let ((cancel (lambda (continuation)
                  (let ((timer (car (last continuation))))
                    (when (timerp timer) (cancel-timer timer))))))
    (cond
     ((fboundp 'jsonrpc--continuations)
      (mapc cancel (jsonrpc--continuations server)))
     ((fboundp 'jsonrpc--request-continuations)
      (maphash (lambda (_id continuation) (funcall cancel continuation))
               (jsonrpc--request-continuations server)))))
  (jsonrpc-forget-pending-continuations server))

(defun coq-eglot-lsp-kill-connecting-servers ()
  "Kill the servers of the current buffer still connecting.
See `coq-eglot-lsp-connecting-servers'.  Their initialization is
abandoned first: Eglot would report it failed, as an error from the
sentinel of the process."
  (dolist (server (coq-eglot-lsp-connecting-servers))
    (ignore-errors
      (coq-eglot-lsp--abandon-requests server)
      (jsonrpc-shutdown server))))

(defvar-local coq-eglot-lsp--waiting nil
  "Functions waiting for the server of the buffer to be connected.
Each one is called with the server once connected, or with nil if the
connection failed, see `coq-eglot-lsp--when-connected'.  The last one
first.")

(defvar-local coq-eglot-lsp--waiting-timer nil
  "Timer watching the connection of the server, see `coq-eglot-lsp--waiting'.")

(defun coq-eglot-lsp--buffers-waiting ()
  "The buffers of the project of the current buffer waiting for its server.
See `coq-eglot-lsp--waiting'."
  (let ((project (eglot--current-project)))
    (seq-filter (lambda (buffer)
                  (with-current-buffer buffer
                    (and coq-eglot-lsp--waiting
                         (equal (eglot--current-project) project))))
                (buffer-list))))

(defun coq-eglot-lsp-shutdown ()
  "Stop the server of the current buffer, even if it is busy.
Also if it is still connecting: like a connected one, it is the server
of all the buffers of the project, and the requests waiting for it in
any of them are forgotten, see `coq-eglot-lsp--waiting'.  Return the
buffers it managed, and those that waited for it."
  (let ((server (coq-eglot-lsp-current-server))
        (waiting (coq-eglot-lsp--buffers-waiting))
        (buffers nil))
    (dolist (buffer waiting)
      (with-current-buffer buffer (coq-eglot-lsp--forget-waiting)))
    (coq-eglot-lsp-kill-connecting-servers)
    (when server
      (setq buffers (eglot--managed-buffers server))
      ;; a busy server does not answer the shutdown request: it is
      ;; killed after the timeout, which signals an error
      (ignore-errors (eglot-shutdown server nil 0.3 t)))
    (seq-uniq (append buffers waiting))))

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
is its jsonrpc id, for `$/cancelRequest'.  POLICY describes its
client-side scheduling, see `coq-eglot-lsp-policy'.  QUEUE-KEY groups
replaceable requests of the same kind.  CANCELLED is non-nil when the
request was abandoned.  DEBOUNCE is its admission delay before it enters the
scheduler, or nil."
  method position version id policy queue-key cancelled debounce)

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
with the key :hyp-sorts, see `coq-eglot-lsp-hyp-sorts-async'), or
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

(cl-defstruct (coq-eglot-lsp-execution
               (:constructor coq-eglot-lsp--make-execution
                             (version start end)))
  "The server starts to execute the sentence from START to END of VERSION.
Sent before each sentence: the bounds of all the sentences checked,
not that they are checked."
  version start end)

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

(defun coq-eglot-lsp-message-string (message)
  "Text of MESSAGE, a `coq-eglot-lsp-message', as Coq prints it.
After \"Error: \" or \"Warning: \" according to its severity, like
in Proof General."
  (concat (pcase (coq-eglot-lsp-message-severity message)
            ('error "Error: ")
            ('warning "Warning: "))
          (coq-eglot-lsp-message-text message)))

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

(defun coq-eglot-lsp--document-version ()
  "The Eglot version of the current buffer's document."
  eglot--versioned-identifier)

(defun coq-eglot-lsp--flush-document ()
  "Send pending changes and return the document version sent."
  (eglot--signal-textDocument/didChange)
  (coq-eglot-lsp--document-version))

(defun coq-eglot-lsp--jsonrpc-request-with-id
    (server method params &rest args)
  "Send an asynchronous request and return its JSON-RPC identifier.
SERVER, METHOD, PARAMS and ARGS are as for `jsonrpc-async-request'.
The public function deliberately returns nil, so this is the only
place where the backend calls `jsonrpc--async-request-1'."
  (car (apply #'jsonrpc--async-request-1 server method params args)))

(defun coq-eglot-lsp-version ()
  "The version of the current buffer last sent to the server."
  (coq-eglot-lsp--document-version))

(defun coq-eglot-lsp-connect ()
  "Start the Coq server of the current buffer if needed, without waiting.
Return it if connected, nil if it is still connecting.  Signal an error
if it cannot be started, like without program: see
`coq-eglot-lsp-ensure-server'."
  (or (coq-eglot-lsp-ensure-server t)
      (and (null (coq-eglot-lsp-connecting-servers))
           (user-error "No Coq language server for this buffer"))))

(defun coq-eglot-lsp--forget-waiting ()
  "Forget the requests of the buffer waiting for its server to connect."
  (setq coq-eglot-lsp--waiting nil)
  (when coq-eglot-lsp--waiting-timer
    (cancel-timer coq-eglot-lsp--waiting-timer)
    (setq coq-eglot-lsp--waiting-timer nil)))

(defun coq-eglot-lsp-connecting-p ()
  "Non-nil if requests of the buffer wait for its server to connect."
  (and coq-eglot-lsp--waiting t))

(defun coq-eglot-lsp--when-connected (fn)
  "Call FN with the server of the buffer, once connected.
Right now if it is connected.  Otherwise start the connection without
waiting, see `coq-eglot-lsp-connect', and call FN in the buffer when
connected; with nil if the connection fails, or takes more than
`eglot-connect-timeout' seconds, if not nil."
  (let ((server (coq-eglot-lsp-connect)))
    (if server
        (funcall fn server)
      (push fn coq-eglot-lsp--waiting)
      (unless coq-eglot-lsp--waiting-timer
        (setq coq-eglot-lsp--waiting-timer
              (run-at-time 0.05 nil #'coq-eglot-lsp--watch-connection
                           (current-buffer) (float-time)))))))

(defun coq-eglot-lsp--watch-connection (buffer start)
  "Watch the connection of the server of BUFFER, asked at time START.
Call the functions waiting for it, see `coq-eglot-lsp--waiting'."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (setq coq-eglot-lsp--waiting-timer nil)
      (let ((server (coq-eglot-lsp-current-server)))
        (if (and (null server)
                 (coq-eglot-lsp-connecting-servers)
                 (not (coq-eglot-lsp--connect-timed-out-p start)))
            ;; still connecting
            (setq coq-eglot-lsp--waiting-timer
                  (run-at-time 0.05 nil #'coq-eglot-lsp--watch-connection
                               buffer start))
          (let ((waiting (reverse coq-eglot-lsp--waiting)))
            (setq coq-eglot-lsp--waiting nil)
            ;; one failing must not starve the others: they
            ;; report their own errors, see `coq-eglot-lsp--async-request'
            (dolist (fn waiting)
              (with-current-buffer buffer
                (with-demoted-errors "Coq: %S"
                  (funcall fn server))))))))))

;; Request admission
;;
;; Automatic UI events may occur in bursts.  Delay the creation of a
;; replaceable request until events with the same key have stopped for a short
;; time.  This is deliberately before request scheduling below: a superseded
;; event allocates no JSON-RPC id, captures no document version and needs no
;; LSP cancellation.

(cl-defstruct (coq-eglot-lsp-debounce
               (:constructor coq-eglot-lsp--make-debounce
                             (key timer on-cancel)))
  "A delayed automatic request.
KEY identifies equivalent events and TIMER runs the last one.  ON-CANCEL is
called if the request is replaced or explicitly cancelled."
  key timer on-cancel)

(defvar-local coq-eglot-lsp--debounces nil
  "Delayed automatic requests of the current buffer, by equal keys.
The value is a hash table created on first use.  Its entries are
`coq-eglot-lsp-debounce' objects.")

(defun coq-eglot-lsp--debounces ()
  "Return the debounce table of the current buffer, creating it if needed."
  (or coq-eglot-lsp--debounces
      (progn
        (add-hook 'kill-buffer-hook #'coq-eglot-lsp--cancel-debounces nil t)
        (setq coq-eglot-lsp--debounces (make-hash-table :test #'equal)))))

(defun coq-eglot-lsp--run-debounce (buffer key debounce request)
  "Run REQUEST for KEY in BUFFER if DEBOUNCE is still its current entry."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (let ((table coq-eglot-lsp--debounces))
        (when (and table (eq (gethash key table) debounce))
          (remhash key table)
          (funcall request))))))

(defun coq-eglot-lsp--cancel-debounce (debounce)
  "Cancel DEBOUNCE if it is still current.
Call its cancellation callback and return non-nil if it was current."
  (let* ((table coq-eglot-lsp--debounces)
         (key (coq-eglot-lsp-debounce-key debounce)))
    (when (and table (eq (gethash key table) debounce))
      (remhash key table)
      (let ((timer (coq-eglot-lsp-debounce-timer debounce)))
        (when (timerp timer) (cancel-timer timer)))
      (when-let ((callback (coq-eglot-lsp-debounce-on-cancel debounce)))
        (funcall callback))
      t)))

(cl-defun coq-eglot-lsp--debounce
    (key delay request &key on-cancel)
  "Run REQUEST after DELAY seconds without another call for KEY.
REQUEST is a function without arguments.  A newer call in the same buffer
with an equal KEY cancels and replaces the delayed request.  Replacement or
explicit cancellation calls ON-CANCEL when non-nil.  Return the internal
debounce object."
  (unless (and (numberp delay) (>= delay 0))
    (error "Invalid debounce delay: %S" delay))
  (unless (functionp request)
    (error "Invalid debounced request: %S" request))
  (let* ((table (coq-eglot-lsp--debounces))
         (old (gethash key table))
         (buffer (current-buffer))
         debounce)
    (when old
      (coq-eglot-lsp--cancel-debounce old))
    (setq debounce
          (coq-eglot-lsp--make-debounce
           key nil on-cancel))
    (setf (coq-eglot-lsp-debounce-timer debounce)
          (run-at-time delay nil #'coq-eglot-lsp--run-debounce
                       buffer key debounce request))
    (puthash key debounce table)
    debounce))

(defun coq-eglot-lsp--cancel-debounces ()
  "Cancel every delayed automatic request of the current buffer."
  (when coq-eglot-lsp--debounces
    (dolist (debounce (hash-table-values coq-eglot-lsp--debounces))
      (coq-eglot-lsp--cancel-debounce debounce))))

;; Request scheduling
;;
;; coq-lsp may interrupt its current synchronous request when it receives
;; another one.  This is useful while it is checking the document, but not
;; while it is formatting the final goals or answering an explicit query.
;; Every request therefore carries three scheduling properties; the queue
;; discipline may additionally wait for a burst of equivalent automatic
;; events to settle before admitting its last request:
;;
;;                           interruption     priority       queue      settle
;;   `finalization'          `protected'       40            `fifo'       -
;;   `user'                  `protected'       30            `fifo'       -
;;   `work'                  `resumable'       20            `latest'     -
;;   `background'            `discardable'     10            `latest'     -
;;   `hover'                 `discardable'      0            `drop'      0.05
;;
;; Interruptibility says what a request of greater priority may do to an
;; active request.  A `protected' request must finish first.  A `resumable'
;; request may be interrupted; if coq-lsp answers Interrupted, the scheduler
;; sends it again after the more important request.  A `discardable' request
;; is cancelled and its result is ignored.
;;
;; Priority decides which waiting request is considered first and whether it
;; may pass active, unprotected requests.  In particular, `finalization' waits
;; for an already active `user' request, but once waiting it runs before newer
;; `user' requests.  A `user' request may pass `work'; `work' may discard
;; `background' presentation enrichment; `background' may discard a `hover'.
;;
;; Queue discipline applies between equivalent requests.  `fifo' preserves
;; every request.  `latest' replaces requests with the same policy and
;; QUEUE-KEY.  `drop' does not queue at all when anything is active or
;; waiting.  Thus hovers never delay useful work, while hypothesis sorts may
;; wait briefly and a newer sorts request replaces the obsolete one.
;; SETTLE-DELAY, when non-nil, is a trailing-edge debounce attached to
;; `latest' or `drop': before entering the scheduler, equivalent events wait
;; that many seconds and only the last one becomes a request.  `fifo' cannot
;; settle because it promises to preserve every request.
;;
;; The named policies are known outside the scheduler: the request adapters
;; below select `finalization', `user', `work', `background' or `hover' for
;; each operation.  Only this scheduler interprets their properties and owns
;; the queues.  Callers outside this pseudo-server normally ask for an
;; operation, not a policy, and the session remains unaware of both policies
;; and transport scheduling: it tracks only the logical proof state.
;;
;; A request adapter is a function such as `coq-eglot-lsp-check-async' or
;; `coq-eglot-lsp-hover-async': it translates one semantic operation into an
;; LSP method and parameters, normalizes its answer, and selects its scheduling
;; policy.  They are grouped under "Request adapters" below; comments there
;; make each policy choice explicit.

(cl-defstruct (coq-eglot-lsp-policy
               (:constructor coq-eglot-lsp--create-policy
                             (name interruptibility priority discipline
                                   settle-delay)))
  "Scheduling properties of a request.
INTERRUPTIBILITY is `protected', `resumable' or `discardable'.  PRIORITY
is a number: a request can pass an unprotected request of lower
priority.  DISCIPLINE is `fifo', `latest' or `drop'.  SETTLE-DELAY, when
non-nil, debounces equivalent events before scheduling.  It is coupled to
DISCIPLINE: it is valid with `latest' or `drop', never with `fifo'."
  name interruptibility priority discipline settle-delay)

(defconst coq-eglot-lsp--supported-policy-combinations
  '((protected fifo)
    (resumable latest)
    (discardable latest)
    (discardable drop))
  "Supported pairs of request interruptibility and queue discipline.
Other combinations do not yet have a complete implementation: in particular,
replacement of an active `protected' request and the place of a resumed `fifo'
request are undefined.  Add a pair only with tests of replacement,
interruption and resumption.")

(defun coq-eglot-lsp--make-policy
    (name interruptibility priority discipline &optional settle-delay)
  "Make a validated scheduling policy named NAME.
See `coq-eglot-lsp-policy' for INTERRUPTIBILITY, PRIORITY, DISCIPLINE and
SETTLE-DELAY.
Signal an error for a combination whose semantics the scheduler does not
implement explicitly."
  (unless (symbolp name)
    (error "Invalid request policy name: %S" name))
  (unless (numberp priority)
    (error "Invalid request priority: %S" priority))
  (unless (memq interruptibility '(protected resumable discardable))
    (error "Invalid request interruptibility: %S" interruptibility))
  (unless (memq discipline '(fifo latest drop))
    (error "Invalid request queue discipline: %S" discipline))
  (unless (or (null settle-delay)
              (and (numberp settle-delay) (>= settle-delay 0)))
    (error "Invalid request settle delay: %S" settle-delay))
  (when (and settle-delay (eq discipline 'fifo))
    (error "A fifo request policy cannot have a settle delay"))
  (unless (member (list interruptibility discipline)
                  coq-eglot-lsp--supported-policy-combinations)
    (error "Unsupported request policy combination: %S with %S"
           interruptibility discipline))
  (coq-eglot-lsp--create-policy
   name interruptibility priority discipline settle-delay))

(defconst coq-eglot-lsp-finalization-policy
  (coq-eglot-lsp--make-policy 'finalization 'protected 40 'fifo)
  "Policy of the short request that finishes a script operation.")

(defconst coq-eglot-lsp-user-policy
  (coq-eglot-lsp--make-policy 'user 'protected 30 'fifo)
  "Policy of an explicit read requested by the user.")

(defconst coq-eglot-lsp-work-policy
  (coq-eglot-lsp--make-policy 'work 'resumable 20 'latest)
  "Policy of long document work that coq-lsp can resume.")

(defconst coq-eglot-lsp-background-policy
  (coq-eglot-lsp--make-policy 'background 'discardable 10 'latest)
  "Policy of optional presentation enrichment.")

(defconst coq-eglot-lsp-hover-policy
  (coq-eglot-lsp--make-policy 'hover 'discardable 0 'drop 0.05)
  "Policy of a hover: settle for 50 ms, then send only if the server is free.")

(defvar-local coq-eglot-lsp--request-queue nil
  "Requests waiting for the scheduler.
Each entry is (CONTEXT . SEND-FUNCTION).")

(defvar-local coq-eglot-lsp--active-requests nil
  "Contexts of the scheduled requests that have not answered yet.")

(defun coq-eglot-lsp--protected-active-p ()
  "Non-nil if an active request must finish before another one starts."
  (seq-some
   (lambda (context)
     (eq (coq-eglot-lsp-policy-interruptibility
          (coq-eglot-lsp-context-policy context))
         'protected))
   coq-eglot-lsp--active-requests))

(defun coq-eglot-lsp--priority (context)
  "Scheduling priority of CONTEXT."
  (coq-eglot-lsp-policy-priority (coq-eglot-lsp-context-policy context)))

(defun coq-eglot-lsp--queue-entry ()
  "Highest-priority entry of `coq-eglot-lsp--request-queue'.
Preserve FIFO order between entries of equal priority."
  (let ((best nil) (priority -1))
    (dolist (entry coq-eglot-lsp--request-queue best)
      (let ((candidate (coq-eglot-lsp--priority (car entry))))
        (when (> candidate priority)
          (setq best entry priority candidate))))))

(defun coq-eglot-lsp--can-start-p (context)
  "Non-nil if CONTEXT may start with the requests currently active."
  (and (not (coq-eglot-lsp--protected-active-p))
       (or (null coq-eglot-lsp--active-requests)
           (> (coq-eglot-lsp--priority context)
              (apply #'max (mapcar #'coq-eglot-lsp--priority
                                   coq-eglot-lsp--active-requests))))))

(defun coq-eglot-lsp--abandon (context)
  "Cancel and forget active or queued CONTEXT, without dispatching."
  (when-let ((debounce (coq-eglot-lsp-context-debounce context)))
    (coq-eglot-lsp--cancel-debounce debounce))
  (setf (coq-eglot-lsp-context-cancelled context) t
        (coq-eglot-lsp-context-debounce context) nil)
  (setq coq-eglot-lsp--active-requests
        (delq context coq-eglot-lsp--active-requests)
        coq-eglot-lsp--request-queue
        (seq-remove (lambda (entry) (eq (car entry) context))
                    coq-eglot-lsp--request-queue))
  (let ((server (coq-eglot-lsp-current-server))
        (id (coq-eglot-lsp-context-id context)))
    (when (and server id)
      (jsonrpc-notify server :$/cancelRequest (list :id id)))))

(defun coq-eglot-lsp--same-queue-kind-p (left right)
  "Non-nil if LEFT and RIGHT replace one another under `latest'."
  (and (eq (coq-eglot-lsp-policy-name
            (coq-eglot-lsp-context-policy left))
           (coq-eglot-lsp-policy-name
            (coq-eglot-lsp-context-policy right)))
       (equal (coq-eglot-lsp-context-queue-key left)
              (coq-eglot-lsp-context-queue-key right))))

(defun coq-eglot-lsp--dispatch-scheduled ()
  "Start the highest-priority request allowed by the active requests."
  (let (entry context)
    (while (and (setq entry (coq-eglot-lsp--queue-entry))
                (progn (setq context (car entry))
                       (coq-eglot-lsp--can-start-p context)))
      (setq coq-eglot-lsp--request-queue
            (delq entry coq-eglot-lsp--request-queue))
      ;; Optional lower-priority requests are discarded, not suspended.
      (dolist (active (copy-sequence coq-eglot-lsp--active-requests))
        (when (and (< (coq-eglot-lsp--priority active)
                      (coq-eglot-lsp--priority context))
                   (eq (coq-eglot-lsp-policy-interruptibility
                        (coq-eglot-lsp-context-policy active))
                       'discardable))
          (coq-eglot-lsp--abandon active)))
      (push context coq-eglot-lsp--active-requests)
      (funcall (cdr entry)))))

(defun coq-eglot-lsp--schedule (context send)
  "Schedule CONTEXT to call SEND.  Return non-nil unless it was dropped."
  (let* ((policy (coq-eglot-lsp-context-policy context))
         (discipline (coq-eglot-lsp-policy-discipline policy)))
    (cond
     ((and (eq discipline 'drop)
           (or coq-eglot-lsp--active-requests coq-eglot-lsp--request-queue))
      (setf (coq-eglot-lsp-context-cancelled context) t)
      nil)
     (t
      (when (eq discipline 'latest)
        (dolist (entry (copy-sequence coq-eglot-lsp--request-queue))
          (when (coq-eglot-lsp--same-queue-kind-p context (car entry))
            (coq-eglot-lsp--abandon (car entry))))
        (dolist (active (copy-sequence coq-eglot-lsp--active-requests))
          (when (coq-eglot-lsp--same-queue-kind-p context active)
            (coq-eglot-lsp--abandon active))))
      (setq coq-eglot-lsp--request-queue
            (append coq-eglot-lsp--request-queue
                    (list (cons context send))))
      (coq-eglot-lsp--dispatch-scheduled)
      t))))

(defun coq-eglot-lsp--request-finished (context)
  "Update the scheduler after the request of CONTEXT answered."
  (setq coq-eglot-lsp--active-requests
        (delq context coq-eglot-lsp--active-requests))
  (coq-eglot-lsp--dispatch-scheduled))

(defun coq-eglot-lsp--reset-scheduler ()
  "Forget all scheduler state of the current buffer."
  (coq-eglot-lsp--cancel-debounces)
  (dolist (entry coq-eglot-lsp--request-queue)
    (setf (coq-eglot-lsp-context-cancelled (car entry)) t))
  (dolist (context coq-eglot-lsp--active-requests)
    (setf (coq-eglot-lsp-context-cancelled context) t))
  (setq coq-eglot-lsp--request-queue nil
        coq-eglot-lsp--active-requests nil))

(defun coq-eglot-lsp--async-request
    (pos method params on-success on-error &optional policy queue-key)
  "Send request METHOD at POS with PARAMS to the server of the buffer.
Without waiting, even for the server to connect, see
`coq-eglot-lsp--when-connected'.  Pending changes of the buffer are sent
first.  Return immediately its `coq-eglot-lsp-context'.  ON-SUCCESS is
called with the answer and the context, ON-ERROR with a
`coq-eglot-lsp-failure', in the current buffer if still live: also if
the server does not connect.  PARAMS is a function returning the
parameters, called after the changes are sent.  POLICY defaults to
`coq-eglot-lsp-user-policy'; QUEUE-KEY distinguishes replaceable
requests under a `latest' policy and is required when the policy has a
settle delay.  Such a request enters the scheduler only after its burst
of equivalent events has settled.  ON-SUCCESS and ON-ERROR are called
from a timer, not from the process filter: they may send other requests.
No request of the backend waits for its answer: while waiting in
`jsonrpc-request', the answers of the others would come, and callbacks
sending other requests would run, nested."
  (let ((buffer (current-buffer))
        (context (coq-eglot-lsp--make-context method pos)))
    (setf (coq-eglot-lsp-context-policy context)
          (or policy coq-eglot-lsp-user-policy)
          (coq-eglot-lsp-context-queue-key context) queue-key)
    (when (and (coq-eglot-lsp-policy-settle-delay
                (coq-eglot-lsp-context-policy context))
               (null queue-key))
      (error "A settled request policy needs a queue key"))
    (cl-labels ((run (fn arg)
                  (when (buffer-live-p buffer)
                    (with-current-buffer buffer (funcall fn arg))))
                (later (fn)
                  (lambda (arg) (run-at-time 0 nil #'run fn arg)))
                (succeed (answer)
                  (unwind-protect
                      (unless (coq-eglot-lsp-context-cancelled context)
                        (funcall on-success answer context))
                    (coq-eglot-lsp--request-finished context)))
                (fail (failure)
                  (if (and (not (coq-eglot-lsp-context-cancelled context))
                           (eq (coq-eglot-lsp-policy-interruptibility
                                (coq-eglot-lsp-context-policy context))
                               'resumable)
                           (= (or (coq-eglot-lsp-failure-code failure) 0)
                              -32001))
                      ;; coq-lsp interrupted the synchronous request to run a
                      ;; more important one.  Reissue it after that request;
                      ;; the document check itself is kept by the server.
                      (progn
                        (setq coq-eglot-lsp--active-requests
                              (delq context coq-eglot-lsp--active-requests))
                        (setf (coq-eglot-lsp-context-id context) nil)
                        (coq-eglot-lsp--schedule context #'send))
                    (unwind-protect
                        (unless (coq-eglot-lsp-context-cancelled context)
                          (funcall on-error failure))
                      (coq-eglot-lsp--request-finished context))))
                (send ()
                  (coq-eglot-lsp--when-connected
                   (lambda (server)
                     (unless (coq-eglot-lsp-context-cancelled context)
                       (if (null server)
                           (funcall (later #'fail)
                                    (coq-eglot-lsp--make-failure
                                     context nil
                                     "The Coq language server did not start"
                                     nil))
                         ;; Maybe called later, from a timer, see
                         ;; `coq-eglot-lsp--when-connected': an error reaches
                         ;; no caller, it must be turned into an answer.
                         (condition-case err
                             (progn
                               (setf (coq-eglot-lsp-context-version context)
                                     (coq-eglot-lsp--flush-document))
                               (setf (coq-eglot-lsp-context-id context)
                                     (coq-eglot-lsp--jsonrpc-request-with-id
                                      server method (funcall params)
                                      :success-fn (later #'succeed)
                                      :error-fn
                                      (later
                                       (lambda (err)
                                         (fail
                                          (coq-eglot-lsp--failure
                                           err context))))
                                      :timeout nil)))
                           (error
                            (funcall
                             (later #'fail)
                             (coq-eglot-lsp--make-failure
                              context nil (error-message-string err)
                              nil)))))))))
                (cancel-admission ()
                  (setf (coq-eglot-lsp-context-cancelled context) t
                        (coq-eglot-lsp-context-debounce context) nil))
                (admit ()
                  (setf (coq-eglot-lsp-context-debounce context) nil)
                  (coq-eglot-lsp--schedule context #'send)))
      (let* ((policy (coq-eglot-lsp-context-policy context))
             (delay (coq-eglot-lsp-policy-settle-delay policy)))
        (if (null delay)
            (coq-eglot-lsp--schedule context #'send)
          (setf (coq-eglot-lsp-context-debounce context)
                (coq-eglot-lsp--debounce
                 (cons (coq-eglot-lsp-policy-name policy) queue-key)
                 delay #'admit
                 :on-cancel #'cancel-admission))))
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
errors for cancelled requests, still come later.  Those waiting for the
server to connect are not sent, and get no answer."
  (coq-eglot-lsp--forget-waiting)
  (coq-eglot-lsp--reset-scheduler)
  (let ((server (coq-eglot-lsp-current-server)))
    (when server
      (dolist (id (coq-eglot-lsp--pending-ids server))
        (jsonrpc-notify server :$/cancelRequest (list :id id))))))

(defun coq-eglot-lsp-cancel-request (context)
  "Ask the server to cancel the request of CONTEXT, if it was sent.
Its answer, an error for a cancelled request, may still come later."
  (when context
    ;; Only after sending the cancellation may a queued request be emitted.
    (coq-eglot-lsp--abandon context)
    (coq-eglot-lsp--dispatch-scheduled)))

(defun coq-eglot-lsp-send-changes ()
  "Send now the pending changes of the current buffer to the server.
Eglot sends them only after a short idle time otherwise.  Must not be
called from `after-change-functions'."
  (when (coq-eglot-lsp-current-server)
    (coq-eglot-lsp--flush-document)))

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

(defvar coq-eglot-lsp-hyp-sort-names-function nil
  "Function returning the hypotheses whose sorts a goals answer needs.
Called with a `coq-eglot-lsp-answer'.  It returns their names as a list
of strings.  If nil, all hypotheses are asked, for compatibility.  The
interface uses this to avoid computing sorts that cannot affect its
formatting.")

(defcustom coq-eglot-lsp-hyp-sorts-wait 0.05
  "Seconds the interface may wait before displaying goals without sorts.
This delay affects presentation only: the goals answer has already been
delivered and the sentence has already been processed."
  :type 'number
  :group 'coq-eglot)

(defcustom coq-eglot-lsp-hyp-sorts-deadline 0.3
  "Seconds before cancelling a hypothesis-sorts request.
Before this timeout, a result that missed the initial display may still
be offered to the user.  After it, the auxiliary request is cancelled
so that context compaction cannot keep Rocq busy indefinitely."
  :type 'number
  :group 'coq-eglot)

(defconst coq-eglot-lsp--hyp-sorts-command
  "1: try (match reverse goal with H : ?T |- _ => \
let s := type of T in idtac \"COQ-EGLOT-SORT\" H s; fail end)."
  "Coq command printing the sort of the type of each hypothesis.
Of the first goal, one message \"COQ-EGLOT-SORT name sort\" each.  The
failure after each message makes `match' try the next hypothesis.")

(defun coq-eglot-lsp--hyp-sorts-command (names)
  "Coq command printing the sorts of the hypotheses NAMES.
With NAMES nil, return nil.  If no selector function is installed,
return the command that visits all hypotheses."
  (cond
   ((null coq-eglot-lsp-hyp-sort-names-function)
    coq-eglot-lsp--hyp-sorts-command)
   ((null names) nil)
   (t
    (format
     "1: %s."
     (mapconcat
      (lambda (name)
        ;; NAME comes from Rocq as a local identifier.  Printing it as a
        ;; string makes parsing independent of `idtac's term printer.
        (format "try (let T := type of %s in let s := type of T in \
idtac \"COQ-EGLOT-SORT %s\" s)" name name))
      names "; ")))))

(defun coq-eglot-lsp--hyp-sort-names (answer)
  "Names of the hypotheses whose sorts are needed in ANSWER."
  (and coq-eglot-lsp-hyp-sort-names-function
       (funcall coq-eglot-lsp-hyp-sort-names-function answer)))

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

(defun coq-eglot-lsp--with-hyp-sorts (answer messages &optional late)
  "ANSWER of a goals request, its first goal with the sorts in MESSAGES.
See `coq-eglot-lsp--parse-hyp-sorts'.  With LATE, keep them under
`:hyp-sorts-late': the interface may offer them, but must not change an
already displayed goal by itself.  ANSWER is unchanged without goals."
  (let ((goals (plist-get (plist-get answer :goals) :goals)))
    (when (> (length goals) 0)
      (plist-put (aref goals 0) (if late :hyp-sorts-late :hyp-sorts)
                 (coq-eglot-lsp--parse-hyp-sorts messages))))
  answer)

(defun coq-eglot-lsp-add-hyp-sorts (answer sorts &optional late)
  "Add SORTS to the first goal of ANSWER and return ANSWER.
SORTS is an alist from hypothesis names to their sorts.  With LATE, use
`:hyp-sorts-late', so displaying the answer is not changed implicitly."
  (let ((goals (and answer (plist-get (coq-eglot-lsp-answer-goals answer)
                                      :goals))))
    (when (> (length goals) 0)
      (plist-put (aref goals 0) (if late :hyp-sorts-late :hyp-sorts) sorts)))
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

(defun coq-eglot-lsp-goals-options ()
  "What the next goals request depends on, besides the position.
A list: the printing width and the printing flags.  For the key of a
request.  Hypothesis sorts are a separate presentation request and do
not affect this key."
  (list (coq-eglot-lsp--printing-width)
        (coq-eglot-lsp--printing-flags)))

;;; Request adapters
;;
;; These functions are the semantic API of the pseudo-server.  Each one owns
;; the scheduling policy of the request it builds; callers normally do not.

(defun coq-eglot-lsp-goals-async
    (pos on-success on-error &optional policy queue-key)
  "Ask asynchronously the goals after the sentence at POS.
ON-SUCCESS is called with a `coq-eglot-lsp-answer', or nil if the
server answered nothing, ON-ERROR with a `coq-eglot-lsp-failure'.
Hypothesis sorts are deliberately not asked here: they are a separate
presentation enrichment, see `coq-eglot-lsp-hyp-sorts-async'.  See
`coq-eglot-lsp--async-request'.  Return the context of the request."
  (let ((width (coq-eglot-lsp--printing-width))
        (flags (coq-eglot-lsp--printing-flags)))
    ;; `user' by default; final goals pass `finalization' below.
    (coq-eglot-lsp--async-request
     pos :proof/goals
     (lambda () (coq-eglot-lsp--goals-params pos width flags))
     (lambda (result context)
       (let ((answer (coq-eglot-lsp--answer result context width flags)))
         ;; Whoever asked, the observers learn the sentence range now.
         (when answer (coq-eglot-lsp--publish answer))
         (funcall on-success answer)))
     on-error policy queue-key)))

(defun coq-eglot-lsp-final-goals-async (pos on-success on-error)
  "Ask the final goals at POS as a short critical section.
Unlike a general goals query, interactive read requests wait for this
one to answer instead of interrupting its synchronous formatting phase."
  ;; `finalization': protect the short synchronous formatting phase.
  (coq-eglot-lsp-goals-async
   pos on-success on-error coq-eglot-lsp-finalization-policy 'final-goals))

(defun coq-eglot-lsp-hyp-sorts-async (answer on-success on-error)
  "Ask asynchronously for the hypothesis sorts needed by ANSWER.
Call ON-SUCCESS with their alist, ON-ERROR with a
`coq-eglot-lsp-failure'.  Return the request context, or nil when no
hypothesis can benefit from the enrichment.  This request is for
presentation only and never changes ANSWER by itself."
  (let* ((context (and answer (coq-eglot-lsp-answer-context answer)))
         (pos (and context (coq-eglot-lsp-context-position context)))
         (names (and answer (coq-eglot-lsp--hyp-sort-names answer)))
         (command (and pos (coq-eglot-lsp--hyp-sorts-command names))))
    (when command
      ;; `background': presentation enrichment must yield to useful work.
      (coq-eglot-lsp-query-async
       pos command
       (lambda (messages)
         (funcall on-success (coq-eglot-lsp--parse-hyp-sorts messages)))
       on-error coq-eglot-lsp-background-policy 'hyp-sorts))))

(defun coq-eglot-lsp-ping (on-answer)
  "Send a cheap request, call ON-ANSWER without argument when it is answered.
Its answer tells that the server is ready again after an interruption."
  ;; `work': this readiness probe participates in interruption recovery.
  (coq-eglot-lsp--async-request
   (point-min) :proof/goals
   (lambda () (coq-eglot-lsp--goals-params (point-min)))
   (lambda (_answer _context) (funcall on-answer))
   (lambda (_failure) (funcall on-answer))
   coq-eglot-lsp-work-policy 'ping))

(defun coq-eglot-lsp-check-async (pos on-success on-error)
  "Ask asynchronously the server to check up to the sentence at POS.
No goals are computed.  ON-SUCCESS is called with a
`coq-eglot-lsp-checked', ON-ERROR with a `coq-eglot-lsp-failure'.  See
`coq-eglot-lsp--async-request'.  Return the context of the request."
  ;; `work': checking is long and can be resumed after an interruption.
  (coq-eglot-lsp--async-request
   pos :petanque/get_state_at_pos
   (lambda ()
     (list :uri (plist-get (eglot--TextDocumentIdentifier) :uri)
           :position (coq-eglot-lsp-position pos)
           :opts (list :memo t :hash :json-false)))
   (lambda (_answer context)
     (funcall on-success (coq-eglot-lsp--make-checked context)))
   on-error coq-eglot-lsp-work-policy 'check))

(defun coq-eglot-lsp-query-async
    (pos command on-success on-error &optional policy queue-key)
  "Run Coq COMMAND asynchronously in the state at POS.
The state is the one after the sentences ending before POS.  The
document does not change.  ON-SUCCESS is called with the messages of
COMMAND, a list of strings, see `coq-eglot-lsp-message-string', ON-ERROR
with a `coq-eglot-lsp-failure'.
See `coq-eglot-lsp--async-request'.  Return the context of the
request."
  ;; `user' by default; presentation adapters may supply `background'.
  (coq-eglot-lsp--async-request
   pos :petanque/run_at_point
   (lambda ()
     (list :textDocument (eglot--VersionedTextDocumentIdentifier)
           :position (coq-eglot-lsp-position pos)
           :command command))
   (lambda (answer _context)
     ;; each feedback is [LEVEL TEXT]
     (funcall on-success
              (mapcar (lambda (feedback)
                        (coq-eglot-lsp-message-string
                         (coq-eglot-lsp--make-message
                          (coq-eglot-lsp--severity (aref feedback 0))
                          (aref feedback 1))))
                      (plist-get answer :feedback))))
   on-error policy queue-key))

(defun coq-eglot-lsp--server-capable (feature)
  "Non-nil if the current Eglot server supports FEATURE."
  (if (fboundp 'eglot-server-capable)
      (eglot-server-capable feature)
    (with-no-warnings (eglot--server-capable feature))))

(defun coq-eglot-lsp-hover-async (pos on-success on-error)
  "Ask for hover information at POS without delaying other requests.
Call ON-SUCCESS with the formatted text and its echo-area preference,
or ON-ERROR with a `coq-eglot-lsp-failure'.  Return the request context,
or nil when hover is unsupported.  Equivalent hover events first settle
briefly; the last one is then sent if the server is free, or dropped rather
than queued."
  (when (coq-eglot-lsp--server-capable :hoverProvider)
    ;; `hover': coalesce cursor movement, then never queue the resulting
    ;; automatic read behind useful work.
    (let ((context
           (coq-eglot-lsp--async-request
            pos :textDocument/hover
            (lambda ()
              (list :textDocument (eglot--TextDocumentIdentifier)
                    :position (coq-eglot-lsp-position pos)))
            (lambda (answer _context)
              (let* ((contents (plist-get answer :contents))
                     (info (unless (seq-empty-p contents)
                             (eglot--hover-info
                              contents (plist-get answer :range)))))
                (funcall on-success info
                         (and info (string-match-p "\n" info)))))
            on-error coq-eglot-lsp-hover-policy 'hover)))
      (unless (coq-eglot-lsp-context-cancelled context)
        context))))

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

;;; Publication of the events

;; The notifications, and the answers of the goals, are published to
;; the observers of the buffer they are about: the functions of
;; `coq-eglot-lsp-event-functions'.  Each observer takes the events it
;; is interested in: the sentences (coq-eglot-sentences.el), the
;; session, the interface.  Whether an event is still valid is decided
;; by the observers.

(defvar-local coq-eglot-lsp-event-functions nil
  "Functions called with each event of the server about the buffer.
An abnormal hook, local to the script buffer.  The events are
`coq-eglot-lsp-answer' (the goals after a sentence, whoever asked),
`coq-eglot-lsp-execution', `coq-eglot-lsp-progress' and
`coq-eglot-lsp-diagnostics', maybe about an older version of the
buffer.")

(defun coq-eglot-lsp--publish (event)
  "Publish EVENT to the observers of the current buffer.
See `coq-eglot-lsp-event-functions'."
  (run-hook-with-args 'coq-eglot-lsp-event-functions event))

(defun coq-eglot-lsp--publish-in (uri event-fn)
  "Publish the event of EVENT-FN to the observers of the buffer of URI.
EVENT-FN is called in the buffer, if any, to make the event."
  (let ((buffer (coq-eglot-lsp--buffer uri)))
    (when buffer
      (with-current-buffer buffer
        (when coq-eglot-lsp-event-functions
          (coq-eglot-lsp--publish (funcall event-fn)))))))

(cl-defmethod eglot-handle-notification
  ((_server coq-eglot-lsp-server) (_method (eql $/coq/fileProgress))
   &key textDocument processing &allow-other-keys)
  "Publish a `coq-eglot-lsp-progress' for the buffer being checked.
PROCESSING is the part of the document still to check: coq-lsp 0.2
sends one range, from the end of the last sentence checked to the end
of the document, even when the check is finished."
  (when (> (length processing) 0)
    (coq-eglot-lsp--publish-in
     (plist-get textDocument :uri)
     (lambda ()
       (coq-eglot-lsp--make-progress
        (plist-get textDocument :version)
        (car (coq-eglot-lsp-range (plist-get (aref processing 0) :range))))))))

(cl-defmethod eglot-handle-notification
  ((_server coq-eglot-lsp-server) (_method (eql $/coq/executionInformation))
   &key textDocument range &allow-other-keys)
  "Publish a `coq-eglot-lsp-execution' for the buffer being checked.
RANGE is the sentence the server starts to execute."
  (when range
    (coq-eglot-lsp--publish-in
     (plist-get textDocument :uri)
     (lambda ()
       (let ((bounds (coq-eglot-lsp-range range)))
         (coq-eglot-lsp--make-execution (plist-get textDocument :version)
                                        (car bounds) (cdr bounds)))))))

;;; Diagnostics

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
  "Publish a `coq-eglot-lsp-diagnostics' for the buffer of URI.
With its DIAGNOSTICS for VERSION, or the current version if not given."
  (coq-eglot-lsp--publish-in
   uri
   (lambda ()
     (coq-eglot-lsp--make-diagnostics
      (or version (coq-eglot-lsp--document-version))
      (mapcar #'coq-eglot-lsp--diagnostic diagnostics)))))

;;; The events buffer

(defconst coq-eglot-lsp-event-json-buffer-name "*coq-eglot JSON*"
  "Name of the buffer where `coq-eglot-lsp-show-event-json' shows a message.")

(declare-function json-pretty-print-buffer "json" (&optional minimize))

(defun coq-eglot-lsp-show-event-json ()
  "Show the JSON message of the current line, indented.
In the events buffer of Eglot (`eglot-events-buffer'), each message is
on one line after a preamble, with the format full of
`eglot-events-buffer-config', the default.  It is shown in the buffer
`coq-eglot-lsp-event-json-buffer-name', point stays on the line.  In
the events buffers of the Coq servers, \\<coq-eglot-lsp-events-map>\
\\[coq-eglot-lsp-show-event-json] runs this command."
  (interactive)
  (require 'json)
  (let ((line (buffer-substring-no-properties (line-beginning-position)
                                              (line-end-position))))
    ;; the preamble has brackets, never braces: a message is an object
    (unless (string-match "{" line)
      (user-error "Coq: no JSON message on this line"))
    (let ((json (substring line (match-beginning 0))))
      ;; `json-pretty-print-buffer' keeps a truncated message as is
      (condition-case err
          (json-parse-string json)
        (json-error
         (user-error "Coq: not a complete JSON message on this line (%s)"
                     (error-message-string err))))
      (with-current-buffer (get-buffer-create
                            coq-eglot-lsp-event-json-buffer-name)
        (let ((inhibit-read-only t))
          (erase-buffer)
          (insert json)
          (json-pretty-print-buffer)
          (goto-char (point-min))
          (unless (derived-mode-p 'js-json-mode)
            (js-json-mode)))
        (display-buffer (current-buffer))))))

(defvar coq-eglot-lsp-events-map
  (let ((map (make-sparse-keymap)))
    (define-key map "j" #'coq-eglot-lsp-show-event-json)
    map)
  "Keymap of the events buffers of the Coq servers.
They have no major mode: this is their local map.")

(defun coq-eglot-lsp--events-json-p (server)
  "Non-nil if the events buffer of SERVER has the messages as JSON.
On one line each, with the format full of `eglot-events-buffer-config'.
Older versions of jsonrpc, like the one of Emacs 29, have no format:
they pretty-print the messages as Lisp."
  (and (slot-exists-p server '-events-buffer-config)
       (eq (plist-get (slot-value server '-events-buffer-config) :format)
           'full)))

(defun coq-eglot-lsp--events-keys (server)
  "Use `coq-eglot-lsp-events-map' in the events buffer of SERVER.
If it is a Coq server whose events buffer has the messages as JSON."
  (when (and (cl-typep server 'coq-eglot-lsp-server)
             (coq-eglot-lsp--events-json-p server))
    (with-current-buffer (jsonrpc-events-buffer server)
      (use-local-map coq-eglot-lsp-events-map))))

(add-hook 'eglot-connect-hook #'coq-eglot-lsp--events-keys)

(provide 'coq-eglot-lsp)

;;; coq-eglot-lsp.el ends here
