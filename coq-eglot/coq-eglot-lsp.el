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
   :pp_type 0))

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

(defun coq-eglot-lsp--contact (&optional _interactive)
  "Eglot contact for Coq: our server class and its command line."
  (let ((command (coq-eglot-lsp-server-command)))
    (cons 'coq-eglot-lsp-server
          (append command
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
and is shared by the files of this directory and its subdirectories."
  (when-let* ((root (locate-dominating-file
                     dir (lambda (d) (funcall coq-project-filename d)))))
    (cons 'transient root)))

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

(defun coq-eglot-lsp-ensure-server ()
  "Return the Coq server of the current buffer, starting it if needed.
Unlike `eglot-ensure', start it now, not after the current command."
  (or (coq-eglot-lsp-current-server)
      (progn
        (apply #'eglot (eglot--guess-contact))
        (coq-eglot-lsp-current-server))))

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

(defun coq-eglot-lsp--server-for-request ()
  "Return the server of the current buffer, after sending pending changes."
  (let ((server (or (coq-eglot-lsp-ensure-server)
                    (user-error "No Coq language server for this buffer"))))
    (eglot--signal-textDocument/didChange)
    server))

(defun coq-eglot-lsp-request (method params)
  "Send request METHOD with PARAMS to the server of the current buffer.
Pending changes of the buffer are sent first.  Return the answer, or
signal an error.  No timeout: checking may be long, \\[keyboard-quit]
stops waiting."
  (jsonrpc-request (coq-eglot-lsp--server-for-request) method params
                   :timeout nil))

(defun coq-eglot-lsp-async-request (method params on-success on-error)
  "Send request METHOD with PARAMS to the server of the current buffer.
Pending changes of the buffer are sent first.  Return immediately the id
of the request, for `coq-eglot-lsp-cancel'.  ON-SUCCESS is called with
the answer, ON-ERROR with the error object, in the current buffer if
still live.  They are called from a timer, not from the process filter,
so that they can send synchronous requests."
  (let ((server (coq-eglot-lsp--server-for-request))
        (buffer (current-buffer)))
    (cl-flet ((later (fn)
                (lambda (arg)
                  (run-at-time 0 nil
                               (lambda ()
                                 (when (buffer-live-p buffer)
                                   (with-current-buffer buffer
                                     (funcall fn arg))))))))
      ;; Internal, but `jsonrpc-async-request' does not return the id
      (car (jsonrpc--async-request-1 server method params
                                     :success-fn (later on-success)
                                     :error-fn (later on-error)
                                     :timeout nil)))))

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

(defun coq-eglot-lsp--goals-params (pos)
  "Parameters of a goals request at buffer position POS."
  (list :textDocument (eglot--VersionedTextDocumentIdentifier)
        :position (coq-eglot-lsp-position pos)
        :pp_format "Str"))

(defun coq-eglot-lsp-goals (pos)
  "Ask the goals after the sentence at buffer position POS.
Return the answer of the server as a plist with keys :range, :goals,
:messages and :error."
  (coq-eglot-lsp-request :proof/goals (coq-eglot-lsp--goals-params pos)))

(defun coq-eglot-lsp-goals-async (pos on-success on-error)
  "Ask asynchronously the goals after the sentence at POS.
See `coq-eglot-lsp-goals' and `coq-eglot-lsp-async-request'."
  (coq-eglot-lsp-async-request :proof/goals (coq-eglot-lsp--goals-params pos)
                               on-success on-error))

(defun coq-eglot-lsp-ping (on-answer)
  "Send a cheap request, call ON-ANSWER when the server answers it.
Its answer tells that the server is ready again after an interruption."
  (coq-eglot-lsp-async-request :proof/goals
                               (coq-eglot-lsp--goals-params (point-min))
                               on-answer on-answer))

(defun coq-eglot-lsp-check-async (pos on-success on-error)
  "Ask asynchronously the server to check up to the sentence at POS.
No goals are computed.  See `coq-eglot-lsp-async-request'."
  (coq-eglot-lsp-async-request
   :petanque/get_state_at_pos
   (list :uri (plist-get (eglot--TextDocumentIdentifier) :uri)
         :position (coq-eglot-lsp-position pos)
         :opts (list :memo t :hash :json-false))
   on-success on-error))

(defun coq-eglot-lsp-query-async (pos command on-success on-error)
  "Run Coq COMMAND asynchronously in the state at POS.
The state is the one after the sentences ending before POS.  The
document does not change.  ON-SUCCESS is called with the messages of
COMMAND, a list of strings.  See `coq-eglot-lsp-async-request'."
  (coq-eglot-lsp-async-request
   :petanque/run_at_point
   (list :textDocument (eglot--VersionedTextDocumentIdentifier)
         :position (coq-eglot-lsp-position pos)
         :command command)
   (lambda (answer)
     ;; each feedback is [LEVEL TEXT]
     (funcall on-success
              (mapcar (lambda (feedback) (aref feedback 1))
                      (plist-get answer :feedback))))
   on-error))

;;; Notifications

(defun coq-eglot-lsp--uri-to-path (uri)
  "File name of URI."
  (if (fboundp 'eglot-uri-to-path)
      (eglot-uri-to-path uri)
    (with-no-warnings (eglot--uri-to-path uri))))

(defun coq-eglot-lsp--buffer (uri)
  "The live buffer visiting URI, or nil."
  (find-buffer-visiting (coq-eglot-lsp--uri-to-path uri)))

(defconst coq-eglot-lsp-minimal-version "0.2.3"
  "Oldest version of coq-lsp supported.
It added the range of the sentence to the answer of proof/goals, and
the request petanque/get_state_at_pos.")

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
It is called with the end of the last checked sentence.")

(cl-defmethod eglot-handle-notification
  ((_server coq-eglot-lsp-server) (_method (eql $/coq/fileProgress))
   &key textDocument processing &allow-other-keys)
  "Call `coq-eglot-lsp-progress-function' of the buffer being checked.
PROCESSING is the part of the document still to check, nothing when
done."
  (let ((buffer (coq-eglot-lsp--buffer (plist-get textDocument :uri))))
    (when (and buffer (> (length processing) 0))
      (with-current-buffer buffer
        ;; ignore notifications about an older version of the buffer
        (when (and coq-eglot-lsp-progress-function
                   (eql (plist-get textDocument :version)
                        eglot--versioned-identifier))
          (funcall coq-eglot-lsp-progress-function
                   (car (coq-eglot-lsp-range
                         (plist-get (aref processing 0) :range)))))))))

;;; Diagnostics

(defvar-local coq-eglot-lsp--diagnostics nil
  "Last diagnostics published by the server for the current buffer.")

;; Eglot still gives the diagnostics to flymake
(cl-defmethod eglot-handle-notification :after
  ((_server coq-eglot-lsp-server)
   (_method (eql textDocument/publishDiagnostics))
   &key uri diagnostics &allow-other-keys)
  (let ((buffer (coq-eglot-lsp--buffer uri)))
    (when buffer
      (with-current-buffer buffer
        (setq coq-eglot-lsp--diagnostics diagnostics)))))

(defun coq-eglot-lsp-error-range (start end)
  "Buffer range (BEG . END) of the first error located between START and END.
Look for it in the last published diagnostics, return nil if none."
  (let (first)
    (cl-loop for diag across coq-eglot-lsp--diagnostics
             for range = (coq-eglot-lsp-range (plist-get diag :range))
             when (and (eql (plist-get diag :severity) 1)
                       (<= start (car range)) (< (car range) end)
                       (or (null first) (< (car range) (car first))))
             do (setq first range))
    first))

(provide 'coq-eglot-lsp)

;;; coq-eglot-lsp.el ends here
