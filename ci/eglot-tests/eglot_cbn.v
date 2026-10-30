(*
 * Coq sources for coq-eglot-test-basic.el, with a sentence that the
 * default interruption of coq-lsp cannot interrupt: cbn computes for
 * several seconds without checking for interruptions.
 *)

Goal 3001 + 3001 = 6002. Proof. cbn. (* marker cbn *)
reflexivity. Qed.
