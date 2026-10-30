(*
 * Coq sources for coq-eglot-test-basic.el, a second script buffer
 *
 * Tests the scripting of several buffers at once.
 *)

Definition other := 0. (* marker other *)

Goal other = 0.
Proof. (* marker proof *)
  reflexivity.
Qed.
