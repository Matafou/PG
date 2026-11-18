(*
 * Coq sources for the tests of the Eglot backend, a second script buffer
 *
 * Tests the scripting of several buffers at once.
 *)

Definition other := 0. (* marker other *)

Goal other = 0.
Proof. (* marker proof *)
  reflexivity.
Qed.
