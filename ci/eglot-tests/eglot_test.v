(*
 * Coq sources for coq-eglot-test-basic.el
 *
 * Tests move the proof position to marker comments and check the
 * goals and response buffers.
 *)

Definition double (n : nat) := n + n. (* marker definition *)

Lemma l : forall n, double n = n + n /\ True. (* marker statement *)
Proof.
  intros n. split. (* marker split *)
  - idtac "hello". (* marker hello *)
    reflexivity.
  - exact I. (* marker subproof *)
Qed.

Lemma bad : 1 = 2.
Proof. (* marker before error *)
  rewrite unknown_lemma. (* marker error *)
Qed.
