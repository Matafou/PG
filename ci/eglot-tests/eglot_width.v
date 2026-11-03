(*
 * Coq sources for coq-eglot-test-basic.el: goals longer than the
 * width of their window.
 *)

Lemma long_goal : forall (aaaaaaaa bbbbbbbbb cccccccccc dddddddddd : nat)
  (Hyp_with_long_name : aaaaaaaa + bbbbbbbbb + cccccccccc =
                        dddddddddd + aaaaaaaa + bbbbbbbbb + cccccccccc),
  aaaaaaaa + bbbbbbbbb * cccccccccc + dddddddddd =
  dddddddddd + cccccccccc * bbbbbbbbb + aaaaaaaa /\ aaaaaaaa = aaaaaaaa.
Proof.
  intros. (* marker intros *)
Abort.
