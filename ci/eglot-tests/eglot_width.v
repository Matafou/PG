(*
 * Coq sources for coq-eglot-test-basic.el: goals longer than the
 * width of their window.
 *)

Lemma long_goal : forall (aaaaaaaa bbbbbbbbb : nat) (Hab : aaaaaaaa = aaaaaaaa)
  (cccccccccc dddddddddd : nat)
  (Hyp_with_long_name : aaaaaaaa + bbbbbbbbb + cccccccccc =
                        dddddddddd + aaaaaaaa + bbbbbbbbb + cccccccccc),
  aaaaaaaa + bbbbbbbbb * cccccccccc + dddddddddd =
  dddddddddd + cccccccccc * bbbbbbbbb + aaaaaaaa /\ aaaaaaaa = aaaaaaaa.
Proof.
  intros. (* marker intros *)
Abort.

(* lines ending with an infix operator, as wide as the printing width *)
Lemma limit : forall (a b c d : nat)
  (H : a + b * c + d = d + c * b + a /\ a = a /\ b + c = c + b),
  a + b * c + d = d + c * b + a /\ a = a /\ b + c = c + b \/ a = b.
Proof.
  intros. (* marker limit *)
Abort.
