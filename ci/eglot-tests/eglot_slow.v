(*
 * Coq sources for coq-eglot-test-basic.el, with slow sentences
 *
 * Tests the progress of the proof position during a check, and the
 * interruption of a check.  The computations return small terms:
 * reading back a big unary number overflows the stack with OCaml 4.
 *)

Fixpoint fact (n : nat) := match n with 0 => 1 | S k => n * fact k end.

Goal Nat.eqb (fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Definition last_one := 0. (* marker last *)
