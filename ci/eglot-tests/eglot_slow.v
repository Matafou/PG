(*
 * Coq sources for coq-eglot-test-basic.el, with slow sentences
 *
 * Tests the progress of the proof position during a check, and the
 * interruption of a check.
 *)

Fixpoint fact (n : nat) := match n with 0 => 1 | S k => n * fact k end.

Goal fact 8 = fact 8. Proof. vm_compute. reflexivity. Qed.
Goal fact 8 = fact 8. Proof. vm_compute. reflexivity. Qed.
Goal fact 8 = fact 8. Proof. vm_compute. reflexivity. Qed.
Goal fact 8 = fact 8. Proof. vm_compute. reflexivity. Qed.
Goal fact 8 = fact 8. Proof. vm_compute. reflexivity. Qed.
Goal fact 8 = fact 8. Proof. vm_compute. reflexivity. Qed.
Goal fact 8 = fact 8. Proof. vm_compute. reflexivity. Qed.
Goal fact 8 = fact 8. Proof. vm_compute. reflexivity. Qed.
Definition last_one := 0. (* marker last *)
