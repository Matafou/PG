(* An early error followed by work which must not delay its display. *)

Fixpoint slow_fact (n : nat) :=
  match n with 0 => 1 | S k => n * slow_fact k end.

Definition before_error := 0. (* marker before slow error *)
Definition broken := unknown_identifier. (* marker slow error *)

Goal Nat.eqb (slow_fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (slow_fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (slow_fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (slow_fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (slow_fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (slow_fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (slow_fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
Goal Nat.eqb (slow_fact 10) 0 = false. Proof. vm_compute. reflexivity. Qed.
