
Require Import Setoid.

Section Group.

Variable A: Type.
Variable e: A.
Variable mul: A -> A -> A.
Variable inv: A -> A.
Notation "x + y" := (mul x y).
Notation "- x" := (inv x ).
Notation "0" := e.

Hypothesis assoc: forall (x y z: A), (x + y) + z = x + (y + z).

Hypothesis left_unit: forall (x: A), 0 + x = x.

Hypothesis left_inv: forall (x: A), (- x) + x = 0.

Theorem right_inv: forall (x: A), x + (- x) = 0.
Proof.
  intros.
  rewrite <- left_unit with (x := x + -x).
  rewrite <- left_inv with (x := - x) at 1.
  rewrite -> assoc.
  rewrite <- assoc with (x := -x).
  rewrite left_inv.
  rewrite left_unit.
  rewrite left_inv.
  reflexivity.
Qed.

Theorem right_unit: forall (x: A), x + 0 = x.
Proof.
  intros.
  rewrite <- left_inv with (x := x).
  rewrite <- assoc.
  rewrite right_inv.
  rewrite left_unit.
  reflexivity.
Qed.

Section Exercise.

Theorem double_inv: forall (x: A), - - x = x.
Proof.
  intros.
  rewrite <- left_unit with (x := - - x).
  rewrite <- right_inv with (x := x).
  rewrite assoc.
  rewrite right_inv.
  rewrite right_unit.
  reflexivity.
Qed.

Theorem funny: forall x y z, (x + y) + (-y + z) = x + z.
Proof.
  intros.
  rewrite<-assoc.
  rewrite assoc with (y := y).
  rewrite right_inv with (x := y).
  rewrite right_unit.
  reflexivity.
Qed.