From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical.

Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Since we are classical, every ringType is a unitRingType *)
Section unit_ring.
  Variable (R : ringType).

  Definition is_inv (x y : R) := (x * y == 1) && (y * x == 1).
  Definition unitP (x : R) := exists y : R, is_inv x y.
  Definition unitB x : bool := `[< unitP x >].

  Fact unitP_inv_right (x : R) : unitP x -> exists y, x * y == 1.
  Proof. by case=> y /andP [invr _]; exists y. Qed.

  Fact unitP_inv_left (x : R) : unitP x -> exists y, y * x == 1.
  Proof. by case=> y /andP [_ invl]; exists y. Qed.

  Definition invS x :=
    if pselect (unitP x) is left ex_inv
      then xchoose ex_inv
      else x.

  Fact invE x : unitP x -> (x * invS x == 1) && (invS x * x == 1).
  Proof.
    rewrite /invS; case: (pselect (unitP x))=>// H _.
    by exact: (xchooseP H).
  Qed.

  Fact R_mulVr : {in unitB, left_inverse 1 invS *%R}.
  Proof.
    by move=> x; rewrite inE => /invE/andP [_ /eqP].
  Qed.

  Fact R_divrr : {in unitB, right_inverse 1 invS *%R}.
  Proof.
    by move=> x; rewrite inE => /invE/andP [/eqP].
  Qed.

  Fact R_mulVrr_unit (x y : R) : y * x = 1 /\ x * y = 1 -> unitB x.
  Proof.
    case=> invl invr.
    apply/asboolP; exists y; apply/andP.
    by split; apply/eqP.
  Qed.

  Fact R_inv_out : {in [predC unitB], invS =1 id}.
  Proof.
    move=> x; rewrite inE => /asboolPn.
    by rewrite /invS; case: (pselect (unitP x)).
  Qed.

  Definition ring_unitRingMixin := UnitRingMixin R_mulVr R_divrr R_mulVrr_unit R_inv_out.
  Canonical ring_unitRingType := Eval hnf in UnitRingType R ring_unitRingMixin.

End unit_ring.

Coercion ring_unitRingType : ringType >-> unitRingType.
