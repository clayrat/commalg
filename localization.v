From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical unit ideal maximal local.

Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section multiplicative_set.
Definition mul_closed (R : comRingType) (S : {pred R}) :=
  forall (x y : R), x \in S -> y \in S -> x * y \in S.
End multiplicative_set.

Section localization.
Import GRing.
Open Scope quotient_scope.

Variables (R : comRingType) (S : {pred R}) (closedS : mul_closed S).

Structure tS := MkMulType { elem : R ; _ : elem \in S }.

Definition tS_eqMixin := @gen_eqMixin tS.
Canonical tS_eqType := EqType tS tS_eqMixin.

Definition tS_choiceMixin := @gen_choiceMixin tS.
Canonical tS_choiceType := ChoiceType tS tS_choiceMixin.

Coercion elem : tS >-> GRing.ComRing.sort.

Definition loc_equiv (p p' : R * tS) :=
  match p, p' with
  | (r1, s1), (r2, s2) => `[< exists t, t * (r1 * (s2 : R) - r2 * (s1 : R)) = 0 >]
  end.

Lemma ref_loc_equiv : reflexive loc_equiv.
Proof.
  case=>r s; apply/asboolP.
  by exists 1; rewrite subrr mul1r.
Qed.

Lemma sym_loc_equiv : symmetric loc_equiv.
Proof.
  by move=> [r1 s1] [r2 s2] /=; apply: asbool_equiv_eq; split; case=> t Ht;
  exists t; apply: oppr_inj; rewrite oppr0 -mulNr -mulrN opprD addrC mulNr opprK.
Qed.

Lemma trans_loc_equiv : transitive loc_equiv.
Proof.
  move=> [r2 s2] [r1 s1] [r3 s3] /asboolP [t1 H1] /asboolP [t2 H2].
  apply/asboolP; exists ((s2 : R) * t1 * t2).
  rewrite mulrBr -[X in X - _]subr0.
  rewrite -(subrr (t1 * t2 * (s1 : R) * (s3 : R) * r2)).
  rewrite [in RHS]subrr opprD opprK addrA.
  rewrite -addrA -[X in _ + (_ - X)]mulrA [X in _ + (_ - X * _)]mulrC.
  rewrite -[X in _ + (_ - X)]mulrA -![X in _ + (X - _)]mulrA.
  rewrite -mulrBr [X in _ * (_ - X)]mulrCA -mulrBr.
  rewrite [X in _ * (_ - X)]mulrA [X in _ * (_ - X)]mulrC -mulrBr.
  rewrite [X in _ + _ * X]mulrCA [(s3 : R) * r2]mulrC [(s2 : R) * r3]mulrC.
  rewrite H2 !mulr0 addr0 -mulrA -mulrA mulrCA.
  rewrite -![X in _ - X]mulrA -mulrBr mulrCA -mulrBr [X in _ - X]mulrCA.
  rewrite [r1 * (s3 : R)]mulrC [X in X - _]mulrCA -mulrBr.
  rewrite mulrCA [X in _ * X]mulrCA [(s2 : R) * r1]mulrC [(s1 : R) * r2]mulrC.
  by rewrite H1 !mulr0.
Qed.

Canonical loc_equiv_equiv := EquivRelPack (EquivClass ref_loc_equiv sym_loc_equiv trans_loc_equiv).
Canonical loc_equiv_encModRel := @defaultEncModRel (prod_choiceType R tS_choiceType) loc_equiv.

Definition localize := {eq_quot loc_equiv}.

(* + and * defined on the localized set *)
Definition loc_add (l1 l2 : (R * tS)) : (R * tS) :=
  match l1, l2 with
  | (r1, MkMulType s1 H1), (r2, MkMulType s2 H2) =>
    (r1 * s2 + s2 * r1, @MkMulType (s1 * s2) (closedS H1 H2))
  end.

Definition loc_mul (l1 l2 : (R * tS)) : (R * tS) :=
  match l1, l2 with
  | (r1, MkMulType s1 H1), (r2, MkMulType s2 H2) =>
    (r1 * r2, @MkMulType (s1 * s2) (closedS H1 H2))
  end.

Definition add_localized := lift_op2 localize loc_add.
Definition mul_localized := lift_op2 localize loc_mul.
End localization.
