From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical.

Open Scope ring_scope.
Open Scope classical_set_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Some basic facts about ideas, not contained within ring_quotient.v *)

Import GRing.Theory.
Section trivial_ideal.
  Variables (R : comUnitRingType).
  Local Notation ideal0 := (@pred1 R 0).

  Fact ideal0_key : pred_key ideal0. Proof. by []. Qed.
  Canonical ideal0_keyed := KeyedPred ideal0_key.

  Fact ideal0_addr_closed : addr_closed ideal0_keyed.
  Proof.
    split=>[|x y]; rewrite !inE // => /eqP -> /eqP ->.
    by rewrite add0r.
  Qed.

  Fact ideal0_oppr_closed : oppr_closed ideal0_keyed.
  Proof.
    move=> x; rewrite !inE => /eqP ->.
    by rewrite oppr0.
  Qed.

  Canonical ideal0_addrPred := AddrPred ideal0_addr_closed.
  Canonical ideal0_zmodPred := ZmodPred ideal0_oppr_closed.

  Lemma ideal0_proper_ideal : proper_ideal ideal0.
  Proof.
    split=>[|a x]; rewrite !inE; first by exact: oner_neq0.
    by move/eqP->; rewrite mulr0.
  Qed.

  Canonical ideal0_idealr := MkIdeal ideal0_zmodPred ideal0_proper_ideal.
End trivial_ideal.
Notation ideal0 := (pred1 0).

Section intersection.
Variables (R : ringType) (I J : {pred R})
          (idealrI : idealr I) (idealrJ : idealr J).

Fact is_true_pred_of_set {T} (A : set T) (x : T) : is_true ((pred_of_set A) x) = A x.
Proof. exact: asboolE. Qed.

Fact in_expand {T} (A : {pred T}) (x : T) : x \in A = A x.
Proof. by []. Qed.

Lemma setI_proper_ideal : proper_ideal ((I `&` J) : {pred R}).
Proof.
  split.
  - have not_1_in : ~ (1 \in I).
    - by apply: negP; case: idealrI => [_ []].
    by apply/negP=>/=; rewrite in_setE /=; case.
  move=> a x; rewrite !inE; case=>/=.
  rewrite -in_expand => xI; rewrite -in_expand => xJ.
  split; rewrite -in_expand.
  - by case: idealrI => _ [_ ->].
  by case: idealrJ => _ [_ ->].
Qed.

Fact setI_key : pred_key (I `&` J). Proof. by []. Qed.
Canonical setI_keyed := KeyedPred setI_key.

Fact setI_addr_closed : addr_closed setI_keyed.
Proof.
  split.
  - rewrite in_setE /=.
    move: idealrI => [[[_ [zeroI _]] _] _].
    by move: idealrJ => [[[_ [zeroJ _]] _] _].
  move=> x y; rewrite !inE; case=>xI xJ[yI yJ] /=.
  split.
    by move: idealrI => [[[_ [_ +]] _] _]; apply.
  by move: idealrJ => [[[_ [_ +]] _] _]; apply.
Qed.

Fact setI_oppr_closed : oppr_closed setI_keyed.
Proof.
  move=> x; rewrite in_setE /=; case=> xI xJ.
  rewrite !inE /=; split.
  - by move: idealrI => [[[_ [_ _]] +] _]; apply.
  by move: idealrJ => [[[_ [_ _]] +] _]; apply.
Qed.

Canonical setI_addrPred := AddrPred setI_addr_closed.
Canonical setI_zmodPred := ZmodPred setI_oppr_closed.

Canonical setI_idealr := MkIdeal setI_zmodPred setI_proper_ideal.
End intersection.

(* The radical of an ideal is an ideal *)
Section radical.
Variables (R : comRingType) (I : {pred R}) (idealI : idealr I).

Definition radical x := `[< exists n : nat, x ^+ n \in I >].

Lemma radical_proper_ideal : proper_ideal radical.
Proof.
  split.
  - move: idealI => [_ [one_notinI _]].
    rewrite unfold_in; apply/negP.
    rewrite in_setE -forallNE => n.
    by rewrite expr1n; apply/negP.
  move=> a x; rewrite !inE; case=>n x_pow_n.
  exists n; rewrite exprMn_comm; last by exact: mulrC.
  by move: idealI => [_ [_ +]]; apply.
Qed.

Fact radical_key : pred_key radical. Proof. by []. Qed.
Canonical radical_keyed := KeyedPred radical_key.

Lemma mulrn_closed x n : x \in I -> x *+ n \in I.
Proof.
  move=> xI; elim: n => [| n IH].
  - by rewrite mulr0n; move: idealI => [[[_ []]]].
  by rewrite mulrSr; move: idealI => [[[_ [_ +]] _] _]; apply.
Qed.

Lemma radical_addr_closed : addr_closed radical.
Proof.
  have mul_closed: forall a x, x \in I -> a * x \in I.
  - by move: idealI => [_ [_ +]]; apply.
  split.
  - apply/asboolP; exists 1%N; rewrite expr0n /=.
    by move: idealI => [[[_ []]]].
  move=> x y; rewrite !inE; case=>n x_pow_n [m y_pow_m].
  exists (m + n)%N; rewrite exprDn.
  elim/big_ind: _=>/=.
  - by move: idealI => [[[_ []]]].
  - by move=>p q Hp Hq; move: idealI => [[[_ [_] +] _ ] _]; apply.
  case=>i i_bound _ /=.
  case: (ltnP i m) => i_cond.
  - rewrite mulrC; apply/mulrn_closed/mul_closed.
    rewrite addnC -addnBA; last by apply: ltnW.
    by rewrite exprD mulrC; apply: mul_closed.
  apply/mulrn_closed/mul_closed.
  by rewrite -(subnKC i_cond) exprD mulrC; apply: mul_closed.
Qed.

Lemma radical_oppr_closed : oppr_closed radical.
Proof.
  move=> x; rewrite !inE; case=>n xpow_I.
  exists n; rewrite exprNn.
  by move: idealI => [_ [_ +]]; apply.
Qed.

End radical.
