From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical unit ideal.

Open Scope ring_scope.
Open Scope classical_set_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section nilpotent.
Import GRing.

Variable (R : comUnitRingType).

Definition nilpotentP (x : R) := exists n, x ^+ n == 0.
Definition nilpotent (x : R) := `[< nilpotentP x >].

Fact introNN (P : Prop) : P -> ~ ~ P.
Proof. by move=> ?. Qed.

(* Next: the set of nilpotents (i.e., nilradical) of R forms an ideal *)
Lemma nilpotent_proper_ideal : proper_ideal nilpotent.
Proof.
  split.
  - rewrite unfold_in; apply/asboolPn.
    by rewrite -forallNE => n; apply/negP; rewrite expr1n oner_neq0.
  move=> x y; rewrite !inE; case=>n Hn.
  exists n; rewrite exprMn_comm.
  - by move/eqP: Hn=>->; rewrite mulr0.
  by rewrite /comm mulrC.
Qed.

Fact nilpotent_key : pred_key nilpotent. Proof. by []. Qed.
Canonical nilpotent_keyed := KeyedPred nilpotent_key.

Fact index_size (i m n : nat) :
       ((m + n - i) >= n)%N || (i >= m)%N.
Proof.
  case: (leqP m i)=> Hm; first by rewrite orbT.
  by rewrite orbF addnC -addnBA; [exact: leq_addr | apply: ltnW].
Qed.

Fact largepow_0 (x : R) (n m : nat) : x ^+ n = 0 -> (n <= m)%N -> x ^+ m = 0.
Proof.
  move=> nilp n_le_m.
  by rewrite -(subnKC n_le_m) exprD nilp mul0r.
Qed.

Lemma nilpotent_addr_closed : addr_closed nilpotent_keyed.
Proof.
  split; first by rewrite inE; exists 1%N; rewrite expr0n.
  move=> x y; rewrite !inE; case=>n /eqP nilp_n [m /eqP nilp_m].
  (* Proof by binomial theorem: at least one binomial exponent is large enough *)
  (* We take the exponent to be m + n but this is certainly not minimal *)
  exists (m + n)%N; rewrite exprDn.
  have tm_zero i : x ^+ (m + n - i) * y ^+ i *+ 'C(m + n, i) = 0.
  - case/orP: (index_size i m n)=> [Hm | Hn].
    - by rewrite (largepow_0 nilp_n Hm) mul0r mul0rn.
    by rewrite (largepow_0 nilp_m Hn) mulr0 mul0rn.
  rewrite (eq_bigr (fun=> 0)); first by rewrite sumr_const mul0rn.
  by move=>i _; rewrite tm_zero.
Qed.

Fact nilpotent_oppr_closed : oppr_closed nilpotent_keyed.
Proof.
  move=> x; rewrite !inE; case=> n /eqP Hn.
  by exists n; rewrite exprNn Hn mulr0.
Qed.

Canonical nilpotent_addrPred := AddrPred nilpotent_addr_closed.
Canonical nilpotent_zmodPred := ZmodPred nilpotent_oppr_closed.

Canonical nilpotent_idealr := MkIdeal nilpotent_zmodPred nilpotent_proper_ideal.
End nilpotent.

(* The nilradical of a commutative ring *)
Notation Nil R := (nilpotent_idealr R).
