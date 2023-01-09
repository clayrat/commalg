From mathcomp Require Import all_ssreflect.
From mathcomp.classical Require Export classical_sets boolp.
Require Export FunctionalExtensionality ProofIrrelevanceFacts ProofIrrelevance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition pred_of_set {T} (p : set T) : {pred T} := asbool \o p.
Coercion pred_of_set : set >-> pred_sort.
