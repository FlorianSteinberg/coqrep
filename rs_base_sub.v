From mathcomp Require Import all_ssreflect.
Require Import all_core rs_base.
Require Import ProofIrrelevance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SUBSPACES.
Fact eq_sub T P (a b : {x : T | P x}) : a = b <-> projT1 a = projT1 b.
Proof.
split=> [->//|]; move: a b => [a Pa] [b Pb] /= eqab.
case: _ / eqab in Pb *; congr (exist _ _ _).
exact: Classical_Prop.proof_irrelevance.
Qed.

Definition range_restriction S T (f: S ->> T) (P: T -> Prop):= 
	(fun s (t: {x | P x}) => f s (projT1 t)).

Lemma rep_sub_space (X: rep_space) (P: X -> Prop):
	(@range_restriction (names X) (space X) (rep X) P) \is_representation.
Proof.
split.
	move => phi [x Px] [y Py] rrdphix rrdphiy.
	by apply eq_sub; apply (rep_sing X phi x y).
move => [s Ps].
have [phi phins]:= rep_sur X s.
by exists phi; rewrite /range_restriction /=.
Qed.

Canonical rep_space_sub_space (X: rep_space) (P: X -> Prop) := @make_rep_space
	({x | P x})
	(questions X)
	(answers X)
	(@range_restriction (names X) (space X) (rep X) P)
	(some_answer X)
  (countable_questions X)
  (countable_answers X)
  (@rep_sub_space X P).
End SUBSPACES.