From mathcomp Require Import all_ssreflect.
Require Import all_rs_base rs_one.
Require Import Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SIERPINSKISPACE.
Inductive Sirp := top | bot.

Definition rep_S phi s :=
	(exists n:nat, phi n = Some star) <-> s = top.

Lemma rep_S_is_rep:
 rep_S \is_representation.
Proof.
split => [ phi s s' [imp imp'] [pmi pmi'] | s].
	case (classic (exists n, phi n = Some star)) => ex; first by rewrite (imp ex) (pmi ex).
	case E: s; first by exfalso; apply ex; apply (imp' E).
	apply NNPP => neq.
	have eq: s' = top by case Q: s' => //; exfalso; apply neq.
	by apply ex; apply pmi'.
case s; last by exists (fun _ => None); split => // [[n ev]].
by exists (fun _ => some star); split => // _; by exists 0.
Qed.

Canonical rep_space_S := @make_rep_space
	(Sirp)
	(nat)
	(option one)
	(rep_S)
	(0%nat)
	(None)
  (nat_count)
  (option_count one_count)
  (rep_S_is_rep).
End SIERPINSKISPACE.

Section space_T.
Inductive T := TL | TR | Tbot.

Definition rep_T phi (t: T) :=
	match t with
		| TL => exists (n: nat), phi n = TL /\ forall m, m < n -> phi m = Tbot
		| TR => exists (n: nat), phi n = TR /\ forall m, m < n -> phi m = Tbot
		| Tbot => forall n, phi n = Tbot
	end.

Lemma rep_T_is_rep:
	rep_T \is_representation.
Proof.
split.
	move => phi t t'.
	case: t; case t' => //=; try move ->; try (move => [n [eq prp]] prp'; by rewrite prp' in eq);
		try (move => prp; case => n []; by rewrite prp).
	- move => [n [eq prp]] [m []].
		case/orP: (leq_total m n) => ineq;
			rewrite leq_eqVlt in ineq.
			case/orP: ineq => [/eqP -> | ineq]; first by rewrite eq.
			by rewrite prp.
		case/orP: ineq => [/eqP <- | ineq]; first by rewrite eq.
		move => eq' prp'; by rewrite prp' in eq.
	move => [n [eq prp]] [m []].
	case/orP: (leq_total m n) => ineq;
		rewrite leq_eqVlt in ineq.
		case/orP: ineq => [/eqP -> | ineq]; first by rewrite eq.
		by rewrite prp.
	case/orP: ineq => [/eqP <- | ineq]; first by rewrite eq.
	move => eq' prp'; by rewrite prp' in eq.
move => t.
case: t; first by exists (fun _ => TL); exists 0.
	by exists (fun _ => TR); exists 0.
by exists (fun _ => Tbot).
Qed.

Lemma T_count:
	T \is_countable.
Proof.
exists (fun n => match n with
	| 0 => Some TR
	| S 0 => Some TL
	| S (S 0) => Some Tbot
	| S (S (S n)) => None
end).
move => ot.
case: ot => [t | ]; last by exists 3.
by case: t; [exists 1 | exists 0 | exists 2].
Qed.

Canonical rep_space_T := @make_rep_space
	T
	nat
	T
	rep_T
	0
	(Tbot)
	nat_count
	(T_count)
	rep_T_is_rep.

End space_T.
