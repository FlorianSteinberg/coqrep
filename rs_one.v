From mathcomp Require Import all_ssreflect.
Require Import all_core all_rs_base.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TERMINAL.
Inductive one := star.

Definition id_rep S := (fun phi (s: S) => phi star = s).

Lemma id_rep_is_rep:
	forall S: Type, (@id_rep S) \is_representation.
Proof.
by split => [ phi s s' eq eq' | s ]; [rewrite -eq -eq' | exists (fun str => s)].
Qed.

Lemma one_count:
	one \is_countable.
Proof.
exists (fun n => match n with 0 => None | S n => Some star end) => q.
by case q => [str | ]; [exists 1; elim: str | exists 0].
Qed.

Canonical rep_space_one := @make_rep_space
	one
	one
	one
	(@id_rep one)
	star
	star
	one_count
	one_count
	(@id_rep_is_rep one).

Definition one_fun (X: rep_space) (x: X) := star.

Lemma trmnl_uprp_fun (X: rep_space):
	exists! f: X -> one, True.
Proof.
by exists (@one_fun X); split => // f _; apply functional_extensionality => x; elim (f x).
Qed.

Lemma one_fun_rec_fun (X: rep_space):
	(@one_fun X) \is_recursive_function.
Proof. by exists (fun phi q => star). Qed.

Lemma term_uprp_rec_fun (X: rep_space):
	exists! f: X -> one, exists (P: f \is_recursive_function), True.
Proof.
exists (@one_fun X); split; first by exists (@one_fun_rec_fun X).
by move => f _; apply functional_extensionality => x; elim (f x).
Qed.

Lemma one_fun_hcr (X: rep_space):
	(F2MF (@one_fun X)) \has_continuous_realizer.
Proof.
exists (F2MF (fun _ _ => star)) => /=.
split; first by rewrite -frlzr_rlzr.
intros; exists nil; split => //.
by move => Fphi/= -> psi _ Fpsi ->.
Qed.

Definition one_cfun X := exist_c (@one_fun_hcr X) : (X c-> rep_space_one).

Lemma trmnl_uprp_cont (X: rep_space):
	exists! f: X c-> rep_space_one, True.
Proof.
exists (@one_cfun X); split => // f _.
apply /eq_sub; apply functional_extensionality => x.
by case: (projT1 f x).
Qed.

Lemma one_cfun_cmpt_elt (X: rep_space):
	(@one_cfun X) \is_recursive_element.
Proof.
exists (fun Lq => inr star).
rewrite /delta/=/is_fun_name/=.
suffices ->: (eval (U (fun Lq => inr star))) =~= F2MF (fun _ _ => star).
	by rewrite -frlzr_rlzr => phi x phinx.
move => T T0 T1 phi Fphi.
rewrite /F2MF/=.
split; last by by move <-; exists 1.
by move => evl; apply functional_extensionality => q; elim (Fphi q).
Qed.

Lemma trmnl_uprp_rec_elt (X: rep_space):
	exists! f: X c-> rep_space_one, exists (P: f \is_recursive_element), True.
Proof.
exists (@one_cfun X); split; first by exists (@one_cfun_cmpt_elt X).
move => f _; apply /eq_sub /functional_extensionality => x.
by case (projT1 f x).
Qed.
End TERMINAL.