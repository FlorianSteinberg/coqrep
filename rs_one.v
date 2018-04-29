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

Lemma one_fun_term (X: rep_space):
	forall f: X -> one, f = @one_fun X.
Proof.
by move => f; apply functional_extensionality => x; elim (f x).
Qed.

Lemma one_fun_prec_fun (X: rep_space):
	(@one_fun X) \is_recursive_function.
Proof.
by exists (fun phi q => star).
Qed.

Lemma one_fun_hcr (X: rep_space):
	(F2MF (@one_fun X)) \has_continuous_realizer.
Proof.
exists (F2MF (fun _ _ => star)) => /=.
split; first by rewrite -frlzr_rlzr.
intros; exists nil; split => //.
by move => Fphi/= -> psi _ Fpsi ->.
Qed.

Definition one_cfun X := exist_fun (@one_fun_hcr X) : (X c-> rep_space_one).

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

(*
Lemma iso_one (X :rep_space) (somex: X):
	(rep_space_one c-> X) ~=~ X.
Proof.
pose f (xf: rep_space_one c-> X) := (projT1 xf) star.
pose L := fix L n := match n with
	| 0 => nil
	| S n => cons (star, star) (L n)
end.
pose F n (phi: names (rep_space_one c-> X)) q := match (phi ((L n), q)) with
	| inl q => None
	| inr a => Some a
end.
have: (eval F) \is_realizer_of f.
move => phi [x [[xf [phinxf fxfx]]] prop].
have [xF icf] := exists_choice (projT1 xf) somex.
split.
	exists x.
	split.
		pose psi (str: one) := star.
		have []:= (phinxf psi).
		(exists (xF star)).
		split; first by exists star; split => //; apply/ icf; apply fxfx.
		move => s psins; exists x; elim s; apply fxfx.
	move => [x' [[phi' [evl phi'nx']]prop']] stuff.
	exists (phi').
	split.
		move => q.
		have [c val]:= evl q.
		exists c.
		apply/ icf'.
pose pT1g (x: X) := F2MF (fun _: rep_space_one => x).
have crlzr: forall x:X, has_cont_rlzr (pT1g x) by move => x; apply one_dscrt.
have sing: forall (x: X), (pT1g x) \is_single_valued by move => x; apply F2MF_sing.
have tot: forall (x: X), (pT1g x) \is_total by move => x; apply F2MF_tot.
pose g (x:X) := exist_fun (conj (conj (sing x) (tot x)) (crlzr x)).
exists f'.
exists (F2MF g).
split.
	admit.
split.
	apply prim_rec_comp.
	pose psi:= fun (phi: names X) => (fun p: seq (one * one) * (questions X) => inr (phi p.2): sum one _).
	exists (psi).
	apply frlzr_rlzr.
	move => phi x phinx/=.
	rewrite /is_fun_name/is_rlzr/=.
	move => p pfd.
	split.
		exists x.
		split.
			exists phi.
			split => //.
			by exists 0.
		move => phi' ev.
		exists x.
		suffices: phi = phi' by move <-.
		apply functional_extensionality => q.
		apply Some_inj.
		have [/=n <-]:= (ev q).
		replace (Some (phi q)) with (U (psi phi) n p q) => //.
		have U0: U (psi phi) 0 p q = Some (phi q) by trivial.
		apply/ U_mon; last by apply U0.
		by replace (pickle 0) with 0 by trivial; lia.
	move => x' [[phi' [ev phi'nx']] prop].
	split.
		exists star.
		split; first by rewrite /id_rep; case (p star).
		suffices eq: phi = phi'	by apply ((\rep_valid X).1 phi x x') => //; rewrite eq.
		apply functional_extensionality => q.
		apply Some_inj.
		have [/=n <-]:= (ev q).
		replace (Some (phi q)) with (U (psi phi) n p q) => //.
		have U0: U (psi phi) 0 p q = Some (phi q) by trivial.
		apply/ U_mon; last by apply U0.
		by replace (pickle 0) with 0 by trivial; lia.
	by move => str eq; exists x.
split.
	rewrite F2MF_comp => x y.
	by rewrite /f /g /pT1g/F2MF/=.
rewrite comp_tot.
split.
	move => [x [b c]].
	rewrite /f in b.
	rewrite -c /g/pT1g/F2MF/=.
	apply eq_sub.
	apply functional_extensionality => str/=.
	elim str.
	apply functional_extensionality => x'/=.
	rewrite /= in b.
Admitted.
*)
End TERMINAL.