From mathcomp Require Import all_ssreflect.
Require Import all_core all_rs_base.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BASIC_REP_SPACES.
Inductive one := star.

Definition id_rep S := (fun phi (s: S) => phi star = s).

Lemma id_rep_is_rep:
	forall S: Type, (@id_rep S) \is_representation.
Proof.
by split => [ phi s s' eq eq' | s ]; [rewrite -eq -eq' | exists (fun str => s)].
Qed.

Lemma one_count:
	one \is_countable.
Proof. by exists (fun n => star); move => star; exists 0%nat; elim star. Qed.

Canonical rep_space_one := @make_rep_space
	one
	one
	one
	(@id_rep one)
	star
	one_count
	one_count
	(@id_rep_is_rep one).

Lemma nat_count:
	nat \is_countable.
Proof. exists (fun n:nat => n); move => n; by exists n. Qed.

Canonical rep_space_nat := @make_rep_space
	nat
	one
	nat
	(@id_rep nat)
	1%nat
	one_count
	nat_count
	(id_rep_is_rep nat).
(* This Definition is equivalent to the notion Arno introduces in "https://arxiv.org/pdf/1204.3763.pdf".
One of the drawbacks fo the version here is that it does not have a computable version.*)
Definition is_dscrt X :=
	forall Y (f: (space X) -> (space Y)), (F2MF f) \has_continuous_realizer.
Notation "X '\is_discrete'" := (is_dscrt X) (at level 2).

Lemma dscrt_rel X:
	X \is_discrete -> (forall Y (f: (space X) ->> (space Y)), f \has_continuous_realizer).
Proof.
move => dscrt Y f_R.
case: (classic (exists y:Y, true)) => [[y _] | ]; last first.
	move => next;	exists (F2MF (fun _ => (fun _:questions Y => some_answer Y))).
	split; first by move => phi [y _]; exfalso; apply next; exists y.
	by move => phi val phifd; exists nil => Fphi /= <- psi _ Fpsi <-.
have [f icf]:= exists_choice f_R y.
have [F [Frf Fcont]]:= (dscrt Y f).
exists F; split => //.
apply/ tight_trans; first by apply Frf.
by apply tight_comp_l; apply icf_F2MF_tight.
Qed.

Lemma one_dscrt: rep_space_one \is_discrete.
Proof.
move => X f.
have [phi phinfs]:= rep_sur X (f star).
exists (F2MF (fun _ => phi)).
split; last by exists nil => Fphi <- psi _ Fpsi <-.
apply frlzr_rlzr => psi str psinstr.
by elim str.
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


Lemma nat_dscrt: rep_space_nat \is_discrete.
Proof.
move => X f.
pose R phi psi:= forall n, phi \is_name_of n -> psi \is_name_of (f n).
have [F icf]:= exists_choice R (fun _ => some_answer X).
exists (F2MF F).
split.
	apply frlzr_rlzr => phi n phinn.
	have [ psi psinfn] := rep_sur X (f n).
	suffices Rphipsi: R phi psi by apply/ (icf phi psi Rphipsi).
	move => n' phinn'.
	by have <-: n = n' by rewrite -(rep_sing rep_space_nat phi n n').
move => n q _.
exists (cons star nil).
move => Fphi /= <- psi coin Fpsi <-.
suffices <-: n = psi by trivial.
apply functional_extensionality => str.
by elim str; rewrite coin.1.
Qed.*)
End BASIC_REP_SPACES.