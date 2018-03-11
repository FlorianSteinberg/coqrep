(* This file provides an alternative formulation of represented spaces that saves
the input and output types of the names *)
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions continuity representations representation_facts baire_space universal_machine.
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

Definition rep_usig_prod (X: rep_space) phi (xn: nat -> X):=
	forall n, (fun p => (phi (n,p))) \is_name_of (xn n).

Lemma rep_usig_prod_is_rep (X: rep_space):
	(@rep_usig_prod X) \is_representation.
Proof.
split => [ phi xn yn phinxn phinyn | xn ].
	apply functional_extensionality => n.
	by apply/ (\rep_valid X).1; [apply phinxn | apply phinyn ].
pose R n phi:= phi \is_name_of (xn n).
have Rtot: R \is_total.
	by move => n; have [phi phinx]:= ((\rep_valid X).2 (xn n)); exists phi.
by have [phi phinxn]:= choice R Rtot; exists (fun p => phi p.1 p.2).
Qed.

Canonical rep_space_usig_prod (X: rep_space) := @make_rep_space
	(nat -> space X)
	(nat * questions X)
	(answers X)
	(@rep_usig_prod X)
	(some_answer X)
  (prod_count nat_count (countable_questions X))
  (countable_answers X)
  (@rep_usig_prod_is_rep X).

Lemma one_to_nat_dscrt Q A (F: (one -> nat) -> (Q -> A)):
	(F2MF F) \is_continuous.
Proof.
move => phi q' phifd.
set L := (star :: nil).
exists L.
move => Fphi FphiFphi /= psi coin.
have eq: phi = psi.
	apply functional_extensionality => str.
	apply: ((coin_lstn phi psi L).1 coin).
	by elim str; left.
rewrite -eq.
move => Fpsi FpsiFpsi.
by rewrite -FphiFphi -FpsiFpsi.
Qed.

Definition is_dscrt X :=
	forall Y (f: (space X) ->> (space Y)), f \has_continuous_realizer.
Notation "X '\is_discrete'" := (is_dscrt X) (at level 2).

Lemma one_dscrt: rep_space_one \is_discrete.
Proof.
move => X f.
pose G phi Fphi:= exists x, phi \is_name_of star -> f star x /\ Fphi \is_name_of x.
have [F Fprop]:= exists_choice G (fun _ => some_answer X).
exists (F2MF F).
split.
	move => phi [x [[str [phinstr fstrx]] _]].
	move: phinstr fstrx; elim str => phinstr fstrx.
	have [psi psinx]:= \rep_sur X x.
	have Gphipsi: G phi psi by exists x.
	have [x' prop]:= Fprop phi psi Gphipsi.
	have [fstrx' Fphinx'] := prop phinstr.
	split.
		exists x'.
		split; first by exists (F phi).
		by move => phi' <-; exists x'.
	move => x'' [[psi' [eq psi'nx'']] prop'].
	split.
		exists star.
		split => //.
		rewrite (\rep_sing X (F phi) x'' x') => //.
		by rewrite eq.
	move => s _.
	by exists x; elim s.
exists nil => Fphi /= <- psi _ Fpsi <-.
suffices: phi = psi by move => <-.
apply functional_extensionality => str.
by elim (phi str); elim (psi str).
Qed.

Lemma nat_dscrt: rep_space_nat \is_discrete.
Proof.
Admitted.

Inductive Sirp := top | bot.

Definition rep_S phi s :=
	(exists n:nat, phi n = Some star) <-> s = top.

Lemma rep_S_is_rep:
 rep_S \is_representation.
Proof.
split => [ phi s s' [imp imp'] [pmi pmi'] | s].
	case (classic (exists n, phi n = Some star)) => ex.
		by rewrite (imp ex) (pmi ex).
	case E: s; first by exfalso; apply ex; apply (imp' E).
	apply NNPP => neq.
	have eq: s' = top by case Q: s' => //; exfalso; apply neq.
	by apply ex; apply pmi'.
case s; last by exists (fun _ => None); split => // [[n ev]].
by exists (fun _ => some star); split => // _; by exists 0.
Qed.

Lemma option_one_count:
	(option one) \is_countable.
Proof.
by exists (fix c n := match n with
	| 0 => Some star
	| S n' => None
end) => s; case: s; [exists 0; elim: a| exists 1].
Qed.

Canonical rep_space_S := @make_rep_space
	(Sirp)
	(nat)
	(option one)
	(rep_S)
	(None)
  (nat_count)
  (option_one_count)
  (rep_S_is_rep).
End BASIC_REP_SPACES.
(*
Lemma iso_one (X :rep_space) (somex: X):
	wisomorphic (rep_space_cont_fun rep_space_one X) X.
Proof.
pose f' (xf: rep_space_cont_fun rep_space_one X) := (projT1 xf) star.
have [f fprop] := exists_choice f' somex.
exists (F2MF f).
pose pT1g (x: X) := F2MF (fun _: rep_space_one => x).
have crlzr: forall x:X, has_cont_rlzr (pT1g x).
	move => x.
	have [phi phinx]:= (\rep_valid X).2 x.
	exists (F2MF (fun _ => phi)).
	split; first by rewrite -frlzr_rlzr.
	exists (star::nil) => /=; rewrite /F2MF.
	by move => Fphi FphiFphi /= psi' coin Fpsi eq; rewrite -FphiFphi -eq.
have sing: forall (x: X), (pT1g x) \is_single_valued by move => x; apply F2MF_sing.
have tot: forall (x: X), (pT1g x) \is_total by move => x; apply F2MF_tot.
pose g (x:X) := exist_fun (conj (conj (sing x) (tot x)) (crlzr x)).
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

Lemma wiso_usig X:
	wisomorphic (rep_space_usig_prod X) (rep_space_cont_fun rep_space_nat X).
Proof.
have crlzr: forall xn: nat -> X, has_cont_rlzr (F2MF xn).
	move => xn.
	pose R phi psi := psi \is_name_of (xn (phi star)).
	have Rtot: R \is_total by move => phi; apply (\rep_valid X).2.
	have [F icf]:= choice R Rtot.
	exists F; split.
		by apply rlzr_mfrlzr => phi x phinx; rewrite -phinx; apply/icf.
	move => phi q phifd; exists ([::star]) => Fphi /= FphiFphi psi coin.
	have eq: phi = psi.
		by apply functional_extensionality => /= str; elim: str; apply coin.
	by rewrite -eq => Fpsi FpsiFpsi; rewrite -FpsiFpsi -FphiFphi.
Admitted.

*)
