From mathcomp Require Import all_ssreflect.
Require Import all_rs_base rs_one rs_nat rs_opt.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DISCRETENESS.
(* This Definition is equivalent to the notion Arno introduces in "https://arxiv.org/pdf/1204.3763.pdf".
One of the drawbacks fo the version here is that it does not have a computable version.*)
Definition is_dscrt X :=
	forall Y (f: (space X) -> (space Y)), (F2MF f) \has_continuous_realizer.
Notation "X '\is_discrete'" := (is_dscrt X) (at level 2).

Lemma dscrt_rel X: X \is_discrete ->
	(forall Y (f: (space X) ->> (space Y)), f \has_continuous_realizer).
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
Qed.

Lemma opt_dscrt X:
	X \is_discrete -> (rep_space_opt X) \is_discrete.
Proof.
move => dscrt Y f.
pose f' a := f (Some a).
have [F' [F'rf' Fcont]]:= dscrt Y f'.
have [psi psinfn] := rep_sur Y (f None).
pose F := (fun (phi: names (rep_space_opt X)) Fphi => match (phi (inl star)).1 with
	| Some str => F' (unsm phi) Fphi
	| None => Fphi = psi
end).
exists F.
move: F'rf'; rewrite rlzr_F2MF => F'rf'.
split.
	apply rlzr_F2MF => phi x phinx.
	case: x phinx => [a [eq phina] | /= phinN].
		split.
			have [Fphi F'phiFphi] := (F'rf' (unsm phi) a phina).1.
			by exists Fphi; rewrite /F eq.
		move => Fphi FphiFphi; rewrite /F eq in FphiFphi.
		by apply (F'rf' (unsm phi) a phina).2.
	split; first by exists psi; rewrite /F phinN.
	by move => Fphi FphiFphi; rewrite /F phinN in FphiFphi; rewrite FphiFphi.
move => phi q [Fphi FphiFphi].
case E: (phi (inl star)).1.
	rewrite /F E in FphiFphi.
	have usphifd: (unsm phi) \from_dom F' by exists Fphi.
	have [L Lprop]:= (Fcont (unsm phi) q usphifd).
	exists (inl star :: map inr L).
	move => Fphi'/= FphiFphi' psi' [eq coin] Fpsi' Fpsi'Fpsi'.
	rewrite /F -eq E in FphiFphi' Fpsi'Fpsi'.
	have /=:= Lprop Fphi' => Lprop'.
	have coin': (unsm phi) \and (unsm psi') \coincide_on L.
		move: coin; elim: (L) => //= a K ih [eq' coin].
		by split; [rewrite eq' | apply ih].
	exact: Lprop' FphiFphi' (unsm psi') coin' Fpsi' Fpsi'Fpsi'.
exists ([:: inl star]).
move => Fphi'/= FphiFphi' psi' [eq _] Fpsi' Fpsi'Fpsi'.
by rewrite /F -eq E in FphiFphi' Fpsi'Fpsi'; rewrite FphiFphi' Fpsi'Fpsi'.
Qed.
End DISCRETENESS.