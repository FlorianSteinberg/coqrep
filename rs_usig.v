From mathcomp Require Import all_ssreflect.
Require Import all_rs_base rs_dscrt.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section USIGPROD.
Definition rep_usig_prod (X: rep_space) phi (xn: nat -> X):=
	forall n, (fun p => (phi (n,p))) \is_name_of (xn n).

Lemma rep_usig_prod_is_rep (X: rep_space):
	(@rep_usig_prod X) \is_representation.
Proof.
split => [ phi xn yn phinxn phinyn | xn ].
	apply functional_extensionality => n.
	by apply/ (rep_sing X); [apply phinxn | apply phinyn ].
pose R n phi:= phi \is_name_of (xn n).
have Rtot: R \is_total.
	by move => n; have [phi phinx]:= (rep_sur X (xn n)); exists phi.
by have [phi phinxn]:= choice R Rtot; exists (fun p => phi p.1 p.2).
Qed.

Canonical rep_space_usig_prod (X: rep_space) := @make_rep_space
	(nat -> space X)
	(nat * questions X)
	(answers X)
	(@rep_usig_prod X)
	((0%nat, some_question X))
	(some_answer X)
  (prod_count nat_count (countable_questions X))
  (countable_answers X)
  (@rep_usig_prod_is_rep X).

Lemma usig_base X (an: nat -> space X) phi:
	phi \is_name_of an -> forall n, (fun q => phi (n,q)) \is_name_of (an n).
Proof. done. Qed.

Definition ptw (X: rep_space) (op: X * X -> X) (fg: (nat -> X) * (nat -> X)) :=
	(fun n => op (fg.1 n, fg.2 n)).

Lemma ptw_prec X (op: rep_space_prod X X -> X):
	op \is_prec_function -> (ptw op) \is_prec_function.
Proof.
move => [Mop Mprop].
exists (fun (phi: names (rep_space_prod (rep_space_usig_prod X)(rep_space_usig_prod X))) q =>
	Mop (name_pair (fun q' => lprj phi (q.1, q')) (fun q' => rprj phi (q.1, q'))) q.2).
abstract by move => phi [an bn] [/=phinan phinbn] n/=; rewrite /ptw/=;
	apply ((Mprop (name_pair (fun q' => lprj phi (n, q')) (fun q' => rprj phi (n, q')))) (an n, bn n));
	split; rewrite rprj_pair lprj_pair/=; [apply phinan | apply phinbn].
Defined.

(*
Lemma wiso_usig X:
	wisomorphic (rep_space_usig_prod X) (rep_space_cont_fun rep_space_nat X).
Proof.
have crlzr: forall xn: nat -> X, hcr (F2MF xn).
	move => xn.
	pose R phi psi := psi \is_name_of (xn (phi star)).
	have Rtot: R \is_total by move => phi; apply (rep_sur X).
	have [F icf]:= choice R Rtot.
	exists F; split.
		by apply rlzr_mfrlzr => phi x phinx; rewrite -phinx; apply/icf.
	move => phi q phifd; exists ([::star]) => Fphi /= FphiFphi psi coin.
	have eq: phi = psi.
		by apply functional_extensionality => /= str; elim: str; apply coin.
	by rewrite -eq => Fpsi FpsiFpsi; rewrite -FpsiFpsi -FphiFphi.
Admitted. *)
End USIGPROD.