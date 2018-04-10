From mathcomp Require Import all_ssreflect.
Require Import all_core all_rs_base rs_one.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NATURALS.

Canonical rep_space_nat := @make_rep_space
	nat
	one
	nat
	(@id_rep nat)
	0%nat
	one_count
	nat_count
	(id_rep_is_rep nat).

Notation nS phi q := (S (phi q)).

Lemma S_prec_fun:
	S \is_prec_function.
Proof.
by exists (fun phi q => nS phi q); move => phi x /= <-.
Defined.

Lemma nat_prec_fun (f: nat -> nat):
	f \is_prec_function.
Proof.
exists (fun phi q => f (phi q): answers rep_space_nat).
by move => phi x /= <-.
Defined.

Lemma nat_nat_prec_fun (f: nat -> nat -> nat):
	(fun p => f p.1 p.2) \is_prec_function.
Proof.
exists (fun phi q => f (phi (inl star)).1 (phi (inr star)).2: answers rep_space_nat).
by move => phi x /= [<- <-].
Defined.

Lemma nat_rs_prec_pind (Z X: rep_space) (f0: Z -> X) (fS: (Z * X) -> X) (f: (Z * nat) -> X):
	f0 \is_prec_function -> fS \is_prec_function ->
		(forall p, f p = (fix f' z n := match n with
			| 0 => f0 z
			| S n' => fS (z, f' z n')
		end) p.1 p.2) -> f \is_prec_function.
Proof.
move => [M0 M0prop] [/=MS MSprop] feq.
pose Mf:= fix Mf phi n q := match n with
	| 0 => M0 phi q
	| S n' => MS (name_pair phi (Mf phi n')) q
end.
exists (fun (phi: names (rep_space_prod Z rep_space_nat)) q => Mf (lprj phi) (rprj phi star) q).
move => phi [z n] [/=phinz phinn]; rewrite /Mf/=.
rewrite /id_rep in phinn.
elim: n phi phinz phinn => [phi phinz -> | n ih phi phinz ->]; first by rewrite feq/=; apply M0prop.
rewrite feq /=; apply MSprop.
split; rewrite lprj_pair rprj_pair => //=.
specialize (ih (name_pair (lprj phi) (fun _ => n))).
by rewrite lprj_pair rprj_pair feq/= in ih; apply ih.
Defined.

Lemma nat_rs_prec_ind (X: rep_space) (f0: X) (fS: X -> X) (f: nat -> X):
	f0 \is_computable_element -> fS \is_prec_function ->
		(forall n, f n = (fix f' n := match n with
			| 0 => f0
			| S n' => fS (f' n')
		end) n) -> f \is_prec_function.
Proof.
move => [M0 M0prop] [/=MS MSprop] feq.
pose Mf:= fix Mf n q := match n with
	| 0 => M0 q
	| S n' => MS (Mf n') q
end.
exists (fun (phi: names (rep_space_nat)) q => Mf (phi star) q).
move => phi n phinn; rewrite /Mf/=.
rewrite /id_rep in phinn.
elim: n phi phinn => [phi -> | n ih phi ->]; first by rewrite feq/=; apply M0prop.
rewrite feq /=; apply MSprop.
specialize (ih (fun _ => n)).
by rewrite feq/= in ih; apply ih.
Qed.
End NATURALS.