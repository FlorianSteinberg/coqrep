From mathcomp Require Import all_ssreflect.
Require Import all_rs rs_reals rs_reals_creals.
Require Import Qreals Reals Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition Cantor:= rep_space_usig_prod (rep_space_opt rep_space_one).

Definition nz (p: Cantor) (s: Sirp) :=
	s = bot <-> forall n, p n = None.

Definition F (phi: names Cantor) (q: questions rep_space_S): answers rep_space_S := (phi (q, inl star)).1.
Require Import Classical.
Lemma nz_is_computable:
	nz \is_computable.
Proof.
apply rec_cmpt.
exists F.
move => phi x phinx _.
case: (classic (forall n, x n = None)) => ass.
	exists bot; split => //.
	rewrite /F /= /rep_S/=.
	by split => // [[n]]; have /=:= phinx n; rewrite ass /= => ->.
exists top; split => //.
rewrite /= /rep_S; split => // _.
have [n neq]:= (not_all_ex_not _ _ ass).
exists n.
rewrite /F /= /rep_S/=.
have /=:= phinx n.
have -> /=: x n = some star.
	by case: (x n) neq => // a; case a.
by case => -> /=.
Qed.
