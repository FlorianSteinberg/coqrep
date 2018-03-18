(* This is example shows how to use a representation of the real numbers by means of rational
approximations to compute on the reals. Usually integers are prefered to avoid to many problems
that arise due to the possibility to use unnecessary high precission approximations. I tried
that approach but it lead to extensive additional work so I gave up at some point. I feel that
the approach in the present file is more appropriate. *)

From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions baire_space continuity.
Require Import machines oracle_machines universal_machine.
Require Import representations representation_facts.
Require Import Qreals Reals Psatz FunctionalExtensionality ClassicalChoice.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.
Import QArith.
Local Open Scope R_scope.

Coercion IZR : Z >-> R.

Definition rep_R : (positive -> Q * Q) -> R -> Prop :=
  fun phi x => (forall n, Q2R (phi n).1 <= x <= Q2R (phi n).2)
  /\
	forall eps, eps > 0 -> exists N, forall n, (N <= n)%positive -> Q2R (phi n).2 - Q2R (phi n).1 <= eps.
(* This is close to the standard definition of the chauchy representation. Usually integers
are prefered to avoid to many possible answers. I tried using integers, but it got very ugly
so I gave up at some point. I feel like the above is the most natural formulation of the Cauchy
representation anyway. *)

Lemma cond_eq_Rle:
	forall x y : R, (forall eps : R, 0 < eps -> Rabs (x - y) <= eps) -> x = y.
Proof.
move => x y cond.
apply cond_eq.
move => eps ineq.
apply/ Rle_lt_trans; first apply (cond (eps/2)); lra.
Qed.

Lemma rep_R_sing: rep_R \is_single_valued.
Proof.
move => phi x x' [xeIn convIn] [x'eIn _].
apply cond_eq_Rle => eps ineq.
have [N prop]:= convIn eps ineq.
have ineq': (N <= N)%positive by lia.
specialize (prop N ineq').
specialize (xeIn N).
specialize (x'eIn N).
split_Rabs; lra.
Qed.

Fixpoint IPR p:= match p with
	| xH => 1
	| xI p' => 2*(IPR p') + 1
	| xO p' => 2 * (IPR p')
end.

(* The notation is_representation is for being single_valued and surjective. *)
Lemma rep_R_is_rep: rep_R \is_representation.
Proof.
split.
	exact: rep_R_sing.
move => x.
exists (fun n =>
	(Qmake (Int_part( (INR (Pos.to_nat n)) * x)) n,
	Qmake (up ( (INR (Pos.to_nat n)) * x)) n)).
split.
	move => n /=.
	rewrite /Q2R /=.
	have eq: x = (x * INR (Pos.to_nat n)* / INR (Pos.to_nat n)).
		field.
		suffices: 0 < INR (Pos.to_nat n) by lra.
		apply pos_INR_nat_of_P.
	split.
		rewrite {2}eq.
		apply Rmult_le_compat_r.
			suffices: 0 < / INR (Pos.to_nat n) by lra.
			apply Rinv_0_lt_compat.
			exact: pos_INR_nat_of_P.
		rewrite Rmult_comm.
		exact: (base_Int_part (x* INR (Pos.to_nat n))).1.
	rewrite {1}eq.
	apply Rmult_le_compat_r.
		suffices: 0 < / INR (Pos.to_nat n) by lra.
		apply Rinv_0_lt_compat.
		exact: pos_INR_nat_of_P.
	rewrite Rmult_comm;	apply Rlt_le; apply Rgt_lt.
	exact: (archimed (INR (Pos.to_nat n) * x)).1.
move => eps ineq.
exists (Z.to_pos (Int_part (x/eps))).
move => n ineq'.
	rewrite /Q2R /=.
admit.
Admitted.

Lemma rationals_countable: (Q * Q) \is_countable.
Proof.
Admitted.

Lemma positive_countable: positive \is_countable.
Proof.
Admitted.

Canonical rep_space_R := @make_rep_space
	R
	positive
	(Q * Q)
	rep_R
	(1%Q,1%Q)
	positive_countable
	rationals_countable
	rep_R_is_rep.

Lemma id_is_computable : (id : R -> R) \is_computable_function.
Proof.
apply/ prec_cmpt_fun_cmpt.
by exists (fun phi => phi).
Qed.

Lemma triang r x y: (Rabs x) + (Rabs y) <= r -> Rabs(x + y) <= r.
Proof.
apply: Rle_trans.
by apply: Rabs_triang.
Qed.

Lemma Rplus_prec : (fun x => Rplus (x.1) (x.2)) \is_prec_function.
Proof.
pose Rplus_realizer := (fun phi (n: positive) =>
	(Qplus (phi (inl n)).1.1 (phi (inr n)).2.1,Qplus (phi (inl n)).1.2 (phi (inr n)).2.2)).
exists Rplus_realizer => phipsi.
set phi := (fun n => (phipsi (inl n)).1).
set psi := (fun n => (phipsi (inr n)).2).
rewrite /= in phi psi.
move => [x y] [[/=xeI convI] [/=yeJ convJ]].
split.
	move: convI convJ => _ _ n.
	have:= (xeI n).
	have:= (yeJ n).
	rewrite /lprj/rprj/Rplus_realizer/= !Q2R_plus; lra.
move: xeI yeJ => _ _ eps ineq.
have ineq': eps/2 > 0 by lra.
have [N Nprop] := convI (eps/2) ineq'.
have [M Mprop] := convJ (eps/2) ineq'.
move: convI convJ => _ _.
exists (Pos.max N M).
move => n ns.
rewrite /Rplus_realizer !Q2R_plus.
have Nln: (N <= n)%positive by lia.
have Mln: (M <= n)%positive by lia.
specialize (Nprop n Nln).
specialize (Mprop n Mln).
move: Nprop Mprop; rewrite /lprj/rprj/=; lra.
Defined.

Lemma Rplus_comp:
	(fun p => Rplus p.1 p.2) \is_computable_function.
Proof.
apply prec_fun_cmpt.
exact Rplus_prec.
Qed.

Lemma Rmult_prec : (fun x => Rmult x.1 x.2) \is_prec_function.
Proof.
Admitted.

Lemma Rmult_cmpt:
	(fun p => Rmult p.1 p.2) \is_computable_function.
Proof.
apply prec_fun_cmpt.
exact Rmult_prec.
Qed.