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
Require Import Interval.Interval_specific_ops.
Require Import Interval.Interval_bigint_carrier.
Require Import Interval.Interval_interval_float_full.
Require Import Interval.Interval_interval.
Require Import Interval.Interval_xreal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.
Import QArith.
Local Open Scope R_scope.

Module SFBI2 := SpecificFloat BigIntRadix2.
Module I := FloatIntervalFull SFBI2.

(* All the operations *)
Search Interval_interval_float.f_interval _.


(* An example *)

(* Precision *)
Definition prec := SFBI2.PtoP 10.

(* [-1;-1] *)
Definition I1 := I.fromZ (-1)%Z.

(* [-2; -2] *)
Definition I2 := I.fromZ (-2)%Z.

(* [-2; -1] *)
Definition I3 := I.meet I1 I2.

Compute I3.

(* [-3; -3] *)
Definition I4 := I.fromZ (-3)%Z.

(* [-4; -4] *)
Definition I5 := I.fromZ (-4)%Z.

(* [-4; -3] *)
Definition I6 := I.meet I4 I5.

Compute I6.

(* [-6; -4] = [-2; -1] + [-4; -3] *)
Compute I.add prec I3 I6.

(* [3; 8] = [-2; -1] * [-4; -3] *)
Compute I.mul prec I3 I6.
Check I1.


Notation D:= SFBI2.type.
Notation mant := BigIntRadix2.smantissa_type.
Notation xpnt := BigIntRadix2.exponent_type.
Print mant.
Print BigIntRadix2.smantissa_type.
Search _ (_ -> BigZ.BigZ.t).
Notation ID := (Interval_interval_float.f_interval SFBI2.type).
Notation XR := Interval_xreal.ExtendedR.
Notation Xreal := Interval_xreal.Xreal.
Notation cntd x I := (Interval_interval.contains (I.convert I) x).
Notation "x '\contained_in' I" := (cntd x I) (at level 2).
Coercion I.convert: ID >-> Interval_interval.interval.
Notation D2R := I.T.toR.
Coercion I.T.toR: D >-> R.
Notation lower := I.lower.
Notation upper := I.upper.
Notation diam I := (I.upper I - I.lower I).
Notation bounded := I.bounded.

Definition rep_R : (positive -> ID) -> R -> Prop :=
  fun I x => (forall n,  bounded (I n) -> lower (I n) <= x <= upper (I n))
  /\
	forall eps, eps > 0 -> exists N, forall n, (N <= n)%positive
		-> bounded (I n) /\ diam (I n) <= eps.

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
move => In x x' [xeIn convIn] [x'eIn _].
apply cond_eq_Rle => eps ineq.
have [N prop]:= convIn eps ineq.
have ineq': (N <= N)%positive by lia.
have [Ibnd dI]:= (prop N ineq').
specialize (xeIn N Ibnd).
specialize (x'eIn N Ibnd).
split_Rabs; lra.
Qed.

(* The notation is_representation is for being single_valued and surjective. *)
Lemma rep_R_is_rep: rep_R \is_representation.
Proof.
split.
	exact: rep_R_sing.
move => x.
rewrite /codom.
exists (fun n => I.bnd 
	(Float (BigZ.BigZ.of_Z (Int_part (x * (IPR n)))) (BigZ.BigZ.of_Z (Z.pos n)))
	(Float (BigZ.BigZ.of_Z (up (x * (IPR n)))) (BigZ.BigZ.of_Z (Z.pos n)))).
Admitted.
(*
split => /=.
	move => n _ .
	rewrite /Q2R /=.
	have eq: x = (x * (IPR n)* / (IPR n)).
		field.
		Search _ IPR.
		apply IZR_nz.
	split.
		rewrite {2}eq.
		apply Rmult_le_compat_r.
			apply Rlt_le; apply Rinv_0_lt_compat.
			admit.
		rewrite Rmult_comm.
		exact: (base_Int_part (x* (Z.pos n))).1.
	rewrite {1}eq.
	apply Rmult_le_compat_r.
		apply Rlt_le; apply Rinv_0_lt_compat.
		admit.
	rewrite Rmult_comm;	apply Rlt_le; apply Rgt_lt.
	exact: (archimed ((Z.pos n) * x)).1.
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
	(0%Q,0%Q)
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
Qed. *)