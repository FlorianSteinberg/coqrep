(* This is example shows how to use a representation of the real numbers by means of rational
approximations to compute on the reals. Usually integers are prefered to avoid to many problems
that arise due to the possibility to use unnecessary high precission approximations. I tried
that approach but it lead to extensive additional work so I gave up at some point. I feel that
the approach in the present file is more appropriate. *)

From mathcomp Require Import all_ssreflect.
Require Import all_rs_base.
Require Import Qreals Reals Psatz FunctionalExtensionality ClassicalChoice.
Require Import Interval.Interval_specific_ops.
Require Import Interval.Interval_bigint_carrier.
Require Import Interval.Interval_interval_float_full.
Require Import Interval.Interval_interval.
Require Import Interval.Interval_xreal.
Import BigN BigZ.
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
	forall eps, ~ eps = Fnan -> D2R eps > 0 -> exists N, forall n, (N <= n)%positive
		-> bounded (I n) /\ diam (I n) <= D2R eps.

Lemma Float_to_R m e:
	D2R (Float (BigZ.of_Z m) (BigZ.of_Z e)) = IZR m * powerRZ 2 e.
Proof.
rewrite /D2R/SFBI2.toX /SFBI2.toF/Interval_definitions.FtoX/=/BigIntRadix2.MtoP/=.
rewrite /BigIntRadix2.mantissa_sign BigZ.spec_eqb BigZ.spec_of_Z/=.
case m => /=.
		by rewrite Rmult_0_l.
	move => p.
	rewrite BigN.spec_of_pos.
	rewrite /Interval_definitions.FtoR/=.
	rewrite /BigIntRadix2.EtoZ BigZ.spec_of_Z.
	case: e.
			rewrite Fcore_Raux.P2R_INR -Z2Nat.inj_pos INR_IZR_INZ Z2Nat.id.
				by rewrite powerRZ_O Rmult_1_r.
			exact: Pos2Z.is_nonneg.
		move => p'.
		rewrite -two_power_pos_correct/=.
		rewrite Fcore_Raux.P2R_INR -Z2Nat.inj_pos INR_IZR_INZ Z2Nat.id; last exact: Pos2Z.is_nonneg.
		rewrite shift_pos_nat.
		rewrite Pos2Z.inj_mul mult_IZR.
		suffices ->: IZR (Z.pos (shift_nat (Pos.to_nat p') 1)) = 2^(Pos.to_nat p') by trivial.
		have /=:= (two_power_nat_equiv (Pos.to_nat p')); rewrite /two_power_nat => ->.
		by rewrite -pow_IZR.
	rewrite Fcore_Raux.P2R_INR -Z2Nat.inj_pos INR_IZR_INZ Z2Nat.id; last exact: Pos2Z.is_nonneg.
	move => p'.
	rewrite -two_power_pos_correct/=.
	rewrite Fcore_Raux.P2R_INR -Z2Nat.inj_pos INR_IZR_INZ Z2Nat.id; last exact: Pos2Z.is_nonneg.
	rewrite shift_pos_nat.
	suffices ->: IZR (Z.pos (shift_nat (Pos.to_nat p') 1)) = 2^(Pos.to_nat p') by trivial.
	have /=:= (two_power_nat_equiv (Pos.to_nat p')); rewrite /two_power_nat => ->.
	by rewrite -pow_IZR.
move => p.
rewrite BigN.spec_of_pos.
rewrite /Interval_definitions.FtoR/=.
rewrite /BigIntRadix2.EtoZ BigZ.spec_of_Z.
case: e.
		rewrite Fcore_Raux.P2R_INR -Z2Nat.inj_pos INR_IZR_INZ Z2Nat.id.
			by rewrite powerRZ_O Rmult_1_r.
		exact: Pos2Z.is_nonneg.
	move => p'.
	rewrite -two_power_pos_correct/=.
	rewrite Fcore_Raux.P2R_INR -Z2Nat.inj_pos INR_IZR_INZ Z2Nat.id; last exact: Pos2Z.is_nonneg.
	rewrite shift_pos_nat.
	rewrite Pos2Z.inj_mul mult_IZR.
	rewrite {1 3}/IZR Ropp_mult_distr_l.
	suffices ->: IZR (Z.pos (shift_nat (Pos.to_nat p') 1)) = 2^(Pos.to_nat p') by trivial.
	have /=:= (two_power_nat_equiv (Pos.to_nat p')); rewrite /two_power_nat => ->.
	by rewrite -pow_IZR.
rewrite Fcore_Raux.P2R_INR -Z2Nat.inj_pos INR_IZR_INZ Z2Nat.id; last exact: Pos2Z.is_nonneg.
move => p'.
rewrite -two_power_pos_correct/=.
rewrite Fcore_Raux.P2R_INR -Z2Nat.inj_pos INR_IZR_INZ Z2Nat.id; last exact: Pos2Z.is_nonneg.
rewrite shift_pos_nat.
suffices ->: IZR (Z.pos (shift_nat (Pos.to_nat p') 1)) = 2^(Pos.to_nat p') by trivial.
have /=:= (two_power_nat_equiv (Pos.to_nat p')); rewrite /two_power_nat => ->.
by rewrite -pow_IZR.
Qed.


Lemma D_accumulates_to_zero r : 0 < r -> exists q : D, 0 < D2R q < r /\ ~ q = Fnan.
Proof.
move: r.
suffices: forall r, 0 < r < 1 -> exists q: D, 0 < D2R q < r /\ ~q = Fnan.
	move => ass r rPos.
	set r' := Rmin r (1/2).
	have ineq: 0 < r' < 1.
		split; first by apply Rmin_pos; lra.
		by apply/ Rle_lt_trans; first apply Rmin_r; lra.
	have [q [[qup qdwn] qr]]:= ass r' ineq.
	exists q.
	by split => //; split; last by apply/ Rlt_le_trans; last apply (Rmin_l _ (1/2)).
move => r [rPos rl1].
have zln2: 0 < ln 2 by rewrite -ln_1; apply ln_increasing; lra.
have ilr_Pos : 0 < ln (/r).
	rewrite -ln_1; apply ln_increasing; try lra.
	rewrite -(Rinv_involutive 1); try lra.
	by apply Rinv_lt_contravar; rewrite Rinv_1 => //; rewrite Rmult_1_r.
pose z := up (ln (/r)/ ln 2).
have irLz : ln (/r) / ln 2 < IZR z by rewrite /z; have := archimed (ln (/r) / ln 2); lra.
have zPos : 0 < IZR z by apply/ Rlt_trans; last exact irLz; apply Rdiv_lt_0_compat.
pose p := Z.to_pos z.
have pE : (' p)%Z = z by rewrite Z2Pos.id //; apply: lt_0_IZR.
exists (Float (BigZ.of_Z 1) (BigZ.of_Z (- z))).
rewrite /D2R/=/BigIntRadix2.EtoZ BigZ.spec_of_Z/= -pE/= Fcore_Raux.Z2R_IZR.
rewrite Zpower_pos_powerRZ -(positive_nat_Z p) -pow_powerRZ.
replace (1 / 2 ^ Pos.to_nat p) with (/2 ^ Pos.to_nat p); last first.
	field; apply pow_nonzero; lra.
have z2: 0 < 2 by lra.
have le2p:= pow_lt 2 (Pos.to_nat p) z2.
split => //.
split; first by apply/ Rinv_0_lt_compat/ pow_lt; lra.
rewrite -(Rinv_involutive r); try lra.
apply Rinv_lt_contravar; first by rewrite Rmult_comm; apply Rdiv_lt_0_compat.
rewrite -(exp_ln (/r)) => //; last by apply Rinv_0_lt_compat.
rewrite -(exp_ln (2 ^ Pos.to_nat p)) => //.
rewrite Rcomplements.ln_pow; try lra; apply exp_increasing.
rewrite -Z2Nat.inj_pos pE INR_IZR_INZ Z2Nat.id; last by rewrite -pE; apply Zle_0_pos.
replace (ln (/r)) with (ln (/r) / ln 2 * ln 2); last first.
	by field; rewrite -ln_1; apply/ Rgt_not_eq/ Rlt_gt/ ln_increasing; lra.
by apply Rmult_lt_compat_r; first by rewrite -ln_1; apply/ ln_increasing; lra.
Qed.

Lemma rep_R_sing: rep_R \is_single_valued.
Proof.
move => In x x' [xeIn convIn] [x'eIn _].
apply cond_eq => e eg0.
have [eps [[epsg0 epsle] epsnum]]:= D_accumulates_to_zero eg0.
have [N prop]:= convIn eps epsnum epsg0.
have ineq': (N <= N)%positive by lia.
have [Ibnd dI]:= (prop N ineq').
specialize (xeIn N Ibnd).
specialize (x'eIn N Ibnd).
split_Rabs; lra.
Qed.

Lemma powerRZ2_neg_pos p:
	powerRZ 2 (Z.neg p) = /powerRZ 2 (Z.pos p).
Proof.
replace (Z.neg p) with (- Z.pos p)%Z by trivial.
rewrite powerRZ_neg; try lra.
by rewrite powerRZ_inv.
Qed.

(* The notation \is_representation is for being single_valued and surjective. *)
Lemma rep_R_is_rep: rep_R \is_representation.
Proof.
split.
	exact: rep_R_sing.
move => x.
exists (fun n => I.bnd 
	(Float (BigZ.BigZ.of_Z (Int_part (x * (powerRZ 2 (Z.pos n))))) (BigZ.BigZ.of_Z (Z.neg n)))
	(Float (BigZ.BigZ.of_Z (up (x * (powerRZ 2 (Z.pos n))))) (BigZ.BigZ.of_Z (Z.neg n)))).
rewrite /rep_R.
split.
	move => n _.
	split.
		rewrite Float_to_R powerRZ2_neg_pos.
		apply/ (Rmult_le_reg_r (powerRZ 2 (Z.pos n))); first by apply powerRZ_lt; lra.
		rewrite Rmult_assoc Rinv_l; last by apply/ Interval_missing.Rlt_neq_sym /powerRZ_lt; lra.
		by rewrite Rmult_1_r; apply: (base_Int_part _).1.
	rewrite Float_to_R powerRZ2_neg_pos.
	apply/ (Rmult_le_reg_r (powerRZ 2 (Z.pos n))); first by apply powerRZ_lt; lra.
	rewrite Rmult_assoc Rinv_l; last by apply/ Interval_missing.Rlt_neq_sym /powerRZ_lt; lra.
	by rewrite Rmult_1_r; apply/ Rle_trans; last exact/ Rlt_le/ (archimed _).1; lra.
move => eps epsnum epsg0.
case: eps epsg0 epsnum => // m e epsg0 _.
case: e epsg0 => e epsg0.
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