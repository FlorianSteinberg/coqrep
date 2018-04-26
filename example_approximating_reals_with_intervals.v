(* This is example shows how to use a representation of the real numbers by means of intervals
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
Import Fcore_Raux Fcore_Zaux.
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
Notation "x '\contained_in' I" :=
(Interval_interval.contains (I.convert I) (Xreal x)) (at level 2).
Coercion I.convert: ID >-> Interval_interval.interval.
Notation D2R := I.T.toR.
Coercion I.T.toR: D >-> R.
Notation lower := I.lower.
Notation upper := I.upper.
Notation diam I := (I.upper I - I.lower I).
Notation bounded := I.bounded.
Notation I0 := (I.fromZ 0).
Definition l := @Fnan mant xpnt.
Definition u := Float 1%bigZ 0%bigZ.
Definition I: ID := Interval_interval_float.Ibnd l u.
Definition J: ID := Interval_interval_float.Inan.
Print xpnt.
Compute I.mul (2)%bigZ I0 J.

Lemma add_correct_R prec x y I J:
	x \contained_in I -> y \contained_in J -> (x + y) \contained_in (I.add prec I J).
Proof.
intros.
replace (Xreal (x + y)) with (Xadd (Xreal x) (Xreal y)) by trivial.
by apply I.add_correct.
Qed.

Lemma mul_correct_R prec x y I J:
	x \contained_in I -> y \contained_in J -> (x * y) \contained_in (I.mul prec I J).
Proof.
intros.
replace (Xreal (x * y)) with (Xmul (Xreal x) (Xreal y)) by trivial.
by apply I.mul_correct.
Qed.

Definition rep_R : (positive -> ID) -> R -> Prop :=
  fun I x => (forall n,  x \contained_in (I n))
  /\
	forall eps, D2R eps > 0 -> exists N, forall n, (N <= n)%positive
		-> bounded (I n) /\ diam (I n) <= D2R eps.

Lemma D2R_SFBI2toX m e:
	SFBI2.toX (Float m e) = Xreal (D2R (Float m e)).
Proof.
rewrite /D2R/proj_val/=/SFBI2.toX/=/Interval_definitions.FtoX/=.
by case: BigIntRadix2.mantissa_sign (Float m e) => //.
Qed.

Lemma D2R_Float (m e: bigZ):
  I.T.toR (Float m e) = IZR [m]%bigZ * powerRZ 2 [e]%bigZ.
Proof.
rewrite /I.T.toR /SFBI2.toX /SFBI2.toF/=.
case: (BigIntRadix2.mantissa_sign m) (BigIntRadix2.mantissa_sign_correct m);
  rewrite /BigIntRadix2.MtoZ /=.
	by move => ->; lra.
move => s p' [-> [p]].
rewrite /BigIntRadix2.EtoZ /BigIntRadix2.MtoP => -> {p'}.
move: [e]%bigZ => {e} [ | e | e ] /=;
  rewrite !Z2R_IZR ?Z.pow_pos_fold ?mult_IZR ?pow_IZR ?positive_nat_Z;
  case: s => //;
  lra.
Qed.

Lemma Float_to_R m e:
	D2R (Float (BigZ.of_Z m) (BigZ.of_Z e)) = IZR m * powerRZ 2 e.
Proof. by rewrite D2R_Float !BigZ.spec_of_Z. Qed.

Lemma D_accumulates_to_zero r : 0 < r -> exists q : D, 0 < D2R q < r.
Proof.
move: r.
suffices: forall r, 0 < r < 1 -> exists q: D, 0 < D2R q < r.
	move => ass r rPos.
	set r' := Rmin r (1/2).
	have ineq: 0 < r' < 1.
		split; first by apply Rmin_pos; lra.
		by apply/ Rle_lt_trans; first apply Rmin_r; lra.
	have [q [qup qdwn]]:= ass r' ineq.
	exists q.
	by split => //; last by apply/ Rlt_le_trans; last apply (Rmin_l _ (1/2)).
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
rewrite D2R_Float !BigZ.spec_of_Z Rmult_1_l.
rewrite powerRZ_neg; try lra.
rewrite -[z]Z2Nat.id; last by rewrite -pE.
rewrite -pow_powerRZ -Rinv_pow; try lra.
split => //; first by apply/ Rinv_0_lt_compat/ pow_lt; lra.
rewrite -pE /= -(Rinv_involutive r); try lra.
apply Rinv_lt_contravar.
	by rewrite Rmult_comm; apply Rdiv_lt_0_compat; first apply pow_lt; lra.
rewrite -(exp_ln (/r)) => //; last by apply Rinv_0_lt_compat.
rewrite -(exp_ln (2 ^ Pos.to_nat p)) => //.
rewrite Rcomplements.ln_pow; try lra; apply exp_increasing.
rewrite -Z2Nat.inj_pos pE INR_IZR_INZ Z2Nat.id; last by rewrite -pE; apply Zle_0_pos.
replace (ln (/r)) with (ln (/r) / ln 2 * ln 2); last first.
	by field; rewrite -ln_1; apply/ Rgt_not_eq/ Rlt_gt/ ln_increasing; lra.
by apply Rmult_lt_compat_r; first by rewrite -ln_1; apply/ ln_increasing; lra.
by apply pow_lt; lra.
Qed.

Lemma nFnan eps:
	0 < D2R eps -> ~ eps = Fnan.
Proof. by case: eps; first by rewrite /D2R/=; lra. Qed.

Lemma rep_R_sing: rep_R \is_single_valued.
Proof.
move => In x x' [xeIn convIn] [x'eIn _].
apply cond_eq => e eg0.
have [eps [epsg0 epsle]]:= D_accumulates_to_zero eg0.
have [N prop]:= convIn eps epsg0.
have ineq': (N <= N)%positive by lia.
have [Ibnd dI]:= (prop N ineq').
move: xeIn (xeIn N) => _ xeIn.
move: x'eIn (x'eIn N) => _ x'eIn.
apply/ Rle_lt_trans; last by apply epsle.
case: (In N) Ibnd dI xeIn x'eIn => // l u/=.
case: u; first by case: l.
by case: l => // um ue lm le; rewrite !D2R_SFBI2toX; split_Rabs; lra.
Qed.

Lemma powerRZ2_neg_pos p:
	powerRZ 2 (Z.neg p) = /powerRZ 2 (Z.pos p).
Proof.
replace (Z.neg p) with (- Z.pos p)%Z by trivial.
rewrite powerRZ_neg; try lra.
by rewrite powerRZ_inv.
Qed.

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
	move => n /=; rewrite !D2R_SFBI2toX.
	replace (BigZ.Neg (BigN.of_pos n)) with (BigZ.of_Z (Z.neg n)) by trivial.
	rewrite !Float_to_R powerRZ2_neg_pos.
	split.
		apply/ (Rmult_le_reg_r (powerRZ 2 (Z.pos n))); first by apply powerRZ_lt; lra.
		rewrite Rmult_assoc Rinv_l.
			by rewrite Rmult_1_r; apply: (base_Int_part _).1.
		by apply/ Interval_missing.Rlt_neq_sym /powerRZ_lt; lra.
	apply/ (Rmult_le_reg_r (powerRZ 2 (Z.pos n))); first by apply powerRZ_lt; lra.
	rewrite Rmult_assoc Rinv_l; last by apply/ Interval_missing.Rlt_neq_sym /powerRZ_lt; lra.
	by rewrite Rmult_1_r/powerRZ; apply/Rle_trans; last exact/Rlt_le/(archimed _).1; lra.
move => eps epsg0.
case: eps epsg0; first by rewrite /D2R/=; lra.
move => m e epsg0 /=.
exists (Pos.max xH (Z.to_pos (BigZ.to_Z (-e + 2)))) => n ineq; split => //.
replace (BigZ.Neg (BigN.of_pos n)) with (BigZ.of_Z (Z.neg n)) by trivial.
rewrite !D2R_Float !BigZ.spec_of_Z.
set a := (x * 2 ^ Pos.to_nat n).
set y := (powerRZ 2 (Z.neg n)).
have pwps: 0 < y by apply powerRZ_lt; lra.
have inv: / y * y = 1 by rewrite Rinv_l; lra.
suffices stuff: IZR (up (a)) -
IZR (Int_part (a)) <=
IZR [m]%bigZ * powerRZ 2 [e]%bigZ * / y.
rewrite -[IZR [m]%bigZ * powerRZ 2 [e]%bigZ]Rmult_1_r -inv -Rmult_assoc.
rewrite /Rminus Ropp_mult_distr_l -Rmult_plus_distr_r.
by apply /Rmult_le_compat_r; first by apply Rlt_le.
rewrite /y Rmult_assoc -powerRZ_inv; try lra.
rewrite -powerRZ_neg; try lra.
rewrite -powerRZ_add; try lra.
have sml: IZR (up a) - IZR (Int_part a) <= 2.
	have:= (archimed a).2.
	have:= (base_Int_part a).2.
	lra.
apply/ Rle_trans; first exact: sml.
have mineq: (1 <= [m]%bigZ)%Z.
	rewrite D2R_Float in epsg0.
	have /Rgt_lt /lt_IZR gtr': IZR [m]%bigZ > IZR 0.
		apply Rlt_gt.
		apply (Rmult_lt_reg_r (powerRZ 2 [e]%bigZ)); first by apply powerRZ_lt; lra.
		by rewrite Rmult_0_l; lra.
	by lia.
rewrite -{1}[2]Rmult_1_l.
apply Rmult_le_compat; try lra.
	by apply IZR_le.
rewrite -{1}[2]powerRZ_1 !powerRZ_Rpower; try lra.
apply /Rlt_le/ Rpower_lt; try lra; first by rewrite /IZR/IPR/=; lra.
apply IZR_lt.
replace (Z.opp (Z.neg n)) with (Z.pos n) by trivial.
rewrite /Z.succ Zplus_0_l.
move:ineq.
admit.
Admitted.

Lemma Intervals_countable: ID \is_countable.
Proof.
Admitted.

Lemma positive_countable: positive \is_countable.
Proof.
Admitted.

Canonical rep_space_R := @make_rep_space
	R
	positive
	ID
	rep_R
	xH
	I0
	positive_countable
	Intervals_countable
	rep_R_is_rep.

Lemma triang r x y: (Rabs x) + (Rabs y) <= r -> Rabs(x + y) <= r.
Proof.
apply: Rle_trans.
by apply: Rabs_triang.
Qed.

Lemma Rplus_prec : (fun x => Rplus (x.1) (x.2)) \is_prec_function.
Proof.
pose Rplus_realizer := (fun phi (n: positive) =>
	I.add (SFBI2.PtoP n) (lprj phi n) (rprj phi n)).
exists Rplus_realizer => phi [x y] [/=[xephin convx] [yephin convy]].
split.
	move => n; rewrite /Rplus_realizer.
	apply/ add_correct_R; [apply xephin | apply yephin].
move => eps epsg0.
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