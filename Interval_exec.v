From mathcomp Require Import all_ssreflect all_algebra.
Require Import Rstruct Reals Psatz Poly_complements CPoly CPoly_exec.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Local Open Scope ring_scope.
Require Import ZArith.
Require Import Interval.Interval_specific_ops.
Require Import Interval.Interval_bigint_carrier.
Require Import Interval.Interval_interval_float_full.
Require Import Interval.Interval_missing.
Require Import Interval.Interval_xreal.
Require Import Interval.Interval_definitions.
Require Import Interval.Interval_float_sig.
Require Import Interval.Interval_interval.
Require Import Interval.Interval_interval_float_full.
Require Import Interval.Interval_integral.
Require Import Interval.Interval_bisect.

Module SFBI2 := SpecificFloat BigIntRadix2.
Module I := FloatIntervalFull SFBI2.

Module MyClenshawStuff (F : FloatOps with Definition even_radix := true).

Module I := FloatIntervalFull F.

Notation mant := BigIntRadix2.smantissa_type.
Notation xpnt := BigIntRadix2.exponent_type.
Check I.fromZ 0.
Notation D := F.type.
Notation ID := (Interval_interval_float.f_interval F.type).
Notation XR := Interval_xreal.ExtendedR.
Notation Xreal := Interval_xreal.Xreal.
Notation "x '\contained_in' I" := (contains (I.convert I) (Xreal x)) (at level 20).
Notation D2R := I.T.toR.
Notation lower := I.lower.
Notation upper := I.upper.
Notation diam I := (I.upper I - I.lower I).
Notation bounded := I.bounded.

Section stuff.
Variable prec: F.precision.
Notation add I J := (I.add prec I J).
Notation mul I J := (I.mul prec I J).
Notation sub I J := (I.sub prec I J).
Notation scl2 I := (I.scale2 I (F.ZtoS 1)).
Notation div I J := (I.div prec I J).
Notation I0 := (I.fromZ 0).

Fixpoint CbIA q (x : ID) : ID * ID :=
 if q is a :: q' then
   let t := CbIA q' x in
   let a1 := sub (add a (scl2 (mul (fst t) x))) (snd t) in
   (a1, (fst t)) else (I0, I0).

Definition CshawIA p x := sub (CbIA p x).1 (mul (CbIA p x).2 x).

Lemma cntd_I0:
	forall x, x \contained_in I0 -> x = 0%R.
Proof.
move => x.
rewrite /contains/I.convert/=.
rewrite  F.fromZ_correct => /= [[]].
rewrite !/IZR.
lra.
Qed.

Lemma mul_correct_R x y I J:
	x \contained_in I -> y \contained_in J -> (x * y) \contained_in (mul I J).
Proof.
by apply I.mul_correct.
Qed.

Lemma sub_correct_R x y I J:
	x \contained_in I -> y \contained_in J -> (x - y) \contained_in (sub I J).
Proof.
by apply I.sub_correct.
Qed.

Lemma add_correct_R x y I J:
	x \contained_in I -> y \contained_in J -> (x + y) \contained_in (add I J).
Proof.
by apply I.add_correct.
Qed.

Lemma div_correct_R x y I J:
	x\contained_in I -> y \contained_in J -> is_zero y = false -> (x / y) \contained_in (div I J).
Proof.
intros.
have /=:= I.div_correct prec I J (Xreal x) (Xreal y).
rewrite /Xdiv' H1 /= => crct.
by apply crct.
Qed.

Lemma scl2_correct_R x I:
	x \contained_in I -> (x *+ 2) \contained_in (scl2 I).
Proof.
intros.
replace (Xreal (x *+ 2)) with (Xmul (Xreal x) (Xreal (bpow radix2 1))).
	by apply I.scale2_correct.
congr Xreal.
by have ->: (x*2 = x + x)%R by lra.
Qed.

Lemma scale2_correct_R x z I:
	x \contained_in I -> (x * (powerRZ 2 z)) \contained_in (I.scale2 I (F.ZtoS z)).
Proof.
intros.
replace (Xreal (x * (powerRZ 2 z))) with (Xmul (Xreal x) (Xreal (bpow radix2 z))).
	by apply I.scale2_correct.
congr Xreal.
by rewrite bpow_powerRZ.
Qed.

Lemma neg_correct_R x I:
	x \contained_in I -> (-x) \contained_in (I.neg I).
Proof.
by move => xeI; have /=:= (I.neg_correct I (Xreal x) xeI).
Qed.

Lemma stuff (p : {poly R}):
	(forall i : nat, p`_i \contained_in nth I0 [::] i) -> p = 0.
Proof.
move => prp.
apply polyP => i.
rewrite coef0.
apply cntd_I0.
move: (prp i).
Search _ Poly.
by rewrite nth_default.
Qed.

Lemma I00:
	0 \contained_in I0.
Proof.
by rewrite /=F.fromZ_correct/=; lra.
Qed.

Lemma CbIA_crct (p: seq R) (pI: seq ID) (x: R) (I: ID):
	(forall i, (p`_i) \contained_in (nth I0 pI i)) -> x \contained_in I  -> size p = size pI ->
		(Cb p x).1 \contained_in (CbIA pI I).1 /\ (Cb p x).2 \contained_in (CbIA pI I).2.
Proof.
move => prp xJ.
elim: pI p prp => [[ | a p]// prp _ | J pI ih [ | a p]// prp eq].
	by split; apply I00.
rewrite /=.
case: (ih p) => // [i | | ih1 ih2 ].
		by apply (prp (S i)).
	by case: eq.
split => //.
apply sub_correct_R => //.
apply add_correct_R; first exact: (prp 0%nat).
apply scl2_correct_R.
by apply mul_correct_R.
Qed.

Lemma CshawIA_crct (p: seq R) (pI: seq ID) (x: R) (J: ID):
	(forall i, p`_i \contained_in (nth I0 pI i)) -> x \contained_in J -> size p = size pI ->
		(Cshaw p x) \contained_in (CshawIA pI J).
Proof.
move => prp xJ.
case: pI p prp => [p prp eq | I pI p prp eq].
	have ->: p = [::] by apply size0nil.
	rewrite /Cshaw/=.
	rewrite /CshawIA/CbIA.
	replace (Xreal 0) with (Xsub (Xreal 0) (Xreal 0)) by
		by rewrite Xsub_split/Xadd/Xneg Ropp_0 Rplus_0_r.
	apply sub_correct_R; first exact: I00.
	by apply mul_correct_R; first exact: I00.
apply sub_correct_R; first by apply CbIA_crct.
by apply mul_correct_R; first by apply CbIA_crct.
Qed.

Lemma CshawIA_correct (p: seq R) (pI: seq ID) (x: R) (J: ID):
	(forall i, p`_i \contained_in (nth I0 pI i)) -> x \contained_in J -> size p = size pI ->
		(Cshaw p x) \contained_in (CshawIA pI J).
Proof.
move => prp xJ.
case: pI p prp => [p prp eq | I pI p prp eq].
	have ->: p = [::].
		by apply size0nil.
	rewrite /Cshaw /= /CshawIA/CbIA.
	apply sub_correct_R; first exact I00.
	by apply mul_correct_R; first exact I00.
rewrite /Cshaw/CshawIA.
apply sub_correct_R; first by apply CbIA_crct.
by apply mul_correct_R; first by apply CbIA_crct.
Qed.

(* The schaebischaef nodes: *)
Definition m_ (i n: positive) := ((IPR i + 1/2) / (IPR n +1))%R.

Definition mI_ (i n: positive) :=
	div (I.fromZ (2* (Z.pos i) + 1)) (I.fromZ (2 * ((Z.pos n) +1 ))).

Lemma IPR0 n:
	(IPR n + 1)%R <> 0%R.
Proof.
rewrite -INR_IPR.
Search _ INR (0 <= _)%R.
replace (INR (Pos.to_nat n) +1)%R with (INR (Pos.to_nat n).+1)%R.
apply Rlt_neq_sym.
Search _ INR Rle.
replace 0%R with (INR 0) by trivial.
apply lt_INR.
have:= pos_INR (nat_of_pos n); lia.
by case: (Pos.to_nat n) => //=; rewrite Rplus_0_l.
Qed.

Lemma mI_correct i n :
	m_ i n \contained_in mI_ i n.
Proof.
replace (m_ i n) with (((IZR 2) * (IPR i) + 1) / ((IZR 2) * (IPR n +1 )))%R; last first.
	by rewrite /m_; field; apply: IPR0.
apply div_correct_R.
		replace (2 * IPR i + 1)%R with (IZR (2* (Z.pos i) + 1)).
			by apply I.fromZ_correct.
		by rewrite plus_IZR mult_IZR.
	replace (2 * (IPR n + 1))%R with (IZR (2* (Z.pos n + 1))).
		by apply I.fromZ_correct.
	by rewrite mult_IZR plus_IZR.
rewrite /is_zero /Req_bool.
rewrite Rcompare_Gt => //.
apply Rmult_lt_0_compat; first lra.
apply Rle_lt_0_plus_1.
rewrite -INR_IPR.
exact: pos_INR.
Qed.

Definition mu_ i n:= cos (m_ i n * PI).

Definition piI := I.pi prec.
Definition muI_ i n:= I.cos prec (mul (mI_ i n) piI).

Lemma cos_correct_R x I:
	x \contained_in I -> (cos x) \contained_in (I.cos prec I).
Proof.
by move => xcI; have /=:= I.cos_correct prec I (Xreal x) xcI.
Qed.

Lemma atan_correct_R x I:
	x \contained_in I -> (atan x) \contained_in (I.atan prec I).
Proof.
by move => xcI; have /=:= I.atan_correct prec I (Xreal x) xcI.
Qed.

Lemma muI_correct i n:
	mu_ i n \contained_in muI_ i n.
Proof.
apply cos_correct_R.
apply mul_correct_R.
apply mI_correct.
exact: I.pi_correct.
Qed.

Lemma sin_correct_R x I:
	x \contained_in I -> (sin x) \contained_in (I.sin prec I).
Proof.
by move => xcI; have /=:= I.sin_correct prec I (Xreal x) xcI.
Qed.

Section CMSin.
Context (I : ID).
Notation aD := (I.lower I).
Notation bD := (I.upper I).
Notation aI := (Interval.Interval_interval_float.Ibnd aD aD).
Notation bI := (Interval.Interval_interval_float.Ibnd bD bD).
Notation a := (D2R aD).
Notation b := (D2R bD).

Lemma aI_correct:
	a \contained_in aI.
Proof.
by rewrite /= /D2R; split; case E: (F.toX aD) => //=; lra.
Qed.

Lemma bI_correct:
	b \contained_in bI.
Proof.
by rewrite /= /D2R; split; case E: (F.toX bD) => //=; lra.
Qed.

Definition f_ i n := sin ((a + b) / 2  + (b - a)/2 * (mu_ i n))%R.

Definition fI_ i n := I.sin prec (I.add prec (I.scale2 (I.add prec aI bI) (F.ZtoS (-1))) (I.mul prec (I.scale2 (I.sub prec bI aI) (F.ZtoS (-1))) (muI_ i n))).

Lemma fI_correct i n:
	f_ i n \contained_in fI_ i n.
Proof.
apply sin_correct_R.
apply add_correct_R.
	replace ((a + b) / 2)%R with ((a + b) * powerRZ 2 (-1)).
	apply scale2_correct_R.
		by apply add_correct_R; [apply: aI_correct | apply: bI_correct].
	replace (Zneg 1) with (Z.opp 1) by trivial.
	rewrite powerRZ_neg; try lra.
	by rewrite powerRZ_1.
apply mul_correct_R; last exact: muI_correct.
replace ((b - a) / 2)%R with ((b - a) * powerRZ 2 (-1)).
	apply scale2_correct_R.
	by apply sub_correct_R; [apply: bI_correct | apply: aI_correct].
replace (Zneg 1) with (Z.opp 1) by trivial.
rewrite powerRZ_neg; try lra.
by rewrite powerRZ_1.
Qed.

Definition iota_pos n := map Pos.of_nat (iota 0 (nat_of_pos n)).

Definition fL n := map (fun i => f_ i n) (iota_pos n).

Lemma size_fL n:
	size (fL n) = nat_of_pos n.
Proof.
by rewrite /fL/iota_pos !size_map size_iota.
Qed.

Definition fLI n := map (fun i => fI_ i n) (iota_pos n).

Lemma size_fLI n:
	size (fLI n) = nat_of_pos n.
Proof.
by rewrite /fLI/iota_pos !size_map size_iota.
Qed.

Lemma fLI_correct i n:
	(fL n)`_i \contained_in nth I0 (fLI n) i.
Proof.
case E: (nat_of_pos n <= i)%nat.
	rewrite !nth_default.
			exact I00.
		by rewrite size_fL.
	by rewrite size_fLI.
rewrite /fL.
by rewrite !(nth_map xH); first exact: fI_correct;
	rewrite /iota_pos size_map size_iota; apply/leP; move/leP: E; lia.
Qed.

Definition c_ k n := Cshaw (fL n) (mu_ k n).
Definition cI_ k n := CshawIA (fLI n) (muI_ k n).

Lemma cI_correct k n:
	c_ k n \contained_in cI_ k n.
Proof.
rewrite /c_ /cI_.
apply CshawIA_correct; first by move => i; apply fLI_correct.
	exact: muI_correct.
by rewrite size_fL size_fLI.
Qed.

Fixpoint fact p := match p with
	| 0 => 1%positive
	| S n => ((Pos.of_nat (S n)) * (fact n))%positive
end.

Fixpoint gamma n x := match n with
		| 0 => - sin x
		| 0.+1 => -cos x
		| 0.+2 => sin x
		| 0.+3 => cos x
		| n.+4 => gamma n x
	end.

Fixpoint Gamma (n: nat) I := match n with
	| 0 => I.neg (I.sin prec I)
	| 0.+1 => I.neg (I.cos prec I)
	| 0.+2 => I.sin prec I
	| 0.+3 => I.cos prec I
	| n.+4 => Gamma n I
end.

Require Import Coquelicot.Coquelicot.
Notation "f ^( n )" := (Derive_n f n) (at level 2, format "f ^( n )").

Ltac toR := rewrite /GRing.add /GRing.opp /GRing.zero /GRing.mul /GRing.inv
  /GRing.one //=.

Lemma induc P:
	P 0%nat -> P 1%nat -> P 2%nat -> P 3%nat -> (forall n, P n -> P (n.+4)) -> forall n, P n.
Proof.
intros.
elim: n {-2}n (leqnn n) => [[]// | n Hn[|[|[|[|m]]]]// Hm].
by apply /X3 /Hn /leP; move/leP: Hm; lia.
Qed.

Lemma Derive_n_sin n x: 	sin^(n +2) x = gamma n x.
Proof.
apply is_derive_n_unique.
suff ->: gamma n x = (if odd (n + 2) then (-1) ^ (n +2)./2 * cos x else (-1) ^ (n + 2)./2 * sin x) by apply coquelicot_compl.is_derive_n_sin.
move: n; apply induc => /=; try toR; try lra.
move => n; case: (odd (n+2)) => /= ->; toR.
	rewrite -!Rmult_assoc.
	replace (-1 * -1) with 1 by lra.
	by rewrite Rmult_1_l.
rewrite -!Rmult_assoc.
replace (-1 * -1) with 1 by lra.
by rewrite Rmult_1_l.
Qed.

Lemma Gamma_correct x n:
	x \contained_in I -> (gamma n x) \contained_in (Gamma n I).
Proof.
intros; move: n.
by apply induc; try apply neg_correct_R; try apply sin_correct_R; try apply cos_correct_R.
Qed.

Lemma lower_Gamma_correct x n:
	F.toX (I.lower (Gamma n I)) <> Xnan ->
	x \contained_in I -> 0 <= D2R (I.lower (Gamma n I)) -> 0 <= sin^(n + 2) x.
Proof.
intros.
rewrite Derive_n_sin.
have /=:= Gamma_correct n H0.
case: (Gamma n I) H1 H; rewrite /D2R/proj_val; first by rewrite F.nan_correct.
move => l u /=.
case: (F.toX l) => //.
move => r ineq _ [ineq' _].
lra.
Qed.

Lemma upper_Gamma_correct x n:
	F.toX (I.upper (Gamma n I)) <> Xnan ->
	x \contained_in I -> D2R (I.upper (Gamma n I)) <= 0 -> sin^(n + 2) x <= 0.
Proof.
intros.
rewrite Derive_n_sin.
have /=:= Gamma_correct n H0.
case: (Gamma n I) H1 H; rewrite /D2R/proj_val; first by rewrite F.nan_correct.
move => l u /=.
case: (F.toX u) => //.
move => r ineq _ [_ ineq'].
lra.
Qed.

Let diamI :=	match I with
	| Interval.Interval_interval_float.Inan => Interval.Interval_interval_float.Inan
	| Interval.Interval_interval_float.Ibnd l u =>
		(I.sub prec (Interval.Interval_interval_float.Ibnd u u) (Interval.Interval_interval_float.Ibnd l l))
end.

Let diamImul2:= I.scale diamI (F.ZtoS 1).
Let radI := I.scale diamI (F.ZtoS (-1)).
Let radIdiv2:= I.scale diamI (F.ZtoS (-2)).

(* Definition V n I := I.power_pos prec J (Pos.of_nat n). *)

Definition Delta (n: nat) I :=
	let J := I.lower_extent (I.abs (Gamma (n.+3) I)) in I.meet J (I.neg J).

End CMSin.
End stuff.

End MyClenshawStuff.
Module V := MyClenshawStuff  SFBI2.

Require Import QArith.
Check V.CshawIA.
Print s_float.
From Bignums Require Import BigQ.
Check bigQ.
Definition a := 1%bigQ.
Compute (2 * 4)%bigQ.
Print s_float.
Import Interval.Interval_specific_ops.
Definition D2Q (d: s_float bigZ bigZ) := match d with
	| Fnan => 0%bigQ
	| Float m e => (BigQ.Qz m * (2^([e]%bigZ)))%bigQ
end.

Locate PtoP.
Definition I1 := I.fromZ (-1)%Z.
Definition I2 := I.fromZ (2)%Z.
Definition I3 := I.fromZ (3)%Z.
Definition lst := [:: I1; I2].
Check I1.
Import Interval.Interval_interval_float.
Definition mapIQ I := match I with
	| Inan => Inan
	| Ibnd a b => Ibnd (D2Q a) (D2Q b)
end.
Compute (mapIQ (V.CshawIA (SFBI2.PtoP 5) [::I.fromZ(-1); (I.fromZ (2)%Z)] (I.fromZ (-1)))).
Print V.CbIA.
Compute V.Gamma (SFBI2.PtoP 15) 0%nat I1.
Compute (Cshaw [::ratz (-1); ratz (2)] (ratz (-1))).
Compute (V.piI (SFBI2.PtoP 100)).











