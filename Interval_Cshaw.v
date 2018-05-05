From mathcomp Require Import all_ssreflect all_algebra.
Require Import Rstruct Reals Psatz example_tchebychevpol.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Local Scope ring_scope.
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
Notation ID := (Interval_interval_float.f_interval F.type).
Notation XR := Interval_xreal.ExtendedR.
Notation Xreal := Interval_xreal.Xreal.
Notation "x '\contained_in' I" := (contains (I.convert I) (Xreal x)) (at level 20).
Notation D2R := I.T.toR.
Notation lower := I.lower.
Notation upper := I.upper.
Notation diam I := (I.upper I - I.lower I).
Notation bounded := I.bounded.

(* All the operations *)
Search Interval_interval_float.f_interval _.


Section stuff.
Variable prec:F.precision.
Notation add I J := (I.add prec I J).
Notation mul I J := (I.mul prec I J).
Notation sub I J := (I.sub prec I J).
Notation scl2 I := (I.scale2 I (F.ZtoS 1)).
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
intros.
replace (Xreal (x * y)) with (Xmul (Xreal x) (Xreal y)) by trivial.
by apply I.mul_correct.
Qed.

Lemma sub_correct_R x y I J:
	x \contained_in I -> y \contained_in J -> (x - y) \contained_in (sub I J).
Proof.
intros.
replace (Xreal (x - y)) with (Xsub (Xreal x) (Xreal y)) by trivial.
by apply I.sub_correct.
Qed.

Lemma add_correct_R x y I J:
	x \contained_in I -> y \contained_in J -> (x + y) \contained_in (add I J).
Proof.
intros.
replace (Xreal (x + y)) with (Xadd (Xreal x) (Xreal y)) by trivial.
by apply I.add_correct.
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

Lemma CshawIA_crct (p: {poly R}) (pI: seq ID) (x: R) (J: ID):
	(forall i, p`_i \contained_in (nth I0 pI i)) -> x \contained_in J -> size p = size pI ->
		(Cshaw p x) \contained_in (CshawIA pI J).
Proof.
move => prp xJ.
case: pI p prp => [p prp eq | I pI p prp eq].
	have ->: p = 0.
		apply polyP => i.
		rewrite [nth 0 (polyseq 0) _]nth_default; last by rewrite size_poly0.
		specialize (prp i).
		move: prp; rewrite [nth I0 _ _]nth_default => // prp.
		by apply cntd_I0.
	replace (Cshaw 0 x) with 0%R by by rewrite Cshaw0.
	rewrite /CshawIA/CbIA.
	replace (Xreal 0) with (Xsub (Xreal 0) (Xreal 0)) by
		by rewrite Xsub_split/Xadd/Xneg Ropp_0 Rplus_0_r.
	apply I.sub_correct.
	specialize (prp 0%nat); rewrite nth_default in prp => //.
	by have <-:= cntd_I0 prp.
	replace 0%R with (Rmult 0 x) by by rewrite Rmult_0_l.
	apply mul_correct_R => //=.
	by rewrite /= F.fromZ_correct /Z2R; lra.
rewrite -[p]polyseqK -lCshaw_spec/lCshaw/CshawIA.
apply sub_correct_R; first by apply CbIA_crct.
by apply mul_correct_R; first by apply CbIA_crct.
Qed.

End stuff.

End MyClenshawStuff.

Module V := MyClenshawStuff  SFBI2.

Require Import QArith.
Check V.CshawIA.
Print s_float.
From Bignums Require Import BigQ.
Check bigQ.
Definition a := 1%bigQ.
Search _ (_-> BigQ.t_).
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
Compute (lCshaw [::ratz (-1); ratz (2)] (ratz (-1))).
Search _ s_float.
Check Interval_specific_ops.Float.