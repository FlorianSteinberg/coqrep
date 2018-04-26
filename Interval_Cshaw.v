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

Variable prec:F.precision.
Notation add I J := (I.add prec I J).
Notation mul I J := (I.mul prec I J).
Notation sub I J := (I.sub prec I J).
Notation scl2 I := (I.scale I (F.ZtoS 2)).
Notation I0 := (I.fromZ 0).

Fixpoint CbIA q (x : ID) : ID * ID :=
 if q is a :: q' then
   let t := CbIA q' x in
   let a1 := sub (scl2 (mul (add a (fst t)) x)) (snd t) in
   (a1, (fst t)) else (I0, I0).

Definition CshawIA p x := sub (CbIA p x).1 (mul (CbIA p x).2 x).

Print I.mul.
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

Lemma CbIA_crct (p: {poly R}) (pI: seq ID) (x: R) (I: ID):
	(forall i, (p`_i) \contained_in (nth I0 pI i)) -> x \contained_in I ->
		(Cb p x).1 \contained_in (CbIA pI I).1 /\ (Cb p x).2 \contained_in (CbIA pI I).2.
Proof.
move => prp xJ.
elim: pI p prp => [p prp | J pI ih p prp].
	have ->: p = 0.
		apply polyP => i.
		rewrite [nth 0 (polyseq 0) _]nth_default; last by rewrite size_poly0.
		specialize (prp i).
		move: prp; rewrite [nth I0 _ _]nth_default => // prp.
		by apply cntd_I0.
	have ->: Cb (0%:P) x = (0%R, 0%R) by by rewrite polyseq0/=.
	replace (CbIA [::] I) with (I0,I0) by by rewrite /CbIA.
	rewrite /=.
	by rewrite /= F.fromZ_correct/Z2R; lra.
split.
Admitted.

Lemma CshawIA_crct (p: {poly R}) (pI: seq ID) (x: R) (J: ID):
	(forall i, p`_i \contained_in (nth I0 pI i)) -> x \contained_in J ->
		(Cshaw p x) \contained_in (CshawIA pI J).
Proof.
move => prp xJ.
elim: pI p prp => [p prp | I pI ih p prp].
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
Admitted.

Definition I1 := I.fromZ (-1)%Z.

End MyClenshawStuff.

Module V := MyClenshawStuff  SFBI2.

Compute V.I1.