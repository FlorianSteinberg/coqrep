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
Notation cntd x I := (contains (I.convert I) x).
Notation "x '\contained_in' I" := (cntd x I) (at level 2).
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

Lemma cntd_I0:
 forall x, x \contained_in I0 -> x = Xreal 0.
Proof.
case => //= r/=.
rewrite  F.fromZ_correct => /= Hr.
congr Xreal; lra.
Qed.

Lemma mul_I0:
	forall x, x \contained_in I0 -> x \contained_in (mul I0 I0).
Proof.
move => x cntd.
have eq:= cntd_I0 cntd.
rewrite eq; rewrite eq in cntd.
replace (Xreal 0) with (Xmul (Xreal 0) (Xreal 0)) by by rewrite xreal_ssr_compat.Xmul_Xreal Rmult_0_r.
by apply (I.mul_correct prec I0 I0).
Qed.

Lemma CshawIA0 x I:
	x \contained_in (CshawIA [::] I) -> x \contained_in I0.
Proof.
Admitted.

Lemma CshawIA_crct (p: {poly R}) (pI: seq ID) (x: R) (J: ID):
	(forall i, (Xreal p`_i) \contained_in (nth (I0) pI i)) -> (Xreal x) \contained_in J ->
		(Xreal (Cshaw p x)) \contained_in (CshawIA pI J).
Proof.
move => prp xJ.
elim: pI prp => prp.
	have ->: p = 0.
		apply polyP => i.
		rewrite [nth 0 (polyseq 0) _]nth_default; last by rewrite size_poly0.
		specialize (prp i).
		suffices: Xreal p`_i = Xreal 0 by case.
		move: prp; rewrite [nth I0 _ _]nth_default => // prp.
		by apply cntd_I0.
	rewrite /Cshaw/CshawIA.
Admitted.

Definition I1 := I.fromZ (-1)%Z.

End MyClenshawStuff.

Module V := MyClenshawStuff  SFBI2.

Compute V.I1.