(* This is example shows how to use a representation of the real numbers by means of rational
approximations to compute on the reals. Usually integers are prefered to avoid to many problems
that arise due to the possibility to use unnecessary high precission approximations. I tried
that approac in the other example file "example_approximating_reals_with_integers" but it lead
to extensive additional work so Igave up at some point. I feel that the approach in the present
file is more appropriate. *)

From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions representations.
Require Import Reals Lra Classical ClassicalFacts Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.
Import QArith.
Local Open Scope R_scope.

(* \begin{syntacticsuggar} *)
Fixpoint P2R n := match n with
  | xH => 1
  | xO m => 2* P2R m
  | xI k => 2* P2R k + 1
end.
(* It eludes me why this function is not provided under the name IPR in the standard Library *)
Fixpoint Z2R z := match z with
  | Z0 => 0
  | Zpos n => P2R n
  | Zneg m => - P2R m
end.
Coercion IZR : Z >-> R.
(* The translation IZR from the standard library translates to natural numbers in unary
and then to a real numbers. I think that is stuped so I tried to replace it. However, it turns
out that IZR is used in some lemmas, so I need to rely on it anyway. *)
Definition Q2R q := QArith_base.Qnum q / QArith_base.QDen q.
(* Coercion Q2R : Q >-> R. *)
(* This is not coerced since it leads to ambiguous paths. *)
(* \end{syntacticalsuggar} *)
(* It turns out that these coercions are not enough. To avoid heaps of burocracy I need to find
a way to also coerce the operators. Any hints about how to do this in a reasonable way are
appreciated *)

(* \begin{usefulllemmas} about the rational numbers provided by Laurent Thery *)
Lemma Q2R_make n d : Q2R (Qmake n d) = IZR n / IZR(' d).
Proof. by []. Qed.

Lemma Q2R_make1 n : Q2R (Qmake n 1) = IZR n.
Proof. by rewrite /Q2R /=; field. Qed.

Lemma Q2R0 : Q2R 0 = 0.
Proof. by rewrite Q2R_make1. Qed.

Lemma Q2R1 : Q2R 1 = 1.
Proof. by rewrite Q2R_make1. Qed.

Lemma plus_Q2R r1 r2 : Q2R (r1 + r2) = Q2R r1 + Q2R r2.
Proof.
rewrite /Q2R /= plus_IZR !mult_IZR.
rewrite Pos2Nat.inj_mul mult_INR /=.
field.
have H1 := pos_INR_nat_of_P (Qden r1).
have H2 := pos_INR_nat_of_P (Qden r2).
by lra.
Qed.

Lemma mul_Q2R r1 r2 : Q2R (r1 * r2) = Q2R r1 * Q2R r2.
Proof.
rewrite /Q2R /= !mult_IZR.
rewrite Pos2Nat.inj_mul mult_INR /=.
field.
have H1 := pos_INR_nat_of_P (Qden r1).
have H2 := pos_INR_nat_of_P (Qden r2).
by lra.
Qed.

Lemma opp_Q2R r : Q2R (-r) = - Q2R r.
Proof.
rewrite /Q2R /= opp_IZR.
field.
have H := pos_INR_nat_of_P (Qden r).
lra.
Qed.

Lemma minus_Q2R r1 r2 : Q2R (r1 - r2) = Q2R r1 - Q2R r2.
Proof. rewrite plus_Q2R opp_Q2R; lra. Qed.

Add Morphism Q2R with signature Qeq ==> eq as Q2R_comp.
Proof.
case=> n1 d1.
case=> n2 d2.
rewrite /Qeq /Q2R /= => H.
apply: Rminus_diag_uniq.
rewrite !INR_IZR_INZ /= !positive_nat_Z.
have F1 : IZR (' d1) <> 0 by move=> /eq_IZR_R0.
have F2 : IZR (' d2) <> 0 by move=> /eq_IZR_R0.
field_simplify=> //.
rewrite -!mult_IZR H !mult_IZR.
by field.
Qed.

Lemma inv_Q2R r : Q2R r <> 0 -> Q2R (/ r) = / (Q2R r).
Proof.
move=> Q2R_neq0.
apply: Rmult_eq_reg_l (Q2R_neq0).
rewrite -mul_Q2R Qmult_inv_r.
  by rewrite Q2R1; field.
contradict Q2R_neq0.
rewrite -Q2R0.
by apply: Q2R_comp.
Qed.

Lemma div_Q2R r1 r2 : Q2R r2 <> 0 -> Q2R (r1 / r2) = (Q2R r1) / (Q2R r2).
Proof. by move=> r2_neq0; rewrite mul_Q2R inv_Q2R. Qed.

Lemma le0_Q2R r : (0 <= r)%Q -> 0 <= Q2R r.
Proof.
rewrite /Qle /= Z.mul_1_r => /IZR_le /= H.
apply: Rmult_le_pos => //.
apply/Rlt_le/Rinv_0_lt_compat.
apply: pos_INR_nat_of_P (Qden r).
Qed.

Lemma le_Q2R r1 r2 : (r1 <= r2)%Q -> Q2R r1 <= Q2R r2.
Proof.
move=> H.
suff: 0 <= Q2R (r2 - r1) by rewrite minus_Q2R; lra.
apply: le0_Q2R; lra.
Qed.

Lemma lt0_Q2R r : (0 < r)%Q -> 0 < Q2R r.
Proof.
rewrite /Qlt /= Z.mul_1_r => /IZR_lt /= H.
apply: Rmult_lt_0_compat => //.
apply: Rinv_0_lt_compat.
apply: pos_INR_nat_of_P (Qden r).
Qed.

Lemma lt_Q2R r1 r2 : (r1 < r2)%Q -> Q2R r1 < Q2R r2.
Proof.
move=> H.
suff: 0 < Q2R (r2 - r1) by rewrite minus_Q2R; lra.
apply: lt0_Q2R; lra.
Qed.

Lemma Q2R_le0 r : 0 <= Q2R r -> (0 <= r)%Q.
Proof.
case: (Qlt_le_dec r 0) => // /lt_Q2R.
rewrite Q2R0; lra.
Qed.

Lemma Q2R_le r1 r2 : Q2R r1 <= Q2R r2 -> (r1 <= r2)%Q.
Proof. by case: (Qlt_le_dec r2 r1) => // /lt_Q2R; lra. Qed.

Lemma Q2R_lt0 r : 0 < Q2R r -> (0 < r)%Q.
Proof.
case: (Qlt_le_dec 0 r) => // /le_Q2R.
rewrite Q2R0; lra.
Qed.

Lemma Q2R_lt r1 r2 : Q2R r1 < Q2R r2 -> (r1 < r2)%Q.
Proof. by case: (Qlt_le_dec r1 r2) => // /le_Q2R; lra. Qed.

Definition Q2Rt := (minus_Q2R, opp_Q2R, mul_Q2R, inv_Q2R, div_Q2R, plus_Q2R, Q2R_make1, Q2R_make).
(* \end{usefulllemmas} *)

Definition rep_R : (Q -> Q) -> R -> Prop :=
  fun phi x => forall eps, (0 < eps)%Q -> Rabs(x-Q2R(phi eps)) <= Q2R eps.
(* This is close to the standard definition of the chauchy representation. Usually integers
are prefered to avoid to many possible answers. I tried this in the other example file
"example_approximating_reals_with_integers" but it leads to extensive additional work so I
gave up at some point. I feel like the above is the most natural formulation of the Cauchy
representation. *)

Lemma approx : forall r, r - Int_part r <= 1.
Proof.
  move => r; move: (base_Int_part r) => [bipl bipr].
  lra.
Qed.

Lemma approx' : forall r, 0 <= r - Int_part r.
Proof.
  move => r; move: (base_Int_part r) => [bipl bipr].
  lra.
Qed.

Lemma rep_R_is_sur: rep_R is_surjective.
Proof.
  move => x.
  exists (fun eps => Qmult eps (Qmake(Int_part(x/(Q2R eps))) xH)).
  move => epsr eg0.
  rewrite !Q2Rt.
  rewrite Rabs_pos_eq.
  set eps := Q2R epsr.
  - set z := Int_part(x/eps).
    replace (x - eps * z) with (eps * (x / eps - z));first last.
    - field.
      by apply: Rlt_dichotomy_converse; right; apply lt0_Q2R.
    rewrite -{3}(Rmult_1_r eps).
    apply: Rmult_le_compat_l.
    - by left; apply lt0_Q2R.
    apply: (approx (x * /eps)).
  set eps := Q2R epsr.
  apply: (Rmult_le_reg_l (/eps)).
  - by apply: Rinv_0_lt_compat; apply: lt0_Q2R.
  rewrite Rmult_0_r.
  set z := Int_part(x/eps).
  replace (/eps*(x - eps * z)) with (x/eps - z);last first.
  - field.
    by apply: Rlt_dichotomy_converse; right; apply lt0_Q2R.
  apply (approx' (x * /eps)).
Qed.

Lemma Q_accumulates_to_zero r : 0 < r -> exists q : Q, 0 < Q2R q < r.
Proof.
move=> rPos.
have ir_Pos : 0 < /r by apply: Rinv_0_lt_compat.
pose z := up (/ r).
have irLz : / r < IZR z by rewrite /z; have := archimed (/ r); lra.
have zPos : 0 < IZR z by lra.
pose p := Z.to_pos z.
have pE : (' p)%Z = z by rewrite Z2Pos.id //; apply: lt_0_IZR.
exists (1 # p).
rewrite /Q2R /= INR_IZR_INZ positive_nat_Z pE [1 / _]Rmult_1_l.
split; first by apply: Rinv_0_lt_compat.
rewrite -(Rinv_involutive r); try lra.
apply: Rinv_lt_contravar; try nra.
Qed.

Lemma cond_eq_rat x y : (forall q, Q2R q > 0 -> Rabs (x - y) <= Q2R q) -> x = y.
Proof.
wlog: x y / y <= x => [Hw Hp|xLy Hp].
  have [/Hw->//|yLx] := Rle_dec y x.
  apply/sym_equal/Hw; try lra.
  by move=> q; rewrite Rabs_minus_sym; apply: Hp.
have [//|xDy] := Req_dec x y.
have /Q_accumulates_to_zero[q Hq] : 0 < x - y by lra.
have : Rabs (x - y) <= Q2R q by apply: Hp; lra.
rewrite Rabs_pos_eq; lra.
Qed.

Lemma rep_R_is_sing: is_sing rep_R.
Proof.
split => phi x x' pinox H.
	apply: cond_eq_rat => q qg0.
	set r := Q2R (phi (Qdiv q (1+1))).
	replace (x-x') with ((x-r) + (r-x')) by field.
	apply: Rle_trans.
	- apply: (Rabs_triang (x-r)).
	rewrite (_ : q == q / (1 + 1) + q / (1 + 1))%Q; last first.
	  by field.
	rewrite plus_Q2R.
	have q2_pos : (0 < q / (1 + 1))%Q.
	  rewrite (_ : 0 == 0 / (1 + 1))%Q; last by field.
	  apply: (Qmult_lt_compat_r 0 q (/(1+1))) => //.
	  by apply: Q2R_lt0; lra.
	apply: Rplus_le_compat.
	- by apply: pinox.
	- replace (Rabs (r - x')) with (Rabs (x' - r)).
	    by apply: H.
	by split_Rabs; lra.
by rewrite -H.
Qed.

Lemma rep_R_is_rep: rep_R is_representation.
Proof.
  split.
  - exact: rep_R_is_sing.
  - exact: rep_R_is_sur.
Qed.

Canonical rep_space_R := @make_rep_space_from_sur
  R
  (Q -> Q)
  (fun n => Qmake Z0 xH)
  rep_R
  rep_R_is_rep.

Lemma id_is_computable : (id : R -> R) is_computable.
Proof.
  by exists (fun phi=>phi).
Qed.
(* This is a trivial example. The proof looks nice, though... The next example uses the product
construction that was introduced in the file representations.v *)

Lemma triang r x y: (Rabs x) + (Rabs y) <= r -> Rabs(x + y) <= r.
Proof.
  apply: Rle_trans.
  apply: Rabs_triang.
Qed.

Lemma Rplus_is_computable : (fun x => Rplus (x.1) (x.2)) is_computable.
Proof.
  set Rplus_realizer := (fun (phi : names rep_space_R * names rep_space_R) eps =>
    (Qplus (phi.1 (Qdiv eps (1+1))) (phi.2(Qdiv eps (1+1))))).
  exists Rplus_realizer.
  move => phi x [phi0 phi1] xie eps eg0.
  rewrite /Rplus_realizer.
  rewrite plus_Q2R.
  set r := Q2R (phi.1 (Qdiv eps (1 + 1))).
  set q := Q2R (phi.2 (Qdiv eps (1 + 1))).
  replace (x.1 + x.2 - (r + q)) with (x.1 - r + (x.2 - q)); last first.
  - field.
  apply: (triang).
  replace (Q2R eps) with (Q2R (eps/ (1 + 1)) + Q2R (eps/ (1 + 1))).
  have exp2_pos : (0 < eps / (1 + 1))%Q.
    rewrite (_ : 0 == 0 / (1 + 1))%Q.
      by apply: (Qmult_lt_compat_r 0 eps (/(1+1))); last first.
    by field.
  - apply: Rplus_le_compat.
    - by apply: phi0.
    - by apply: phi1.
  - by rewrite !Q2Rt /=; lra.
Qed.

Lemma Rmult_is_computable : (fun x => Rmult (x.1) (x.2)) is_computable.
Proof.
  set rab := (fun (phi : Q -> Q) => 1# Z.to_pos (up(Rabs(Q2R(phi(1%Q)))))).
  set four := (1 + 1 + 1 + 1)%Q.
  set Rmult_realizer := (fun (phi : names rep_space_R * names rep_space_R) eps =>
    ((phi.1 (eps / four /(rab phi.2)) * (phi.2(eps /four/(rab phi.1))))%Q)).
  exists Rmult_realizer.
  move => phi x [phi0 phi1] xie eps eg0.
  rewrite /Rmult_realizer.
  rewrite mul_Q2R.
  set dx := (eps / four /(rab phi.2))%Q.
  set dy := (eps / four /(rab phi.1))%Q.
  set r := Q2R (phi.1 dx).
  set q := Q2R (phi.2 dy).
  replace (x.1 * x.2 - (r * q)) with ((x.1 - r) * x.2 + r * (x.2 - q)); last first.
  - field.
  apply: (triang).
  replace (Q2R eps) with (Q2R (eps/ (1 + 1)) + Q2R (eps/ (1 + 1))).
  - rewrite Rabs_mult Rabs_mult.
    apply: Rplus_le_compat.
		move: .
	
Admitted.