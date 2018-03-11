(* This is example shows how to use a representation of the real numbers by means of rational
approximations to compute on the reals. Usually integers are prefered to avoid to many problems
that arise due to the possibility to use unnecessary high precission approximations. I tried
that approach but it lead to extensive additional work so I gave up at some point. I feel that
the approach in the present file is more appropriate. *)

From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions baire_space continuity.
Require Import machines oracle_machines universal_machine representations.
Require Import Reals Lra Classical ClassicalFacts Psatz FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.
Import QArith.
Local Open Scope R_scope.

Fixpoint P2R n := match n with
  | xH => 1
  | xO m => 2* P2R m
  | xI k => 2* P2R k + 1
end.
Coercion IZR : Z >-> R.
Definition Q2R q := QArith_base.Qnum q / QArith_base.QDen q.

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
are prefered to avoid to many possible answers. I tried using integers, but it got very ugly
so I gave up at some point. I feel like the above is the most natural formulation of the Cauchy
representation anyway. *)

(* The following are auxiliary lemmas that are needed for the proof that the relation defined
above is the graph of a partial function. I.e. that it is single valued as a multi-valued
function. Laurent Thery provided the proofs of the following lemmas and improved their statments *)
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

Lemma rep_R_sing: rep_R \is_single_valued.
Proof.
move => phi x x' pinox H.
apply: cond_eq_rat => q qg0.
set r := Q2R (phi (Qdiv q (1+1))).
replace (x-x') with ((x-r) + (r-x')) by field.
apply: Rle_trans.
	apply: (Rabs_triang (x-r)).
rewrite (_ : q == q / (1 + 1) + q / (1 + 1))%Q; last first.
  by field.
rewrite plus_Q2R.
have q2_pos : (0 < q / (1 + 1))%Q.
  rewrite (_ : 0 == 0 / (1 + 1))%Q; last by field.
  apply: (Qmult_lt_compat_r 0 q (/(1+1))) => //.
  by apply: Q2R_lt0; lra.
apply: Rplus_le_compat.
	by apply: pinox.
replace (Rabs (r - x')) with (Rabs (x' - r)).
	by apply: H.
by split_Rabs; lra.
Qed.

(* Auxillary lemmas for the proof that the Cauchy representation is surjective. *)
Lemma approx : forall r, r - Int_part r <= 1.
Proof.
move => r; move: (base_Int_part r) => [bipl bipr]; lra.
Qed.

Lemma approx' : forall r, 0 <= r - Int_part r.
Proof.
move => r; move: (base_Int_part r) => [bipl bipr]; lra.
Qed.

(* The notation is_representation is for being single_valued and surjective. *)
Lemma rep_R_is_rep: rep_R \is_representation.
Proof.
split.
	exact: rep_R_sing.
move => x.
exists (fun eps => Qmult eps (Qmake(Int_part(x/(Q2R eps))) xH)).
move => epsr eg0.
rewrite !Q2Rt.
rewrite Rabs_pos_eq.
	set eps := Q2R epsr.
	set z := Int_part(x/eps).
	replace (x - eps * z) with (eps * (x / eps - z));first last.
		field.
		by apply: Rlt_dichotomy_converse; right; apply lt0_Q2R.
	rewrite -{3}(Rmult_1_r eps).
	apply: Rmult_le_compat_l.
		by left; apply lt0_Q2R.
	apply: (approx (x * /eps)).
set eps := Q2R epsr.
apply: (Rmult_le_reg_l (/eps)).
	by apply: Rinv_0_lt_compat; apply: lt0_Q2R.
rewrite Rmult_0_r.
set z := Int_part(x/eps).
replace (/eps*(x - eps * z)) with (x/eps - z);last first.
	field.
	by apply: Rlt_dichotomy_converse; right; apply lt0_Q2R.
by apply (approx' (x * /eps)).
Qed.

Lemma rationals_countable: Q \is_countable.
Proof.
Admitted.

Canonical rep_space_R := @make_rep_space
	R
	Q
	Q
	rep_R
	1%Q
	rationals_countable
	rationals_countable
	rep_R_is_rep.

Lemma id_is_computable : (id : R -> R) \is_computable_function.
Proof.
by exists (fun phi => phi).
Qed.

Lemma triang r x y: (Rabs x) + (Rabs y) <= r -> Rabs(x + y) <= r.
Proof.
apply: Rle_trans.
by apply: Rabs_triang.
Qed.

Lemma Rplus_is_computable : (fun x => Rplus (x.1) (x.2)) \is_computable_function.
Proof.
set Rplus_realizer := (fun phi eps =>
  (Qplus (phi (inl (Qdiv eps (1+1)))).1 (phi (inr (Qdiv eps (1+1)))).2)).
exists Rplus_realizer.
move => phi x phinx eps eg0.
rewrite /Rplus_realizer.
rewrite plus_Q2R.
set phi0 := (fun q => (phi (inl q)).1).
set phi1 := (fun q => (phi (inr q)).2).
set r := Q2R (phi0 (Qdiv eps (1 + 1))).
set q := Q2R (phi1 (Qdiv eps (1 + 1))).
replace (x.1 + x.2 - (r + q)) with (x.1 - r + (x.2 - q)); last first.
	field.
apply: (triang).
replace (Q2R eps) with (Q2R (eps/ (1 + 1)) + Q2R (eps/ (1 + 1))).
have exp2_pos : (0 < eps / (1 + 1))%Q.
	rewrite (_ : 0 == 0 / (1 + 1))%Q.
		by apply: (Qmult_lt_compat_r 0 eps (/(1+1))); last first.
	by field.
by apply: Rplus_le_compat; apply phinx.
by rewrite !Q2Rt /=; lra.
Qed.

Lemma Rmult_is_computable : (fun x => Rmult (x.1) (x.2)) \is_computable_function.
Proof.
set rab := (fun (phi : Q -> Q) => 1# Z.to_pos (up(Rabs(Q2R(phi(1%Q)))))).
set four := (1 + 1 + 1 + 1)%Q.
set Rmult_realizer := (fun phi eps =>
  ((phi (inl (eps / four /(rab (fun q => (phi(inl q)).1))))).1
  *
  (phi (inr (eps /four/(rab (fun q => (phi(inr q) ).2))))).2))%Q.
exists Rmult_realizer.
move => phi x phinx eps eg0.
rewrite /Rmult_realizer.
rewrite mul_Q2R.
set phi1 := (fun q:Q => (phi (inl q)).1:Q).
set phi2 := (fun q:Q => (phi (inr q)).2:Q).
set r := Q2R (phi (inr (eps / four / rab phi2)%Q)).2.
set q := Q2R (phi (inl (eps / four / rab phi1)%Q)).1.
replace (x.1 * x.2 - (r * q)) with ((x.1 - r) * x.2 + r * (x.2 - q)); last first.
	field.
rewrite -(Rplus_0_r (x.1 * x.2)).
rewrite -(Rplus_opp_r (x.1 * q)).
replace (x.1 * x.2 + (x.1 * q + - (x.1 * q)) - q * r)
	with (x.1 * (x.2 - q)	+ (x.1 - r) * q) by field.
apply: (triang).
replace (Q2R eps) with (Q2R (eps/ (1 + 1)) + Q2R (eps/ (1 + 1))).
	rewrite Rabs_mult Rabs_mult.
apply: Rplus_le_compat.
Admitted.

Require Import basic_represented_spaces.

Lemma seq_dscrt (xn: nat -> R):
	(F2MF xn) \has_continuous_realizer.
Proof.
pose R psi phi := phi \is_name_of (xn (psi star)).
have Rtot: R \is_total.
	move => n.
	have [phi phinxn]:= ((\rep_valid rep_space_R).2 (xn (n star))).
	by exists phi.
have [F Fprop]:= (choice R Rtot).
exists (F2MF F).
split; last exact: one_to_nat_dscrt.
apply/ frlzr_rlzr.
move => phi x phinx.
rewrite -phinx.
exact: (Fprop phi).
Qed.

Definition lim_rel xn x :=
	forall eps, eps > 0 -> exists N:nat, forall n:nat, (N <= n)%coq_nat -> Rabs (x - xn n) <= eps.

Lemma lim_sing:
	lim_rel \is_single_valued.
Proof.
move => xn x x' limxnx limxnx'.
apply/ cond_eq_rat => eps ineq.
have ineq': Q2R eps/(1 + 1) > 0 by lra.
move: (limxnx (Q2R eps/2) ineq') => [N prop].
move: (limxnx' (Q2R eps/2) ineq') => [M prop'].
rewrite -(Rplus_0_r x).
rewrite -(Rplus_opp_r (xn (M + N)%coq_nat)).
replace (x + (xn (M + N)%coq_nat + - xn (M + N)%coq_nat) - x')
	with ((x - xn (M + N)%coq_nat) - (x' - xn (M + N)%coq_nat)) by field.
apply triang.
replace (Q2R eps) with (Q2R eps/2 + Q2R eps/ 2) by field.
apply: Rplus_le_compat.
	by apply (prop (M + N)%coq_nat); lia.
rewrite Rabs_Ropp.
by apply (prop' (M + N)%coq_nat); lia.
Qed.

(*
Lemma lim_not_cont: ~lim_rel \has_continuous_realizer.
Proof.
move => [/= F [/= rlzr cont]].
pose xn (n: nat) := 0.
have xnc: has_cont_rlzr (F2MF xn) by apply seq_dscrt.
have xns: (F2MF xn) \is_single_valued by apply F2MF_sing.
have xnt: (F2MF xn) \is_total by apply F2MF_tot.
have yn := exist_fun (conj (conj xns xnt) xnc).
set G:= (fun (phi: one -> nat) (eps: Q) => 0%Q).
have psinx: (fun phiq => inr 0%Q) \is_name_of yn.
	rewrite /delta/=/is_fun_name/=.
	suffices: eval (U (fun _ : seq (one * nat) * Q => inr 0)) = F2MF G.
exists G.
split => [ | phi n phinn].
	split => [ | phi ev]; first	by exists (fun q => 0%Q) => eps; exists 0%nat.
	apply functional_extensionality => eps.
	move: (ev eps) => [n]; have U0: U 0 psi s eps = some (0%Q) by trivial.
	have Un: U n psi s eps = some (0%Q) by apply/ U_mon; [ | apply: U0 ]; lia.
	by rewrite Un; apply Some_inj.
replace (projT1 yn) with xn by admit.
have psifd: psi \from_dom (F2MF F) by apply/ F2MF_tot.
have [/= L Lprop]:= (cont psi 1%Q psifd).
set melt := fix melt (K: seq ((seq (one * nat) * Q))) := match K with
	| Coq.Lists.List.nil => 0%nat
	| Coq.Lists.List.cons pq K' => Nat.max (List.hd (star, 0%nat) pq.1).2 (melt K')
end.
set m := melt L.
pose x'n n := if (n <= m)%nat then 0 else 2.
have x'nc: has_cont_rlzr (F2MF x'n) by apply seq_dscrt.
have y'n := (exist (fun x=> (@has_cont_rlzr rep_space_N rep_space_R (F2MF x))) x'n x'nc).
set psi' := (fun (phiq: ((seq (one * nat))* Q)) => match phiq.1 with
	| Coq.Lists.List.nil => inl star
	| Coq.Lists.List.cons p K' => if (p.2 <= m)%nat then inr 0%Q else inr (1 +1)%Q:(one + Q)
end).
set G':= (fun (phi: one -> nat) (eps: Q) =>
	if (phi star <= m)%nat then 0%Q else (1 +1)%Q).
have psinx: psi' \is_name_of yn.
exists G'.
split => [ | phi' n' phi'nn'].
	split => [ | phi' ev'].
		exists (fun q => if (s star <= m)%nat then 0%Q else (1 +1)%Q) => eps.
Admitted.
*)