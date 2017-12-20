Load representations.

From mathcomp Require Import ssrnat.
Require Import Reals Lra Classical ClassicalFacts Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Local Open Scope Z_scope.
(* This is some auxilliary stuff whose proof breaks if an R_scope is opened.
Ignore them for now *)
Definition round_4 (d : Z) : Z := ((d / 2 + 1) / 2)%Z.
Lemma rounding (d : Z): (d-2<= 4*round_4(d) <= d+2)%Z.
Proof.
  rewrite /round_4.
  rewrite  (Zdiv.Z_div_mod_eq d 4); try lia.
  replace (4*(d/4)) with (d/4*2*2) by ring.
  rewrite Zdiv.Z_div_plus_full_l; try lia.
  rewrite Zplus_assoc_reverse.
  rewrite Zdiv.Z_div_plus_full_l; try lia.
  have : d mod 4 = 0 \/ d mod 4 = 1 \/ d mod 4 = 2 \/ d mod 4 = 3.
  have : 0 <= d mod 4 < 4.
  apply: Zdiv.Z_mod_lt; lia.
  lia.
  (case; [idtac|case;[idtac| case]]) => -> ;
  rewrite [(_/_ + _)/2] /=.
  change (1/2) with 0.
  lia.
  change (1/2) with 0.
  lia.
  change (2/2) with 1.
  lia.
  change (2/2) with 1.
  lia.
Qed.
Import QArith.
Local Open Scope R_scope.

(* \begin{syntacticsuggar} *)
Fixpoint P2R n := match n with
  | xH => 1
  | xO m => 2* P2R m
  | xI k => 2* P2R k + 1
end.
(* It eludes my why this function is not provided under the name IPR in the standard Library *)
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
Coercion Q2R : Q >-> R.
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
(* \end{usefulllemmas} *)

Definition rep_R : (Q -> Q) -> R -> Prop :=
  fun phi x => forall eps, (0 < eps)%Q -> Rabs(x-(phi eps)) <= eps.
(* This is close to the standard definition of the chauchy representation. Usually integers
are prefered to avoid to many possible answers. I try this further down but it leads to 
extensive additional work so I gave up at some point. I also moved the error bound to the
left side of the inequality because it is better for the proofs. I'll probbably change the
type of names to Q -> Q soon. Most difficulties are encountered because of translations
between different types not working properly, so it seems good to avoid the use of to many
different types. Also I feel like this is the most natural formulation of the Cauchy
representation. (Compare for instance "bounded time computation for metric spaces and Banach
spaces" by Matthias and me.) *)

(* Lemma INR_Pos_to_nat_P2R: forall n, INR( Pos.to_nat n) = P2R n.
Admitted.
Lemma pos_positive: forall n, P2R n > 0.
Admitted.
Todo: proof these. Am I missing something, or is the type positive unusable in its current form? *)


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

Lemma rep_R_is_sur: is_sur rep_R.
Proof.
  move => x.
  exists (fun eps => Qmult eps (Qmake(Int_part(x/eps)) xH)).
  move => eps eg0.
  rewrite mul_Q2R.
  rewrite Q2R_make1.
  rewrite Rabs_pos_eq.
  - rewrite -{1}(Rmult_1_l x).
    rewrite -(Rinv_r (eps)).
    rewrite Rmult_assoc.
    rewrite -{5}(Rmult_1_r eps).
    rewrite -(Rmult_minus_distr_l eps).
    - apply: (Rmult_le_compat_l (eps)).
      apply: le0_Q2R.
      by apply: Qlt_le_weak.
    rewrite (Rmult_comm (/eps)).
    rewrite /Rdiv.
    apply (approx (x * /eps)).
    apply: Rlt_dichotomy_converse.
    right.
    by apply: lt0_Q2R.
  apply: (Rmult_le_reg_l (/eps));last first.
  rewrite Rmult_0_r.
  rewrite Rmult_minus_distr_l.
  rewrite -Rmult_assoc.
  Search _ "Rinv".
  rewrite -(Rinv_l_sym eps).
  - rewrite Rmult_1_l.
    rewrite (Rmult_comm (/eps)).
    rewrite /Rdiv.
    apply (approx' (x * /eps)).
    apply: Rlt_dichotomy_converse.
    right.
    by apply: lt0_Q2R.
  apply : Rinv_0_lt_compat.
  by apply: lt0_Q2R.
Qed.

Lemma rep_R_is_sing: is_sing rep_R.
Admitted.

(* This is Admitted here. The proof of this statement for the more traditional cauchy representation
is carried out below. The proofs do not carry over easily but simplify a lot (compare the proof of the
surjectivity to that of the traditional cauchy representation) *)

Lemma rep_R_is_rep: is_rep rep_R.
Proof.
  split.
  - exact: rep_R_is_sur.
  - exact: rep_R_is_sing.
Qed.

Canonical rep_space_R := @make_rep_space
  R
  (Q -> Q)
  (fun n => Qmake Z0 xH)
  rep_R
  rep_R_is_rep.

Lemma id_is_computable : is_computable (id : R -> R).
Proof.
  by exists (fun phi=>phi).
Qed.
(* This is a trivial example. The proof looks nice, though... The next example uses the product
construction that was introduced in the file representations.v *)

(* Lemma cond_eq_nat : forall x y, (forall n, (P2R n) * Rabs (x - y) <= 1) -> x = y.
Admitted. *)
(* This will be needed in the next proof. Since the proof is not finished I don't need it yet. *)

Lemma Rplus_is_computable : is_computable (fun x => Rplus (x.1) (x.2)).
Proof.
  Definition Rplus_realizer (phi : names rep_space_R * names rep_space_R) eps : Q :=
    (Qplus (phi.1 (Qmult (Qmake 1 2) eps)) (phi.2(Qmult (Qmake 1 2) eps))).
  exists Rplus_realizer.
  move => phi x [phi0 phi1] eps eg0.
  set r := phi.1 (Qmult (Qmake 1 2) eps).
  set q := phi.2 (Qmult (Qmake 1 2) eps).
  have round : (Rabs((Rplus_realizer phi eps) -r-q) <= /2).
  rewrite /Rplus_realizer /=.
  rewrite /r /q.
Admitted.
(*
  rewrite plus_IZR in stufffff.
  split_Rabs; try lra.
  admit.
  have rapprox : Rabs(x.1 - r/2^n) <= 2^n.+2.
  move : phi0.
  rewrite /(is_name).
  Search _ "Int_part".
  admit.
  have qapprox : Rabs(x.2 - q/2^n) <= 2^n.+2.
  admit.
  set sum := Rabs( x.1 + x.2 - (r+q)/2^n) + Rabs(addition_realizer phi n -r-q)/2^n.
  have add : sum <= /2^n.
  admit.
  suff esti: Rabs(x.1 + x.2 -addition_realizer phi n /2^n) <= sum.
  apply : (Rle_trans _ sum) => //.
  by rewrite /Rdiv Rmult_1_l.
  admit.
*)

(* Frome here on I try to work with the traditional Cauchy representation used by people who
do complexity theory based on the TTE approach but who don't want to talk about signed digits.
I do not suggest trying to follow the proofs, they are pretty technical and I want to move
away from this. Some of the proofs where provided by Laurent Thiery. *)

Definition C_rep_R : (nat -> Z) -> R -> Prop := fun phi x => forall n,
  Rabs(x-(phi n) / 2^n) <= (1/2^n).

Lemma cond_eq_nat : forall x y, (forall n, Rabs (x - y) <= / 2 ^ n) -> x = y.
Proof.
move=> x y H.
have [// | H1] : x = y \/ Rabs (x - y) > 0.
  split_Rabs; lra.
have H2 : Rabs (x - y) <= / 2.
  have := H 1%N.
  simpl.
  lra.
have H3 : 2 <= / Rabs (x - y).
  replace 2 with (/(/2))%R by field.
  apply Rinv_le_contravar; lra.
have H4 := ln_lt_2.
pose z := - ln (Rabs (x - y)) / ln 2.
have Pz : 0 <= z.
  replace 0 with (0 * /(ln 2)) by ring.
  apply Rmult_le_compat; try lra.
  suff : 0 < / ln 2 by lra.
  apply Rinv_0_lt_compat; try lra.
  replace 0 with (-0) by ring.
  rewrite - ln_1.
  apply Ropp_le_contravar.
  suff : ln (Rabs (x - y)) < ln 1 by lra.
  apply ln_increasing; lra.
pose u := Int_part  z.
pose n := Z.to_nat (1 + u).
suff : / 2 ^ n < Rabs (x - y).
  have := H n; lra.
replace (Rabs (x - y)) with (/ /(Rabs (x - y)))%R by (field; lra).
apply Rinv_1_lt_contravar.
  replace 1 with (/ / 1)%R by field.
  apply Rinv_le_contravar; lra.
apply ln_lt_inv; try lra.
  apply pow_lt; lra.
rewrite -Rpower_pow; try lra.
rewrite ln_exp.
rewrite INR_IZR_INZ.
rewrite ln_Rinv; try lra.
rewrite Z2Nat.id; last first.
  apply le_0_IZR.
  rewrite  plus_IZR.
  rewrite [IZR 1]/=.
  have := base_Int_part z.
  rewrite /u; lra.
rewrite  plus_IZR.
rewrite [IZR 1]/=.
replace (- ln (Rabs (x - y))) with (z * ln 2); last first.
  rewrite /z; field; lra.
have := base_Int_part z.
rewrite /u.
nra.
Qed.

Lemma CrepRisrep : is_rep C_rep_R.
Proof.
  split.
  - move => t.
    exists (fun n => Int_part(t*2^n)).
    move => n.
    set m := 2^n.
    rewrite Rabs_pos_eq.
    - apply: (Rmult_le_reg_l m).
      - apply: pow_lt.
        lra.
      rewrite Rmult_minus_distr_l -!Rmult_assoc !(Rmult_comm m) !Rmult_assoc.
      rewrite (Rinv_r m).
      - rewrite !Rmult_1_r.
        apply (approx (t * m)).
      apply Rlt_dichotomy_converse.
      right.
      apply: pow_lt.
      lra.
    apply: (Rmult_le_reg_l m).
    - apply: pow_lt.
      lra.
    rewrite Rmult_minus_distr_l -!Rmult_assoc Rmult_0_r
      !(Rmult_comm m) Rmult_assoc.
    rewrite (Rinv_r m).
    - rewrite Rmult_1_r.
      apply approx'.
    apply Rlt_dichotomy_converse.
    right.
    apply: pow_lt.
    lra.
  - move => phi t t' [noft noft'].
    apply: cond_eq_nat => n.
    move: Rle_trans => trans.
    apply: (trans _ (1/2^(n.+1) + 1/2^(n.+1)) (/2^n)).
    - rewrite -(Rplus_minus (phi (n.+1)/(2^n.+1)) t').
      rewrite /Rminus Ropp_plus_distr -Rplus_assoc.
      apply: (Rle_trans _ (Rabs(t + - ((phi ((n.+1))) / 2 ^ (n.+1)))
        + Rabs(- (t' + - ((phi ((n.+1))) / 2 ^ (n.+1)))))).
      - apply: Rabs_triang.
      apply: (Rplus_le_compat
      (Rabs (t + - ((phi ((n.+1))) / 2 ^ (n.+1)))) (1/2^(n.+1))
      (Rabs (- (t' + - ((phi ((n.+1))) / 2 ^ (n.+1))))) (1/2^(n.+1))).
      - by move: (noft ((n.+1))).
      - rewrite Rabs_Ropp.
        by move: (noft' ((n.+1))).
    rewrite /=.
    rewrite (Rmult_comm 2) /Rdiv Rinv_mult_distr.
    - rewrite Rmult_1_l eps2 -(Rmult_1_l (/ 2 ^ n)).
      by apply Rle_refl.
    apply: Rgt_not_eq.
    move: (pow_lt 2 n).
    lra.
  lra.
Qed.

Definition traditional_rep_space_R := @make_rep_space
  R
  (nat->Z)
  (fun n => Z0)
  C_rep_R
  CrepRisrep.

Notation Rc := traditional_rep_space_R.

Lemma idiscomputable : is_computable (id : Rc -> Rc).
Proof.
  by exists (fun phi=>phi).
Qed.

Lemma rounding_R (d : Z) : (d-2<= 4*round_4(d) <= d+2)%R.
Admitted.

Lemma additioniscomputable : @is_computable _ Rc (fun (x : (rep_space_prod Rc Rc)) => Rplus (x.1) (x.2)).
(* This would look a lot less complicated if there wouldn't be the "standard" way to compute on R by means
of rep_space_R, i.e. the representation rep_R instead of C_rep_R. *)
Proof.
  Definition addition_realizer (phi : names Rc* names Rc) n : Z :=
    round_4(phi.1 (n.+2) + phi.2 (n.+2)).
  exists addition_realizer.
  move => phi x [phi0 phi1] n.
  set r := phi.1 (n.+2)/4.
  set q := phi.2 (n.+2)/4.
  have round : Rabs((addition_realizer phi n) -r-q) <= /2.
  rewrite /addition_realizer.
  move : (rounding_R (phi.1 (n.+2) + phi.2 (n.+2))) => stufffff.
  rewrite /r /q.
  rewrite plus_IZR in stufffff.
  split_Rabs; try lra.
  (* From here on it is more an outline of how the proof should proceed. I am unsure I want to put more work into
  this as I feel it is an overly complicated setting to work in. This is why I decided to change to a simpler
  representation. *)
  have rapprox : Rabs(x.1 - r/2^n) <= 2^n.+2.
  move : phi0.
  admit.
  have qapprox : Rabs(x.2 - q/2^n) <= 2^n.+2.
  admit.
  set sum := (Rabs( x.1 + x.2 - (r+q)/2^n) + Rabs(addition_realizer phi n -r-q)/2^n)%R.
  have add : sum <= /2^n.
  admit.
  suff esti: (Rabs(x.1 + x.2 -addition_realizer phi n /2^n) <= sum)%R.
  apply : (Rle_trans _ sum) => //.
  by rewrite /Rdiv Rmult_1_l.
Admitted.