Load representations.
From mathcomp Require Import ssrnat.
Require Import Reals Lra Classical ClassicalFacts Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

(* The following is just to make the rest look nicer. *)
Local Open Scope R_scope.
Coercion IZR : Z >-> R.
Definition Q2R (q : QArith_base.Q) : R := QArith_base.Qnum q / QArith_base.QDen q.
Notation Q := QArith_base.Q.
Notation Qmake := QArith_base.Qmake.
Coercion Q2R : Q >-> R.
Coercion Pos.of_nat : nat >-> positive.
Print positive.
Fixpoint IPR (n : positive) : R := match n with
  | xH => 1
  | xO m => 2* IPR m
  | xI k => 2* IPR k +1
end.
Coercion IPR : positive >-> R.

Lemma INR_Pos_to_nat_IPR: forall n, INR( Pos.to_nat n) = IPR n.
Admitted.
Lemma pos_positive: forall n, IPR n > 0.
Admitted.
(* Todo: proof these. Am I missing something, or is the type positive unusable in its current form? *)

Definition rep_R : (positive -> Q) -> R -> Prop :=
  fun phi x => forall n, (IPR n) * Rabs(x-(phi n)) <= 1.
(* This is close to the standard definition of the chauchy representation. Usually integers
are prefered to avoid to many possible answers. I try this further down but it leads to 
extensive additional work so I gave up at some point. I also moved the error bound to the
left side of the inequality because it is better for the proofs. *)

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
  move => t.
  exists (fun n => Qmake (Int_part(t*(IPR n))) n).
  move => n.
  rewrite Rabs_pos_eq.
  - rewrite Rmult_minus_distr_l.
    rewrite -!Rmult_assoc /=.
    rewrite (INR_Pos_to_nat_IPR (n)).
    rewrite !(Rmult_comm (IPR n)).
    rewrite !Rmult_assoc.
    rewrite (Rinv_r (IPR n)).
    - rewrite !Rmult_1_r.
      apply (approx (t * (IPR n))).
    apply: Rlt_dichotomy_converse.
    right.
    apply: pos_positive.
  apply: (Rmult_le_reg_l (IPR n)).
  - apply: pos_positive.
  rewrite Rmult_minus_distr_l.
  rewrite -!Rmult_assoc /=.
  rewrite (INR_Pos_to_nat_IPR (n)).
  rewrite Rmult_0_r.
  rewrite !(Rmult_comm (IPR n)).
  rewrite Rmult_assoc.
  rewrite (Rinv_r (IPR n)).
  - rewrite Rmult_1_r.
    apply approx'.
  apply Rlt_dichotomy_converse.
  right.
  apply: pos_positive.
Qed.

Lemma cond_eq_nat : forall x y, (forall n, (IPR n) * Rabs (x - y) <= 1) -> x = y.
Admitted.

Lemma rep_R_is_sing: is_sing rep_R.
Admitted.
(* These two are Admitted here, but the proofs are carried out for the cauchy representation
below. They do not carry over easily, and I have not had time to fix that. *)

Lemma rep_R_is_rep: is_rep rep_R.
Proof.
  split.
  - exact: rep_R_is_sur.
  - exact: rep_R_is_sing.
Qed.

Canonical rep_space_R := @make_rep_space
  R
  (positive -> Q)
  (fun n => Qmake Z0 xH)
  rep_R
  rep_R_is_rep.

Lemma idiscomputable : is_computable (id : R -> R).
Proof.
  by exists (fun phi=>phi).
Qed.
(* This is a trivial example. The proof looks nice, though... The next example uses the product
construction that was introduced in the file representations.v *)

Lemma additioniscomputable : is_computable (fun x => Rplus (x.1) (x.2)).
Proof.
  Definition addition_realizer (phi : names rep_space_R * names rep_space_R) n : Q :=
    (QArith_base.Qplus (phi.1 (xO n)) (phi.2 (xO n))).
  exists addition_realizer.
  move => phi x [phi0 phi1] n.
  set r := phi.1 (xO n).
  set q := phi.2 (xO n).
  have round : (Rabs((addition_realizer phi n) -r-q) <= /2).
  rewrite /addition_realizer /=.
  rewrite /r /q.
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

Canonical Repspace_R := @Repspace
  R
  (nat->Z)
  (fun n => Z0)
  C_rep_R
  CrepRisrep.

Lemma idiscomputable : is_computable (id : R -> R).
Proof.
  by exists (fun phi=>phi).
Qed.

Open Scope Z_scope.

Definition round_4 (d : Z) : Z := ((d / 2 + 1) / 2)%Z.

Lemma rounding (d : Z): (d-2<= 4*round_4(d) <= d+2)%Z.
Proof.
  rewrite /round_4.
  Search Z.div Z.modulo.
  rewrite  (Zdiv.Z_div_mod_eq d 4); try lia.
  replace (4*(d/4)) with (d/4*2*2) by ring.
  rewrite Zdiv.Z_div_plus_full_l; try lia.
  rewrite Zplus_assoc_reverse.
  rewrite Zdiv.Z_div_plus_full_l; try lia.
  have : d mod 4 = 0 \/ d mod 4 = 1 \/ d mod 4 = 2 \/ d mod 4 = 3.
  Search Z.modulo.
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

Lemma rounding_R (d : Z) : (d-2<= 4*round_4(d) <= d+2)%R.
Admitted.

Lemma additioniscomputable : is_computable (fun x => Rplus (x.1) (x.2)).
Proof.
  Definition addition_realizer (phi : descriptions Repspace_R* descriptions Repspace_R) n : Z :=
    round_4(phi.1 (n.+2) + phi.2 (n.+2)).
  exists addition_realizer.
  move => phi x [phi0 phi1] n.
  set r := phi.1 (n.+2)/4.
  set q := phi.2 (n.+2)/4.
  have round : (Rabs((addition_realizer phi n) -r-q) <= /2).
  rewrite /addition_realizer.
  move : (rounding_R (phi.1 (n.+2) + phi.2 (n.+2))) => stufffff.
  rewrite /r /q.
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