(* This file contains attempts to make the traditional Cauchy representation used by people who
do complexity theory based on the TTE approach but who don't want to talk about signed digits work.
It turns out to be a pain and I moved to using rationals to approximate real numbers in the better
example file "example_approximating_reals_with_rationals.v". Some of the proofs here
were provided by Laurent Thery. *)

Load representations.
From mathcomp Require Import ssrnat.
Require Import Reals Lra Classical ClassicalFacts Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Local Open Scope Z_scope.

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