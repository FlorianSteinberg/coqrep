Require Import Reals Psatz.
Open Scope R_scope.

Lemma Rminus_eq_0 x : x - x = 0.
Proof. ring. Qed.

Lemma Rmult_minus_distr_r x y z : (x - y) * z = x * z - y * z.
Proof. ring. Qed.

Lemma pow2_sqrt x : 0 <= x -> sqrt x ^ 2 = x.
Proof. now intros x0; simpl; rewrite Rmult_1_r, sqrt_sqrt. Qed.

Local Ltac lt0 :=
  match goal with
  | |- _ => assumption
  | |- 0 < exp _ => apply exp_pos
  | |- 0 < pos _ => apply cond_pos
  | |- _ > 0 => unfold Rgt; lt0
  | |- 0 < 1 =>  apply Rlt_0_1
  | |- 0 < 2 => apply Rlt_0_2
  | |- 0 < PI => apply PI_RGT_0
  | |- _ <> 0 => apply Rgt_not_eq; lt0
  | |- 0 < Rabs _ + _ => apply (Rplus_le_lt_0_compat _ _ (Rabs_pos _)); lt0
  | |- 0 < _ * _ => apply Rmult_lt_0_compat; lt0
  | |- 0 < _ + _ => apply Rplus_lt_0_compat; lt0
  | |- 0 < Rmin _ _ => apply Rmin_glb_lt; lt0
  | |- 0 < / _ => apply Rinv_0_lt_compat; lt0
  | |- 0 < sqrt _ => apply sqrt_lt_R0; lt0
  | |- 0 < _ / _ => unfold Rdiv; apply Rmult_lt_0_compat; lt0
  | |- 0 < _ ^ _ => apply pow_lt; lt0
  | |- 0 < _ ^ 2 + _ => apply Rplus_le_lt_0_compat;[apply pow2_ge_0 | lt0]
  | |- 0 < (?x * (?x * 1))%R + _ => 
                        apply Rplus_le_lt_0_compat;[apply pow2_ge_0 | lt0]
  | |- 0 <= Rabs _ => apply Rabs_pos
  | |- _ <= _ => apply Rlt_le; lt0
  | |- _ => psatzl R
  end.

Definition arcsinh x := ln (x + sqrt (x ^ 2 + 1)).

Lemma arcsinh_sinh : forall x, arcsinh (sinh x) = x.
Proof.
intros x; unfold sinh, arcsinh.
rewrite <- exp_0, <- (Rminus_eq_0 x); unfold Rminus.
rewrite exp_plus.
match goal with |- context[sqrt ?a] => 
  replace a with (((exp x + exp(-x))/2)^2) by field
end. 
rewrite sqrt_pow2;[ | lt0].
match goal with |- context[ln ?a] => replace a with (exp x) by field end. 
rewrite ln_exp; reflexivity.
Qed.

Lemma sinh_arcsinh x : sinh (arcsinh x) = x.
Proof.
unfold sinh, arcsinh.
assert (cmp : 0 < x + sqrt (x ^ 2 + 1)).
 destruct (Rle_dec x 0).
  replace (x ^ 2) with ((-x) ^ 2) by ring.
  assert (sqrt ((- x) ^ 2) < sqrt ((-x)^2+1)).
   apply sqrt_lt_1_alt.
   split;[apply pow2_ge_0 | psatzl R].
  pattern x at 1; replace x with (- (sqrt ((- x) ^ 2))).
   assert (t:= sqrt_pos ((-x)^2)); psatzl R.
  rewrite sqrt_pow2; psatzl R.
 assert (0 < x) by psatzl R; lt0.
rewrite exp_ln;[ | assumption].
rewrite exp_Ropp, exp_ln;[ | assumption].
apply Rminus_diag_uniq; unfold Rdiv; rewrite Rmult_minus_distr_r.
assert (t: forall x y z, x - z = y -> x - y - z = 0);[ | apply t; clear t].
 intros a b c H; rewrite <- H; ring.
apply Rmult_eq_reg_l with (2 * (x + sqrt (x ^ 2 + 1)));[ | psatzl R].
field_simplify; [rewrite pow2_sqrt;[field | lt0] | lt0].
Qed.

Lemma sinh_lt : forall x y, x < y -> sinh x < sinh y.
Proof.
intros x y xy; destruct (MVT_cor2 sinh cosh x y xy) as [c [Pc _]].
 intros; apply derivable_pt_lim_sinh.
apply Rplus_lt_reg_r with (Ropp (sinh x)); rewrite Rplus_opp_r.
unfold Rminus at 1 in Pc; rewrite Pc; apply Rmult_lt_0_compat;[ | psatzl R].
unfold cosh; lt0.
Qed.

Lemma derivable_pt_lim_arcsinh :
  forall x, derivable_pt_lim arcsinh x (/sqrt (x ^ 2 + 1)).
Proof.
intros x; unfold arcsinh.
assert (0 < x + sqrt (x ^ 2 + 1)).
 destruct (Rle_dec x 0);[ | assert (0 < x) by psatzl R; lt0].
 replace (x ^ 2) with ((-x) ^ 2) by ring.
 assert (sqrt ((- x) ^ 2) < sqrt ((-x)^2+1)).
  apply sqrt_lt_1_alt.
  split;[apply pow2_ge_0 | psatzl R].
 pattern x at 1; replace x with (- (sqrt ((- x) ^ 2))).
  assert (t:= sqrt_pos ((-x)^2)); psatzl R.
 rewrite sqrt_pow2; psatzl R.
replace (/sqrt (x ^ 2 + 1)) with
 (/(x + sqrt (x ^ 2 + 1)) * 
    (1 + (/(2 * sqrt (x ^ 2 + 1)) * (INR 2 * x ^ 1 + 0)))).
apply (derivable_pt_lim_comp (fun x => x + sqrt (x ^ 2 + 1)) ln).
 apply (derivable_pt_lim_plus).
  apply derivable_pt_lim_id.
   apply (derivable_pt_lim_comp (fun x => x ^ 2 + 1) sqrt x).
    apply derivable_pt_lim_plus.
     apply derivable_pt_lim_pow.
    apply derivable_pt_lim_const.
   apply derivable_pt_lim_sqrt; lt0.
  apply derivable_pt_lim_ln; lt0.
 replace (INR 2 * x ^ 1 + 0) with (2 * x) by (simpl; ring).
replace (1 + / (2 * sqrt (x ^ 2 + 1)) * (2 * x)) with
 (((sqrt (x ^ 2 + 1) + x))/sqrt (x ^ 2 + 1)) by (field; lt0).
apply Rmult_eq_reg_l with (x + sqrt (x ^ 2 + 1));[ | lt0].
 rewrite <- Rmult_assoc, Rinv_r;[field | ]; lt0.
Qed.

Lemma arcsinh_lt : forall x y, x < y -> arcsinh x < arcsinh y.
Proof.
intros x y xy.
case (Rle_dec (arcsinh y) (arcsinh x));[ | psatzl R].
intros abs; case (Rlt_not_le _ _ xy).
rewrite <- (sinh_arcsinh y), <- (sinh_arcsinh x).
destruct abs as [lt | q];[ | rewrite q; psatzl R].
apply Rlt_le, sinh_lt; assumption.
Qed.

Lemma arcsinh_le : forall x y, x <= y -> arcsinh x <= arcsinh y.
Proof.
intros x y [xy | xqy].
 apply Rlt_le, arcsinh_lt; assumption.
rewrite xqy; apply Rle_refl.
Qed.

Lemma arcsinh_0 : arcsinh 0 = 0.
Proof.
 unfold arcsinh; rewrite pow_ne_zero, !Rplus_0_l, sqrt_1, ln_1;
  [reflexivity | discriminate].
Qed.

Lemma equiv_ln_arcsinh :
  forall f, (forall n, 0 < f n) ->
  Un_cv f 0 ->
  Un_cv (fun n => ln (/f n)/arcsinh (/f n)) 1.
Proof.
intros f fp cvf.
assert (ctv : continuity_pt Rinv 1) by (reg; lt0).
intros eps ep.
destruct (ctv eps ep) as [eps' [ep' Pe']].
destruct (cvf 1 Rlt_0_1) as [N1 Pn1].
destruct (cvf (exp (-(ln 3/eps'))) (exp_pos _)) as [N2 Pn2].
exists (N1 + N2)%nat; intros n nN.
assert (nN1 : (N1 <= n)%nat) by lia.
assert (nN2 : (N2 <= n)%nat) by lia.
assert (0 < f n) by auto.
assert (1 < / f n).
 generalize (Pn1 n nN1); unfold R_dist; rewrite Rminus_0_r.
 rewrite Rabs_right; intros; try lt0.
 rewrite <- Rinv_1; apply Rinv_lt_contravar;[lt0 | tauto].
assert (0 < ln (/ f n)) by (rewrite <- ln_1; apply ln_increasing; lt0).
assert (0 < arcsinh (/ f n)).
 rewrite <- arcsinh_0; apply arcsinh_lt; psatzl R.
assert (1 < (/ f n) ^ 2).
 simpl; rewrite Rmult_1_r, <- (Rmult_1_r 1).
 apply Rmult_le_0_lt_compat; lt0.
assert (0 < sqrt ((/ f n) ^ 2 + 1)) by lt0.
assert (/f n < /f n + sqrt ((/f n)^2 + 1)) by psatzl R.
assert (sqrt ((/f n) ^ 2 + 1) < sqrt (2 ^ 2 * (/ f n) ^ 2)).
 apply sqrt_lt_1_alt; psatzl R.
assert (/f n + sqrt ((/f n) ^ 2 + 1) < 3 * / f n).
replace (3 * / f n) with (/ f n + 2 * / f n) by ring.
 apply Rplus_lt_compat_l.
 rewrite <- (sqrt_pow2 2);[ | lt0]. 
 pattern (/ f n) at 2; rewrite <- (sqrt_pow2 (/ f n)); try lt0.
 rewrite <- sqrt_mult; lt0.
replace (ln (/ f n) / arcsinh (/ f n)) with (/( (arcsinh (/ f n))/ln (/f n)))
 by (field;split; lt0).
rewrite <- Rinv_1.
destruct (Req_EM_T ((arcsinh (/ f n) / ln (/ f n))) 1) as [q | nq].
 rewrite q, R_dist_eq; assumption.
apply Pe';split;[unfold D_x, no_cond; auto | ].
simpl; unfold R_dist, arcsinh, Rdiv; rewrite Rabs_pos_eq.
 apply Rlt_trans with (ln (3 * / f n)/ln(/f n) - 1).
  apply Rplus_lt_compat_r; apply Rmult_lt_compat_r;[lt0 | ].
  apply ln_increasing.
   rewrite Rplus_comm; lt0.
  assumption.
 unfold Rdiv, Rminus; rewrite ln_mult, Rmult_plus_distr_r, Rinv_r; try lt0.
 rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
 apply Rmult_lt_reg_r with (/eps' * ln (/ f n));[lt0 | ].
 rewrite <- (Rmult_assoc eps'), Rinv_r, Rmult_1_l;[ | lt0].
 rewrite Rmult_assoc, (Rmult_comm (/ ln (/ f n))), Rmult_assoc.
 rewrite Rinv_r, Rmult_1_r;[ | lt0].
 rewrite ln_Rinv, <- (Ropp_involutive (_ * _));[ | lt0]; apply Ropp_lt_contravar.
 rewrite <- (ln_exp (- _)); apply ln_increasing; try lt0.
 generalize (Pn2 _ nN2); unfold R_dist; rewrite Rminus_0_r; intros main.
 now rewrite Rabs_right in main; lt0.
assert (1 <= ln (/ f n + sqrt ((/ f n) ^ 2 + 1)) * / ln (/ f n));[ | psatzl R].
apply Rmult_le_reg_r with (ln (/ f n));[lt0 | ].
unfold Rdiv; rewrite Rmult_1_l, Rmult_assoc, Rinv_l, Rmult_1_r;[ | lt0].
apply Rlt_le, ln_increasing; lt0.
Qed.
