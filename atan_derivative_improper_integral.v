(* This file was tested with coq 8.5.1 and coquelicot 2.1.1 *)

Require Import Reals Coquelicot.Coquelicot Fourier Psatz.

Lemma lim_atan_p_infty :
  filterlim atan (Rbar_locally p_infty) (at_left (PI/2)).
Proof.
assert (0 < PI) by (assert (t := PI2_RGT_0); psatzl R).
intros S [ep Pep].
set (e' := Rmin (PI/2) ep).
assert (0 < e') by now apply Rmin_glb_lt; destruct ep; auto; psatzl R.
assert (e' <= PI/2) by apply Rmin_l.
exists (tan (PI/2 - e')); intros x Px.
assert (atan x < PI/2) by (destruct (atan_bound x); psatzl R).
apply Pep;[|psatzl R].
change (Rabs (atan x - PI/2) < ep).
rewrite Rabs_left, Ropp_minus_distr;[| psatzl R].
apply Rlt_le_trans with (PI / 2 - atan (tan (PI / 2 - e'))).
  now apply Rplus_lt_compat_l, Ropp_lt_contravar, atan_increasing.
replace (atan (tan (PI / 2 - e'))) with (PI / 2 - e').
  now ring_simplify; apply Rmin_r.
apply tan_is_inj;[psatzl R | apply atan_bound | now rewrite atan_right_inv].
Qed.

Lemma lim_atan_m_infty :
  filterlim atan (Rbar_locally m_infty) (at_right (-PI/2)).
Proof.
apply filterlim_ext with (fun x => - (atan (- x))).
  now intros; rewrite atan_opp, Ropp_involutive.
apply (filterlim_comp _ _ _ (fun x => atan (- x)) Ropp _ (at_left (PI/2))).
  apply (filterlim_comp _ _ _ Ropp atan _ (Rbar_locally p_infty)).
    now apply filterlim_Rbar_opp.
  now apply lim_atan_p_infty.
replace (- PI / 2) with (- (PI / 2)) by field.
apply filterlim_Ropp_left.
Qed.

Lemma atan_left_inv x : -PI / 2 < x < PI / 2 -> atan (tan x) = x.
Proof.
intros [intx1 intx2].
destruct (atan_bound (tan x)).
destruct (Rtotal_order (atan (tan x)) x) as [abs | [ it | abs]]; auto;
  apply tan_increasing in abs; try fourier; rewrite atan_right_inv in abs;
  fourier.
Qed.

Lemma atan_lim_pinfty : Lim atan p_infty = PI/2.
Proof. 
assert (t := PI2_RGT_0).
apply is_lim_unique; intros P [eps Peps].
assert (ep2 : 0 < Rmin eps (PI/4)).
  apply Rmin_glb_lt;[apply cond_pos | fourier].
set (eps' := mkposreal _ ep2).
assert (eps' < PI / 2).
  unfold eps'; simpl.
  apply Rle_lt_trans with (PI/4).
    now apply Rmin_r.
  fourier.
assert (eps' <= eps).
  now unfold eps'; simpl; apply Rmin_l.
assert (0 < eps') by apply cond_pos.
exists (tan (PI / 2 - eps')); intros x cx.
apply Peps. change (Rabs (atan x -PI/2) < eps).
  rewrite Rabs_left; cycle 1.
  destruct (atan_bound x); fourier.
enough (PI / 2 - eps' < atan x) by fourier.
rewrite <- (atan_left_inv (PI/2 - eps')); cycle 1.
  now split; psatzl R.
now apply atan_increasing.
Qed.

Lemma atan_lim_minfty : Lim atan m_infty = -PI/2.
Proof. 
assert (t := PI2_RGT_0).
apply is_lim_unique; intros P [eps Peps].
assert (ep2 : 0 < Rmin eps (PI/4)).
  apply Rmin_glb_lt;[apply cond_pos | fourier].
set (eps' := mkposreal _ ep2).
assert (eps' < PI / 2).
  unfold eps'; simpl.
  apply Rle_lt_trans with (PI/4).
    now apply Rmin_r.
  fourier.
assert (eps' <= eps).
  now unfold eps'; simpl; apply Rmin_l.
assert (0 < eps') by apply cond_pos.
exists (tan (-PI / 2 + eps')); intros x cx.
apply Peps; change (Rabs (atan x - -PI/2) < eps).
  rewrite Rabs_right; cycle 1.
  destruct (atan_bound x); fourier.
enough (atan x < -PI / 2 + eps') by fourier.
rewrite <- (atan_left_inv (-PI/2 + eps')); cycle 1.
  now split; psatzl R.
now apply atan_increasing.
Qed.

Lemma integral_atan_comp_scal m : 0 < m ->
   is_RInt_gen (fun x => /m * /((x / m) ^ 2 + 1)) 
       (Rbar_locally m_infty) (Rbar_locally p_infty) PI.
Proof.
(* assert (tmp := PI2_RGT_0). *)
intros m0.
assert (is_derive_atan_scal : forall x,  
           is_derive (fun x => atan (x / m)) x (/ m * /((x/m)^2 + 1))).
  intros x; auto_derive; auto; field.
  split; apply Rgt_not_eq; auto; apply Rplus_le_lt_0_compat.
    now apply pow2_ge_0.
  now apply pow2_gt_0, Rgt_not_eq.
intros P [eps Peps].
(* assert (ep2 : 0 < Rmin eps (PI/2)).
  apply Rmin_glb_lt;[apply cond_pos | psatzl R].
assert (eps' := mkposreal _ ep2).
*)
assert (atle : at_left (PI/2) (ball (PI/2) (pos_div_2 eps))).
  now exists (pos_div_2 eps); intros; tauto.
assert (atri : at_right (-PI/2) (ball (-PI/2) (pos_div_2 eps))).
  now exists (pos_div_2 eps); intros; tauto.
assert (H0 := lim_atan_p_infty _ atle).
assert (H0' := lim_atan_m_infty _ atri).
assert (abs' : 0 < / m) by now apply Rinv_0_lt_compat.
assert (H1 : filterlim (fun x => x / m) (Rbar_locally p_infty)
                (Rbar_locally p_infty)).
  replace (Rbar_locally p_infty) with (Rbar_locally (Rbar_mult p_infty (/ m))) at 2.
    now apply filterlim_Rbar_mult_r.
  apply f_equal; simpl; case (Rle_dec 0 (/ m)).
    intros r; case (Rle_lt_or_eq_dec 0 (/ m) r); auto.
    now intros abs; rewrite <- abs in abs'; case (Rlt_irrefl 0).
  now intros abs; case abs; apply Rlt_le.
assert (H2 : filterlim (fun x => x / m) (Rbar_locally m_infty)
                (Rbar_locally m_infty)).
  replace (Rbar_locally m_infty) with (Rbar_locally (Rbar_mult m_infty (/ m))) at 2.
    now apply filterlim_Rbar_mult_r.
  apply f_equal; simpl; case (Rle_dec 0 (/ m)).
    intros r; case (Rle_lt_or_eq_dec 0 (/ m) r); auto.
    now intros abs; rewrite <- abs in abs'; case (Rlt_irrefl 0).
  now intros abs; case abs; apply Rlt_le.
assert (t := filterlim_comp R R R (fun x => x / m) atan (Rbar_locally p_infty)
              (Rbar_locally p_infty) (at_left (PI/2)) H1 lim_atan_p_infty).
assert (t' := filterlim_comp R R R (fun x => x / m) atan (Rbar_locally m_infty)
              (Rbar_locally m_infty) (at_right (-PI/2)) H2 lim_atan_m_infty ).
specialize (t _ atle).
specialize (t' _ atri).
unfold filtermapi, filtermap in t, t' |- *.
apply (Filter_prod _ _ _ _ _ t' t).
intros x y; exists (atan (y/m) - atan (x/m)); split.
  apply (is_RInt_derive (fun x => atan (x / m))).
    intros z _; exact (is_derive_atan_scal z).
  intros z _; apply (ex_derive_continuous (fun x1 => /m * / ((x1 / m) ^ 2 + 1))).
  auto_derive; change ((z / m) ^ 2 + 1 <> 0).
  now apply Rgt_not_eq, Rplus_le_lt_0_compat;
           [apply pow2_ge_0 | apply Rlt_0_1].
apply Peps.
change (Rabs ((atan (y / m) - atan (x / m)) - PI) < eps).
replace ((atan (y / m) - atan (x / m)) - PI) with
    ((atan (y / m) - PI / 2) - (atan (x / m) + PI / 2)) by field.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
apply Rplus_lt_compat.
  exact H3.
rewrite <- Rabs_Ropp, !Ropp_plus_distr, Ropp_involutive, <- Ropp_div.
exact H.
Qed.

Lemma atan_derivative_improper_integral :
  is_RInt_gen (fun x => /(x ^ 2 + 1))
     (Rbar_locally m_infty) (Rbar_locally p_infty) PI.
Proof.
apply is_RInt_gen_ext with (fun x =>  /1 * /((x/1)^2 + 1)).
  exists (Rgt 0) (Rlt 0); try (exists 0; intros; psatzl R).
  intros x y _ _ z _; rewrite Rdiv_1, Rinv_1, Rmult_1_l; reflexivity.
apply integral_atan_comp_scal; psatzl R.
Qed.
