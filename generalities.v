Require Import Reals Coquelicot.Coquelicot Fourier Psatz.
Require Import filter_Rlt atan_derivative_improper_integral.
Require Import arcsinh.
Require Import Interval.Interval_tactic.
Import mathcomp.ssreflect.ssreflect.

Hint Mode ProperFilter' - + : typeclass_instances.

Ltac lt0 :=
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

(* TODO : move to coquelicot. *)
Lemma filter_prod_le {T : Type} (F G F' G' : (T -> Prop) -> Prop) :
  filter_le F F' -> filter_le G G' -> filter_le (filter_prod F G)
    (filter_prod F' G').
Proof.  now intros FF GG S [S1 S2 FS GS Imp]; exists S1 S2; auto. Qed.

Lemma is_RInt_gen_filter_le {T : NormedModule R_AbsRing}
  F G F' G' {FF : Filter F} {FG : Filter G}
  {FF' : Filter F'} {FG' : Filter G'} (f : R -> T) v :
  filter_le F' F -> filter_le G' G -> is_RInt_gen f F G v ->
  is_RInt_gen f F' G' v.
Proof.
intros lef leg intf P PP; unfold filtermapi.
now apply (filter_prod_le _ _ _ _ lef leg), intf.
Qed.

Lemma is_RInt_gen_comp {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa}
  {FFb : Filter Fb} (f : R -> R) (dg g : R -> R) l :
  filter_prod Fa Fb (fun p =>
      forall y, Rmin (fst p) (snd p) <= y <= Rmax (fst p) (snd p) ->
             continuous f (g y) /\
             is_derive g y (dg y) /\ continuous dg y) ->
  is_RInt_gen f (filtermap g Fa) (filtermap g Fb) l ->
  is_RInt_gen (fun x => scal (dg x) (f (g x))) Fa Fb l.
Proof.
intros dp intf P PP.
destruct dp as [S1 S2 FS1 FS2 dp].
destruct (intf P PP) as [S S' FS FS' fp1].
exists (fun x => S (g x) /\ S1 x) (fun x => S' (g x) /\ S2 x);
      try now apply filter_and; auto.
intros x y [sgx s1x] [sgy s2y]; simpl.
exists (RInt f (g x) (g y)); split.
  destruct (fp1 (g x) (g y)); try tauto.
  apply (is_RInt_comp f g dg).
     intros z zcond. 
     now destruct (dp x y s1x s2y z); auto.
  intros z zcond.
  now destruct (dp x y s1x s2y z); auto.
destruct (fp1 (g x) (g y) sgx sgy) as [v [isint Pv]]; simpl in isint.
now rewrite -> (is_RInt_unique _ _ _ _ isint).
Qed.

Lemma is_RInt_gen_equiv F G F' G' (f : R -> R) v:
  (forall s, F s <-> F' s) -> (forall s, G s <-> G' s) ->
  is_RInt_gen f F G v -> is_RInt_gen f F' G' v.
Proof.
intros eqF eqG intf P PP'; unfold filtermapi.
assert (tmp := filter_prod_le F' G' F G); unfold filter_le in tmp; apply tmp.
    now intros A; rewrite eqF.
  now intros A; rewrite eqG.
now apply (intf P PP').
Qed.

Lemma ex_RInt_gen_unique
  (F G : (R -> Prop) -> Prop) {FF : ProperFilter F}
  {FG : ProperFilter G} (f : R -> R) :
  ex_RInt_gen f F G -> exists ! v, is_RInt_gen f F G v.
Proof.
intros [v Pv]; exists (RInt_gen f F G); unfold unique.
rewrite -> (is_RInt_gen_unique _ _ Pv) at 1; split;[assumption | ].
now intros v' Pv'; rewrite -> (is_RInt_gen_unique _ _ Pv').
Qed.

(* TODO : move to standard. *)
Lemma inv_sqrt x : 0 < x -> / sqrt x = sqrt (/ x).
Proof.
intros x0.
assert (sqrt x <> 0) by (apply Rgt_not_eq; lt0).
apply Rmult_eq_reg_r with (sqrt x); auto.
rewrite Rinv_l; auto.
rewrite <- sqrt_mult_alt; try lt0.
rewrite -> Rinv_l, sqrt_1; auto with real.
Qed.

(* TOD0 : move to standard. *)
Lemma sqrt_pow_2 x : 0 <= x -> sqrt x ^ 2 = x.
Proof. now intros x0; simpl; rewrite -> Rmult_1_r, sqrt_sqrt. Qed.

Lemma ints : 0 < /sqrt 2 < 1.
Proof. split; interval. Qed.

(* standard *)
Lemma CVU_derivable :
  forall f f' g g' c r,
   CVU f' g' c r ->
   (forall x, Boule c r x -> Un_cv (fun n => f n x) (g x)) ->
   (forall n x, Boule c r x -> derivable_pt_lim (f n) x (f' n x)) ->
   forall x, Boule c r x -> derivable_pt_lim g x (g' x).
Proof.
intros f f' g g' c d cvu cvp dff' x bx.
set (rho_ :=
       fun n y =>
           match Req_EM_T y x with
              left _ => f' n x
           |right _ => ((f n y - f n x)/ (y - x)) end).
set (rho := fun y =>
               match Req_EM_T y x with
                 left _ => g' x
               | right _ => (g y - g x)/(y - x) end).
assert (ctrho : forall n z, Boule c d z -> continuity_pt (rho_ n) z).
 intros n z bz.
 destruct (Req_EM_T x z) as [xz | xnz].
  rewrite <- xz.
  intros eps' ep'.
  destruct (dff' n x bx eps' ep') as [alp Pa].
  exists (pos alp);split;[apply cond_pos | ].
  intros z'; unfold rho_, D_x, dist, R_met; simpl; intros [[_ xnz'] dxz'].
   destruct (Req_EM_T z' x) as [abs | _].
    case xnz'; symmetry; exact abs.
   destruct (Req_EM_T x x) as [_ | abs];[ | case abs; reflexivity].
  pattern z' at 1; replace z' with (x + (z' - x)) by ring.
  apply Pa;[psatzl R | exact dxz'].
 destruct (Ball_in_inter c c d d z bz bz) as [delta Pd].
 assert (dz :  0 < Rmin delta (Rabs (z - x))).
  apply Rmin_glb_lt;[apply cond_pos | apply Rabs_pos_lt; psatzl R].
 assert (t' : forall y : R,
      R_dist y z < Rmin delta (Rabs (z - x)) ->
      (fun z : R => (f n z - f n x) / (z - x)) y = rho_ n y).
  intros y dyz; unfold rho_; destruct (Req_EM_T y x) as [xy | xny].
   rewrite xy in dyz.
   destruct (Rle_dec  delta (Rabs (z - x))).
    rewrite -> Rmin_left, R_dist_sym in dyz; unfold R_dist in dyz; psatz R.
   rewrite -> Rmin_right, R_dist_sym in dyz; unfold R_dist in dyz; psatzl R.
  reflexivity.
 apply (continuity_pt_ext_loc (fun z => (f n z - f n x)/(z - x))).
 exists (mkposreal _ dz); exact t'.
 reg;[ | psatzl R].
 apply derivable_continuous_pt; eapply exist.
 apply dff'; assumption.
assert (CVU rho_ rho c d ).
 intros eps ep.
 assert (ep8 : 0 < eps/8) by psatzl R.
 destruct (cvu _ ep8) as [N Pn1].
 assert (cauchy1 : forall n p, (N <= n)%nat -> (N <= p)%nat ->
           forall z, Boule c d z -> Rabs (f' n z - f' p z) < eps/4).
  intros n p nN pN z bz; replace (eps/4) with (eps/8 + eps/8) by field.
  rewrite <- Rabs_Ropp.
  replace (-(f' n z - f' p z)) with (g' z - f' n z - (g' z - f' p z)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _); rewrite Rabs_Ropp.
  apply Rplus_lt_compat; apply Pn1; assumption.
 assert (step_2 : forall n p, (N <= n)%nat -> (N <= p)%nat ->
         forall y, Boule c d y -> x <> y ->
         Rabs ((f n y - f n x)/(y - x) - (f p y - f p x)/(y - x)) < eps/4).
  intros n p nN pN y b_y xny.
  assert (mm0 : (Rmin x y = x /\ Rmax x y = y) \/
                (Rmin x y = y /\ Rmax x y = x)).
   destruct (Rle_dec x y).
    rewrite -> Rmin_left, Rmax_right; psatzl R.
   now rewrite -> Rmin_right, Rmax_left; psatzl R.
  assert (mm : Rmin x y < Rmax x y).
   destruct mm0 as [[q1 q2] | [q1 q2]]; generalize (Rmin_Rmax x y).
   now rewrite -> q1, q2; intros; psatzl R.
   now psatzl R.
  assert (dm : forall z, Rmin x y <= z <= Rmax x y ->
            derivable_pt_lim (fun x => f n x - f p x) z (f' n z - f' p z)).
   intros z intz; rewrite <- is_derive_Reals; apply: is_derive_minus.
    rewrite is_derive_Reals.
    apply dff'; apply Boule_convex with (Rmin x y) (Rmax x y);
      destruct mm0 as [[q1 q2] | [q1 q2]]; revert intz; rewrite -> ?q1, ?q2; intros;
     try assumption.
   rewrite is_derive_Reals.
   apply dff'; apply Boule_convex with (Rmin x y) (Rmax x y);
      destruct mm0 as [[q1 q2] | [q1 q2]]; revert intz; rewrite -> ?q1, ?q2;
    intros;
     try assumption.

  replace ((f n y - f n x) / (y - x) - (f p y - f p x) / (y - x))
    with (((f n y - f p y) - (f n x - f p x))/(y - x)) by (field; psatzl R).
  destruct (MVT_cor2 (fun x => f n x - f p x) (fun x => f' n x - f' p x)
             (Rmin x y) (Rmax x y) mm dm) as [z [Pz inz]].
  destruct mm0 as [[q1 q2] | [q1 q2]].
   replace ((f n y - f p y - (f n x - f p x))/(y - x)) with
    ((f n (Rmax x y) - f p (Rmax x y) - (f  n (Rmin x y) - f p (Rmin x y)))/
      (Rmax x y - Rmin x y)) by (rewrite -> q1, q2; reflexivity).
   unfold Rdiv; rewrite -> Pz, Rmult_assoc, Rinv_r, Rmult_1_r.
    apply cauchy1; auto.
    apply Boule_convex with (Rmin x y) (Rmax x y);
      revert inz; rewrite -> ?q1, ?q2; intros;
     assumption || psatzl R.
   rewrite -> q1, q2; psatzl R.
  replace ((f n y - f p y - (f n x - f p x))/(y - x)) with
    ((f n (Rmax x y) - f p (Rmax x y) - (f  n (Rmin x y) - f p (Rmin x y)))/
      (Rmax x y - Rmin x y)).
   unfold Rdiv; rewrite -> Pz, Rmult_assoc, Rinv_r, Rmult_1_r.
    apply cauchy1; auto.
    apply Boule_convex with (Rmin x y) (Rmax x y);
     revert inz; rewrite -> ?q1, ?q2; intros;
    assumption || psatzl R.
   rewrite -> q1, q2; psatzl R.
  rewrite -> q1, q2; field; psatzl R.
 assert (unif_ac :
  forall n p, (N <= n)%nat -> (N <= p)%nat ->
     forall y, Boule c d y ->
       Rabs (rho_ n y - rho_ p y) <= eps/2).
  intros n p nN pN y b_y.
  destruct (Req_dec x y) as [xy | xny].
   destruct (Ball_in_inter c c d d x bx bx) as [delta Pdelta].
   destruct (ctrho n y b_y _ ep8) as [d' [dp Pd]].
   destruct (ctrho p y b_y _ ep8) as [d2 [dp2 Pd2]].
   assert (0 < (Rmin (Rmin d' d2) delta)/2) by lt0.
   apply Rle_trans with (1 := R_dist_tri _ _ (rho_ n (y + Rmin (Rmin d' d2) delta/2))).
   replace (eps/2) with (eps/8 + (eps/4 + eps/8)) by field.
   apply Rplus_le_compat.
    rewrite R_dist_sym; apply Rlt_le, Pd;split;[split;[exact I | psatzl R] | ].
    simpl; unfold R_dist.
    unfold Rminus; rewrite -> (Rplus_comm y), Rplus_assoc, Rplus_opp_r, Rplus_0_r.
    rewrite Rabs_pos_eq;[ | psatzl R].
    apply Rlt_le_trans with (Rmin (Rmin d' d2) delta);[psatzl R | ].
    apply Rle_trans with (Rmin d' d2); apply Rmin_l.
   apply Rle_trans with (1 := R_dist_tri _ _ (rho_ p (y + Rmin (Rmin d' d2) delta/2))).
   apply Rplus_le_compat.
    apply Rlt_le.
     replace (rho_ n (y + Rmin (Rmin d' d2) delta / 2)) with
          ((f n (y + Rmin (Rmin d' d2) delta / 2) - f n x)/
            ((y + Rmin (Rmin d' d2) delta / 2) - x)).
     replace (rho_ p (y + Rmin (Rmin d' d2) delta / 2)) with
          ((f p (y + Rmin (Rmin d' d2) delta / 2) - f p x)/
             ((y + Rmin (Rmin d' d2) delta / 2) - x)).
      apply step_2; auto; try psatzl R.
      assert (0 < pos delta) by (apply cond_pos).
      apply Boule_convex with y (y + delta/2).
        assumption.
       destruct (Pdelta (y + delta/2)); auto.
       rewrite xy; unfold Boule; rewrite Rabs_pos_eq; try psatzl R; auto.
      split; try psatzl R.
      apply Rplus_le_compat_l, Rmult_le_compat_r;[lt0 | apply Rmin_r].
     unfold rho_.
     destruct (Req_EM_T (y + Rmin (Rmin d' d2) delta/2) x);psatzl R.
    unfold rho_.
    destruct (Req_EM_T (y + Rmin (Rmin d' d2) delta / 2) x); psatzl R.
   apply Rlt_le, Pd2; split;[split;[exact I | psatzl R] | ].
   simpl; unfold R_dist.
   unfold Rminus; rewrite -> (Rplus_comm y), Rplus_assoc, Rplus_opp_r, Rplus_0_r.
   rewrite Rabs_pos_eq;[ | psatzl R].
   apply Rlt_le_trans with (Rmin (Rmin d' d2) delta); [psatzl R |].
   apply Rle_trans with (Rmin d' d2).
    solve[apply Rmin_l].
   solve[apply Rmin_r].
  apply Rlt_le, Rlt_le_trans with (eps/4);[ | psatzl R].
  unfold rho_; destruct (Req_EM_T y x); solve[auto].
 assert (unif_ac' : forall p, (N <= p)%nat ->
           forall y, Boule c d y -> Rabs (rho y - rho_ p y) < eps).
  assert (cvrho : forall y, Boule c d y -> Un_cv (fun n => rho_ n y) (rho y)).
   intros y b_y; unfold rho_, rho; destruct (Req_EM_T y x).
    intros eps' ep'; destruct (cvu eps' ep') as [N2 Pn2].
    exists N2; intros n nN2; rewrite R_dist_sym; apply Pn2; assumption.
   apply CV_mult.
    apply CV_minus.
     apply cvp; assumption.
    apply cvp; assumption.
   intros eps' ep'; simpl; exists 0%nat; intros; rewrite R_dist_eq; assumption.
  intros p pN y b_y.
  replace eps with (eps/2 + eps/2) by field.
  assert (ep2 : 0 < eps/2) by psatzl R.
  destruct (cvrho y b_y _ ep2) as [N2 Pn2].
  apply Rle_lt_trans with (1 := R_dist_tri _ _ (rho_ (max N N2) y)).
  apply Rplus_lt_le_compat.
   solve[rewrite R_dist_sym; apply Pn2, Max.le_max_r].
  apply unif_ac; auto; solve [apply Max.le_max_l].
 exists N; intros; apply unif_ac'; solve[auto].
intros eps ep.
destruct (CVU_continuity _ _ _ _ H ctrho x bx eps ep) as [delta [dp Pd]].
exists (mkposreal _ dp); intros h hn0 dh.
replace ((g (x + h) - g x) / h) with (rho (x + h)).
 replace (g' x) with (rho x).
  apply Pd; unfold D_x, no_cond;split;[split;[auto | psatzl R] | ].
  simpl; unfold R_dist; replace (x + h - x) with h by ring; exact dh.
 unfold rho; destruct (Req_EM_T x x) as [ _ | abs];[ | case abs]; reflexivity.
unfold rho; destruct (Req_EM_T (x + h) x) as [abs | _];[psatzl R | ].
replace (x + h - x) with h by ring; reflexivity.
Qed.

Lemma ball_Rabs x y e : ball x e y <-> Rabs (y - x) < e.
Proof. intros; tauto. Qed.

Lemma cv_div2 a : is_lim_seq (fun n => a / 2 ^ n) 0.
Proof.
apply is_lim_seq_mult with a 0.
    now apply is_lim_seq_const.
  apply (is_lim_seq_ext (fun n => (/2) ^ n)).
    now symmetry; apply Rinv_pow; lt0.
apply is_lim_seq_geom; rewrite Rabs_right; lt0.
now unfold is_Rbar_mult; simpl; rewrite Rmult_0_r.
Qed.


Lemma filterlim_sqrt_0 : filterlim sqrt (at_right 0) (at_right 0).
Proof.
intros P [eps peps].
assert (ep2 : 0 < eps * eps) by (destruct eps; simpl; lt0).
exists (mkposreal _ ep2); intros y bay y0.
assert (0 < sqrt y) by lt0; apply peps; auto.
change (Rabs (sqrt y - 0) < eps); rewrite -> Rabs_right, Rminus_0_r; try lt0.
replace (pos eps) with (sqrt (eps * eps)); [ |  now rewrite sqrt_square; lt0].
apply sqrt_lt_1_alt; split;[lt0 | ].
change (Rabs (y - 0) < eps * eps) in bay; revert bay.
now rewrite -> Rabs_right, Rminus_0_r; lt0.
Qed.

Lemma int_arcsinh x :
  0 < x -> RInt (fun y => / sqrt (y ^ 2 + x ^ 2)) 0 (sqrt x) =
           arcsinh (/ sqrt x).
Proof.
intros x0; apply is_RInt_unique.
assert (s0 : 0 < sqrt x) by lt0.
assert (heq  : forall y,  /sqrt (y ^ 2 + x ^ 2) =
                   / x * /sqrt ((y / x) ^ 2 + 1)).
intros y; replace (y ^ 2 + x ^ 2) with (x ^ 2 * ((y / x) ^ 2 + 1))
   by (field; lt0).
  now rewrite -> sqrt_mult, sqrt_pow2; try lt0; field; split; lt0.
apply (is_RInt_ext (fun y => / x * / sqrt ((y / x) ^ 2 + 1))).
  now intros; rewrite heq.
evar_last.
  apply: (is_RInt_comp (fun t => / sqrt (t ^ 2 + 1)) (fun y => y / x)
          (fun _ => / x)).
    now intros; apply: ex_derive_continuous; auto_derive; repeat split; lt0.
  now intros z _; split;[auto_derive; lt0 | apply continuous_const].
lazy beta; replace (sqrt x / x) with (/ sqrt x); cycle 1.
  now rewrite <- (sqrt_sqrt x) at 3; try lt0; field; lt0.
replace (0 / x) with 0 by (unfold Rdiv; ring).
rewrite <- (Rminus_0_r (arcsinh _)); rewrite <- arcsinh_0 at 2.
apply is_RInt_unique. apply (is_RInt_derive arcsinh).
  now intros z intz; rewrite is_derive_Reals; apply derivable_pt_lim_arcsinh.
now intros; apply: ex_derive_continuous; auto_derive; repeat split; lt0.
Qed.

Lemma equiv_trans F {FF : Filter F} (f g h : R -> R) :
  F (fun x => g x <> 0) -> F (fun x => h x <> 0) ->
  filterlim (fun x => f x / g x) F (locally 1) ->
  filterlim (fun x => g x / h x) F (locally 1) ->
  filterlim (fun x => f x / h x) F (locally 1).
Proof.
intros g0 h0 fg gh P [eps Peps].
set eps' := Rmin eps 1.
assert (ep' : 0 < eps').
  now apply Rmin_pos;[destruct eps; simpl; assumption | lt0].
assert (ep4 : 0 < eps' / 4) by lt0.
assert (ep1 : eps' <= 1) by now unfold eps'; apply Rmin_r.
assert (fg4 := fg _ (locally_ball _ (mkposreal _ ep4))); simpl in fg4.
assert (gh4 := gh _ (locally_ball _ (mkposreal _ ep4))); simpl in gh4.
unfold filtermap in fg4, gh4;
  assert (fh4 := filter_and _ _ g0
                  (filter_and _ _ h0 (filter_and _ _ fg4 gh4))).
apply filter_imp with (2 := fh4); intros x cx; apply Peps.
change (Rabs (f x / h x - 1) < eps).
apply Rlt_le_trans with eps'; [ | apply Rmin_l].
replace (f x / h x - 1) with ( (f x / g x - 1) + (f x / g x) * (g x / h x - 1));
  cycle 1.
  field; tauto.
replace eps' with (eps'/4 + 3 / 4 * eps') by field.
apply Rle_lt_trans with (1 := Rabs_triang _ _); apply Rplus_lt_compat.
  change (ball 1 (eps' / 4) (f x / g x)); tauto.
apply Rlt_le_trans with (3 * (eps' / 4)); [ | psatzl R].
rewrite Rabs_mult; apply Rmult_le_0_lt_compat; cycle 3.
      change (ball 1 (eps' / 4) (g x / h x)); tauto.
    now apply Rabs_pos.
  now apply Rabs_pos.
replace (f x / g x) with ((f x / g x - 1) + 1) by ring.
change 3 with (1 + 2).
apply Rle_lt_trans with (1 := Rabs_triang _ _); apply Rplus_lt_compat; cycle 1.
  now rewrite Rabs_right; lt0.
apply Rlt_trans with (eps' / 4).
  change (ball 1 (eps' / 4) (f x / g x)); tauto.
now psatzl R.
Qed.

Lemma ln_arcinh_equiv_infty :
  filterlim (fun x => arcsinh x / ln x)
       (Rbar_locally p_infty) (locally 1).
Proof.
assert (gt1 : Rbar_locally p_infty (Rlt 1)) by (now exists 1).
intros P [eps Peps].
set (delta := Rmax (exp (ln 3 / eps)) 1).
exists delta; intros x px; apply Peps.
assert (x1 : 1 < x).
  now apply Rle_lt_trans with (2 := px); unfold delta; apply Rmax_r.
assert (0 < sqrt (x ^ 2 + 1)) by lt0.
assert (0 < ln x).
  now rewrite <- ln_1; apply ln_increasing; auto; psatzl R.
change (Rabs (arcsinh x / ln x - 1) < eps).
rewrite Rabs_right; cycle 1.
  apply Rle_ge, Raux.Rle_0_minus.
  apply Rmult_le_reg_r with (ln x); auto.
  unfold Rdiv; rewrite -> Rmult_1_l, Rmult_assoc, Rinv_l, Rmult_1_r; cycle 1.
    now psatzl R.
  unfold arcsinh; apply Rlt_le, ln_increasing;[psatzl R | ].
  now psatzl R.
apply Rlt_trans with (ln (3 * x) / ln x - 1); cycle 1.
  apply Rmult_lt_reg_r with (ln x); auto; unfold Rdiv.
  rewrite -> Rmult_minus_distr_r, Rmult_1_l, Rmult_assoc, Rinv_l; try psatzl R.
  rewrite -> Rmult_1_r, ln_mult; try psatzl R.
  replace (ln 3 + ln x - ln x) with (ln 3) by ring.
  apply Rmult_lt_reg_l with (/ eps).
    now destruct eps; simpl; lt0.
  rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l;[ | destruct eps; simpl; lt0].
  rewrite <- (ln_exp (_ * _)), Rmult_comm; apply ln_increasing.
    now apply exp_pos.
  now apply Rle_lt_trans with (2 := px), Rmax_l.
apply Rplus_lt_compat_r, Rmult_lt_compat_r;[lt0 | ].
apply ln_increasing;[lt0 | ].
assert (1 < 3 * x ^ 2).
  apply Rle_lt_trans with (x ^ 2).
    replace 1 with (1 ^ 2) at 1 by ring.
    now apply pow_incr; psatzl R.
  assert (0 < x ^ 2) by lt0; psatzl R.
apply Rlt_le_trans with (x + sqrt (x ^ 2 + 3 * x ^ 2)).
  now apply Rplus_lt_compat_l, sqrt_lt_1; lt0.
replace (x ^ 2 + 3 * x ^ 2) with ((2 * x) ^ 2) by ring.
rewrite sqrt_pow2;[psatzl R | lt0].
Qed.

(* standard *)
Lemma sqrt_lt : forall x, 1 < x -> sqrt x < x.
Proof.
intros x x1.
 assert (x0 : 0 < x) by (apply Rlt_trans with (1 := Rlt_0_1)(2 := x1)).
 assert (s0 : 0 < sqrt x) by (apply sqrt_lt_R0; assumption).
 pattern x at 2; rewrite <- sqrt_sqrt;[|apply Rlt_le; assumption].
 pattern (sqrt x) at 1; rewrite <- Rmult_1_l.
 apply Rmult_lt_compat_r;[assumption | ].
 rewrite <- sqrt_1; apply sqrt_lt_1_alt;split;[apply Rlt_le, Rlt_0_1|assumption].
Qed.

Lemma small_taylor_lagrange2 :
  forall f f1 f2 x z, x < z ->
    (forall y, x < y < z -> is_derive f y (f1 y)) ->
    (forall y, x < y < z -> is_derive f1 y (f2 y)) ->
    forall u v, x < u < v -> v < z ->
    exists zeta, u < zeta < v /\
    f v = f u + f1 u * (v - u) + f2 zeta * (v - u)^2/2.
Proof.
intros f f1 f2 x z xz d1 d2 u v xuv vz.
set (delta := Rmin (u - x) (z - v)).
assert (delta0 : 0 < delta).
 unfold delta; apply Rmin_glb_lt; psatzl R.
assert (delta <= u - x) by apply Rmin_l.
assert (delta <= z - v) by apply Rmin_r.
assert (dn : forall y, u <= y <= v ->
             forall k, (k <= 2)%nat -> ex_derive_n f k y).
 intros y xyz [ | [ | [ | k]]]; simpl.
    now trivial.
   intros _; exists (f1 y); apply d1; psatzl R.
  intros _; apply (ex_derive_ext_loc f1).
   exists (mkposreal _ delta0); intros t int; symmetry.
   apply is_derive_unique, d1.
   apply ball_Rabs in int; apply Rabs_def2 in int; simpl in int.
   now unfold minus, plus, opp in int; simpl in int; psatzl R.
  now exists (f2 y); apply d2; psatzl R.
 now lia.
assert (uv : u < v) by psatzl R.
destruct (Taylor_Lagrange f 1 u v uv dn) as [zeta [inzeta qq]].
exists zeta; split; [assumption | rewrite qq].
simpl; replace (1 / 1) with 1 by field; rewrite !Rmult_1_l; rewrite !Rmult_1_r.
replace (Derive (fun y => Derive (fun z => f z) y) zeta) with (f2 zeta).
  replace (Derive (fun y => f y) u) with (f1 u).
    field.
  now symmetry; apply is_derive_unique, d1; psatzl R.
symmetry; apply is_derive_unique.
apply (is_derive_ext_loc f1).
  exists (mkposreal _ delta0); simpl; intros t int.
  apply ball_Rabs in int; apply Rabs_def2 in int; simpl in int.
  unfold minus, plus, opp in int; simpl in int.
  now symmetry; apply is_derive_unique, d1; psatzl R.
apply d2; psatzl R.
Qed.

Lemma Rpower_Rinv x y : 0 < x -> Rpower (/ x) y = / (Rpower x y).
Proof.
intros x0; rewrite <- (Rpower_1 x) at 1; auto; rewrite <- Rpower_Ropp.
now rewrite -> Rpower_mult, <- Ropp_mult_distr_l, Rmult_1_l, Rpower_Ropp.
Qed.

Lemma gt1_imp_sqrt_lt x : 1 < x -> sqrt x < x.
Proof.
intros x1; set (y := x - 1); replace x with (y + 1) by (unfold y; ring).
rewrite <- (sqrt_pow2 (y + 1)) at 2; [ | unfold y; psatzl R].
apply sqrt_lt_1; try (unfold y; lt0).
now rewrite <- (Rmult_1_r (y + 1)) at 1; simpl; apply Rmult_lt_compat_l;
  unfold y; lt0.
Qed.

Lemma is_RInt_gen_at_right_at_point (f : R -> R) (a : R) F {FF : ProperFilter F}
  v :
  locally a (continuous f) -> is_RInt_gen f (at_right a) F v ->
  is_RInt_gen f (at_point a) F v.
Proof.
intros [delta1 pd1].
destruct (pd1 a (ball_center a delta1)
          (ball (f a) (mkposreal _ Rlt_0_1)) (locally_ball _ _)) as
    [delta2 Pd2].
intros intf.
set (M := Rabs (f a) + 1).
assert (M0 : 0 < M) by (assert (t:= Rabs_pos (f a)); unfold M; fourier).
assert (close : forall y, y <> a -> ball a delta2 y -> Rabs (f y) < M).
  intros y ay b_y; unfold M.
  replace (f y) with (f a + (f y - f a)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  now apply Rplus_lt_compat_l, Pd2; auto.
assert (atrd1 : at_right a (ball a delta1)) by (exists delta1; tauto).
assert (exrint_close : forall a', ball a delta1 a' -> ex_RInt f a a').
  intros a' baa'.
  apply (ex_RInt_continuous f); intros z pz; apply pd1.
  destruct (Rle_dec a a') as [aa' | a'a].
    rewrite -> Rmin_left, Rmax_right in pz; auto.
    change (Rabs (z - a) < delta1).
    rewrite Rabs_right; cycle 1.
      destruct pz; fourier.
    destruct pz; apply Rle_lt_trans with (a' - a); try fourier.
    rewrite <- (Rabs_right (a' - a)); try fourier.
    tauto.
  change (Rabs (z - a) < delta1).
  apply Rnot_le_lt in a'a.
  destruct (Rle_dec a z) as [az | za].
    rewrite -> Rmin_right, Rmax_left in pz; destruct pz; try fourier.
    rewrite Rabs_right; try fourier.
    case delta1; intros; simpl; fourier.
  apply Rnot_le_lt in za.
  rewrite -> Rmin_right, Rmax_left in pz; try fourier.
  rewrite Rabs_left; [ | fourier].
  destruct pz; apply Rle_lt_trans with (a - a'); try fourier.
  rewrite <- (Rabs_right (a - a')); try fourier.
  now change (ball a' delta1 a); apply ball_sym; tauto.
intros P [eps Peps].
assert (pre_ep2 : 0 < eps / 2 * /M).
  apply Rmult_lt_0_compat;[ | now apply Rinv_0_lt_compat].
  now destruct eps; simpl; fourier.
set (ep2 := mkposreal _ pre_ep2).
destruct (intf (ball v (pos_div_2 eps))) as [Q R FQ FR vfi'].
  now apply locally_ball.
exists (eq a) R; auto.
  now easy.
intros x y ax Ry; simpl; rewrite <- ax; clear ax x.
assert (atrd2 : at_right a (ball a delta2)) by (exists delta2; tauto).
assert (atre2 : at_right a (ball a ep2)) by (exists ep2; tauto).
destruct (filter_ex _ (filter_and _ _ atrd1 (filter_and _ _ atrd2
                          (filter_and _ _ FQ atre2)))) as
      [a' Pa'].
assert (ex_RInt f a a') by (apply exrint_close; tauto).
exists (RInt f a y); split; cycle 1.
  apply Peps.
  replace (pos eps) with (eps/2 + M * (eps / 2 * / M)); cycle 1.
    now field; apply Rgt_not_eq.
  apply ball_triangle with (RInt f a' y).
    destruct (vfi' a' y) as [a'y Pa'y]; try tauto.
    now rewrite (is_RInt_unique _ _ _ _ (proj1 Pa'y)); tauto.
  assert (ex_RInt f a' y).
   destruct (vfi' a' y) as [a'y Pa'y]; try tauto; exists a'y; tauto.
  change (Rabs (RInt f a y - RInt f a' y) < M * (eps / 2 * / M)).
  apply Rle_lt_trans with (RInt (fun x => Rabs (f x)) (Rmin a a') (Rmax a a')).
    replace (RInt f a y - RInt f a' y) with (RInt f a a'); cycle 1.
      apply Rplus_eq_reg_r with (RInt f a' y).
      assert (tmp := RInt_Chasles f a a' y); change plus with Rplus in tmp.
      (* BUG: need to figure out how to make ring work without the Rplus_0_r. *)
      now rewrite -> tmp;[symmetry; ring | | ]; auto.
    destruct (Rle_dec a a') as [aa' | a'a].
      rewrite -> Rmin_left, Rmax_right; try fourier.
      apply abs_RInt_le; assumption.
    apply Rnot_le_lt in a'a.
    rewrite <- (opp_RInt_swap f), Rabs_Ropp, Rmin_right, Rmax_left; try fourier; cycle 1.
      now apply ex_RInt_swap.
    apply abs_RInt_le;[ apply Rlt_le | apply ex_RInt_swap]; assumption.
  apply Rle_lt_trans with (RInt (fun _ => M) (Rmin a a') (Rmax a a')).
  apply RInt_le.
          now apply Rminmax.
        apply (ex_RInt_continuous (fun x => Rabs (f x))).
        rewrite -> Rmin_left, Rmax_right; try apply Rminmax.
        intros z pz; apply continuous_comp;[ | now apply continuous_Rabs].
        apply pd1, Rle_lt_trans with (Rabs (a' - a));[ | tauto].
        unfold abs, minus, plus, opp; simpl.
        destruct (Rle_dec a a') as [aa' | a'a].
          now rewrite -> Rmin_left, Rmax_right in pz; destruct pz;
            try rewrite !Rabs_right; fourier.
        rewrite -> Rmin_right, Rmax_left in pz; destruct pz;
          apply Rnot_le_lt in a'a;
          try rewrite (Rabs_left (a' - a)); try fourier.
        destruct (Req_dec z a) as [za | nza].
          rewrite -> za,Rplus_opp_r, Rabs_R0; fourier.
        rewrite Rabs_left; try fourier.
        now apply Rnot_le_lt; intros abs; case nza; apply Rle_antisym; fourier.
      now apply ex_RInt_const.
    intros z pz; apply Rlt_le, close.
      destruct (Rle_dec a a') as [aa' | a'a].
        rewrite -> Rmin_left, Rmax_right in pz; destruct pz; try fourier.
        now apply Rgt_not_eq; assumption.
      rewrite -> Rmin_right, Rmax_left in pz; destruct pz;
      apply Rnot_le_lt in a'a; try fourier.
      now apply Rlt_not_eq; assumption.
    apply Rlt_trans with (Rabs (a' - a));[ | tauto].
    unfold abs, minus, plus, opp; simpl.
    destruct (Rle_dec a a') as [aa' | a'a].
      now rewrite -> Rmin_left, Rmax_right in pz; destruct pz;
        try rewrite !Rabs_right; fourier.
    rewrite -> Rmin_right, Rmax_left in pz; destruct pz;
      try rewrite (Rabs_left (a' - a)); apply Rnot_le_lt in a'a; try fourier.
    destruct (Req_dec z a) as [za | nza].
      now rewrite -> za,Rplus_opp_r, Rabs_R0; fourier.
    now rewrite Rabs_left; fourier.
  rewrite -> RInt_const, Rmult_comm.
  apply Rmult_lt_compat_l;[fourier | ].
  destruct (Rle_dec a a') as [aa' | a'a].
    rewrite -> Rmax_right, Rmin_left; try fourier.
    now rewrite <- (Rabs_right (a' - a));[tauto | fourier].
  rewrite -> Rmax_left, Rmin_right; apply Rnot_le_lt in a'a ; try fourier.
  replace (a - a') with (- (a' - a)) by ring.
  now rewrite <- (Rabs_left (a' - a)); try fourier; tauto.
apply (RInt_correct f).
apply (ex_RInt_Chasles f a a' y); auto.
now destruct (vfi' a' y) as [a'y pa'y]; try tauto; exists a'y.
Qed.
