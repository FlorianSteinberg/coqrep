(* This is example shows how to use a representation of the real numbers by means of rational
approximations to compute on the reals. Usually integers are prefered to avoid to many problems
that arise due to the possibility to use unnecessary high precission approximations. I tried
that approach but it lead to extensive additional work so I gave up at some point. I feel that
the approach in the present file is more appropriate. *)

From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions baire_space continuity.
Require Import machines oracle_machines universal_machine.
Require Import representations representation_facts.
Require Import Qreals Reals Psatz FunctionalExtensionality ClassicalChoice.
Require Import Interval.Interval_interval.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.
Import QArith.
Local Open Scope R_scope.
Coercion IZR : Z >-> R.

Definition rep_R : (Q -> Q) -> R -> Prop :=
  fun phi x => forall eps, 0 < Q2R eps-> Rabs(x-Q2R(phi eps)) <= Q2R eps.
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
rewrite /Q2R /= INR_IZR_INZ positive_nat_Z pE [1 * / _]Rmult_1_l.
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
rewrite -(eps2 (Q2R q)).
replace (Q2R q * / 2) with (Q2R (q * / (1 + 1))); last first.
	rewrite Q2R_mult Q2R_inv; last by lra.
	replace (Q2R (1 + 1)) with 2.
		by field.
	rewrite Q2R_plus.
	replace (Q2R 1) with 1 => //.
	by rewrite /Q2R/IZR /=;	field.
apply: Rplus_le_compat.
	apply: pinox.
	rewrite Q2R_div; last by lra.
	rewrite {2}/Q2R/=; lra.
replace (Rabs (r - x')) with (Rabs (x' - r)).
	apply: H.
	rewrite Q2R_div; last by lra.
	rewrite {2}/Q2R/=; lra.
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
rewrite Q2R_mult.
set eps := Q2R epsr.
rewrite Rabs_pos_eq.
	set z := Int_part(x/eps).
	replace (x - eps * Q2R (z#1)) with (eps * (x / eps - z));first last.
		rewrite /Q2R/=; field.
		by apply: Rlt_dichotomy_converse; right; rewrite /eps.
	rewrite -{3}(Rmult_1_r eps).
	apply: Rmult_le_compat_l; first by left; rewrite /eps.
	apply: (approx (x * /eps)).
apply: (Rmult_le_reg_l (/eps)).
	by apply: Rinv_0_lt_compat; rewrite /eps.
rewrite Rmult_0_r.
set z := Int_part(x/eps).
replace (/eps*(x - eps * Q2R (z#1))) with (x/eps - z);last first.
	rewrite /Q2R/=.
	field.
	by apply: Rlt_dichotomy_converse; right; rewrite /eps.
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
apply/ prec_cmpt_fun_cmpt.
by exists (fun phi => phi).
Qed.

Lemma triang r x y: (Rabs x) + (Rabs y) <= r -> Rabs(x + y) <= r.
Proof.
apply: Rle_trans.
by apply: Rabs_triang.
Qed.

Lemma Q_cmpt_elts:
	forall q: Q, (Q2R q) \is_computable_element.
Proof.
move => q.
exists (fun eps => q).
move => eps ineq.
apply/ Rbasic_fun.Rabs_le; lra.
Defined.

Lemma Rplus_prec : (fun x => Rplus (x.1) (x.2)) \is_prec_function.
Proof.
set Rplus_realizer := (fun phi eps =>
  (Qplus (phi (inl (Qdiv eps (1+1)))).1 (phi (inr (Qdiv eps (1+1)))).2)).
exists Rplus_realizer.
move => phi x phinx eps eg0.
rewrite /Rplus_realizer.
rewrite Q2R_plus.
set phi0 := (fun q => (phi (inl q)).1).
set phi1 := (fun q => (phi (inr q)).2).
set r := Q2R (phi0 (Qdiv eps (1 + 1))).
set q := Q2R (phi1 (Qdiv eps (1 + 1))).
replace (x.1 + x.2 - (r + q)) with (x.1 - r + (x.2 - q)); last first.
	field.
apply: triang.
rewrite -(eps2 (Q2R eps)).
replace ((Q2R eps)*/2) with (Q2R (eps/ (1 + 1))); last first.
	rewrite Q2R_div; last by lra.
	by rewrite {2}/Q2R/=; lra.
apply: Rplus_le_compat; apply phinx.
	rewrite Q2R_div /=; last by lra.
	by rewrite {2}/Q2R/=; lra.
rewrite Q2R_div /=; last by lra.
by rewrite {2}/Q2R/=; lra.
Defined.

Lemma Rplus_comp:
	(fun p => Rplus p.1 p.2) \is_computable_function.
Proof.
apply prec_fun_cmpt.
exact Rplus_prec.
Qed.

(* Multiplication is more involved as the precision of approximations that have to be used
depends on the size of the inputs *)
Lemma Rmult_prec : (fun x => Rmult x.1 x.2) \is_prec_function.
Proof.
set rab := (fun (phi : Q -> Q) => inject_Z(up(Rabs(Q2R(phi (1#2)))+1))).
have rab_pos: forall phi, Q2R (rab phi) >= 1.
	move => phi; rewrite /Q2R/rab/=.
	replace (/ 1) with 1 by field; rewrite Rmult_1_r; apply Rle_ge.
	apply: Rle_trans; last by	apply Rlt_le; apply archimed.
	by rewrite -{1}(Rplus_0_l 1); apply Rplus_le_compat_r; exact: Rabs_pos.
pose trunc eps := if Qlt_le_dec eps 1 then eps else 1%Q.
have ineq: forall eps, Q2R (trunc eps) <= (Q2R eps).
	by move => eps; rewrite /trunc; case: (Qlt_le_dec eps 1) => ass /=; [lra | apply Qle_Rle].
set Rmult_realizer := (fun phi eps =>
  ((phi (inl (trunc eps / (1 + 1)/(rab (fun q => (phi(inr q)).2))))).1
  *
  (phi (inr (eps / (1 + 1)/(rab (fun q => (phi(inl q) ).1))))).2))%Q.
exists Rmult_realizer.
move => phipsi [x y] [phinx psiny] eps eg0 /=.
rewrite Q2R_mult.
set phi := (fun q:Q => (phipsi (inl q)).1:Q).
rewrite -/phi/= in phinx.
set psi := (fun q:Q => (phipsi (inr q)).2:Q).
rewrite -/psi/= in psiny.
set r := Q2R (phi (trunc eps / (1 + 1) / rab psi)%Q).
set q := Q2R (psi (eps / (1 + 1) / rab phi)%Q).
rewrite /Rmult_realizer; move: Rmult_realizer => _; specialize (ineq eps).
have truncI: 0 < Q2R (trunc eps) <= 1.
	rewrite /trunc; case: (Qlt_le_dec eps 1) => /= ass; last by rewrite /Q2R/=; lra.
	split => //; apply Rlt_le; replace 1 with (Q2R 1) by by rewrite /Q2R/=; lra.
	by apply Qlt_Rlt.
have g0: 0 < Q2R (eps / (1 + 1)).
	rewrite Q2R_div; last by lra.
	rewrite {2}/Q2R/=; lra.
have rabneq: forall phi', ~ rab phi' == 0.
	move => phi' eq; move: (Qeq_eqR (rab phi') 0 eq).
	apply Rgt_not_eq; replace (Q2R 0) with 0 by by rewrite /Q2R/=; lra.
	specialize (rab_pos phi'); lra.
replace (x * y - r * q) with ((x - r) * y + r * (y - q)) by field.
apply: triang.
replace (Q2R eps) with (Q2R (eps/ (1 + 1)) + Q2R (eps/ (1 + 1))); last first.
	rewrite Q2R_div; last by lra.
	by rewrite {2 4}/Q2R/=; lra.
apply: Rplus_le_compat.
	specialize (rab_pos psi).
	rewrite Rabs_mult.
	case: (classic (y = 0)) => [eq | neq].
		apply/ Rle_trans; last apply Rlt_le;last apply: g0.
		by rewrite eq Rabs_R0; lra.
	rewrite -(Rmult_1_r (Q2R (eps / (1 + 1)))) -(Rinv_l (Rabs y)); last by split_Rabs; lra.
	rewrite -Rmult_assoc;	apply: Rmult_le_compat; [ split_Rabs | split_Rabs | | ]; try lra.
	apply/ Rle_trans; first apply phinx; last first.
		rewrite Q2R_div => //.
		apply Rmult_le_compat; [ | apply Rlt_le; apply Rinv_0_lt_compat; lra | | ].
				rewrite Q2R_div; first rewrite {2}/Q2R/=; first apply Rlt_le; lra.
			by rewrite !Q2R_div; [ | lra | lra]; apply Rmult_le_compat_r; first by rewrite /Q2R/=; lra.
		apply: Rinv_le_contravar; first	exact: Rabs_pos_lt.
		rewrite /rab {1}/Q2R/=; replace (/1) with 1 by lra; rewrite Rmult_1_r.
		apply/ Rle_trans; last apply/ Rlt_le; last apply: (archimed (Rabs (Q2R (psi (1#2)))+1)).1.
		suffices: (Rabs y -Rabs (Q2R (psi (1#2))) <= 1) by lra.
		apply/ Rle_trans; first by apply: Rabs_triang_inv.
		apply: Rle_trans; first apply: psiny; rewrite /Q2R/=; lra.
	rewrite Q2R_div => //.
	apply Rmult_gt_0_compat; last by apply Rlt_gt; apply Rinv_0_lt_compat; lra.
	apply Rlt_gt; rewrite Q2R_div; last by lra.
	rewrite {2}/Q2R/=; lra.
rewrite Rabs_mult.
case: (classic (r = 0)) => [eq | neq].
	apply/ Rle_trans; last apply Rlt_le;last apply: g0.
	by rewrite eq Rabs_R0; lra.
rewrite /Qdiv -(Rmult_1_l (Q2R (eps / (1 + 1)))).
rewrite -(Rinv_r (Rabs r)); last by split_Rabs; lra.
rewrite Rmult_assoc.
apply: Rmult_le_compat; [ split_Rabs | split_Rabs | | ]; try lra; rewrite Rmult_comm.
apply/ Rle_trans; first rewrite /q; first apply psiny; last first.
	rewrite Q2R_div => //.
	apply Rmult_le_compat_l => //; first by rewrite Q2R_div => //; apply Rlt_le; rewrite {2}/Q2R/=; lra.
	apply Rle_Rinv; first exact: Rabs_pos_lt.
		specialize (rab_pos phi); lra.
	rewrite /rab {1}/Q2R/=; replace (/1) with 1 by lra; rewrite Rmult_1_r.
	apply/ Rle_trans; last apply/ Rlt_le; last apply: (archimed (Rabs (Q2R (phi (1#2)))+1)).1.
	suffices: (Rabs r -Rabs (Q2R (phi (1#2))) <= 1) by lra.
	apply/ Rle_trans; first apply: Rabs_triang_inv.
	apply: Rle_trans.
		replace (r - Q2R (phi (1#2))) with ((r - x) - (Q2R (phi (1#2)) - x)) by field.
		apply triang.
		apply/ Rplus_le_compat.
			rewrite Rabs_minus_sym; apply phinx.
			specialize (rab_pos psi); rewrite !Q2R_div => //; rewrite {2}/Q2R/=.
			by apply Rmult_gt_0_compat; last apply Rlt_gt; last apply Rinv_0_lt_compat; lra.
		rewrite Ropp_minus_distr.
		by apply phinx; rewrite /Q2R/=; lra.
	specialize (rab_pos psi).
	rewrite !Q2R_div; [ | by lra | ] => //.
	rewrite {4}/Q2R/= {1}/Rdiv.
	replace (1 * / 2) with (/2 * 1) by lra.
	rewrite -{3 4}(Rinv_r (Q2R (rab psi))); try lra.
	rewrite -Rmult_assoc -Rmult_plus_distr_r.
	apply: Rmult_le_compat_r; first by apply Rlt_le; apply Rinv_0_lt_compat; lra.
	suffices: Q2R (trunc eps) / Q2R (1 + 1) <= Q2R (rab psi)/2 by lra.
	rewrite !/Rdiv {2}/Q2R/=; apply Rmult_le_compat; try lra.
rewrite Q2R_div => //; apply Rmult_gt_0_compat=>//; apply Rlt_gt.
apply Rinv_0_lt_compat; have:= rab_pos phi; lra.
Defined.

Lemma Rmult_cmpt:
	(fun p => Rmult p.1 p.2) \is_computable_function.
Proof. by apply prec_fun_cmpt; apply Rmult_prec. Qed.

Require Import basic_represented_spaces.

Definition lim xn x :=
	forall eps, eps > 0 -> exists N:nat, forall n:nat, (N <= n)%coq_nat -> Rabs (x - xn n) <= eps.

Lemma lim_sing:
	lim \is_single_valued.
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

Lemma lim_not_cont: ~lim \has_continuous_realizer.
Proof.
move => [/= F [/= rlzr cont]].
pose xn (n: nat):R := 0.
pose qn (p: (nat * Q)) := 0%Q.
have qnxn: @delta (rep_space_usig_prod rep_space_R) qn xn.
	move => n eps ineq; rewrite /qn /xn {1}/Q2R/=; split_Rabs; lra.
have limxn0: lim xn 0.
	move => eps ineq;	exists 0%nat.
	move => n ineq'; rewrite /xn;	split_Rabs; lra.
pose zn (eps:Q) := 0%Q.
have zn0: zn \is_name_of 0.
	move => eps ineq; rewrite {1}/Q2R/=; split_Rabs; lra.
have qnfdF: qn \from_dom F.
	have qnfd: qn \from_dom (lim o (delta (r:=rep_space_usig_prod rep_space_R))).
		exists 0;	split.
			exists xn => //.
		move => yn name.
		rewrite -(rep_sing (rep_space_usig_prod rep_space_R) qn xn yn) => //.
		by exists 0.
	have [x [[phi [Fqnphi]]] _ _]:= (rlzr qn qnfd).1.
	by exists phi.
have [L Lprop]:= (cont qn 1%Q qnfdF).
set m:= List.fold_left max (unzip1 L) 0%N.
have mprop: forall n eps, List.In (n, eps) L -> (n <= m)%nat.
	move: Lprop => _; rewrite /m; move: m => _.
	elim: L => // a L ih n eps /= lstn.
	rewrite /= in lstn.
	admit.
pose yn n := if (n <= m)%nat then 0 else 3.
pose rn (p: nat * Q) := if (p.1 <= m)%nat then 0%Q else 3#1.
have rnyn: @delta (rep_space_usig_prod rep_space_R) rn yn.
	move => n eps ineq; rewrite /rn /yn.
	case: ifP => ineq'; rewrite {1}/Q2R/=; split_Rabs; lra.
have limyn3: lim yn 3.
	move => eps ineq.
	exists (S m) => n ineq'.
	rewrite /yn.
	case: ifP; last by split_Rabs; lra.
	move  => ineq''.
	have: (n <= m)%coq_nat by apply /leP.
	lia.
have rnfdF: rn \from_dom F.
	have rnfd: rn \from_dom (lim o (delta (r:=rep_space_usig_prod rep_space_R))).
		exists 3;	split.
			exists yn => //.
		move => y'n name.
		rewrite -(rep_sing (rep_space_usig_prod rep_space_R) rn yn y'n) => //.
		by exists 3.
	have [x [[phi [Fqnphi]]] _ _]:= (rlzr rn rnfd).1.
	by exists phi.
have coin: qn \and rn \coincide_on L.
	apply /coin_lstn => [[n eps] listin].
	rewrite /qn /rn.
	case: ifP => // /= ineq.
	specialize (mprop n eps listin).
	have nineq: (~n <= m)%coq_nat by apply /leP; rewrite ineq.
	have ge:= not_le n m nineq.
	have fineq: (n <= m)%coq_nat by apply /leP.
	lia.
have [phi Frnphi ]:= rnfdF.
have [psi Fqnpsi]:= qnfdF.
have /=eq':= Lprop psi Fqnpsi rn coin phi Frnphi.
have eq: psi 1%Q == phi 1%Q by rewrite eq'.
have := Qeq_eqR (psi 1%Q) (phi 1%Q) eq.
have psin0: psi \is_name_of 0 by apply/ rlzr_val_sing; [apply lim_sing | apply rlzr | | | ].
have phin3: phi \is_name_of 3.
	by apply/ rlzr_val_sing; [apply lim_sing | apply rlzr | apply rnyn | | ].
have l01: 0 < Q2R 1 by rewrite /Q2R/=; lra.
have:= psin0 1%Q l01.
have:= phin3 1%Q l01.
rewrite {2 4}/Q2R/=.
split_Rabs; lra.
Admitted.

Definition eff_conv xn := exists x, forall n, Rabs (xn n - x) <= 1/2^n.
Definition lim_eff := lim \restricted_to eff_conv.

Lemma lim_eff_prec:
	lim_eff \is_prec.
Proof.
rewrite /is_prec/=.
Admitted.