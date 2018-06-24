(* This files proves some general Lemmas about the real numbers that are
usefull when considering computability. *)

From mathcomp Require Import all_ssreflect.
Require Import core_mf.
Require Import Qreals Reals Psatz ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import QArith.
Local Open Scope R_scope.

Section accumulation.
Definition acc P x := forall eps, eps > 0 -> exists y, P y /\ R_dist y x < eps.

Lemma cond_eq_P P x y:
	acc P 0 -> (forall z, P z -> R_dist x y <= Rabs z) -> x = y.
Proof.
move => acc prp; apply cond_eq => eps epsg0.
have [z [pz ineq]]:= acc eps epsg0.
apply /Rle_lt_trans; first by apply (prp z).
by rewrite /R_dist Rminus_0_r in ineq.
Qed.

Definition acc_f_zero_plus T (f: T -> R) := forall eps, eps > 0 -> exists t, 0 < f t < eps.

Lemma acc_f_acc T (f: T -> R):
	acc_f_zero_plus f <-> acc (fun x => codom (F2MF f) x /\ x > 0) 0.
Proof.
split => acc eps epsg0; have := acc eps epsg0.
	move => [t [g0 leps]]; exists (f t); split.
		by split; try lra; exists t.
	by rewrite /R_dist Rminus_0_r Rabs_pos_eq; lra.
move => [y [[[t <-] neq]]]; rewrite /R_dist Rminus_0_r => ineq.
exists t; split => //.
by rewrite -[f t]Rabs_pos_eq; lra.
Qed.

Lemma cond_eq_f T (f: T -> R) x y:
	acc_f_zero_plus f -> (forall z, 0 < f z -> R_dist x y <= f z) -> x = y.
Proof.
move => accu prp.
apply cond_eq => eps epsg0.
have [t [g0 ineq]]:= accu eps epsg0.
by apply/ Rle_lt_trans; first by apply /prp /g0.
Qed.

Lemma pwr2gtz m: exists n, (2^n > m)%nat.
Proof.
elim: m => [ | m [n /leP ih]]; first by exists 0%nat; apply /leP => /=; lia.
exists n.+1; apply /leP => /=; lia.
Qed.

Lemma accf_2pown: acc_f_zero_plus (fun n => /2^n).
Proof.
move => r rgt0; pose z := Z.to_nat (up (1/r)).
have [n /leP nprp]:= pwr2gtz z; have g0: 0 < 2^n by apply pow_lt; lra.
exists n; split; first by apply /Rinv_0_lt_compat /pow_lt; lra.
rewrite -[r]Rinv_involutive; try lra.
apply Rinv_lt_contravar; first by rewrite Rmult_comm; apply Rdiv_lt_0_compat;  try lra.
apply /Rlt_trans; first by have:= (archimed (1 / r)).1 => ineq; rewrite -[/r]Rmult_1_l; apply ineq.
case E: (up (1/r)) => [ | p | p] //; have pos:= (Pos2Z.pos_is_pos p); last first.
	by apply /(@Rlt_le_trans _ (IZR 0)); [apply IZR_lt; lia | apply Rlt_le].
rewrite -[Z.pos _]Z2Nat.id; try lia; rewrite -E -/z -INR_IZR_INZ.
have ->: 2 = INR 2 by trivial.
by rewrite -pow_INR; apply lt_INR => /=; lia.
Qed.

Lemma accf_Q2R_0: acc_f_zero_plus Q2R.
Proof.
move=> r rPos.
have ir_Pos : 0 < /r by apply: Rinv_0_lt_compat.
pose z := up (/ r).
have irLz : / r < IZR z by rewrite /z; have := archimed (/ r); lra.
have zPos : 0 < IZR z by lra.
pose p := Z.to_pos z.
have pE : (Z.pos p)%Z = z by rewrite Z2Pos.id //; apply: lt_0_IZR.
exists (1 # p).
rewrite /Q2R /= pE Rmult_1_l; try lra.
split; first by apply Rinv_0_lt_compat.
rewrite -(Rinv_involutive r); try lra.
by apply: Rinv_lt_contravar; try nra.
Qed.

Definition lim xn x:=
	forall eps, eps > 0 -> exists N, forall n, (N <= n)%nat -> Rabs (x - xn n) <= eps.

Lemma Uncv_lim : 	Un_cv =~= lim.
Proof.
move => xn x; split => ass eps epsg0.
	have [N Nprp]:= ass eps epsg0; exists N => n ineq.
	apply Rlt_le; rewrite Rabs_minus_sym.
	by rewrite /R_dist in Nprp; apply /Nprp/leP.
have [ | N Nprp]:= ass (eps/2); try lra; exists N => n ineq.
rewrite /R_dist Rabs_minus_sym; apply /Rle_lt_trans; first by apply /Nprp /leP.
lra.
Qed.

Definition limQ xn x :=
	forall eps, Q2R eps > 0 -> exists N, forall n, (N <= n)%nat -> Rabs (x - xn n) <= Q2R eps.

Lemma Uncv_limQ:
	Un_cv =~= limQ.
Proof.
move => xn x.
split => limxnx eps epsg0.
	have [N Nprop]:= limxnx (Q2R eps) epsg0.
	exists N => n ineq.
	have ineq': (n >= N)%coq_nat by apply /leP.
	have:= Nprop n ineq'; rewrite /R_dist.
	split_Rabs; lra.
have [qeps [qepsg0 ineq]]:= accf_Q2R_0 epsg0.
have [N Nprop]:= limxnx qeps qepsg0.
exists N => n ineq'; rewrite /R_dist.
apply /Rle_lt_trans; last exact ineq.
by rewrite Rabs_minus_sym; apply /Nprop /leP.
Qed.

Lemma lim_limQ: lim =~= limQ.
Proof. by rewrite -Uncv_lim Uncv_limQ. Qed.

Lemma triang r x y: (Rabs x) + (Rabs y) <= r -> Rabs(x + y) <= r.
Proof. by apply /Rle_trans /Rabs_triang. Qed.

Lemma lim_sing: lim \is_single_valued.
Proof.
move => xn x x' limxnx limxnx'.
apply cond_eq => eps epsg0.
have [ | N Nprop]:= limxnx (eps/3); try lra.
have [ | M Mprop]:= limxnx' (eps/3); try lra.
pose k:= maxn N M.
have -> : x - x' = x - xn k + (xn k - x') by lra.
apply /Rle_lt_trans.
	apply /triang /Rplus_le_compat; first by apply /Nprop/leq_maxl.
	rewrite Rabs_minus_sym; apply /Mprop/leq_maxr.
lra.
Qed.

Lemma limQ_sing: limQ \is_single_valued.
Proof. rewrite -lim_limQ; exact: lim_sing. Qed.

Lemma Z_tech a b : (0 < b -> a / b * b > a  - b)%Z.
Proof.
move=> Pb; rewrite {2}(Z_div_mod_eq a b); try lia.
suffices : (0 <= a mod b < b)%Z by lia.
by apply: Z_mod_lt; lia.
Qed.

Definition Int_partQ eps := ((Qnum eps)/(Z.pos (Qden eps)))%Z.
Coercion IZR : Z >-> R.

Lemma base_Int_partQ eps:
	IZR (Int_partQ eps) <= Q2R eps /\ IZR (Int_partQ eps) - Q2R eps > -1.
Proof.
have ineq: (Z.pos (Qden eps) > 0)%Z.
	suffices: (0 < Z.pos (Qden eps))%Z by lia.
	apply lt_IZR; replace (IZR (Z.pos (Qden eps))) with (IPR (Qden eps)) by trivial.
	by rewrite -INR_IPR; apply: pos_INR_nat_of_P.
rewrite /Int_partQ /Q2R.
split.
	rewrite -(Rmult_1_r (Qnum eps / Z.pos (Qden eps))%Z).
	rewrite -(Rinv_r (Z.pos (Qden eps))); last exact: IZR_nz.
	rewrite -Rmult_assoc.
	apply/ Rmult_le_compat_r => //.
		apply Rlt_le; apply Rinv_0_lt_compat.
		apply IZR_lt; lia.
	rewrite Rmult_comm -mult_IZR.
	by apply IZR_le; apply Z_mult_div_ge; lia.
have ineq': ((Qnum eps / Z.pos (Qden eps)) * (Z.pos (Qden eps)) > Qnum eps - Z.pos (Qden eps))%Z.
apply (@Z_tech (Qnum eps) (Z.pos (Qden eps))); lia.
apply Rlt_gt.
suffices ineq'': (Qnum eps - Z.pos (Qden eps)) < (Qnum eps / Z.pos (Qden eps))%Z * Z.pos (Qden eps).
	suffices:(Qnum eps * / Z.pos (Qden eps) - 1 < (Qnum eps / Z.pos (Qden eps))%Z) by lra.
	replace (Qnum eps * / Z.pos (Qden eps) - 1) with ((Qnum eps  - Z.pos (Qden eps))/ Z.pos (Qden eps)); last field.
	replace (IZR(Qnum eps / Z.pos (Qden eps))%Z) with
		((Qnum eps / Z.pos (Qden eps))%Z * Z.pos (Qden eps)/ Z.pos (Qden eps)); last field => //.
	by apply Rmult_lt_compat_r; first by apply Rinv_0_lt_compat; apply IZR_lt; lia.
	apply IZR_neq; apply Z.neg_pos_cases; right; lia.
rewrite -mult_IZR -minus_IZR.
apply IZR_lt; lia.
Qed.

Definition upQ eps:= (Int_partQ eps + 1)%Z.
Lemma archimedQ r:
	IZR (upQ r) > Q2R r /\ IZR (upQ r) - Q2R r <= 1.
Proof.
rewrite /upQ; split; have [h1 h2]:= base_Int_partQ r; rewrite plus_IZR; lra.
Qed.

Definition Cauchy_crit_eff xn:= forall n m, Rabs (xn n - xn m) <= /2^n + /2^m.

Lemma Cauchy_crit_eff_Cauchy_crit xn : Cauchy_crit_eff xn -> Cauchy_crit xn.
Proof.
move => Cauchy eps epsg0.
have [N [_ ineq]]:= accf_2pown epsg0.
exists N.+2 => n m nineq mineq.
apply /Rle_lt_trans; last exact ineq.
apply /Rle_trans.
	by apply Cauchy.
rewrite -[/2^ N]eps2.
apply /Rplus_le_compat.
	rewrite Rmult_comm -[/2]pow_1 !Rinv_pow; try lra; rewrite -Rdef_pow_add.
		rewrite -!Rinv_pow; try lra; apply Rinv_le_contravar; first by apply pow_lt; lra.
	by apply Rle_pow; try lra; lia.
rewrite Rmult_comm -[/2]pow_1 !Rinv_pow; try lra; rewrite -Rdef_pow_add.
	rewrite -!Rinv_pow; try lra; apply Rinv_le_contravar; first by apply pow_lt; lra.
by apply Rle_pow; try lra; lia.
Qed.

Lemma Cauchy_crit_eff_suff xn:
	(forall n m, (n <= m)%nat -> Rabs (xn n - xn m) <= /2^n + /2^m) -> Cauchy_crit_eff xn.
Proof.
move => ass n m.
case /orP: (leq_total n m) => ineq; first by apply ass.
by rewrite Rabs_minus_sym Rplus_comm; apply ass.
Qed.

Lemma Cauchy_crit_suff_twopown xn:
	(forall k, exists N, forall n m,  (N <= n <= m)%nat -> Rabs (xn n - xn m) <= /2^k) ->
	Cauchy_crit xn.
Proof.
move => ass eps epsg0.
have [N [g0 ineq]]:= accf_2pown epsg0.
have [M Mprp]:= ass N.
exists M => n m nineq mineq.
case/orP: (leq_total n m) => /leP ineq'; last rewrite /R_dist Rabs_minus_sym;
	apply /(Rle_lt_trans _ _ _ _ ineq) /Mprp /andP; split; apply /leP; lia.
Qed.

Definition lim_eff xn x:= forall n, Rabs (xn n - x) <= /2^n.

Lemma lim_exte_lim_eff : lim \extends lim_eff.
Proof.
move => xn x limeff eps epsg0.
have [N [g0 ineq]]:= accf_2pown epsg0.
exists N => n ineq'; rewrite Rabs_minus_sym.
apply /Rle_trans; last exact /Rlt_le /ineq.
apply /Rle_trans; first apply /limeff.
apply Rinv_le_contravar; first by apply pow_lt; lra.
by apply Rle_pow; try lra; apply /leP.
Qed.

Lemma lim_tight_lim_eff: lim \tightens lim_eff.
Proof.
apply sing_exte_tight; [exact lim_sing | exact lim_exte_lim_eff].
Qed.

Lemma Cauchy_conv xn: Cauchy_crit_eff xn <-> exists x, lim_eff xn x.
Proof.
split => [Cauchy | [x conv] n m]; last first.
	have -> : xn n - xn m = xn n - x + (x - xn m) by lra.
	apply /triang /Rplus_le_compat; first exact: conv.
	by rewrite Rabs_minus_sym; apply: conv.
have [ | x /Uncv_lim prp] := R_complete xn ; first by apply Cauchy_crit_eff_Cauchy_crit.
exists x => n.
apply le_epsilon => eps epsg0.
have [m ineq]:= accf_2pown epsg0.
have ieq: 0 < eps - /2^m by lra.
have [m' m'prp]:= prp (eps - /2^ m) ieq.
set k:= maxn m m'.
have -> : xn n - x = xn n - xn k + (xn k - x) by lra.
apply /triang.
have -> : /2 ^ n + eps = /2 ^ n + /2^ k + (eps - /2^ k) by lra.
apply Rplus_le_compat; first exact: Cauchy.
apply /Rle_trans.
	rewrite Rabs_minus_sym.
	by apply /m'prp /leq_maxr.
suff : /2^k <= /2 ^ m by lra.
apply: Rinv_le_contravar; first by apply pow_lt; lra.
apply Rle_pow; try lra.
exact /leP /leq_maxl.
Qed.

Lemma lim_eff_sing:
	lim_eff \is_single_valued.
Proof.
by apply /exte_sing; first apply/ lim_exte_lim_eff; last apply/lim_sing.
Qed.

Lemma lim_eff_Cauchy: lim_eff =~= lim \restricted_to Cauchy_crit_eff.
Proof.
move => xn x; split => [limeff | [Cauchy limx]].
	by split; [apply Cauchy_conv; exists x | apply: lim_exte_lim_eff].
have [y limy]:= (Cauchy_conv _).1 Cauchy.
by rewrite (@lim_sing xn x y); last apply lim_exte_lim_eff.
Qed.

Lemma Qnum_gt:
	forall eps: Q, (0 < eps)%Q -> (0 < Qnum eps)%Z.
Proof.
move => eps epsg0.
rewrite Zlt_Qlt/inject_Z.
have eq: eps == Qnum eps # Qden eps by trivial.
have lt: (0 * (Z.pos (Qden eps)#1) < eps * ((Z.pos (Qden eps))#1))%Q by apply Qmult_lt_compat_r.
apply Rlt_Qlt.
have:= (Qlt_Rlt (0 * (Z.pos (Qden eps) # 1)) (eps * (Z.pos (Qden eps) # 1)) (lt)).
rewrite Q2R_mult /Q2R/= mult_IZR Pos.mul_1_r !Rmult_assoc Rinv_r; last exact: IZR_nz.
by rewrite Rinv_1.
Qed.
End accumulation.
