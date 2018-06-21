From mathcomp Require Import all_ssreflect.
Require Import core_mf.
Require Import Qreals Reals Psatz ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Lemma accf_2powSn: acc_f_zero_plus (fun n => /2^(n.+1)).
Proof.
move => r rgt0; pose z := Z.to_nat (up (1/r)).
have [n /leP nprp]:= pwr2gtz z; have g0: 0 < 2^n.+1 by apply pow_lt; lra.
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

End accumulation.
