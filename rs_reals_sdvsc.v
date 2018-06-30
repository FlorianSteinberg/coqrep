From mathcomp Require Import all_ssreflect all_algebra.
Require Import all_rs rs_reals rs_reals_sdreals rs_reals_creals Rstruct under.
Require Import Reals Qreals Psatz ClassicalChoice.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope R_scope.

Section sdreals_to_creals.
Definition sd_to_c (sds: names rs_reals_sdreals.rep_space_R) eps := (inject_Z (lprj sds star) + (inject_Z (SDs2Zn (rprj sds) (Pos_size (Qden eps))))/(Qpower (2#1) (Z.of_nat (Pos_size (Qden eps)))))%Q.

Lemma Q2R_IZR z : 	Q2R (inject_Z z) = IZR z.
Proof. by rewrite /Q2R /=; lra. Qed.

Lemma Q2R_pow q n : Q2R (q ^ (Z.of_nat n)) = (Q2R q) ^ n.
Proof.
elim: n => [ | n ih]; first by rewrite /= /Q2R /=; lra.
rewrite [RHS]/= Nat2Z.inj_succ -Z.add_1_r.
have ->: forall z, Q2R (q ^ (z + 1)) = Q2R (q * q ^ z).
	admit.
by rewrite Q2R_mult ih.
Admitted.

Lemma sd_to_c_correct sds x:
	rs_reals_sdreals.rep_R sds x -> rs_reals_creals.rep_R (sd_to_c sds) x.
Proof.
move => sdsnx eps epsg0.
rewrite /sd_to_c /=.
rewrite Q2R_plus Q2R_div.
rewrite !Q2R_IZR SDs2Zn_SDs2Rn.
rewrite Rmult_comm /Rdiv Rmult_assoc.
have -> : 2 ^ Pos_size (Qden eps) * / Q2R ((2 # 1) ^ Z.of_nat (Pos_size (Qden eps))) = 1.
	suff ->: 2 ^ Pos_size (Qden eps) = Q2R ((2 # 1) ^ Z.of_nat (Pos_size (Qden eps))).
		rewrite Rinv_r => //; rewrite Q2R_pow /Q2R /=.
		have : 0 < 2 ^ Pos_size (Qden eps) by apply pow_lt; lra.
		rewrite Rinv_1 Rmult_1_r; lra.
	rewrite Q2R_pow /Q2R /= Rinv_1 Rmult_1_r; lra.
rewrite Rmult_1_r.
rewrite /rs_reals_sdreals.rep_R /= in sdsnx.
have [[[z y [[/=-> sdsny]] eq] _]]:= sdsnx.
rewrite /F2MF /ZUI2R /= in eq.
suff: Rabs (sval y - SDs2Rn (rprj sds) (Pos_size (Qden eps))) <= Q2R eps by split_Rabs; try lra.
have := sdsny; rewrite /rep_UI /= SDs2R_eff => limf.
apply /Rle_trans; first by rewrite Rabs_minus_sym; apply limf.
by apply size_Qden_leq.
admit.
Admitted.
End sdreals_to_creals.

Section creals_to_sdreals.
End creals_to_sdreals.










