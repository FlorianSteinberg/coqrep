From mathcomp Require Import all_ssreflect all_algebra.
Require Import FunctionalExtensionality.
Require Import all_rs rs_reals Rstruct under.
Require Import Qreals Reals Psatz ClassicalChoice.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope R_scope.

Section signed_digits.
Inductive SD := minusone | zero | one.

Definition SD2OB sd := match sd with
	| minusone => some false
	| zero => None
	| one => some true
end.

Lemma SD_eqClass: Equality.class_of SD.
Proof.
exists (fun sd sd' => (SD2OB sd == SD2OB sd')%bool).
by case; case; try exact: ReflectT; try exact: ReflectF.
Qed.

Canonical SD_eqType := Equality.Pack SD_eqClass Type.

Lemma SD_count:
	SD \is_countable.
Proof.
exists (fun n => match n with
	| 0%nat => Some minusone
	| S 0 => Some zero
	| S (S 0) => Some one
	| S (S (S n)) => None
end).
by case; [case; [exists 0%nat | exists 1%nat | exists 2%nat] | exists 3%nat].
Qed.

Definition UI := { x | -1 <= x <= 1}.

Definition SD2R sd := match sd with
	| one => 1
	| zero => 0
	| minusone => -1
end.

Definition SDs2Rn (sds: nat -> SD) n:= \sum_(i < n) SD2R (sds i) * /2 ^ i.+1.

Lemma SDs2Rn0 sds: SDs2Rn sds 0%nat = 0.
Proof. by rewrite /SDs2Rn big_ord0. Qed.

Lemma Rabs_SDs2Rn u n : Rabs (SDs2Rn u n) <= 1 - /2^n.
Proof.
rewrite /SDs2Rn; case: n => [ | n]; first by rewrite big_ord0/= /GRing.zero /=; split_Rabs; lra.
elim: n => [ | n ih].
	rewrite /SDs2Rn big_ord1/= /GRing.mul /=.
	by case: (u 0%nat) => /=; split_Rabs; try lra.
rewrite /SDs2Rn big_ord_recr/=.
have p2lt: 0 < /2^n by apply /Rinv_0_lt_compat/pow_lt; lra.
have p2lt': 0 < 2^n by apply /pow_lt; lra.
apply triang.
have ->: 1 - / (2 * (2 * 2 ^ n)) = 1 - /2^n.+1 + (/2^n.+1 -  / (2 * (2 * 2 ^ n))) by lra.
apply Rplus_le_compat; first exact ih; rewrite !Rinv_mult_distr; try lra.
by case: (u n.+1); rewrite /GRing.mul /= ?Rmult_0_l; split_Rabs; try lra.
Qed.

Lemma SDs2RnS sds n : SDs2Rn sds n.+1 = SDs2Rn sds n + SD2R (sds n) * /2^n.+1.
Proof.
by rewrite /SDs2Rn big_ord_recr /=.
Qed.

Lemma SDs2RSn sds n : SDs2Rn sds n.+1 = /2 * SDs2Rn (fun i => sds i.+1) n + /2 * SD2R (sds 0%nat).
Proof.
rewrite /SDs2Rn big_ord_recl /= addrC.
congr (_ + _); last rewrite Rmult_1_r /GRing.mul /=; try lra.
elim: n => [ | n ih]; first by rewrite !big_ord0 /GRing.zero /=; lra.
rewrite big_ord_recr /= ih.
rewrite [\sum_(i < n.+1) _] big_ord_recr /=.
have ->: bump 0%nat n = n.+1 by rewrite /bump.
rewrite Rmult_plus_distr_l.
congr (_ + _).
have plt:= pow_lt 2 n.
by rewrite !Rinv_mult_distr /GRing.mul /=; try lra.
Qed.

Lemma Rabs_SDs2Rnm sds n m (ineq: (n <= m)%nat):
	Rabs (SDs2Rn sds m - SDs2Rn sds n) <= /2^n  - /2^m.
Proof.
elim: n m ineq sds => [m ineq sds| n ih m ineq].
	rewrite {2}/SDs2Rn big_ord0 Rminus_0_r Rinv_1; exact: Rabs_SDs2Rn.
move => sds; case: m ih ineq => // m ih ineq.
rewrite !SDs2RSn; specialize (ih m ineq (fun i => sds i.+1)).
have lt1:= pow_lt 2n; have lt2:= pow_lt 2 m; rewrite /= !Rinv_mult_distr; split_Rabs; try lra.
Qed.

Lemma Cauchy_crit_eff_SDs2Rn sds :	Cauchy_crit_eff (SDs2Rn sds).
Proof.
apply /Cauchy_crit_eff_suff => n m ineq.
rewrite Rabs_minus_sym; have lt: 0 < /2^m by apply /Rinv_0_lt_compat /pow_lt; lra.
by apply /Rle_trans; first apply Rabs_SDs2Rnm; try lra.
Qed.

Lemma Cauchy_crit_SDs2Rn sds :	Cauchy_crit (SDs2Rn sds).
Proof. exact /Cauchy_crit_eff_Cauchy_crit /Cauchy_crit_eff_SDs2Rn. Qed.

Definition SDs2R := lim o (F2MF SDs2Rn).

Lemma SDs2R_sing: SDs2R \is_single_valued.
Proof. by apply /comp_sing; [exact /lim_sing | exact /F2MF_sing]. Qed.

Lemma SDs2R_lim_eff: SDs2R =~= lim_eff o (F2MF SDs2Rn).
Proof.
rewrite lim_eff_Cauchy /SDs2R !F2MF_comp => sds x.
split => [limx| [Cauchy limx]]; first by split; first exact: Cauchy_crit_eff_SDs2Rn.
apply lim_exte_lim_eff.
have [y limeffy]:= (Cauchy_conv (SDs2Rn sds)).1 Cauchy.
by rewrite (@lim_sing (SDs2Rn sds) x y) => //; apply lim_exte_lim_eff.
Qed.

Lemma SDs2R_eff sds x: SDs2R sds x <-> lim_eff (SDs2Rn sds) x.
Proof. have:= SDs2R_lim_eff; rewrite F2MF_comp => prp; apply prp. Qed.

Lemma SDs2R_UI u x: SDs2R u x -> -1 <= x <= 1.
Proof.
move => /SDs2R_eff val; move: (val 0%nat) => /=.
rewrite /SDs2Rn big_ord0/= Rminus_0_l Rabs_Ropp; split_Rabs; lra.
Qed.

Fixpoint SDL2R L:= match L with
	| [::] => 0
	| sd :: K => SDL2R K + SD2R sd * /2 ^ (size L)
end.

Lemma SDs2Rn_SDL2R sds n:
	SDs2Rn sds n = SDL2R (in_seg sds n).
Proof.
elim: n => [ | n ih]; first by rewrite /SDs2Rn big_ord0.
by rewrite /= SDs2RnS /= size_inseg ih.
Qed. 

Definition rep_SD_inc phi (x: UI) :=
	forall sdL, Rabs (projT1 x - SDL2R sdL) <= /2^(size sdL)
	->
	Rabs (projT1 x - SDL2R ((phi sdL) :: sdL)) <= /2^(size sdL).+1.

Lemma rep_SD_inc_cotot: is_cotot rep_SD_inc.
Proof.
move => [x ineq].
rewrite /codom/rep_SD_inc.
pose R sdL sd := Rabs (x - SDL2R sdL) <= / 2 ^ size sdL ->
  Rabs (x - SDL2R (sd :: sdL)) <=
  / 2 ^ (size sdL).+1.
have Rtot: R \is_total.
	move => sdL.
	case: (classic (x <= SDL2R sdL)) => leq.
		exists minusone => ineq' /=.
		have leq':= pow_lt 2 (size sdL).
		rewrite Rinv_mult_distr; try lra.
		have leq'': 0 < /2 ^ (size sdL) by apply Rinv_0_lt_compat; lra.
		by split_Rabs; try lra.
	exists one => ineq' /=.
	have leq':= pow_lt 2 (size sdL).
	rewrite Rinv_mult_distr; try lra.
	have leq'': 0 < /2 ^ (size sdL) by apply Rinv_0_lt_compat; lra.
	by split_Rabs; try lra.
exact: (choice R Rtot).
Qed.

Definition rep_SD sds (x: UI):= SDs2R sds (projT1 x).

Lemma foldr_sum L: 	foldr Rplus 0 L = \sum_(i < size L) nth 0 L i.
Proof.
elim: L => [ | a L ih]; first by rewrite /= big_ord0.
by rewrite /= big_ord_recl /= ih.
Qed.

Lemma inducleq (P: nat -> Prop):
	P 0%nat -> (forall m: nat, (forall n, (n <= m)%nat -> P n) -> P m.+1) -> forall n, P n.
Proof.
move => P0 induc n.
elim: n {-2}n (leqnn n) => [ | n ih m ineq]; first by move => n; rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt in ineq; case /orP: ineq.
	by move => /eqP ->; apply induc.
by move => ineq; apply ih.
Qed.

Lemma SDs2UI_cotot: is_cotot rep_SD.
Proof.
move => x.
have [Lf Lfnx]:= rep_SD_inc_cotot x.
move: x Lfnx => [x ineq] Lfnx.
pose admiss := fix admiss sdL m := match m with
	| 0%nat => True
	| S n => match sdL with
		| [ :: ] => True
		| (a :: L) => Lf L = a /\ admiss L n
	end
end.
have admissD: forall p k L, admiss L (k + p)%nat -> admiss L k.
	elim => [ | p ih].
		elim => [L | k ih L]; first by case: L.
		by case: L => // a L /= [-> add]; split; last apply ih.
	elim => [L | k ihk L]; first by case: L.
	rewrite addSn /=.
	by case: L => // a L /= [] ->; split => //; apply ihk.
have exL: forall n, exists! L, size L = n /\ forall m, (m <= n)%nat -> admiss L m.
	elim => [ | n [L [[eq Lprp]]ih]].
		by exists ([::]); split; [split => // m leq /=; by case: m leq | move => sd [/size0nil ->]].
	exists (Lf L :: L).
	split.
		split => [/= | m leq]; first by rewrite eq.
		case E: m => [ | k]// /=; split => //.
		apply Lprp.
		by rewrite E in leq.
	case => [[] /=| a K [[sz] prp]]//.
	have -> : L = K.
		apply ih; split => // m leq.
		by have /=[]:= prp m.+1 leq.
	f_equal.
	by have /=[]:= prp n.+1.
pose Rel n sd := forall sdL, size sdL = n -> admiss sdL n -> admiss (sd :: sdL) (size sdL).+1.
have Rtot: Rel \is_total.
	move => n.
	have [L [[sz prp] unqe]]:= exL n.
	exists (Lf L) => K szK admK /=.
	rewrite (unqe K) szK => //.
	split => //.
	move => m leq.
	rewrite -(subnK leq) addnC in admK.
	by apply (admissD (n - m)%nat m).
have [f fprp]:= choice _ Rtot.
exists f.
rewrite /rep_SD /=.
rewrite SDs2R_eff.
elim => [ | n]; rewrite SDs2Rn_SDL2R /=; first by split_Rabs; lra.
rewrite SDs2RnS {1}Rabs_minus_sym => ih.
have /=[]:= fprp n (in_seg f n).
		by rewrite size_inseg.
	elim: (n) => // k ihk.
	rewrite /=; split => //.
	by have /=[]:= fprp k (in_seg f k) _ ihk; rewrite size_inseg.
rewrite size_inseg => <- adm.
have /=:= Lfnx (in_seg f n).
rewrite size_inseg => namex.
specialize (namex ih).
by rewrite SDs2Rn_SDL2R Rabs_minus_sym.
Qed.

Lemma rep_SD_sing: 	rep_SD \is_single_valued.
Proof.
move => sds x y sdsnx sdsny; apply /eq_sub /SDs2R_sing; [apply sdsnx | apply sdsny].
Qed.

Lemma rep_sd_is_rep: rep_SD \is_representation.
Proof.
split => [ | x]; first exact :rep_SD_sing.
by have [sds val]:= SDs2UI_cotot x; exists sds.
Qed.

Canonical rep_space_UIsd := @make_rep_space
	UI
	_
	_
	rep_SD
	(some_question _)
	zero
	(countable_questions _)
	SD_count
	rep_sd_is_rep.
End signed_digits.

Section sd_coinduction.
Lemma SDs2R_hd sds x: SDs2R sds x -> - 1 <= 2 * x - SD2R (sds 0%nat) <= 1.
Proof.
move: x => x; rewrite /=/GRing.zero /= SDs2R_eff => unx.
specialize (unx 1%nat); move: unx; rewrite /SDs2Rn big_ord1.
by case: (sds 0%nat) => /=; rewrite /GRing.mul /=; split_Rabs; lra.
Qed.

Lemma SDs2R_tl sds x: SDs2R sds x -> SDs2R (fun n => sds n.+1) (2 * x - SD2R (sds 0%nat)).
Proof.
rewrite !SDs2R_eff => unx n; apply: (Rmult_le_reg_l (/2)); try lra.
rewrite -[/2 * / _]Rinv_mult_distr; try lra; last by have:= pow_lt 2 n; lra.
apply/ Rle_trans; last by apply: unx n.+1.
rewrite {2}/SDs2Rn big_ord_recl /= /SDs2Rn.
suff <- : (/ 2 * \sum_(i < n) SD2R (sds i.+1) * /2 ^ i.+1) = \sum_(i < n) SD2R (sds (bump 0 i)) * / (2 * (2 * 2 ^ i)) by rewrite /GRing.mul /GRing.add/=; split_Rabs; try lra.
elim: n => [ | n ih]; first by rewrite !big_ord0 /GRing.zero /=; lra.
have p2lt: 0 < 2^n by apply pow_lt; lra.
rewrite big_ord_recr/= Rmult_plus_distr_l ih [RHS]big_ord_recr/=.
congr (_ + _).
have -> : bump 0 n = n.+1%nat by trivial.
rewrite !Rinv_mult_distr; try lra.
by rewrite /GRing.mul/=; try lra.
Qed.
End sd_coinduction.

Section rep_sd_total.
Lemma SDs2R_tot: SDs2R \is_total.
Proof.
rewrite /SDs2R F2MF_comp => sds.
have [x /Uncv_lim xprp]:= R_complete _ (Cauchy_crit_SDs2Rn sds).
by exists x.
Qed.

Lemma SDs2UI_tot: rep_SD \is_total.
Proof.
move => sds; have [x val]:= SDs2R_tot sds.
by exists (exist _ x (SDs2R_UI sds x val)).
Qed.
End rep_sd_total.