From mathcomp Require Import all_ssreflect all_algebra.
Require Import FunctionalExtensionality.
Require Import all_rs rs_reals Rstruct under.
Require Import Reals Qreals Psatz ClassicalChoice.

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

Definition SD2Z sd : Z := match sd with
	| one => 1%Z
	| zero => 0%Z
	| minusone => -1%Z
end.

Fixpoint SDs2Zn (sds: nat -> SD) n := match n with
	| 0%nat => 0%Z
	| m.+1 => (2 * SDs2Zn sds m + SD2Z (sds m))%Z
end.

Lemma SDs2ZnS sds n :
	SDs2Zn sds n.+1 = (2 * SDs2Zn sds n + SD2Z (sds n))%Z.
Proof. by trivial. Qed.

Definition SD2R sd := match sd with
	| one => 1
	| zero => 0
	| minusone => -1
end.

Lemma IZR_SD2Z_SD2R sd: SD2R sd = IZR (SD2Z sd).
Proof. by case: sd. Qed.

Definition SDs2Rn (sds: nat -> SD) n := \sum_(i < n) SD2R (sds i) * /2 ^ i.+1.

Lemma SDs2Rn_SDs2Zn sds n: SDs2Rn sds n = IZR (SDs2Zn sds n) / 2^n.
Proof.
elim: n => [ | n ih]; first by rewrite /SDs2Rn big_ord0 /GRing.zero /=; try lra.
rewrite SDs2ZnS plus_IZR mult_IZR Rdiv_plus_distr Rmult_comm /Rdiv.
rewrite /SDs2Rn in ih.
rewrite /SDs2Rn big_ord_recr /= ih IZR_SD2Z_SD2R Rmult_assoc.
have ->: 2 * / (2 * 2 ^ n) = / 2 ^ n by have lt:= pow_lt 2 n; rewrite Rinv_mult_distr; try lra.
rewrite /GRing.mul/GRing.add/=; try lra.
Qed.

Lemma SDs2Zn_SDs2Rn sds n: IZR (SDs2Zn sds n) = 2 ^ n * SDs2Rn sds n.
Proof.
have lt:= pow_lt 2 n.
by rewrite SDs2Rn_SDs2Zn /Rdiv Rmult_comm Rmult_assoc Rinv_l; try lra.
Qed.

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

Lemma SDs2R_tot: SDs2R \is_total.
Proof.
rewrite /SDs2R F2MF_comp => sds.
have [x /Uncv_lim xprp]:= R_complete _ (Cauchy_crit_SDs2Rn sds).
by exists x.
Qed.

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

Lemma SDL2RS sd L: SDL2R (sd :: L) = SDL2R L + SD2R sd * /2 ^ (size L).+1.
Proof. done. Qed.

Fixpoint SDL2Z L := match L with
	| [::] => 0%Z
	| sd :: K => (2 * SDL2Z K + SD2Z sd)%Z
end.

Lemma SDL2ZS a L: SDL2Z (a :: L) = (2 * SDL2Z L + SD2Z a)%Z.
Proof. done. Qed.

Lemma SDL2Z_SDL2R L: IZR (SDL2Z L) = SDL2R L * 2^(size L).
Proof.
elim: L => [ | a L]; first by rewrite /=; lra.
rewrite SDL2ZS [RHS]/= plus_IZR mult_IZR => -> /=; have lt:= pow_lt 2 (size L).
rewrite Rmult_plus_distr_r Rmult_assoc Rinv_l ?IZR_SD2Z_SD2R; try lra.
Qed.

Lemma SDs2Zn_SDL2Z sds n:
	SDs2Zn sds n = SDL2Z (in_seg sds n).
Proof. by elim: n => // n ih; rewrite SDs2ZnS ih. Qed.

Lemma SDs2Rn_SDL2R sds n:
	SDs2Rn sds n = SDL2R (in_seg sds n).
Proof.
elim: n => [ | n ih]; first by rewrite /SDs2Rn big_ord0.
by rewrite /= SDs2RnS /= size_inseg ih.
Qed.

Definition rep_SD sds (x: UI):= SDs2R sds (projT1 x).

Lemma rep_sd_tot: rep_SD \is_total.
Proof.
move => sds; have [x val]:= SDs2R_tot sds.
by exists (exist _ x (SDs2R_UI sds x val)).
Qed.

Lemma rep_SD_sing: 	rep_SD \is_single_valued.
Proof.
move => sds x y sdsnx sdsny; apply /eq_sub /SDs2R_sing; [apply sdsnx | apply sdsny].
Qed.

Definition rep_SD_inc phi (x: UI) :=
	forall L, Rabs (projT1 x - SDL2R L) <= /2^(size L)
	->
	Rabs (projT1 x - SDL2R (phi L :: L)) <= /2^(size L).+1.

Fixpoint SD_inc_to_SD_rec (Lf: seq SD -> SD) m := match m with
	| 0%nat => [::]
	| S k => (Lf (SD_inc_to_SD_rec Lf k):: SD_inc_to_SD_rec Lf k)
end.

Lemma SD_inc_to_SD_rec_size Lf n:
	size (SD_inc_to_SD_rec Lf n) = n.
Proof. by elim: n => // n /= ->. Qed.

Definition SD_inc_to_SD (Lf: seq SD -> SD) n := Lf (SD_inc_to_SD_rec Lf n).

Lemma SD_inc_to_SD_inseg Lf n:
	in_seg (SD_inc_to_SD Lf) n = SD_inc_to_SD_rec Lf n.
Proof. by elim :n => // n /= ->. Qed.

Lemma SD_inc_to_SD_correct Lf x:
	rep_SD_inc Lf x -> rep_SD (SD_inc_to_SD Lf) x.
Proof.
move: x => [x ineq] Lfnx; rewrite /rep_SD SDs2R_eff; elim => [ | n /=].
	by rewrite /= SDs2Rn0; split_Rabs; try lra.
rewrite SDs2RnS SDs2Rn_SDL2R Rabs_minus_sym SD_inc_to_SD_inseg.
have ltn: 0<2^n by apply pow_lt; lra.
rewrite -{2}(SD_inc_to_SD_rec_size Lf n); try lra; move => ih.
have /=:= Lfnx (SD_inc_to_SD_rec Lf n) ih.
by rewrite SD_inc_to_SD_rec_size Rabs_minus_sym.
Qed.

Lemma rep_SD_inc_sing: rep_SD_inc \is_single_valued.
Proof.
move => Lf x y Lfnx Lfny.
by apply /(rep_SD_sing (SD_inc_to_SD Lf)); apply SD_inc_to_SD_correct.
Qed.

Lemma rep_SD_inc_nc (x: UI): 
	(forall q, exists a, Rabs (projT1 x - SDL2R q) <= /2^(size q)
		-> Rabs (projT1 x - SDL2R (a :: q)) <= /2^(size q).+1)
	-> x \from_codom rep_SD_inc.
Proof. by move => R; apply (choice _ R). Qed.

Lemma rep_SD_inc_cotot: is_cotot rep_SD_inc.
Proof.
move => [x ineq].
apply rep_SD_inc_nc => sdL.
case: (classic (x <= SDL2R sdL)) => leq.
	exists minusone => /= ineq'.
have leq':= pow_lt 2 (size sdL).
	rewrite Rinv_mult_distr; try lra.
	have leq'': 0 < /2 ^ (size sdL) by apply Rinv_0_lt_compat; lra.
	by split_Rabs; try lra.
exists one => /= ineq'.
have leq':= pow_lt 2 (size sdL).
rewrite Rinv_mult_distr; try lra.
have leq'': 0 < /2 ^ (size sdL) by apply Rinv_0_lt_compat; lra.
by split_Rabs; try lra.
Qed.

Lemma rep_SD_inc_is_rep: 	rep_SD_inc \is_representation.
Proof.
split; [exact rep_SD_inc_sing | exact rep_SD_inc_cotot].
Qed.

Definition rep_space_SD_inc :=
@make_rep_space UI (seq SD) SD rep_SD_inc [::] zero (list_count SD_count) (SD_count) rep_SD_inc_is_rep.

Lemma rep_SD_cotot: is_cotot rep_SD.
Proof.
move => x.
have [Lf Lfnx]:= rep_SD_inc_cotot x.
exists (SD_inc_to_SD Lf).
by apply SD_inc_to_SD_correct.
Qed.

Lemma rep_sd_is_rep: rep_SD \is_representation.
Proof.
by split; [exact: rep_SD_sing | exact: rep_SD_cotot].
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

Section SD_and_SD_inc.
(* The representation rec_SD_inc provides more information about signed digits:
One can extend any valid begining segment of a name in the usual representation
to a full name. Its definition is convenient for proving the signed digit representation
surjective and it is comptuationally equivalent. The equivalence is currently not executable
since I couldn't figure out how to properly do branching on rational numbers.*)

(* This function should do the branching over the rational numbers so it
is executable. *)
Definition SD_to_SD_inc sds L :=
	if is_left (Z_lt_dec (SDs2Zn sds (size L).+1) (2 * SDL2Z L)) then minusone
		else if is_left (Z_lt_dec (2 * SDL2Z L) (SDs2Zn sds (size L).+1)) then one
			else zero.

Fixpoint sds n := match n with
	| 0%nat => one
	| S 0 => zero
	| S (S 0) => minusone
	| S (S (S n)) => sds n
end.

Lemma SD_to_SD_inc_correct sds x:
	rep_SD sds x -> rep_SD_inc (SD_to_SD_inc sds) x.
Proof.
move: x => [x xui] /SDs2R_eff /= sdsnx L /= ineq1.
have g0: 0 < 2 ^ size L by apply pow_lt; lra.
have := sdsnx (size L).+1; rewrite Rabs_minus_sym Rinv_mult_distr; try lra.
move => ineq2.
rewrite /SD_to_SD_inc; case: ifP; case: Z_lt_dec => // lt _.
	move/(Zlt_le_succ _ _)/IZR_le: lt.
	rewrite /Z.succ plus_IZR mult_IZR SDs2Zn_SDs2Rn SDL2Z_SDL2R => /= lt.
	have ineq3: (SDs2Rn sds (size L).+1) <= SDL2R L - /2* /2^size L.
		apply: (Rmult_le_reg_r (2* 2^size L)); try lra.
		rewrite [(_ - _) * _]Rmult_comm Rmult_minus_distr_l.
		by rewrite -Rinv_mult_distr; try lra; rewrite Rinv_r; lra.
	by split_Rabs; try lra.
case: ifP; case: Z_lt_dec => // gt _.
	move/(Zlt_le_succ _ _)/IZR_le: gt.
	rewrite /Z.succ plus_IZR mult_IZR SDs2Zn_SDs2Rn SDL2Z_SDL2R => /= gt.
	have ineq3: (SDL2R L) <= SDs2Rn sds (size L).+1 - /2* /2^size L.
		apply: (Rmult_le_reg_r (2* 2^size L)); try lra.
		rewrite [(_ - _) * _]Rmult_comm Rmult_minus_distr_l.
		by rewrite -Rinv_mult_distr; try lra; rewrite Rinv_r; lra.
	by split_Rabs; try lra.
have eq: (SDs2Zn sds (size L).+1 = 2 * SDL2Z L)%Z by lia.
have:= IZR_eq _ _ eq.
move: eq; rewrite SDs2Zn_SDs2Rn mult_IZR SDL2Z_SDL2R /= => _ eq.
have: (SDs2Rn sds (size L).+1 = SDL2R L).
	apply: (Rmult_eq_reg_l (2 * 2 ^size L)); lra.
by move <-; split_Rabs; try lra.
Qed.

Lemma SD_SD_inc_iso: wisomorphic rep_space_UIsd rep_space_SD_inc.
Proof.
do 2 exists ((fun x y => x = y)).
split; last split; last by split => x y; apply comp_id_l.
	apply rec_cmpt; exists SD_to_SD_inc => phi x phinx _.
	by exists x; split => //; apply SD_to_SD_inc_correct.
apply rec_cmpt; exists SD_inc_to_SD => phi x phinx _.
by exists x; split => //; apply SD_inc_to_SD_correct.
Qed.
End SD_and_SD_inc.

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

Section output_and_examples.
Definition SDs2Qn sds n := (inject_Z (SDs2Zn sds n) / (2#1)^Z.of_nat n)%Q.
(*Example: Compute Qreduction.Qred (SDs2Qn sds 17). *)
End output_and_examples.
