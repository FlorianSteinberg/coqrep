From mathcomp Require Import all_ssreflect all_algebra.
Require Import all_rs rs_reals_creals Rstruct.
Require Import Qreals Reals Psatz.

Section Gray_code.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope R_scope.
Definition SD := option bool.

Notation one := (Some true).
Notation zero := None.
Notation minusone := (Some false).

Definition interp sd := match sd with
	| one => 1
	| zero => 0
	| minusone => -1
end.

Definition UI := { x | -1 <= x <= 1}.

Definition rep_sd (phi: nat -> SD) (x: UI) :=
	forall n, Rabs (projT1 x - \sum_(i < n) interp (phi i) * (powerRZ 2 (- Z.of_nat i.+1))) <= powerRZ 2 (- Z.of_nat n.+1).

Definition accumulates_to_zero T f:= forall r, r > 0 -> exists t: T, Rabs (f t) < r.

Lemma pwr2gtz (z: Z): exists n, 2^n > z.
Proof.
elim: z => [ | p | p ]; first by exists 0%nat; rewrite pow_O; lra.
	elim: p => [p [n ih]| p [n ih]]; last by 	exists 1%nat; rewrite pow_1; lra.
		have ineq: 1 <= IZR (Z.pos p) by apply /IZR_le; have:= Pos2Z.is_pos; lia.
		exists n.+2 => /=; apply Rlt_gt; rewrite -Rmult_assoc.
		apply /Rle_lt_trans; last by apply Rmult_lt_compat_l; last exact: ih; lra.
		by rewrite Pos2Z.inj_xI plus_IZR mult_IZR; lra.
	have ineq: 1 <= IZR (Z.pos p) by apply /IZR_le; have:= Pos2Z.is_pos; lia.
	exists n.+2 => /=; apply Rlt_gt; rewrite -Rmult_assoc.
	apply /Rle_lt_trans; last by apply Rmult_lt_compat_l; last exact: ih; lra.
	by rewrite Pos2Z.inj_xO mult_IZR; lra.
exists 0%nat; rewrite pow_O.
rewrite -[1]Ropp_involutive -[IZR (Z.neg p)] Ropp_involutive.
apply Ropp_lt_contravar; rewrite -!opp_IZR /=; apply IZR_lt.
by apply /Z.lt_le_trans; last exact/ Zle_0_pos; lia.
Qed.

Lemma twopowern_accumulates_to_zero:
	accumulates_to_zero Z (fun z => powerRZ 2 z).
Proof.
move => r rgt0.
pose z := (up (1/r)).
have [n nprp]:= pwr2gtz z.
have : 0 < 2^n by apply pow_lt; lra.
exists (Z.opp (Z.of_nat n)).
rewrite Rabs_pos_eq; last by apply powerRZ_le; lra.
rewrite powerRZ_neg; try lra; rewrite -pow_powerRZ -Rinv_pow; try lra.
rewrite -[r]Rinv_involutive; try lra.
apply Rinv_lt_contravar; first by rewrite Rmult_comm; apply Rdiv_lt_0_compat.
apply/ Rlt_trans.
	have:= (archimed (1 / r)).1 => ineq; rewrite -[/r]Rmult_1_l; apply ineq.
done.
Qed.

Lemma cond_eq_f T f x y:
	accumulates_to_zero T f -> (forall z, Rabs (x - y) <= Rabs (f z)) -> x = y.
Proof.
move => acc cond.
apply cond_eq => eps epsg0.
have [t ineq]:= (acc eps epsg0).
by apply /Rle_lt_trans; first by apply: (cond t).
Qed.

Lemma cond_eq_pwr x y : (forall z, Rabs (x - y) <= powerRZ 2 z) -> x = y.
Proof.
intros.
apply (cond_eq_f Z (fun z => powerRZ 2 z) _ _ twopowern_accumulates_to_zero) => z.
rewrite [Rabs (powerRZ 2 z)]Rabs_pos_eq => //.
by apply: powerRZ_le; lra.
Qed.

Lemma rep_sd_sing:
	rep_sd \is_single_valued.
Proof.
move => phi [x ineqx] [y ineqy] phinx phiny.
apply /eq_sub /cond_eq_pwr => /= z.
pose q:= \sum_(i < Z.to_nat (- (z - 1))) interp (phi i) * powerRZ 2 (- Z.of_nat i.+1).
have ->: x - y = x - q  + (q - y) by lra.
apply triang; rewrite [_ (q - y)]Rabs_minus_sym.
have -> : (z = z -1 +1)%Z by lia.
rewrite powerRZ_add; last by lra.
rewrite powerRZ_1 Rmult_comm.
have two: 2 = 1 + 1 by lra.
rewrite {1}two Rmult_plus_distr_r Rmult_1_l.
apply Rplus_le_compat.
	apply /Rle_trans;	first by apply phinx.
	rewrite !powerRZ_Rpower; try lra.
	apply Rle_Rpower; try lra.
	case: (z)%Z => [ | p | p]; first by rewrite /=; lra.
		apply /IZR_le; lia.
	apply /IZR_le; rewrite Nat2Z.inj_succ Z2Nat.id /=; lia.
apply /Rle_trans; first by apply phiny.
rewrite !powerRZ_Rpower; try lra.
apply Rle_Rpower; try lra.
apply /IZR_le; case: (z-1)%Z => [ | p | p]; rewrite /=; lia.
Qed.

Lemma rep_sd_is_rep:
	rep_sd \is_representation.
Proof.
split; first exact :rep_sd_sing.
move => [x ineq].
Admitted.

Lemma SD_count:
	SD \is_countable.
Proof. by apply countType_count. Qed.

Canonical rep_space_UIsd := @make_rep_space
	UI
	nat
	SD
	rep_sd
	0%nat
	zero
	nat_count
	SD_count
	rep_sd_is_rep.

Lemma aux p (x: UI):
	p \is_name_of x -> -1 <= 2 * sval x - interp (p 0%nat) <= 1.
Proof.
move: x => [x ineq].
rewrite /=/rep_sd/GRing.zero/=.
move => pnx.
specialize (pnx 0%nat).
move: pnx; rewrite big_ord0/= Rmult_1_r.
case: (p 0%nat); first case; rewrite /interp /=.
(*split_Rabs; lra.
Qed.*)
Admitted.

Lemma coinduct_sd (p: names rep_space_UIsd) x (pnx: p \is_name_of x):
	Rabs (2 * sval x - interp (p 0%nat)) <= 1 /\ (fun (n: questions rep_space_UIsd) => p (S n)) \is_name_of (@exist R _ (2 * sval x - interp (p 0%nat)) (aux p x pnx)).
Proof.
split; first by have:= (aux p x pnx);	split_Rabs; lra.
move: x pnx; rewrite /=/rep_sd => [[x ineq]] pnx.
move => n.
move: (pnx n.+1).
rewrite big_ord_recl.

Definition interpT t := match t with
	| TL => -1
	| TR => 1
	| Tbot => 1
end.

Coercion interpT: T >-> R.

Definition UI_Tomega_rep (p: rep_space_Tomega) (x: UI) :=
	forall n, Rabs (projT1 x - sum_f 0 n (fun i => -(prod_f_R0 (fun j => - p j) n) * (pow (1/2) i))) <= pow (1/2) n.

Definition sg (u: names rep_space_UIsd) (p: rep_space_Tomega) :=
	exists (x: UI), rep_sd u x /\ UI_Tomega_rep p x.

Definition tent x := 1 - 2 * Rabs x.

Lemma tenttoUI (x: UI):
	-1<= tent (projT1 x) <= 1.
Proof.
move: x => [x ineq].
rewrite /tent /=.
split_Rabs; lra.
Qed.

Definition tentUI (x: UI) := @exist R _ (tent (projT1 x)) (tenttoUI x): UI.

Lemma tentUI_correct (x: UI):
	projT1 (tentUI x) = tent (projT1 x).
Proof. done. Qed.

Fixpoint UI2Tomega_rec (x: UI) n:= match n with
	| 0%nat => if Rlt_dec (projT1 x) 0 then TL else if Rlt_dec 0 (projT1 x) then TR else Tbot
	| S n => UI2Tomega_rec (tentUI x) n
end.

Definition UI2Tomega (x: rep_space_UIsd) := (fun n => UI2Tomega_rec x n): rep_space_Tomega.

Definition SDSDtoT (sd sd': SD):= if sd == zero then Tbot else
	if sd == sd' then TL else TR.

Definition UI2Tomega_rlzr (u: names rep_space_UIsd) : names rep_space_Tomega :=
	fun an => match an.2 with
		| 0%nat => match u 0%nat with
			| one => TR
			| minusone => TL
			| zero => SDSDtoT (u an.1) (minusone)
		end
		| S n => if u n == zero then
				match n with
					| 0%nat => TR
					| S m => if u m == zero then TL else TR
				end
			else
				if u an.2 == zero then SDSDtoT (u (an.2 + an.1)%nat) (u n) else SDSDtoT (u an.2) (u n)
		end.

Lemma UI2Tomega_frlzr:
	UI2Tomega_rlzr \is_realizer_function_for UI2Tomega.
Proof.
rewrite /frlzr => u.
move => [x xinUI].
move => unx.
rewrite /=/rep_usig_prod.
move => n.
elim: n => /=.
case: ifP => [ineq | ].
rewrite /rep_T.
exists 0%nat.
split => //.
rewrite /UI2Tomega_rlzr/=.
rewrite /SDSDtoT /=.
rewrite /=/rep_sd in unx.
case E: (u 0%nat) => [b | ] /=. case E': b; rewrite E' in E; move: E' => _//.
	exfalso.
	specialize (unx 0%nat).
	rewrite /sum_f/interp/= in unx.
	move: unx.
	rewrite E.
	rewrite Rmult_1_l.
	have : x < 0  by rewrite /is_true/is_left in ineq; move: ineq; case: Rlt_dec.
	move: ineq => _ ineq.
	by split_Rabs; lra.
admit.
move => ineq.
case: ifP; last first.
	rewrite -ineq /is_true/is_left //; case Rlt_dec; case Rlt_dec; move => //; try lra.
	move => xl0 olx _.
	have eq: x = 0 by lra.
	move: xl0 olx => _ _.
	admit.
move => ineq'.
	rewrite ineq.

	move/eqP: ineq.
	rewrite /Rlt_dec.
	Check Rlt_dec.
	rewrite /Rlt_dec in ineq.
	split_Rabs; lra.
case: ifP => /=.
Admitted.

Lemma sg_correct: sg \tightens ((rep rep_space_Tomega) o (F2MF UI2Tomega_rlzr)).
Proof.
rewrite /sg.
apply /tight_trans; last first.
	have:= UI2Tomega_frlzr.

rewrite frlzr_rlzr /rlzr.

Definition hn sd:= match sd with
	| TR => false
	| Tbot => true
	| TL => true
end.

Definition flip t:= match t with
	| TL => TR
	| Tbot => Tbot
	| TR => TL
end.

Fixpoint flip_digit (u: rep_space_Tomega) n := match n with
	| 0%nat => true
	| S n => xorb (hn (u (S n))) (flip_digit u n)
end.

Definition flip_sequence u n:= if flip_digit u n then flip (u n) else u n.

Definition nh (L: seq T):= match L with
	| [::] => [::]
	| (a :: K) => (flip a :: K)
end.

Lemma flip_sequence_spec L i a:
	(i < size L)%nat -> flip_sequence (fun j => nth a L j) i = nth a (nh L) i.
Proof.
elim: L => // b L /=.
elim: i => //= n ih1 ih2 ineq.
rewrite /flip_sequence /=.
case: ifP => [A | ].
rewrite /hn.
Admitted.


Definition UI2G_rlzr' (u: names rep_space_Rsd):
	fun an => match u an.2 with
		| one => if flip_digit u an.2 then some true else some false
		| minusone => if  flip_digit u an.2 then some false else some true
		| zero => if flip_digit u an.2 then SDtoob (u (an.2 + an.1)%nat) else SDtoob (flip (u (an.2 + an.1)%nat))
	end.


Definition one_fun: names (rep_space_Rsd) := (fun n => one).

Compute UI2G_rlzr one_fun (0,4)%nat.


Fixpoint sgfirst (p: nat -> SD) n := match n with
	

Fixpoint sg (p: nat -> SD) n := match n with
	| 0 => 
	

End Gray_code.