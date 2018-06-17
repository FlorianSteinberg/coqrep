From mathcomp Require Import all_ssreflect all_algebra.
Require Import all_rs rs_reals_creals Rstruct under.
Require Import Qreals Reals Psatz.

Section Gray_code.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope R_scope.

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

Definition SD2R sd := match sd with
	| one => 1
	| zero => 0
	| minusone => -1
end.

Definition UI := { x | -1 <= x <= 1}.

Definition rep_sd (u: nat -> SD) (x: UI) :=
	forall n, Rabs (projT1 x - \sum_(i < n.+1) SD2R (u i) * /2 ^ i) <= /2^n.+1.

Definition accumulates_to_zero T f:= forall r, r > 0 -> exists t: T, Rabs (f t) < r.

Lemma cond_eq_f T f x y:
	accumulates_to_zero T f -> (forall z, Rabs (x - y) <= Rabs (f z)) -> x = y.
Proof.
move => acc cond.
apply cond_eq => eps epsg0.
have [t ineq]:= (acc eps epsg0).
by apply /Rle_lt_trans; first by apply: (cond t).
Qed.

Lemma pwr2gtz m: exists n, (2^n > m)%nat.
Proof.
elim: m => [ | m [n /leP ih]]; first by exists 0%nat; apply /leP => /=; lia.
exists n.+1; apply /leP => /=; lia.
Qed.

Lemma twopowern_accumulates_to_zero: accumulates_to_zero _ (fun n => /2^(n.+1)).
Proof.
move => r rgt0; pose z := Z.to_nat (up (1/r)).
have [n /leP nprp]:= pwr2gtz z; have : 0 < 2^n.+1 by apply pow_lt; lra.
exists (n).
rewrite Rabs_pos_eq; last by rewrite Rinv_pow; try lra; apply /pow_le; lra.
rewrite -[r]Rinv_involutive; try lra.
apply Rinv_lt_contravar; first by rewrite Rmult_comm; apply Rdiv_lt_0_compat.
apply /Rlt_trans; first by have:= (archimed (1 / r)).1 => ineq; rewrite -[/r]Rmult_1_l; apply ineq.
case E: (up (1/r)) => [ | p | p] //; have pos:= (Pos2Z.pos_is_pos p); last first.
	by apply /(@Rlt_le_trans _ (IZR 0)); [apply IZR_lt; lia | apply Rlt_le].
rewrite -[Z.pos _]Z2Nat.id; try lia; rewrite -E -/z -INR_IZR_INZ.
have ->: 2 = INR 2 by trivial.
rewrite -pow_INR; apply lt_INR => /=; lia.
Qed.

Lemma cond_eq_pwr x y : (forall n, Rabs (x - y) <= /2 ^ n.+1) -> x = y.
Proof.
intros.
apply (cond_eq_f _ _ _ _ twopowern_accumulates_to_zero) => n.
rewrite [Rabs (/2 ^ n.+1)]Rabs_pos_eq => //.
by rewrite Rinv_pow; first apply: pow_le; lra.
Qed.

Lemma rep_sd_sing:
	rep_sd \is_single_valued.
Proof.
move => u [x ineqx] [y ineqy] unx uny.
apply /eq_sub /cond_eq_pwr => n.
pose q:= \sum_(i < n.+2) SD2R (u i) * /2 ^ i.
have ->: x - y = x - q  + (q - y) by lra.
apply triang; rewrite [_ (q - y)]Rabs_minus_sym.
apply /Rle_trans; first by apply: Rplus_le_compat; [exact: unx | exact: uny].
have neq:= pow_lt 2 n; rewrite /= Rinv_mult_distr; try lra.
Qed.

Lemma rep_sd_is_rep:
	rep_sd \is_representation.
Proof.
split; first exact :rep_sd_sing.
move => [x ineq].
Admitted.

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

Lemma aux u (x: UI):
	u \is_name_of x -> - 1 <= 2 * sval x - SD2R (u 0%nat) <= 1.
Proof.
move: x => [x ineq]; rewrite /=/rep_sd/GRing.zero /= => unx.
specialize (unx 0%nat); move: unx; rewrite big_ord1/= Rmult_1_r.
case: (u 0%nat); rewrite /= Rinv_1 mulr1; split_Rabs; try lra.
Qed.

Lemma coinduct_sd (u: names rep_space_UIsd) x (unx: u \is_name_of x):
	Rabs (2 * sval x - SD2R (u 0%nat)) <= 1 /\ (fun (n: questions rep_space_UIsd) => u (S n)) \is_name_of (@exist R _ (2 * sval x - SD2R (u 0%nat)) (aux u x unx)).
Proof.
split; first by have:= (aux u x unx);	split_Rabs; lra.
move: x unx => [x ineq] unx => n /=.
have:= unx n.+1; rewrite big_ord_recl /= Rinv_1 mulr1.
Admitted.

Definition T2R t := match t with
	| TL => -1
	| TR => 1
	| Tbot => 0
end.

Coercion T2R: T >-> R.

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
move => u [x xinUI] unx n.
elim: n => /=.
case: ifP => [ineq | ].

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