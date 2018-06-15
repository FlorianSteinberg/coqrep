From mathcomp Require Import all_ssreflect.
Require Import all_rs rs_reals_creals.
Require Import Qreals Reals Psatz.

Section Gray_code.
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
	forall n, Rabs (projT1 x - sum_f 0 n (fun i => interp (phi i) * (powerRZ 2 (- Z.of_nat i)))) <= powerRZ 2 (- Z.of_nat n).

Definition accumulates_to_zero T f:= forall r, exists t: T, Rabs (f t) < Rabs r.

Lemma twopowern_accumulates_to_zero:
	accumulates_to_zero Z (fun z => powerRZ 2 z).
Proof.
Admitted.

Lemma cond_eq_f T f x y:
	accumulates_to_zero T f -> (forall z, Rabs (x - y) <= Rabs (f z)) -> x = y.
Proof.
move => acc cond.
apply cond_eq => eps epsg0.
have [t ineq]:= (acc eps).
apply /Rle_lt_trans; first by apply: (cond t).
apply /Rlt_le_trans; first by apply ineq.
by rewrite Rabs_pos_eq; lra.
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
move => phi [x ineqx] [y ineqy] phinx phiny/=.
apply /eq_sub /cond_eq_pwr => /= z.
rewrite /rep_sd /= in phinx phiny; move: ineqx ineqy => _ _.
pose q:= sum_f 0 (Z.to_nat (- (z - 1))) (fun i : nat => interp (phi i) * powerRZ 2 (- Z.of_nat i)).
have ->: x - y = x - q  + (q - y) by lra.
apply triang; rewrite [_ (q - y)]Rabs_minus_sym.
have -> : (z = z -1 +1)%Z by lia.
rewrite powerRZ_add; last by lra.
rewrite powerRZ_1 Rmult_comm.
have two: 2 = 1 + 1 by lra.
rewrite {1}two Rmult_plus_distr_r Rmult_1_l.
apply Rplus_le_compat.
	apply /Rle_trans; first by apply phinx.
	rewrite !powerRZ_Rpower; try lra.
	apply Rle_Rpower; try lra.
	case: (z-1)%Z => [ | p | p]; first by rewrite Z2Nat.id => //; rewrite opp_IZR; 	apply Rle_refl.
		by rewrite /=; apply /IZR_le /Zle_0_pos.
	by rewrite Z2Nat.id; try lia; rewrite opp_IZR; lra.
apply /Rle_trans; first by apply phiny.
rewrite !powerRZ_Rpower; try lra.
apply Rle_Rpower; try lra.
case: (z-1)%Z => [ | p | p]; first by rewrite Z2Nat.id => //; rewrite opp_IZR; 	apply Rle_refl.
	by rewrite /=; apply /IZR_le /Zle_0_pos.
by rewrite Z2Nat.id; try lia; rewrite opp_IZR; lra.
Qed.



Lemma rep_sd_is_rep:
	rep_sd \is_representation.
Proof.
split; first exact :rep_sd_sing.
Admitted.

Lemma SD_count:
	SD \is_countable.
Proof.
by apply countType_count.
Qed.

Canonical rep_space_Rsd := @make_rep_space
	UI
	nat
	SD
	rep_sd
	0%nat
	zero
	nat_count
	SD_count
	rep_sd_is_rep.

Definition interpT t := match t with
	| TL => -1
	| TR => 1
	| Tbot => 1
end.

Coercion interpT: T >-> R.

Check prod_f_R0.
Definition UI_Tomega_rep (p: rep_space_Tomega) (x: UI) :=
	forall n, Rabs (projT1 x - sum_f 0 n (fun i => -(prod_f_R0 (fun j => - p j) n) * (pow (1/2) i))) <= pow (1/2) n.

Definition sg (u: names rep_space_Rsd) (p: rep_space_Tomega) :=
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

Fixpoint UI2G_rec (x: UI) n:= match n with
	| 0%nat => if Rlt_dec (projT1 x) 0 then TL else if Rlt_dec 0 (projT1 x) then TR else Tbot
	| S n => UI2G_rec (tentUI x) n
end.

Definition UI2G (x: rep_space_Rsd) := (fun n => UI2G_rec x n): rep_space_Tomega.

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

Definition SDSDtoT (sd sd': SD):= if sd == zero then Tbot else
	if sd == sd' then TL else TR.

Definition UI2G_rlzr (u: names rep_space_Rsd) : names rep_space_Tomega :=
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

Lemma UI2G_frlzr:
	UI2G_rlzr \is_realizer_function_for UI2G.
Proof.
move => u x unx n.
rewrite /UI2G/=/rep_T/=.
elim: n => /=.
case: ifP => /=.
	case E: (UI2G_rec x n).

rewrite /UI2G_rlzr.
elim: n.
	case: ifP => /=ineq.
case E: (UI2G x n) => /=.
Search (Rle

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