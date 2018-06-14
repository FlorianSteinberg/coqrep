From mathcomp Require Import all_ssreflect.
Require Import all_rs rs_reals_creals.
Require Import Qreals Reals Psatz.

Section Gray_code.
Local Open Scope R_scope.
Print rep_space_R.
Definition rep_space_UI := rep_sub_space (fun x => -1 <= x <= 1).

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
	forall n, Rabs (projT1 x - sum_f 0 n (fun i => interp (phi i) * (pow (1/2) i))) <= pow (1/2) n.

Lemma rep_sd_is_rep:
	rep_sd \is_representation.
Proof.
Admitted.

Lemma SD_count:
	SD \is_countable.
Proof.
Admitted.

Definition rep_space_Rsd := @make_rep_space
	UI
	nat
	SD
	rep_sd
	0%nat
	zero
	nat_count
	SD_count
	rep_sd_is_rep.
Print T.

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

Fixpoint UI2G x n:= match n with
	| 0%nat => if Rlt_dec x 0 then TL else if Rlt_dec 0 x then TR else Tbot
	| S n => UI2G (tent x) n
end.

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
case: ifP.
rewrite /hn.
Admitted.

Definition SDSDtoT (sd sd': SD):= if sd == zero then Tbot else
	if sd == sd' then TL else TR.

Definition UI2G_rlzr (u: names (rep_space_Rsd)): (names rep_space_Tomega) :=
	fun an => match an.2 with
		| 0%nat => if 
		| S n => if u n == zero then
				match n with
					| 0%nat => TR
					| S m => if u m == zero then TL else TR
				end
			else
				if u an.2 == zero then SDSDtoT (u (an.2 + an.1)%nat) (u n) else SDSDtoT (u an.2) (u n).
		end

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