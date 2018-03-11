(* This file contains some definitions of what it can mean for functions
between different spaces to be computable. *)
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions continuity initial_segments oracle_machines.
Require Import FunctionalExtensionality ClassicalChoice Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MACHINES.
Context (A Q: Type) (C: countType).
Notation B := (Q -> A).
Notation "Q ~> A" := (C -> Q -> option A) (at level 2).

Definition meval (N: Q ~> A) q a :=
	exists n, N n q = some a.
Notation eval N q a := (meval N q a).

Notation "N '\computes' f" := ((meval N) \tightens f) (at level 2).

Definition is_comp (f: Q ->> A) :=
	{N | N \computes f}.
Notation "f '\is_computable'" := (is_comp f) (at level 2).

Definition is_prec (f: Q ->> A) :=
	{M | M \is_choice_for f}.
Notation "f '\is_primitive_recursive'" := (is_prec f) (at level 2).

Lemma prec_cmpt (f: Q ->> A) (c: C):
	f \is_primitive_recursive -> f \is_computable.
Proof.
move => [M Mprop].
exists (fun n q => Some (M q)) => q ex.
move: ((icf_F2MF_tight M f).1 Mprop) => thight.
split => [ | t' [n nprop]]; first by exists (M q); exists c.
apply (thight q ex).
by apply Some_inj.
Qed.

Definition is_mon_mac (N: Q ~> A):=
	forall c c' q a, pickle c <= pickle c' -> N c q = Some a -> N c' q = Some a.
Notation "N '\is_monotone_machine'" := (is_mon_mac N) (at level 2).

Lemma mon_sing (N: Q ~> A):
	N \is_monotone_machine -> (meval N) \is_single_valued.
Proof.
move => mon q t t' [n ev] [n' ev']; apply Some_inj.
case: (PeanoNat.Nat.le_gt_cases (pickle n) (pickle n')) => ineq.
	by rewrite -(mon n n' q t _ ev).
have ineq': (pickle n' <= pickle n)%coq_nat by lia.
by rewrite -ev; apply/ (mon n' n).
Qed.

Definition mon_cmpt (N: Q ~> A) (f: Q ->> A):=
	forall q a, f q a -> exists c: C, N c q = Some a.
Notation "N '\monotone_computes' f" := (mon_cmpt N f) (at level 2).

Lemma sing_mon_cmpt (N: Q ~> A) (f: Q ->> A) :
	f \is_single_valued -> N \is_monotone_machine -> (N \monotone_computes f <-> N \computes f).
Proof.
move => sing mon.
split => [comp q [a fqa] | comp q a fqa].
	split => [ | a' evl ]; first by exists a; apply (comp q a fqa).
	suffices eq: a' = a by rewrite eq.
	by apply/ mon_sing; [ | apply evl | apply comp ].
have qfd: q \from_dom f by exists a.
have [[a' [c evl]] prop]:= (comp q qfd).
exists c.
suffices: a' = a by move => <-.
by apply/ sing; [apply prop; exists c | ].
Qed.

Lemma cmpt_fun N f:
	N \is_monotone_machine -> N \computes (F2MF f) <-> forall q, (meval N) q (f q).
Proof.
split => [comp q | prop].
	have ex: exists a, f q = a by exists (f q).
	have [[a [n Nnqa] prop]]:= (comp q ex).
	by exists n; rewrite Nnqa (prop a) //; exists n.
apply sing_mon_cmpt => //; first exact: F2MF_sing.
move => q a eq.
have [c val]:= (prop q).
by exists c; rewrite -eq.
Qed.

Definition is_mon_cmpt (f: Q ->> A) :=
	{N | N \is_monotone_machine /\ N \computes f}.
Notation "f '\is_monotone_computable'" := (is_mon_cmpt f) (at level 2).

Lemma cmpt_mon_cmpt (f: Q ->> A):
	f \is_computable -> f \is_monotone_computable.
Proof.
move => [M sc].
pose R q c:= exists a, M c q = some a.
pose p q n:= match (pickle_inv C n) with
	| None => false
	| Some c' => match M c' q with
		| None => false
		| Some a => true
	end
end.
pose r (c: C) q:= searchU (p q) (pickle c) (pickle c).
pose N c q:= match (pickle_inv C (r c q)) with
	| None => None
	| Some c' =>  M c' q
end.
exists N.
split => [n m q a ineq ev | q qfd]; last first.
	split => [| a [c]].
		have [[a [c Mqa]] prop]:= sc q qfd.
		have pqrc: p q (r c q) by	apply searchU_correct; rewrite /p pickleK_inv Mqa.
		have [c' uprcq]: exists c':C, pickle_inv C (r c q) = Some c'.
			by case E: (pickle_inv C (r c q)) => [c' | ]; [exists c'| rewrite /p E in pqrc].
		have [a' mcqsa]: exists a', M c' q = Some a'.
			by case E: (M c' q) => [a' | ]; [exists a'| rewrite /p uprcq E in pqrc].
		by exists a'; exists c; rewrite /N uprcq.
	rewrite /N; case E: (pickle_inv C (r c q)) => [c' | ] // eq.
	have ev: (eval M q a) by exists c'.
	exact ((sc q qfd).2 a ev).
have [c rnc]: exists c:C, (r n q) = pickle c.
	case E: (pickle_inv C (r n q)) => [c' | ]; last by rewrite /N E in ev.
	by exists c'; move: (pickle_invK C (r n q)); rewrite E.
rewrite /N rnc pickleK_inv in ev.
have pc: p q (pickle c) by rewrite /p pickleK_inv ev.
have eq: pickle c = r c q.
	suffices: pickle c <= r c q.
		move: (searchU_le (p q) (pickle c) (pickle c)).
		rewrite /r;	lia.
	rewrite -rnc.
	apply searchU_min.
	by apply searchU_correct.
rewrite /N.
suffices: r m q = pickle c by move => ->; rewrite pickleK_inv.
have ineq': pickle c <= pickle m.
	rewrite -rnc; suffices: r n q <= pickle n by lia.
	exact: searchU_le.
by rewrite eq /r (searchU_good _ (ineq')).
Qed.

End MACHINES.
Notation "f '\is_computable'" := (is_comp nat_countType f) (at level 2).
Notation "Q ~> A" := (nat -> Q -> option A) (at level 2).
Notation "M '\is_monotone_machine'" := (is_mon_mac M) (at level 2).

Section COMPUTABILITY_LEMMAS.
Context (A Q: Type) (C: countType).
Notation B := (Q -> A).
Notation "Q ~~> A" := (C -> Q -> option A) (at level 2).
Context (Q' A': Type).
Notation B' := (Q' -> A').

Lemma cmpt_op_cmpt (f: Q -> A) (F: B ->> B'):
	f \from_dom F -> is_cmpt_op C F -> F \is_single_valued
	-> is_comp C (fun q' a' => exists Ff, F f Ff /\ (Ff q') = a').
Proof.
move => fd comp' sing.
have [M [mon comp]]:= (cmpt_sing_mon_op comp' sing).
pose N c q' := M c f q' .
exists N.
have Nmon: N \is_monotone_machine by move => c c'; rewrite /N; apply/ mon.
apply sing_mon_cmpt => //.
	move => q a a' [Ff [FfFf eq]] [Ff' [Ff'Ff' eq']].
	suffices: Ff' = Ff by rewrite -eq -eq'; move <-.
	by apply/ sing; last by apply FfFf.
move => q' a' [Ff [FfFf eq]].
have [[Mf MfMf] prop]:= (comp f fd).
have [c val]:= (MfMf q').
exists c. rewrite /N.
rewrite -eq.
suffices: Mf q' = Ff q' by move => <-.
by apply/ sing_cmpt_elt; [ apply comp | | | apply val ].
Qed.

Lemma cmptbl_comp (f: Q' ->> A') (g: Q ->> Q'):
	f \is_computable -> g \is_computable -> (f o g) \is_computable.
Proof.
move => fcomp gcomp.
have [M [Mmon Mcomp]]:= cmpt_mon_cmpt fcomp.
have [N [Nmon Ncomp]]:= cmpt_mon_cmpt gcomp.
exists (fun n q => match N n q with
	|None => None
	|some q' => M n q'
end).
move => q [a't [[q't [gqq't fq'ta't]] prop]].
split.
	have qfd: q \from_dom g by exists q't.
	have [[q' evl] prop']:= (Ncomp q qfd).
	have q'fd: q' \from_dom f by apply/ prop; apply prop'.
	have [c val] := evl.
	have [[a' [c' val']] prop'']:= (Mcomp q' q'fd).
	exists a'.
	case E: (pickle c' <= pickle c)%N.
		exists c.
		rewrite val.
		apply/ Mmon; last by apply val'.
		by apply/leP; rewrite E.
	exists c'.
	rewrite -val'.
	suffices eq: N c' q = Some q' by rewrite eq.
	apply/ Nmon; last by apply val.
	suffices: ~pickle c' <= pickle c by lia.
	by apply/ leP; rewrite E.
move => a' [/= c evl].
split.
	have ex: exists q', N c q = Some q'.
		case E: (N c q) => [q' | ].
			by exists q'.
		by rewrite E in evl.
	have [q' eq] := ex.
	rewrite eq in evl.
	exists q'.
	have gqq': g q q'.
		have qfd: q \from_dom g by exists q't.
		apply/ (Ncomp q qfd).2.
		by exists c.
	split => //.
	have q'fd: q' \from_dom f by apply prop.
	apply/ (Mcomp q' q'fd).2.
	by exists c.
move => q' gqq'.
by apply prop.
Qed.
End COMPUTABILITY_LEMMAS.




























