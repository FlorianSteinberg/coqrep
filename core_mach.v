(* This file contains some definitions of what it can mean for functions
between different spaces to be computable. *)
From mathcomp Require Import all_ssreflect.
Require Import core_mf core_cont core_inseg core_omach.
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

Definition is_rec (f: Q ->> A) :=
	{M | M \is_choice_for f}.
Notation "f '\is_recursive'" := (is_rec f) (at level 2).

Lemma rec_cmpt (f: Q ->> A) (c: C):
	f \is_recursive -> f \is_computable.
Proof.
case => M Mprop; exists (fun n q => Some (M q)) => q [fq fqfq].
abstract by split => [ | t' [n [<-]]]; [exists (M q); exists c | apply/ Mprop/fqfq].
Defined.

Definition is_mon_mac (N: Q ~> A):=
	forall c c' q a, pickle c <= pickle c' -> N c q = Some a -> N c' q = Some a.
Notation "N '\is_monotone_machine'" := (is_mon_mac N) (at level 2).

Lemma mon_sing (N: Q ~> A):
	N \is_monotone_machine -> (meval N) \is_single_valued.
Proof.
move => mon q t t' [n ev] [n' ev']; apply Some_inj.
case/orP: (leq_total (pickle n) (pickle n')) => ineq.
	by rewrite -(mon n n' q t _ ev).
by rewrite -ev; apply/ (mon n' n).
Qed.

Definition mon_cmpt (N: Q ~> A) (f: Q ->> A):=
	forall q a, f q a -> exists c: C, N c q = Some a.
Notation "N '\monotone_computes' f" := (mon_cmpt N f) (at level 2).

Lemma sing_mon_cmpt N f:f \is_single_valued -> N \is_monotone_machine ->
	(N \monotone_computes f <-> N \computes f).
Proof.
split => [comp q [a fqa] | comp q a fqa].
	split => [ | a' evl ]; first by exists a; apply (comp q a fqa).
	by have ->: a' = a by apply/ mon_sing; [ | apply evl | apply comp ].
have [ |[a' [c evl]] prop]:= (comp q _); first by exists a.
by exists c; have <-: a' = a by apply/ H; [apply prop; exists c | ].
Qed.

Lemma cmpt_fun N f: N \is_monotone_machine ->
	N \computes (F2MF f) <-> forall q, (meval N) q (f q).
Proof.
split => [comp q | prop].
	have [ | [a [n Nnqa] prop]]:= (comp q _); first by exists (f q).
	by exists n; rewrite Nnqa (prop a) //; exists n.
by apply sing_mon_cmpt => //[ | q _ <-]; [exact: F2MF_sing | have [c]:= prop q; exists c].
Qed.

Definition is_mon_cmpt (f: Q ->> A) :=
	{N | N \is_monotone_machine /\ N \computes f}.
Notation "f '\is_monotone_computable'" := (is_mon_cmpt f) (at level 2).

Lemma cmpt_mon_cmpt (f: Q ->> A):
	f \is_computable -> f \is_monotone_computable.
Proof.
case => M comp.
pose p (c: C) q n:= if n < (pickle c) then
match (pickle_inv C n) with
	| None => false
	| Some c' => match M c' q with
		| None => false
		| Some a => true
	end
end else true.
have pprop: forall c q' n, p c q' n -> n < pickle c -> exists (c': C), pickle c' = n.
	move => c q' n; rewrite /p; case: ifP => // ineq.
	case E: (pickle_inv C n) => [c' | ]//; case: (M c' q') => // _ _ _.
	by exists c'; rewrite -(pickle_invK C n) E /=.
pose r (c: C) q':= search (p c q') (pickle c).
have rprop: forall c q', exists (c': C), pickle c' = r c q'.
	move => c q'; case E: (r c q' == pickle c); first by exists c; apply /esym/eqP; rewrite E.
	have ineq: r c q' < pickle c.
		by rewrite ltn_neqAle; apply /andP; split; [apply/esym/negP; rewrite E |apply search_le].
	apply/ (pprop c q' (r c q') _ ineq) /search_correct.
	by rewrite /p pickleK_inv; case: ifP => //;rewrite (ltnn (pickle c)).
pose N c q:= match (pickle_inv C (r c q)) with
	| None => None
	| Some c' =>  M c' q
end.
exists N.
have mon: N \is_monotone_machine.
	move => n m q' a' ineq.
	case E: (pickle n < pickle m)%N;[move => evl | move <-; f_equal]; last first.
		suffices eq: pickle n = pickle m by apply Some_inj; rewrite -!pickleK_inv eq.
		by apply/eqP; rewrite eqn_leq; apply /andP; split => //; rewrite leqNgt E.
	have[c rneqc]:= rprop n q'.
	have[c' rmeqc']:= rprop m q'.
	rewrite /N -rneqc pickleK_inv in evl.
	have rmlrn: r m q' <= r n q'.
		by apply/search_min; rewrite /p -rneqc pickleK_inv evl; case: ifP.
	suffices rnlrm: r n q' <= r m q'.
		have eq: r m q' = r n q' by apply/eqP; rewrite eqn_leq; apply /andP.
		by rewrite /N eq -rneqc pickleK_inv.
	apply/search_min; rewrite /p -rmeqc' pickleK_inv; case: ifP => // ha.
	have: (p m q' (r m q')).
		by rewrite search_correct => //; rewrite /p; case: ifP => //; rewrite ltnn.
	rewrite /p; have ->: r m q' < pickle m by rewrite -rmeqc'; apply /(leq_trans ha).
	by rewrite -rmeqc' pickleK_inv.
split => // q qfd; split; last first.
	move => a [c Nqa]; apply (comp q qfd).2.
	have [c' rc]:= rprop c q.
	by exists (c'); rewrite /N -rc pickleK_inv in Nqa.
have [[a [c Mqa]] prop]:= comp q qfd.
have: p c q (r c q).
	by apply search_correct; rewrite /p; case: ifP => //; rewrite pickleK_inv Mqa.
have [c' rc]:= rprop c q.
rewrite /p -rc; case: ifP => ass.
	rewrite pickleK_inv; case E': (M c' q) => [a' | ] // _.
	by exists a'; exists c; rewrite /N -rc pickleK_inv.
suffices eq: c' = c by exists a; exists c; rewrite /N -rc pickleK_inv eq.
suffices eq: pickle c' = pickle c by apply Some_inj; rewrite -!pickleK_inv -eq.
have ineq: pickle c' <= pickle c by rewrite rc; apply/search_le.
by apply /eqP; rewrite eqn_leq; apply /andP; split; last rewrite leqNgt ass.
Qed.

End MACHINES.
Notation "f '\is_computable'" := (is_comp nat_countType f) (at level 2).
Notation "Q ~> A" := (nat -> Q -> option A) (at level 2).
Notation "M '\is_monotone_machine'" := (is_mon_mac M) (at level 2).
Notation eval N q a := (meval N q a).
Notation "N '\computes' f" := ((meval N) \tightens f) (at level 2).

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
have [M [mon comp]]:= (cmpt_sing_mon_op sing comp').
pose N c q' := M c f q'; exists N.
have Nmon: N \is_monotone_machine by rewrite /N => c c' q a; apply/mon.
apply sing_mon_cmpt => //.
	by move => q a a' [Ff [H <-]] [Ff' [H0 <-]]; rewrite (sing f Ff Ff').
have [[Mf MfMf] prop]:= (comp f fd) => q' a' []Ff[]; have [c val]:= (MfMf q').
by exists c; rewrite /N -b val; f_equal; apply/sing_cmpt_elt; [apply comp | | | apply val].
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
have qfd: q \from_dom g by exists q't.
split => [ | a' [/= c evl]]; last first.
	split; last by intros; apply prop.
	case E: (N c q) evl => [q' | ] // evl.
	exists q'; split; first by apply/ (Ncomp q qfd).2; exists c.
	apply/ (Mcomp q' _).2; last by exists c.
	by apply prop; apply Ncomp; [exists q't | exists c].
have [[q' [c evl]] prop']:= (Ncomp q qfd).
have [ | [a' [c' val']] prop'']:= (Mcomp q' _); first by apply/prop/prop'; exists c.
exists a'; case E: (pickle c' <= pickle c)%N.
	by exists c; rewrite evl; apply/ Mmon; last apply val'; first rewrite E.
exists c'; suffices ->: N c' q = Some q' => //; apply/ Nmon; last exact: evl.
by apply /leq_trans; [exact: leqnSn | rewrite ltnNge E].
Qed.
End COMPUTABILITY_LEMMAS.




























