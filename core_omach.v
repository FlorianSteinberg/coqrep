(* This file contains some definitions of what it can mean for functions
between different spaces to be computable. *)
From mathcomp Require Import all_ssreflect.
Require Import core_mf core_cont core_inseg.
Require Import FunctionalExtensionality ClassicalChoice Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope coq_nat_scope.
Section ORACLE_MACHINES.
Context (A A' Q Q': Type) (C: countType).
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation "B o~> B'" := (C -> B -> Q' -> option A') (at level 2).

Definition oeval (M: B o~> B') phi Mphi :=
	forall q', exists c, M c phi q' = some (Mphi q').

Notation "M '\computes' F" := ((oeval M) \tightens F) (at level 2).

Definition is_cmpt_op (F: B ->> B') :=
	{M| M \computes F}.
Notation "F '\is_computable_operator'" := (is_cmpt_op F) (at level 2).

Definition is_rec_op (F: B ->> B') :=
	{M | M \is_choice_for F}.
Notation "F '\is_recursive_operator'" := (is_rec_op F) (at level 2).

Lemma rec_F2MF_op (F: B -> B') (somec: C):
	(fun n phi q => Some(F phi q)) \computes (F2MF F).
Proof.
move => phi _.
split => [ | Fphi ev].
	by exists (F phi) => q'; exists somec.
apply functional_extensionality => q'.
have [c val]:= ev q'.
by apply Some_inj.
Qed.

Lemma prec_cmpt_op (F: B ->> B') (somec: C):
	F \is_recursive_operator -> F \is_computable_operator.
Proof.
move => [M Mprop].
exists (fun n phi q => Some (M phi q)).
apply/ tight_trans.
	apply rec_F2MF_op => //.
by apply icf_F2MF_tight.
Qed.

Definition is_mon_omac (M: B o~> B):=
	forall c c' phi q' a', pickle c <= pickle c' -> M c phi q' = Some a' -> M c' phi q' = Some a'.
Notation "M '\is_monotone_oracle_machine'" := (is_mon_omac M) (at level 2).

Lemma mon_sing_op (M: B o~> B):
	M \is_monotone_oracle_machine -> (oeval M) \is_single_valued.
Proof.
move => mon phi Fphi Fphi' ev ev'.
apply functional_extensionality => q'.
move: (ev q') (ev' q') => [n val] [n' val'].
apply Some_inj.
case: (PeanoNat.Nat.le_gt_cases (pickle n) (pickle n')) => ineq.
	by rewrite -(mon n n' phi q' (Fphi q') ineq).
have ineq': (pickle n' <= pickle n)%coq_nat by lia.
by rewrite -val; apply/ (mon n' n).
Qed.

Definition mon_cmpt (M: B o~> B') (F: B ->> B'):=
	forall phi Fphi, F phi Fphi -> (oeval M) phi Fphi.
Notation "M '\monotone_computes' F" := (mon_cmpt M F) (at level 2).

Lemma cmpt_mon_sing_op (M: B o~> B') (F: B ->> B') :
	M \is_monotone_oracle_machine -> F \is_single_valued -> (M \monotone_computes F <-> M \computes F).
Proof.
move => mon sing.
split => [comp phi [Fphi FphiFphi] | comp phi Fphi FphiFphi].
	split => [ | Mphi ev]; first by exists Fphi; apply/ (comp phi Fphi FphiFphi).
	suffices eq: Fphi = Mphi by rewrite -eq.
	by apply/ mon_sing_op; [apply/ mon | apply/ (comp phi Fphi) | apply ev].
have phifd: phi \from_dom F by exists Fphi.
have [[Mphi MphiMphi] prop] := (comp phi phifd).
suffices eq: Fphi = Mphi by rewrite eq.
by apply/ sing; [apply FphiFphi | apply prop].
Qed.

Lemma mon_cmpt_op M F:
	M \is_monotone_oracle_machine -> M \computes (F2MF F) <-> forall phi, (oeval M) phi (F phi).
Proof.
split => [comp phi q' | prop].
	have phifd: exists Fphi, F phi = Fphi by exists (F phi).
	have [[Mphi evl] prop]:= (comp phi phifd).
	have [c val] := (evl q').
	exists c; rewrite val.
	suffices: Mphi = (F phi) by move => <-.
	by rewrite (prop Mphi).
apply cmpt_mon_sing_op => //; first exact: F2MF_sing.
move => phi Fphi eq q'.
have [c val]:= (prop phi q').
by exists c; rewrite -eq.
Qed.

Definition is_mon_cmpt (F: B ->> B'):=
	{M | M \is_monotone_oracle_machine /\ M \computes F}.
Notation "F '\is_monotone_computable'" := (is_mon_cmpt F) (at level 2).

Lemma sing_cmpt_elt (M: B o~> B') (F: B ->> B') c phi Fphi q' a':
	M \computes F -> F \is_single_valued -> F phi Fphi -> M c phi q' = Some a' -> a' = Fphi q'.
Proof.
move => comp sing FphiFphi ev.
have phifd: phi \from_dom F by exists Fphi.
have [[Mphi MphiFphi] prop]:= (comp phi phifd).
have eq: Fphi = Mphi.
	suffices: F phi Mphi by apply/ sing.
	by apply prop.
rewrite -eq in MphiFphi.
move: Mphi eq => _ _.
pose Nphi q a:= (q <> q' /\ Fphi q = a) \/ (q' = q /\ a' = a).
have Nphitot: Nphi \is_total.
	by move => q;	case: (classic (q = q')) => ass; [exists a'; right | exists (Fphi q); left].
have [Mphi Mphiprop]:= choice Nphi Nphitot.
have MphiMphi: (oeval M) phi Mphi.
	by move => q; case: (Mphiprop q) => [[_ <-] | [<- <-]]; [apply MphiFphi | exists c].
apply Some_inj.
case: (Mphiprop q') => [[ctr] | [_ ->]] //.
suffices: Mphi = Fphi by move <-.
by apply/ sing; apply prop.
Qed.

Lemma cmpt_sing_mon_op (F: B ->> B'):
	F \is_computable_operator -> F \is_single_valued -> F \is_monotone_computable.
Proof.
move => [M comp] sing.
pose p (c: C) phi q n:= if (n < (pickle c))%N then
match (pickle_inv C n) with
	| None => false
	| Some c' => match M c' phi q with
		| None => false
		| Some a => true
	end
end else true.
have pprop: forall c phi q' n, p c phi q' n -> n < pickle c -> exists (c': C), pickle c' = n.
	move => c phi q' n pcn.
	case E: (pickle_inv C n) => [c' | ] ineq.
		by exists c'; rewrite -(pickle_invK C n) E.
	rewrite /p E in pcn.
	have ineq': (n < pickle c)%N by apply /leP; lia.
	by rewrite ineq' in pcn.
pose r (c: C) phi q':= search (p c phi q') (pickle c).
have rprop: forall c phi q', exists (c': C), pickle c' = r c phi q'.
	move => c phi q'.
	case E: (r c phi q' == pickle c).
		have ->: (r c phi q' = pickle c) by apply /eqP; rewrite E.
		by exists c.
	suffices ineq: r c phi q' < pickle c.
		apply/ (pprop c phi q' (r c phi q')) => //.
		apply search_correct.
		rewrite /p pickleK_inv.
		case: ifP => // fals.
		have: pickle c < pickle c by apply /leP.
		lia.
	suffices: r c phi q' <= pickle c.
		have: r c phi q' <> pickle c by apply/eqP; rewrite E.
		lia.
	exact /leP/search_le.
pose N c phi q:= match (pickle_inv C (r c phi q)) with
	| None => None
	| Some c' =>  M c' phi q
end.
exists N.
have mon: N \is_monotone_oracle_machine.
	move => n m phi q' a' ineq evl.
	case E: (pickle n < pickle m)%N.
		have[c rneqc]:= rprop n phi q'.
		have[c' rmeqc']:= rprop m phi q'.
		rewrite /N -rneqc pickleK_inv in evl.
		have rmlrn: r m phi q' <= r n phi q'.
			apply/leP/search_min.
			by rewrite /p -rneqc pickleK_inv evl; case: ifP.
		suffices rnlrm: r n phi q' <= r m phi q'.
			have eq: r m phi q' = r n phi q' by lia.
			by rewrite /N eq -rneqc pickleK_inv.
		apply/leP/search_min.
		rewrite /p -rmeqc' pickleK_inv.
		case: ifP => // ha.
		have pm: (p m phi q' (r m phi q')).
			rewrite search_correct => //.
			rewrite /p; case: ifP => // ineq'.
			have: pickle m < pickle m by apply /leP.
			by lia.
		rewrite /p in pm.
		have nq: (r m phi q' < pickle m)%N = true.
			apply /leP.
			suffices: pickle c' < pickle n by rewrite rmeqc'; lia.
			by apply /leP.
		rewrite nq in pm.
		by rewrite -rmeqc' pickleK_inv in pm.
	suffices ineq': pickle m <= pickle n.
		have eq: n = m.
			apply Some_inj.
			rewrite -!pickleK_inv.
			suffices <-: pickle n = pickle m by trivial.
			by lia.
		by rewrite -eq.
	by apply PeanoNat.Nat.Private_Tac.not_gt_le; apply /leP; rewrite E.
split => //.
rewrite -cmpt_mon_sing_op => //.
move => phi Fphi FphiFphi.
move => q'.
have phifd: phi \from_dom F by exists Fphi.
have [[Mphi MphiMphi] prop]:= comp phi phifd.
have [c val]:= MphiMphi q'.
have pqrc: p c phi q' (r c phi q').
	apply search_correct; rewrite /p.
	by case: ifP => // _; rewrite pickleK_inv val.
have [c' uprcq]:= rprop c phi q'.
rewrite /p -uprcq in pqrc.
case E: (pickle c' < pickle c)%N pqrc.
	rewrite pickleK_inv.
	case E': (M c' phi q') => // _.
	exists c; rewrite /N -uprcq pickleK_inv.
	by rewrite -(sing_cmpt_elt comp sing FphiFphi E').
move => _.
have eq: c' = c.
	suffices eq: pickle c' = pickle c by apply Some_inj; rewrite -!pickleK_inv -eq.
	have ineq: pickle c' <= pickle c by rewrite uprcq; apply/leP/search_le.
	suffices: ~pickle c' < pickle c by lia.
	by apply/ leP; rewrite E.
exists c; rewrite /N -uprcq pickleK_inv eq (sing phi Fphi Mphi) => //.
by apply prop.
Qed.

Lemma mon_sing_cmpt_op (F: B ->> B'):
	F \is_single_valued -> F \is_computable_operator -> F \is_monotone_computable.
Proof.
by move => sing [N comp]; apply/ cmpt_sing_mon_op; first exists N.
Qed.

End ORACLE_MACHINES.
Notation eval M := (@oeval _ _ _ _ nat_countType M).
Notation "M '\ocomputes' F" := ((oeval M) \tightens F) (at level 2).
Notation "F '\is_computable_operator'" := (is_cmpt_op F) (at level 2).
Notation "F '\is_recursive_operator'" := (is_rec_op F) (at level 2).
Notation "M '\is_monotone_oracle_machine'" := (is_mon_omac M) (at level 2).
Notation "M '\monotone_computes' F" := (mon_cmpt M F) (at level 2).
Notation "F '\is_monotone_computable'" := (@is_mon_cmpt _ _ _ _ nat_countType F) (at level 2).
Notation "f '\is_computable_operator'" := (is_cmpt_op nat_countType f) (at level 2).