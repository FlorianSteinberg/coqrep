(* This file contains some definitions of what it can mean for functions
between different spaces to be computable. *)
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions continuity initial_segments.
Require Import FunctionalExtensionality ClassicalChoice Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ORACLE_MACHINES.
Context (A A' Q Q': Type) (C: countType).
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation "B o~> B'" := (C -> B -> Q' -> option A') (at level 2).

Definition oeval (M: B o~> B') phi Mphi :=
	forall q', exists c, M c phi q' = some (Mphi q').
Notation eval M := (oeval M).

Notation "M '\computes' F" := ((oeval M) \tightens F) (at level 2).

Definition is_cmpt_op (F: B ->> B') :=
	{M| M \computes F}.
Notation "F '\is_computable_operator'" := (is_cmpt_op F) (at level 2).

Definition is_prim_rec_op (F: B ->> B') :=
	{M | M \is_choice_for F}.
Notation "F '\is_primitive_recursive_operator'" := (is_prim_rec_op F) (at level 2).

Lemma prec_F2MF_op (F: B -> B') (somec: C):
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
	F \is_primitive_recursive_operator -> F \is_computable_operator.
Proof.
move => [M Mprop].
exists (fun n phi q => Some (M phi q)).
apply/ tight_trans.
	apply prec_F2MF_op => //.
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
	forall phi Fphi, F phi Fphi -> (eval M) phi Fphi.
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
	M \is_monotone_oracle_machine -> M \computes (F2MF F) <-> forall phi, (eval M) phi (F phi).
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
have MphiMphi: (eval M) phi Mphi.
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
pose R phi q c:= exists a, M c phi q = some a.
pose p phi q n:= match (pickle_inv C n) with
	| None => false
	| Some c' => match M c' phi q with
		| None => false
		| Some a => true
	end
end.
pose r (c: C) phi q:= searchU (p phi q) (pickle c) (pickle c).
pose N c phi q:= match (pickle_inv C (r c phi q)) with
	| None => None
	| Some c' =>  M c' phi q
end.
exists N.
split => [n m phi q' a' ineq evl | phi phifd]; last first.
	split => [| Fphi evl].
		have [[Mphi MphiMphi] prop]:= comp phi phifd.
		exists Mphi => q'.
		have [c val]:= MphiMphi q'.
		have pqrc: p phi q' (r c phi q') by apply searchU_correct; rewrite /p pickleK_inv val.
		have [c' uprcq]: exists c':C, pickle_inv C (r c phi q') = Some c'.
			by case E: (pickle_inv C (r c phi q')) => [c' | ]; [exists c'| rewrite /p E in pqrc].
		have [a' mcqsa]: exists a', M c' phi q' = Some a'.
			by case E: (M c' phi q') => [a' | ]; [exists a'| rewrite /p uprcq E in pqrc].
		exists c; rewrite /N uprcq.
		suffices: a' = (Mphi q') by move => <-.
		by apply/ sing_cmpt_elt; [apply comp | apply sing | apply prop | apply mcqsa ].
	apply (comp phi phifd).2 => q'.
	have [c val]:= (evl q').
	have [c' uprcq]: exists c':C, pickle_inv C (r c phi q') = Some c'.
		by case E: (pickle_inv C (r c phi q')) => [c' | ]; [exists c' | rewrite /N E in val].
	by exists c';rewrite /N uprcq in val.
have [c rnc]: exists c:C, (r n phi q') = pickle c.
	case E: (pickle_inv C (r n phi q')) => [c' | ]; last by rewrite /N E in evl.
	by exists c'; move: (pickle_invK C (r n phi q')); rewrite E.
rewrite /N rnc pickleK_inv in evl.
have pc: p phi q' (pickle c) by rewrite /p pickleK_inv evl.
have eq: pickle c = r c phi q'.
	suffices: pickle c <= r c phi q'.
		move: (searchU_le (p phi q') (pickle c) (pickle c)).
		rewrite /r;	lia.
	rewrite -rnc.
	apply searchU_min.
	by apply searchU_correct.
rewrite /N.
suffices: r m phi q' = pickle c by move => ->; rewrite pickleK_inv.
have ineq': pickle c <= pickle m.
	rewrite -rnc; suffices: r n phi q' <= pickle n by lia.
	exact: searchU_le.
by rewrite eq /r (searchU_good _ (ineq')).
Qed.

Lemma mon_sing_cmpt_op (F: B ->> B'):
	F \is_single_valued -> F \is_computable_operator -> F \is_monotone_computable.
Proof.
by move => sing [N comp]; apply/ cmpt_sing_mon_op; first exists N.
Qed.
End ORACLE_MACHINES.
Notation eval M := (@oeval _ _ _ _ nat_countType M).
Notation "M '\computes' F" := ((oeval M) \tightens F) (at level 2).
Notation "F '\is_computable_operator'" := (is_cmpt_op F) (at level 2).
Notation "F '\is_primitive_recursive_operator'" := (is_prim_rec_op F) (at level 2).
Notation "M '\is_monotone_oracle_machine'" := (is_mon_omac M) (at level 2).
Notation "M '\monotone_computes' F" := (mon_cmpt M F) (at level 2).
Notation "F '\is_monotone_computable'" := (is_mon_cmpt F) (at level 2).
Notation "f '\is_computable_operator'" := (is_cmpt_op nat_countType f) (at level 2).






























