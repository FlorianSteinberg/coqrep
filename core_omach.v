(* This file contains some definitions of what it can mean for functions
between different spaces to be computable. *)
From mathcomp Require Import all_ssreflect.
Require Import core_mf core_cont core_inseg.
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
case => M Mprop; exists (fun n phi q => Some (M phi q)).
abstract by apply/ tight_trans; [apply rec_F2MF_op | apply icf_F2MF_tight].
Defined.

Definition is_mon_omac (M: B o~> B):=
	forall c c' phi q' a', pickle c <= pickle c' -> M c phi q' = Some a' -> M c' phi q' = Some a'.
Notation "M '\is_monotone_oracle_machine'" := (is_mon_omac M) (at level 2).

Lemma mon_sing_op (M: B o~> B):
	M \is_monotone_oracle_machine -> (oeval M) \is_single_valued.
Proof.
move => mon phi Fphi Fphi' ev ev'.
apply functional_extensionality => q'; apply Some_inj.
move: (ev q') (ev' q') => [n val] [n' val'].
case/orP: (leq_total (pickle n) (pickle n')) => ineq.
	by rewrite -(mon n n' phi q').
by rewrite -val -(mon n' n phi q').
Qed.

Definition mon_cmpt (M: B o~> B') (F: B ->> B'):=
	forall phi Fphi, F phi Fphi -> (oeval M) phi Fphi.
Notation "M '\monotone_computes' F" := (mon_cmpt M F) (at level 2).

Lemma cmpt_mon_sing_op M F: M \is_monotone_oracle_machine -> F \is_single_valued ->
	(M \monotone_computes F <-> M \computes F).
Proof.
split => [comp phi [] | comp phi]; intros; first (split; first by exists x; apply/ comp).
	by move => y val; have <-: x = y by apply/ mon_sing_op => //; last by apply/ comp.
have [ | [Mphi MphiMphi] prop] := (comp phi _); first by exists Fphi.
by have ->: Fphi = Mphi by apply/ H0; [ | apply prop].
Qed.

Lemma mon_cmpt_op M F:
	M \is_monotone_oracle_machine -> M \computes (F2MF F) <-> forall phi, (oeval M) phi (F phi).
Proof.
split => [comp phi q' | prop]; last first.
	apply cmpt_mon_sing_op => //; first exact: F2MF_sing; move => phi Fphi eq q'.
	by have [c val]:= (prop phi q'); exists c; rewrite -eq.
have [ | [Mphi evl] prop]:= (comp phi _); first by exists (F phi).
have [c val] := (evl q'); exists c; rewrite val.
by have ->: Mphi = (F phi) by rewrite (prop Mphi).
Qed.

Definition is_mon_cmpt (F: B ->> B'):=
	{M | M \is_monotone_oracle_machine /\ M \computes F}.
Notation "F '\is_monotone_computable'" := (is_mon_cmpt F) (at level 2).

Lemma sing_cmpt_elt M F c phi Fphi q' a':	M \computes F -> F \is_single_valued ->
	F phi Fphi -> M c phi q' = Some a' -> a' = Fphi q'.
Proof.
move => comp sing FphiFphi ev.
have [ | [Mphi MphiFphi] prop]:= (comp phi _); first by exists Fphi.
have eq: Mphi = Fphi by rewrite -(sing phi Fphi Mphi); last apply prop.
move: Mphi eq MphiFphi => _ -> MphiFphi.
pose Nphi q a:= (q <> q' /\ Fphi q = a) \/ (q' = q /\ a' = a).
have Nphitot: Nphi \is_total => [q | ].
	by case: (classic (q = q')) => ass; [exists a'; right | exists (Fphi q); left].
have [Mphi Mphiprop]:= choice Nphi Nphitot.
have MphiMphi: (oeval M) phi Mphi => [q | ].
	by case: (Mphiprop q) => [[_ <-] | [<- <-]]; [ | exists c].
apply Some_inj; case: (Mphiprop q') => [[ctr] | [_ ->]] //.
by have <-: Mphi = Fphi by apply/ sing; apply prop.
Qed.

Lemma cmpt_sing_mon_op F: F \is_single_valued ->
	F \is_computable_operator -> F \is_monotone_computable.
Proof.
move => sing [M comp].
pose p (c: C) phi q n:= if n < (pickle c) then
match (pickle_inv C n) with
	| None => false
	| Some c' => match M c' phi q with
		| None => false
		| Some a => true
	end
end else true.
have pprop: forall c phi q' n, p c phi q' n -> n < pickle c -> exists (c': C), pickle c' = n.
	move => c phi q' n; rewrite /p; case: ifP => //.
	case E: (pickle_inv C n) => [c' | ] ineq => //.
	by case: (M c' phi q') => //; exists c'; rewrite -(pickle_invK C n) E.
pose r (c: C) phi q':= search (p c phi q') (pickle c).
have rprop: forall c phi q', exists (c': C), pickle c' = r c phi q' => [c phi q' | ].
	case E: (r c phi q' == pickle c); first by exists c; apply /esym/eqP; rewrite E.
	have ineq: r c phi q' < pickle c.
		by rewrite ltn_neqAle; apply /andP; split; [rewrite E | apply/search_le].
	by apply/(pprop c _ q') => //; apply search_correct; rewrite /p pickleK_inv (ltnn (pickle c)).
pose N c phi q:= match (pickle_inv C (r c phi q)) with
	| None => None
	| Some c' =>  M c' phi q
end; exists N.
have mon: N \is_monotone_oracle_machine.
	move => n m phi q' a' ineq evl.
	case E: (pickle n < pickle m)%N.
		have[c rneqc]:= rprop n phi q'.
		have[c' rmeqc']:= rprop m phi q'.
		rewrite /N -rneqc pickleK_inv in evl.
		have rmlrn: r m phi q' <= r n phi q'.
			by apply/search_min; rewrite /p -rneqc pickleK_inv evl; case: ifP.
		suffices rnlrm: r n phi q' <= r m phi q'.
			have /eqP eq: r m phi q' == r n phi q' by rewrite eqn_leq; apply /andP.
			by rewrite /N eq -rneqc pickleK_inv.
		apply/search_min; rewrite /p -rmeqc' pickleK_inv; case: ifP => // ha.
		have: (p m phi q' (r m phi q')).
			by rewrite search_correct => //; rewrite /p; case: ifP => //; rewrite (ltnn (pickle m)).
		rewrite /p -rmeqc' pickleK_inv; case: ifP => [ | <- _]; case: (M c' phi q') => //.
		by apply/leq_trans; first apply/ ha; apply/leq_trans; [apply: ineq | apply/ leqnn].
	have ineq': pickle m <= pickle n by rewrite leqNgt E.
	rewrite -evl; f_equal; apply Some_inj; rewrite -!pickleK_inv; f_equal.
	by apply/eqP; rewrite eqn_leq; apply /andP.
split => //; rewrite -cmpt_mon_sing_op => // phi Fphi FphiFphi q'.
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
	have ineq: pickle c' <= pickle c by rewrite uprcq; apply/search_le.
	by apply/eqP; rewrite eqn_leq; apply/andP; split => //; rewrite leqNgt E.
exists c; rewrite /N -uprcq pickleK_inv eq (sing phi Fphi Mphi) => //.
by apply prop.
Qed.

Lemma mon_sing_cmpt_op (F: B ->> B'):
	F \is_single_valued -> F \is_computable_operator -> F \is_monotone_computable.
Proof.
by move => sing cmpt; apply/ cmpt_sing_mon_op.
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