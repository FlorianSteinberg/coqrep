(* This file is supposed to contain the definition of a universal machine and the proof
that the machine is actually universal. The universal machine is a machine of type two
and it should work for any continuous function from B -> B. Usually B is the Baire space,
here, i.e. the set of all mappings from strings to strings. However, since I don't want
to rely on a handwritten type of strings as I attempted in the file "operators.v" I use
more generaly a space S -> T as substitute for B. *)
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions continuity.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MACHINES.
Context (Q I Q' I' : Type).
Notation A := (option I).
Notation A' := (option I').
Notation B := (Q -> I).
Notation B' := (Q' -> I').
Notation "B ~> B'" := (nat -> B -> Q' -> A') (at level 2).

Definition eval (M: B ~> B') phi Mphi:=
	forall q', exists n, M n phi q' = some (Mphi q').

Definition comp (M: B ~> B') (F: B ->> B'):=
  (eval M) tightens F.
Notation "M 'computes' F" := (comp M F) (at level 2).

Definition is_comp (F: B ->> B'):=
	exists M, M computes F.
Notation "F 'is_computable'" := (is_comp F) (at level 2).

Definition is_prim_rec (F: B ->> B'):=
	exists M, forall phi, phi from_dom F -> F phi (fun q' => M phi q').
Notation "F 'is_primitive_recursive'" := (is_prim_rec F) (at level 2).

Lemma prim_rec_is_comp (F: B ->> B'):
	F is_primitive_recursive -> F is_computable.
Proof.
move => [] M Mprop.
exists (fun n phi q' => some(M phi q')).
move => phi => [] [] Fphi Fphiprop.
split.
	exists (fun q' => M phi q').
	move => q'.
	by exists 0.
move => Mphi MphiMphi.
replace Mphi with (fun q' => M phi q').
	apply/ Mprop.
	by exists Fphi.
apply functional_extensionality => q'.
move: (MphiMphi q') => [] n eq.
by apply Some_inj.
Qed.
End MACHINES.
Notation "M 'computes' F" := (comp M F) (at level 2).
Notation "F 'is_computable'" := (is_comp F) (at level 2).
Notation "F 'is_primitive_recursive'" := (is_prim_rec F) (at level 2).
