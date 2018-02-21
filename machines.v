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
Context (Q A Q' A' : Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation "Q ~> A" := (nat -> Q -> option A) (at level 2).
Notation "B ~>> B'" := (nat -> B -> Q' -> option A') (at level 2).

Definition eval (N: Q ~> A) q Nq :=
	exists n, N n q = some (Nq).

Definition comp (N: Q ~> A) (f: Q ->> A) :=
	(eval N) \tightens f.
Notation "N '\computes' f" := (comp N f) (at level 2).

Lemma comp_sing N f:
	N \computes (F2MF f) -> forall q, (eval N) q (f q).
Proof.
move => comp q.
have ex: exists a, f q = a by exists (f q).
move: (comp q ex) => [] [] a [] n Nnqa prop.
exists n.
rewrite Nnqa (prop a) //.
by exists n.
Qed.

Definition is_comp (f: Q ->> A) :=
	{N | N \computes f}.
Notation "f '\is_computable'" := (is_comp f) (at level 2).

Definition is_prim_rec (f: Q ->> A) :=
	{M | M \is_choice_for f}.
Notation "f '\is_primitive_recursive'" := (is_prim_rec f) (at level 2).

Lemma prim_rec_sing f :
	is_prim_rec (F2MF f).
Proof.
by exists f.
Qed.

Lemma prim_rec_is_comp (f: Q ->> A):
	f \is_primitive_recursive -> f \is_computable.
Proof.
move => [] M Mprop.
exists (fun n q => Some (M q)) => q ex.
specialize (Mprop q ex).
split; first by exists (M q); exists 0.
move => t' ev.
apply/ (Mprop.2 t').
move: (ev) => [] n prop.
by apply Some_inj.
Qed.

Definition evaltt (M: B ~>> B') phi Mphi :=
	forall q', exists n, M n phi q' = some (Mphi q').

Definition comptt (M: B ~>> B') (F: B ->> B'):=
  (evaltt M) \tightens F.
Notation "M '\type_two_computes' F" := (comptt M F) (at level 2).

Definition is_comptt (F: B ->> B') :=
	{M| M \type_two_computes F}.
Notation "F '\is_type_two_computable'" := (is_comptt F) (at level 2).

Definition is_prim_rectt (F: B ->> B') :=
	{M | M \is_choice_for F}.
Notation "F '\is_type_two_primitive_recursive'" := (is_prim_rectt F) (at level 2).

Lemma prim_rec_is_comp_tt (F: B ->> B'):
	F \is_type_two_primitive_recursive -> F \is_type_two_computable.
Proof.
move => [] M Mprop.
exists (fun n phi q => Some (M phi q)) => phi ex.
specialize (Mprop phi ex).
split; first by exists (M phi) => q'; exists 0.
move => t' ev.
apply/ (Mprop.2 t').
apply functional_extensionality => q'.
move: (ev q') => [] n prop.
by apply Some_inj.
Qed.

End MACHINES.
Notation "f '\is_computable'" := (is_comp f) (at level 2).
Notation "Q ~> A" := (nat -> Q -> option A) (at level 2).
Notation "N '\computes' f" := (comp N f) (at level 2).
Notation "M '\type_two_computes' F" := (comptt M F) (at level 2).