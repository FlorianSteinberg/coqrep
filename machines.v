(* This file contains some definitions of what it can mean for functions
between different spaces to be computable. *)
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions continuity.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MACHINES.
Context (Q A Q' A' C : Type).

Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation "Q ~> A" := (nat -> Q -> option A) (at level 2).
Notation "B ~~> B'" := (nat -> B -> Q' -> option A') (at level 2).

Definition eval (N: Q ~> A) q Nq :=
	exists n, N n q = some (Nq).

Definition comp (N: Q ~> A) (f: Q ->> A) :=
	(eval N) \tightens f.
Notation "N '\computes' f" := (comp N f) (at level 2).

Lemma compu_sing N f:
	N \computes (F2MF f) -> forall q, (eval N) q (f q).
Proof.
move => comp q.
have ex: exists a, f q = a by exists (f q).
have [[a [n Nnqa] prop]]:= (comp q ex).
by exists n; rewrite Nnqa (prop a) //; exists n.
Qed.

Definition is_comp (f: Q ->> A) :=
	{N | N \computes f}.
Notation "f '\is_computable'" := (is_comp f) (at level 2).

Definition is_prim_rec (f: Q ->> A) :=
	{M | M \is_choice_for f}.
Notation "f '\is_primitive_recursive'" := (is_prim_rec f) (at level 2).

Lemma prim_rec_sing f :
	is_prim_rec (F2MF f).
Proof. by exists f. Qed.

Lemma prim_rec_is_comp (f: Q ->> A):
	f \is_primitive_recursive -> f \is_computable.
Proof.
move => [M Mprop].
exists (fun n q => Some (M q)) => q ex.
move: ((icf_F2MF_tight M f).1 Mprop) => thight.
split => [ | t' [n nprop]]; first by exists (M q); exists 0.
apply (thight q ex).
by apply Some_inj.
Qed.

Definition monotone (M: Q ~> A):=
	forall n m q a, n <= m -> M n q = Some a -> M m q = Some a.

Definition evaltt (M: B ~~> B') phi Mphi :=
	forall q', exists n, M n phi q' = some (Mphi q').

Definition comptt (M: B ~~> B') (F: B ->> B'):=
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
move: ((icf_F2MF_tight M F).1 Mprop) => thight.
specialize (thight phi ex).
split; first by exists (M phi) => q'; exists 0.
move => t' ev.
apply/ (thight.2 t').
apply functional_extensionality => q'.
move: (ev q') => [] n prop.
by apply Some_inj.
Qed.

Definition monotonett (M: B ~~> B):=
	forall n m phi q' a', n <= m -> M n phi q' = Some a' -> M m phi q' = Some a'.

End MACHINES.
Notation "f '\is_computable'" := (is_comp f) (at level 2).
Notation "Q ~> A" := (nat -> Q -> option A) (at level 2).
Notation "N '\computes' f" := (comp N f) (at level 2).
Notation "M '\type_two_computes' F" := (comptt M F) (at level 2).