(* This file is supposed to be come a module for multivalued functions *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Notation "S ->> T" := (S -> T -> Prop) (format "S ->> T", at level 2).

Definition mf_prod (S S' T T' : Type) (f : S ->> T) (g : S' ->> T') : (S * S') ->> (T * T') :=
  fun c x => f c.1 x.1 /\ g c.2 x.2.

Notation "f , g" := (mf_prod f g) (format "f , g", at level 50).

Definition is_sing S T (f: S ->> T) :=
  forall s t t', and (f s t) (f s t') -> t = t'.

Lemma prod_sing S S' T T' (f: S ->> T) (g : S' ->> T') :
  is_sing f /\ is_sing g -> is_sing (f , g).
Proof.
  move => [Fissing Gissing] a x y.
    move => [] [a0isxname a1isxname] [a0isyname a1isyname].
    apply: injective_projections.
    - apply: (Fissing (a.1) x.1 y.1).
      by split.
    - apply: (Gissing (a.2) x.2 y.2).
      by split.
Qed.

Definition is_sur S T (F: S ->> T) :=
  forall t, exists s, F s t.

Lemma prod_sur S S' T T' (f: S ->> T) (g : S' ->> T') :
  is_sur f /\ is_sur g -> is_sur (f , g).
Proof.
  move => [Fissur Gissur] x.
  move: (Fissur x.1) (Gissur x.2) => [c ciscode] [d discode].
  by exists (pair c d).
Qed.

Notation "S ~> T" := (S -> nat -> option T) (format "S ~> T", at level 2).

Definition eval S T (M : S ~> T) : (S ->> T) := fun a b => exists n b, M a n = some b.

Definition is_comp S T (f: S ->> T):=
  exists M, forall a b, f a b -> eval M a b.
