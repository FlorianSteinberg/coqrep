From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Definition is_fun S T (F: S -> T -> Prop) :=
  forall s t t', and (F s t) (F s t') -> t = t'.

Definition is_sur S T (F: S -> T-> Prop) :=
  forall t, exists s, F s t.

Definition is_rep S T (delta: S -> T -> Prop) :=
  is_sur delta /\ is_fun delta.

Definition prod_fun (S S' T T' : Type)
  (F : S -> T -> Prop) (G : S' -> T' -> Prop) : S * S' -> (T * T') -> Prop :=
  fun c x => F c.1 x.1 /\ G c.2 x.2.

Definition dom (S T : Type) (f : S -> T -> Prop) (s : S) := exists t, f s t.

Definition is_surjective S T (F: S -> T-> Prop) :=
  forall t, exists s, F s t.

Lemma prod_surj (S S' T T' : Type) (F: S -> T -> Prop) (G : S' -> T' -> Prop) :
  is_surjective F /\ is_surjective G -> is_surjective (prod_fun F G).
Proof.
  move => [Fissur Gissur] x.
  move: (Fissur x.1) (Gissur x.2) => [c ciscode] [d discode].
  by exists (c,d).
Qed.

Definition is_single_valued S T (F: S -> T -> Prop) :=
  forall s t t', and (F s t) (F s t') -> t = t'.

Lemma prod_single_valued
(S S' T T' : Type) (F: S -> T -> Prop) (G : S' -> T' -> Prop) :
  is_single_valued F /\ is_single_valued G -> is_single_valued (prod_fun F G).
Proof.
  move => [Fissing Gissing] a x y.
    move => [] [a0isxname a1isxname] [a0isyname a1isyname].
    apply: injective_projections.
    - apply: (Fissing (a.1) x.1 y.1).
      by split.
    - apply: (Gissing (a.2) x.2 y.2).
      by split.
Qed.