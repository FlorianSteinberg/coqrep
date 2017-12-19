From mathcomp Require Import all_ssreflect ssrnat.
Require Import Reals Lra Classical ClassicalFacts Psatz.
Require Import ClassicalChoice FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Structure SizeType := size_type {
  elems :> Type;
  size : elems -> nat;
  inh: elems
  }.

Inductive one : Type :=
  | star.

Canonical SizeType_one := @size_type
  one
  (fun x => 1)
  star.

Canonical SizeType_nat := @size_type 
  nat
  (fun n => n)
  0.

Fixpoint size_pos (n : positive) := match n with
  | xH => 0
  | xO m => S (size_pos m)
  | xI m => S (size_pos m)
end.

Canonical SizeType_pos := @size_type 
  positive
  size_pos
  xH
  .

Fixpoint size_Z (z : Z) := match z with
  | Z0 => 1
  | Zpos n => size_pos n + 1
  | Zneg n => size_pos n + 1
end.

Canonical SizeType_Z := @size_type 
  Z
  size_Z
  Z0.

Fixpoint size_Q (q : QArith_base.Q) :=
  size_Z (QArith_base.Qnum q) + size_pos (QArith_base.Qden q).

Canonical Q := @size_type
  QArith_base.Q
  size_Q
  (QArith_base.Qmake 0 1).

Canonical SizeType_sum X Y := @size_type
  (elems X + elems Y)
  (fun z => (match z with
    | inl x => size x
    | inr y => size y
   end))
   ( inl ( inh X ) ).

Canonical SizeType_prod X Y := @size_type
  (elems X * elems Y)
  (fun x => size x.1 + size x.2)
  ( (inh X, inh Y) ).
