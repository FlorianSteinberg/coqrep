Load size_types.

Inductive one : Type :=
  | star.

Canonical size_type_one := @make_size_type
  one
  Major_nat
  (fun x n => n = 1)
  star.

Canonical size_type_nat := @make_size_type 
  nat
  Major_nat
  (fun n m => n = m)
  0.

Require Import Reals.

Fixpoint size_pos (n : positive) := match n with
  | xH => 0
  | xO m => S (size_pos m)
  | xI m => S (size_pos m)
end.

Canonical size_type_pos := @make_size_type
  positive
  Major_nat
  (fun n m => size_pos n = m)
  xH
  .

Fixpoint size_Z (z : Z) := match z with
  | Z0 => 1
  | Zpos n => size_pos n + 1
  | Zneg n => size_pos n + 1
end.

Canonical size_type_Z := @make_size_type 
  Z
  Major_nat
  (fun z n => size_Z z = n)
  Z0.

Require Import Lra.

Fixpoint size_Q (q : QArith_base.Q) :=
  size_Z (QArith_base.Qnum q) + size_pos (QArith_base.Qden q).

Canonical size_type_Q := @make_size_type
  QArith_base.Q
  Major_nat
  (fun q n => size_Q q = n)
  (QArith_base.Qmake 0 1).