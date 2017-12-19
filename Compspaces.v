From mathcomp Require Import all_ssreflect ssrnat.
Require Import Reals Lra Classical ClassicalFacts Psatz.
Require Import ClassicalChoice FunctionalExtensionality.
Load representations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Load SizeTypes.

Structure Compsp := Compspace {
  elts :> Type;
  codes : SizeType;
  is_code : codes -> elts -> Prop;
  not_is_valid : is_rep is_code;
  }.

Lemma id_rep (S :Type) : is_rep (fun (a b : S) => a = b).
Proof.
  split.
  - move => a.
    by exists a.
  - move => c a b [cea ceb].
    by rewrite -cea -ceb.
Qed.

Canonical Compspace_nat := @Compspace
  nat
  SizeType_nat
  (fun n m => n = m)
  (id_rep nat).

Canonical Compspace_pos := @Compspace
  positive
  SizeType_pos
  (fun n m => n = m)
  (id_rep positive).

Canonical Compspace_Z := @Compspace
  Z
  SizeType_Z
  (fun n m => n = m)
  (id_rep Z).

Canonical Compspace_Q := @Compspace
  Q
  Q
  (fun n m => n = m)
  (id_rep Q).
