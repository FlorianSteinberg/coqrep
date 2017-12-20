Load representations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Structure copolish_space := make_copolish_space {
  elts :> rep_space;
  size : (@names elts) ->> nat;
  size_matches : (is_sing size) /\ (forall phi, dom (@is_name elts) phi -> dom size phi)
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
