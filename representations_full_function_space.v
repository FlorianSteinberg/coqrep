Load representations.

Require Import ClassicalChoice FunctionalExtensionality.
(* These are only needed to guarantee that it is always possible to provide a
realizer of a function. *)

Lemma is_realizer_is_rep (X Y : rep_space): is_rep (@is_realizer X Y).
Proof.
  move: (representation_is_valid X) (representation_is_valid Y)
    => [Xsur Xsing] [Ysur Ysing].
  set C := names X.
  set D := names Y.
  split.
  - move => f.
    set R := fun c d => forall x, is_name c x -> is_name d (f x).
    apply: (@choice (names X) (names Y) R) => c.
    case: (classic (exists x, is_name c x)).
    - move => [x xisnameofc].
      move: (Ysur (f x)) => [d dinofx].
      exists d.
      move => x0 cinox0.
      have: x = x0.
      - by apply: (Xsing c x x0).
      move => xeqx0.
      by rewrite -xeqx0.
    - move => assump.
      exists (inhe Y).
      move => x cisnox.
      exfalso.
      apply: assump.
      by exists x.
  - move => phi f g [isnamex isnamey].
    apply: functional_extensionality => x.
    move: (Xsur x) => [a ainox].
    apply (Ysing (phi a) (f x) (g x)).
    split.
    - by apply isnamex.
    - by apply isnamey.
Qed.
Arguments is_realizer_is_rep {X Y}.

(* Using this lemma it is possible to provide a full functionspace construction
This functionspace construction will usually be utterly useless as the types
of names become higher and higher type objects. For a better function space one
should at least restrict to the continuously realizable functions. But for to make
that function space construction work a lot more work is needed. *)

Canonical rep_space_all_functions X Y := @make_rep_space
  (space X -> space Y)
  (names X -> names Y)
  (fun c => (inhe Y))
  (is_realizer)
  (is_realizer_is_rep).