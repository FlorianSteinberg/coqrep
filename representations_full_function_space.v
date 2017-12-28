Load representations.
(* This stopped working when I started to allow representing subsets. *)

Require Import ClassicalChoice FunctionalExtensionality.
(* These are only needed to guarantee that it is always possible to provide a
realizer of a function. *)

Lemma is_realizer_is_rep (X Y : rep_space):
  (@is_realizer X Y) is_representation_of (fun f => forall x, (x is_element) -> (f x) is_element).
Proof.
  move: (representation_is_valid X) (representation_is_valid Y)
    => [Xsing Xsur] [Ysing Ysur].
  set C := names X.
  set D := names Y.
  split.
  - move => phi f g cond cond' isnamex isnamey.
    apply: functional_extensionality => x.
    move: (Xsur x) => a.
    move: cond (cond x ) cond' (cond' x ) => _ cond _ cond'.
    apply (Ysing (phi a) (f x) (g x)).
    split.
    - by apply isnamex.
    - by apply isnamey.
  - move => phi.
    set R := fun c d => forall x, delta c x -> delta d (f x).
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