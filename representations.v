Load functions.
Require Import ClassicalChoice FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Structure Repsp := Repspace {
  space :> Type;
  names : Type;
  inhe: names;
  is_name : names -> space -> Prop;
  representation_is_valid : is_rep is_name
  }.

Definition is_realizer (X Y : Repsp) phi (f : X -> Y) :=
  forall a x, is_name a x -> is_name (phi a) (f x).

Lemma function_representation (X Y : Repsp): is_rep (@is_realizer X Y).
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