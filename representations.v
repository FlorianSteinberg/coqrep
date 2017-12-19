Load functions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Definition is_rep S T (delta: S -> T -> Prop) :=
  is_sur delta /\ is_sing delta.

Structure rep_space := make_rep_space {
  space :> Type;
  names : Type;
  inhe: names;
  is_name : names ->> space;
  representation_is_valid : is_rep is_name
  }.

Lemma prod_rep (X Y : rep_space): is_rep (@is_name X,@is_name Y).
Proof.
  move: (representation_is_valid X) (representation_is_valid Y)
    => [issurd issingd] [issurd' issingd'].
  split.
  - by apply: prod_sur.
  - by apply: prod_sing.
Qed.

Canonical rep_space_prod X Y := @make_rep_space
  (space X * space Y)
  (names X * names Y)
  (pair (inhe X) (inhe Y))
  (@is_name X, @is_name Y)
  (@prod_rep X Y).

Definition is_mf_realizer (X Y : rep_space) (F: names X -> names Y) (f : X ->> Y) :=
  forall phi x y, is_name phi x -> is_name (F phi) (y) -> f x y.

Notation "S ~> T" := (S -> nat -> option T) (format "S ~> T", at level 2).

Definition is_realizer (X Y : rep_space) (F: names X -> names Y) (f : X -> Y) :=
  forall phi x, is_name phi x -> is_name (F phi) (f x).

Require Import ClassicalChoice FunctionalExtensionality.

Lemma function_representation (X Y : rep_space): is_rep (@is_realizer X Y).
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