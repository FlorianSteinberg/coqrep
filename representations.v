Load functions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Definition is_rep S T (delta: S ->> T) :=
  is_sur delta /\ is_sing delta.
(* S ->> T is a notation for S -> T -> Prop. This defines a representation to be a
surjective and singlevalued multi-valued function. Due to delta being single-valued
this can also be phrased as a representation being a partial surjection. *)

Structure rep_space := make_rep_space {
  space :> Type;
  names : Type;
  inhe: names;
  is_name : names ->> space;
  representation_is_valid : is_rep is_name
  }.
(* To construct a represented space it is necessary to provide a proof that the
representation is actually a representation. The names can be an arbitrary type
but will usually be something that can be computed on, i.e. Baire space or something.
I forgot why the names have to be inherited, but I believe there was a reason. *)

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
(* This is the product of represented spaces. At some point I should prove that this
is the product in some category, but I am unsure what the morphisms are supposed to be. *)

Definition is_mf_realizer (X Y : rep_space) (F: names X -> names Y) (f : X ->> Y) :=
  forall phi x y, is_name phi x -> is_name (F phi) (y) -> f x y.
(* One candidate for the morphisms: The multivalued realizable functions. *)

Definition is_realizer (X Y : rep_space) (F: names X -> names Y) (f : X -> Y) :=
  forall phi x, is_name phi x -> is_name (F phi) (f x).
(* A second candidate: the total singlevalued realizable functions *)

Definition is_computable (X Y : rep_space) (f : X -> Y) :=
  exists F, is_realizer F f.
(* I don't like this notion of computability as it requires the existence of a total
realizer. I think actually the realizer will automatically be primitive recursive.
Of course the use of mathematical functions is not debatable but I want to replace it
by a better notion of computability at some point. A candidate can be found at the end
of the functions.v file, but that candidate is not usable yet, so I will work with the
above notion of computability for now. *)

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
(* Using this lemma it is possible to provide a full functionspace construction
This functionspace construction will usually be utterly useless as the types
of names become higher and higher type objects. For a better function space one
should at least restrict to the continuously realizable functions. But for to make
that function space construction work a lot more work is needed. *)

Canonical rep_space_all_functions X Y := @make_rep_space
  (space X -> space Y)
  (names X -> names Y)
  (fun c => (inhe Y))
  (@is_realizer X Y)
  (@is_realizer_is_rep X Y).