Load functions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Definition is_rep S T (delta: S ->> T) :=
  is_sur delta /\ is_sing delta.
Notation "delta 'is_representation'" := (is_rep delta) (at level 2).
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
Notation "phi 'is_name_of' x" := (is_name phi x) (at level 2).
Notation "'delta' X" := (@is_name X) (at level 2).

Lemma prod_rep (X Y : rep_space): (delta X\, delta Y) is_representation.
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
  (delta X \, delta Y)
  (@prod_rep X Y).
(* This is the product of represented spaces. At some point I should prove that this
is the product in some category, but I am unsure what the morphisms are supposed to be. *)

Definition is_mf_realizer (X Y : rep_space) (F: names X -> names Y) (f : X ->> Y) :=
  forall phi x y, is_name phi x -> is_name (F phi) (y) -> f x y.
(* One candidate for the morphisms: The multivalued realizable functions. *)

Definition is_realizer (X Y : rep_space) (F: names X -> names Y) (f : X -> Y) :=
  forall phi x, is_name phi x -> is_name (F phi) (f x).
(* A second candidate: the total singlevalued realizable functions *)
Notation "F 'is_realizer_of f" := (is_realizer F f) (at level 2).
Arguments is_realizer {X Y}.

Definition is_comp (X Y : rep_space) (f : X -> Y) :=
  exists F, is_realizer F f.
(* I don't like this notion of computability as it requires the existence of a total
realizer. I think actually the realizer will automatically be primitive recursive.
Of course the use of mathematical functions is not debatable but I want to replace it
by a better notion of computability at some point. A candidate can be found at the end
of the functions.v file, but that candidate is not usable yet, so I will work with the
above notion of computability for now. *)
Notation "f 'is_computable'" := (is_comp f) (at level 2).