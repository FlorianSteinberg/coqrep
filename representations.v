Load functions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Definition is_rep S T (delta: S ->> T) :=
  delta is_single_valued /\ delta is_surjective.
Notation "delta 'is_representation'" := (is_rep delta) (at level 2).
(* S ->> T is a notation for S -> T -> Prop. This defines a representation to be a
surjective and singlevalued multi-valued function. Due to delta being single-valued
this can also be phrased as a representation being a partial surjection. *)

Definition is_rep_of S T (delta: S ->> T) (elements : T -> Prop) :=
  delta is_single_valued /\ forall t, elements t -> range delta t.
Notation "delta 'is_representation_of' elements" := (is_rep_of delta elements) (at level 2).
(* To make subspaces work, we allow predicates as the underlying set of a represented space. *)

Lemma sur_rep S T (delta: S ->> T) :
  delta is_representation -> delta is_representation_of (fun x => True).
Proof.
  move => [issing issur].
  by split.
Qed.

(* To construct a represented space it is necessary to provide a proof that the
representation is actually a representation. The names can be an arbitrary type
but will usually be something that can be computed on, i.e. Baire space or something.
I forgot why the names have to be inherited, but I believe there was a reason. *)
Structure rep_space := make_rep_space {
  space :> Type;
  elements : space -> Prop;
  names : Type;
  inhe: names;
  delta : names ->> space;
  representation_is_valid : delta is_representation_of elements
  }.
(* The corecion shouldn't be there anymore because of the use of subspaces: For
instance both the real numbers and the unit interval should have the real numbers
as space, so the structure as represented space is not determined by the space any-
more. It is inconvenient to go without the coercion though and up unitl now it has
not lead to problems. Maybe I have to have a structure "rep_subspace" at some
point? *)
Notation "'rep'" := @delta (at level 2).
Notation "phi 'is_name_of' x" := (delta phi x) (at level 2).
Notation "x 'is_element'" := (elements x) (at level 2).

Definition make_rep_space_from_sur
  (space : Type) (names : Type) (inhe : names)
  (delta : names ->> space) (representation_is_valid : is_rep delta) :=
  @make_rep_space space (fun x=> True) names inhe delta (sur_rep representation_is_valid).

Lemma fun_rep_on_range S T (f : S -> T) :
  (F2MF f) is_representation_of (range (F2MF f)).
Proof.
  split.
  - move => s t t' [fst fst'].
    by rewrite -fst -fst'.
  - by move => t tfrf.
Qed.

Definition make_rep_space_from_fun
  (space : Type) (names : Type) (inhe:names) (delta: names -> space) :=
    @make_rep_space space (range (F2MF delta)) names inhe
      (F2MF delta) (fun_rep_on_range delta).

Lemma prod_rep (X Y : rep_space):
  (rep X \, rep Y) is_representation_of (fun x => x.1 is_element /\ x.2 is_element).
Proof.
  move: (representation_is_valid X) (representation_is_valid Y)
    => [issingd issurd] [issingd' issurd'].
  split.
  - by apply: prod_sing.
  - move => x [x1ie x2ie].
    move: (issurd x.1 x1ie) (issurd' x.2 x2ie) => x1inr x2inr.
    by apply: prod_range.
Qed.

Canonical rep_space_prod X Y := @make_rep_space
  (space X * space Y)
  (fun x => x.1 is_element /\ x.2 is_element)
  (names X * names Y)
  (pair (inhe X) (inhe Y))
  (rep X \, rep Y)
  (@prod_rep X Y).
(* This is the product of represented spaces. At some point I should prove that this
is the product in some category, but I am unsure what the morphisms are supposed to be. *)

Definition is_mf_realizer (X Y : rep_space) (F: names X -> names Y) (f : (space X) ->> (space Y)) :=
  forall phi x y, delta phi x -> delta (F phi) (y) -> f x y.
(* One candidate for the morphisms: The multivalued realizable functions. *)

Definition is_realizer (X Y : rep_space) (F: names X -> names Y) (f : space X -> space Y) :=
  forall phi x, phi is_name_of x -> x is_element
    -> (f x) is_element /\ (F phi) is_name_of (f x).
(* A second candidate: the total singlevalued realizable functions *)
Notation "F 'is_realizer_of' f" := (is_realizer F f) (at level 2).
Arguments is_realizer {X Y}.

Definition is_comp (X Y : rep_space) (f : space X -> space Y) :=
  exists F, is_realizer F f.
(* I don't like this notion of computability as it requires the existence of a total
realizer. I think actually the realizer will automatically be primitive recursive.
Of course the use of mathematical functions is not debatable but I want to replace it
by a better notion of computability at some point. A candidate can be found at the end
of the functions.v file, but that candidate is not usable yet, so I will work with the
above notion of computability for now. *)
Notation "f 'is_computable'" := (is_comp f) (at level 2).