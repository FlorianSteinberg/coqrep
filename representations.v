From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Definition is_rep S T (delta: S ->> T) :=
  delta is_single_valued /\ delta is_surjective.
Notation "delta 'is_representation'" := (is_rep delta) (at level 2).
(* S ->> T is a notation for S -> T -> Prop. This defines a representation to be a
surjective and singlevalued multi-valued function. Due to delta being single-valued
this can also be phrased as a representation being a partial surjection. *)

Definition is_rep_of S T (delta: S ->> T) (P : T -> Prop) :=
  delta is_single_valued_wrt (fun t t' => P t -> P t' -> t = t') /\ delta is_surjective_wrt P.
Notation "delta 'is_representation_of' elements" := (is_rep_of delta elements) (at level 2).
(* To make subspaces work, we allow predicates as the underlying set of a represented space. *)

Definition is_rep_of_wrt S T (delta: S ->> T) (P: T -> Prop) (R: T-> T -> Prop) :=
  delta is_single_valued_wrt R /\ delta is_surjective_wrt P.
Notation "delta 'is_representation_wrt' equals 'of' elements" := 
  (is_rep_of_wrt delta elements equals) (at level 2).
(* This is to make it possible to identify elements arbirarily, i.e. make quotients work. *)

Lemma sur_rep_b S T (delta: S ->> T) :
  delta is_representation <-> delta is_representation_of (fun x => True).
Proof.
split.
- move => [issing issur].
	split.
 		move => s t t' dst dst' _ _.
 		by apply: (issing s t t').
  move => t _ .
  move: (issur t) => [] s dst.
  by exists s.
move => [issing issur].
split.
- move => s t t' dst dst'.
  by apply: (issing s t t').
move => t.
have: True.
	done.
move => true.
move: (issur t true) => []s []dst_.
by exists s.
Qed.

Lemma sur_rep S T (delta: S ->> T) :
  delta is_representation -> delta is_representation_of (fun x => True).
Proof.
  move: (sur_rep_b delta) => [cond cond'].
  exact: cond.
Qed.

Lemma sur_rep_sing_b S T (delta: S ->> T) (P: T -> Prop) :
  delta is_representation_of P <-> delta is_representation_wrt (fun x y => P x -> P y -> x = y) of P.
Proof.
done.
Qed.

Lemma sur_rep_sing S T (delta: S ->> T) (P: T -> Prop) :
  delta is_representation_of P -> delta is_representation_wrt (fun x y => P x -> P y -> x = y) of P.
Proof.
  move: (sur_rep_sing_b delta P) => [cond cond'].
  exact: cond.
Qed.

(* To construct a represented space it is necessary to provide a proof that the
representation is actually a representation. The names can be an arbitrary type
but will usually be something that can be computed on, i.e. Baire space or something.
At some point I will probably change the names to be a size_type. The type of names
must be inherited for the rather irrelevant full function-space construction to
work. This may change depending on whether other function space constructions also
need this or not. *)
Module rep_space.
Structure type := make_rep_space {
  space : Type;
  elements : space -> Prop;
  equals : space -> space -> Prop;
  names : Type;
  inhe: names;
  delta : names ->> space;
  representation_is_valid : delta is_representation_wrt equals of elements
  }.

Lemma prod_rep (X Y : type):
  (@delta X \, @delta Y)
    is_representation_wrt
  (fun x y => equals x.1 y.1 /\ equals x.2 y.2)
    of
  (fun x => elements x.1 /\ elements x.2).
Proof.
move: (@representation_is_valid X) (@representation_is_valid Y) => [xsing xsur] [ysing ysur].
split.
	move => phi x y [inx1 inx2] [iny1 iny2].
  split.
  - by apply: (xsing phi.1 x.1 y.1).
  by apply: (ysing phi.2 x.2 y.2).
move => [x y] [xe ye].
move: (xsur x xe) => []phi[]dphix condx.
move: (ysur y ye) => []psi[]dpsiy condy.
exists (phi,psi).
split.
	by split.
move => []phi' psi' [x' y'] [dphi'x' dpsi'y'] [dphi'x dphi'y].
split.
	by apply (condx phi' x').
by apply (condy psi' y').
Qed.

End rep_space.
(* This is the product of represented spaces. At some point I should prove that this
is the product in some category, but I am unsure what the morphisms are supposed to be. *)

Notation rep_space := rep_space.type.
Notation "'rep'" := @rep_space.delta (at level 2).
Notation "phi 'is_name_of' x" := (rep_space.delta phi x) (at level 2).
Notation "x 'is_element'" := (rep_space.elements x) (at level 2).
Notation "x 'is_from' X" := (@rep_space.elements X x) (at level 2).
Notation "x 'equal' y" := (@rep_space.equals x y) (at level 2).
Notation names X := (rep_space.names X).
Notation space X := (rep_space.space X).
Notation delta X := (rep_space.delta X).
Notation equals X := (rep_space.equals X).

Canonical rep_space_prod X Y := @rep_space.make_rep_space
  (space X * space Y)
  (fun x => x.1 is_element /\ x.2 is_element)
  (fun x y => equals x.1 y.1 /\ equals x.2 y.2)
  (names X * names Y)
  (pair (rep_space.inhe X) (rep_space.inhe Y))
  (rep X \, rep Y)
  (@rep_space.prod_rep X Y).

Definition make_rep_space_from_sur
  (space : Type) (names : Type) (inhe : names)
  (delta : names ->> space) (representation_is_valid : is_rep delta) :=
  @rep_space.make_rep_space space
    (fun x=> True)
    (fun x y => True -> True -> x= y)
    names
    inhe
    delta
    (sur_rep_sing (sur_rep representation_is_valid))
  .

Lemma fun_rep_on_range S X (f : S -> X) :
  (F2MF f) is_representation_of (range (F2MF f)).
Proof.
split.
	move => s t t' fst fst' tfr t'fr.
  by rewrite -fst -fst'.
move => t [] s fst.
exists s.
split => //.
move => s' x' fs't fs't'.
by exists s'.
Qed.

Definition make_rep_space_from_fun
  (space : Type)
  (names : Type)
  (inhe : names)
  (delta : names -> space) :=
    @rep_space.make_rep_space
      space
      (range (F2MF delta))
      (fun x y => x from_range (F2MF delta) -> y from_range (F2MF delta) -> x = y)
      names
      inhe
      (F2MF delta)
      (sur_rep_sing (fun_rep_on_range delta))
    .

Lemma single_valued_rep_on_range S T (f : S ->> T) :
  f is_single_valued -> f is_representation_of (range f).
Proof.
move => sing.
split => //.
	move => s t t' fst fst' tfr t'fr.
	by apply (sing s t t').
move => t [] s fst.
exists s.
split => //.
move => s' t' _ fs't'.
by exists s'.
Qed.

Definition make_rep_space_from_mfun
  (space: Type)
  (names : Type)
  (inhe:names)
  (delta: names ->> space)
  (sing: delta is_single_valued) :=
    @rep_space.make_rep_space
      space
      (range delta)
      (fun x y => x from_range delta -> y from_range delta -> x = y)
      names
      inhe
      delta
      (sur_rep_sing (single_valued_rep_on_range sing)).

Definition is_mf_realizer (X Y : rep_space) (F: names X -> names Y) (f : (space X) ->> (space Y)) :=
  forall phi x y, delta phi x -> delta (F phi) (y) -> f x y.
(* One candidate for the morphisms: The multivalued realizable functions. *)

Definition is_realizer (X Y : rep_space) (F: names X -> names Y) (f : space X -> space Y) :=
  forall phi x, phi is_name_of x -> x is_element -> (F phi) is_name_of (f x).
(* A second candidate: the total singlevalued realizable functions *)
Notation "F 'is_realizer_of' f" := (is_realizer F f) (at level 2).
Arguments is_realizer {X Y}.

Definition is_comp (X Y : rep_space) (f : space X -> space Y) :=
  exists F, is_realizer F f.
(* I don't like this notion of computability as it requires the existence of a total
realizer. I want to replace it by a better notion of computability at some point.
A candidate can be found at the end of the functions.v file, but that candidate is not
usable yet, so I will work with the above notion for now. *)
Notation "f 'is_computable'" := (is_comp f) (at level 2).