(* This file provides an alternative formulation of represented spaces that saves
the input and output types of the names *)
Load universal_machine.

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
  delta is_single_valued_in elements /\ forall t, elements t -> range delta t.
Notation "delta 'is_representation_of' elements" := (is_rep_of delta elements) (at level 2).
(* To make subspaces work, we allow predicates as the underlying set of a represented space. *)

Definition is_rep_of_wrt S T (delta: S ->> T) (elements: T -> Prop) (equals: T-> T -> Prop) :=
  (forall s t t', elements t -> elements t' -> delta s t -> delta s t' -> equals t t')
    /\ (forall t t' s, equals t t' -> delta s t -> delta s t')
    /\ forall t, elements t -> range delta t.
Notation "delta 'is_representation_wrt' eq 'of' elements" := 
  (is_rep_of_wrt delta elements eq) (at level 2).
(* This is to make it possible to identify elements arbirarily, i.e. make quotients work. *)

Lemma sur_rep_b S T (delta: S ->> T) :
  delta is_representation <-> delta is_representation_of (fun x => True).
Proof.
  split.
  - move => [issing issur].
    by split.
  - move => [issing issur].
    split.
    - move => s.
      by apply: (issing s).
    - move => s.
      by apply: (issur s).
Qed.

Lemma sur_rep S T (delta: S ->> T) :
  delta is_representation -> delta is_representation_of (fun x => True).
Proof.
  move: (sur_rep_b delta) => [cond cond'].
  exact: cond.
Qed.

Lemma sur_rep_sing_b S T (delta: S ->> T) (elements: T -> Prop) :
  delta is_representation_of elements <-> delta is_representation_wrt (fun x y => x = y) of elements.
Proof.
  split.
  - move => [sing sur].
    split.
    - move => s t t'.
      by apply: (sing s t t').
    - split.
      - move => t t' s tet'.
        by rewrite -tet'.
      - by apply sur.
  - move => [sing [eq sur]].
    split.
    - move => s t t'.
      apply: (sing s t t').
    - done.
Qed.

Lemma sur_rep_sing S T (delta: S ->> T) (elements: T -> Prop) :
  delta is_representation_of elements -> delta is_representation_wrt (fun x y => x = y) of elements.
Proof.
  move: (sur_rep_sing_b delta elements) => [cond cond'].
  exact: cond.
Qed.


(* To construct a represented space it is necessary to provide a proof that the
representation is actually a representation. The names can be an arbitrary type
but will usually be something that can be computed on, i.e. Baire space or something.
At some point I will probably change the names to be a size_type. The type of names
must be inherited for the rather irrelevant full function-space construction to
work. This may change depending on whether other function space constructions also
need this or not. *)
Structure type := make_rep_space {
  space : Type;
  elements : space -> Prop;
  equals : space -> space -> Prop;
  questions : Type;
  answer_type : Type;
  delta : (questions -> option(answer_type)) ->> space;
  representation_is_valid : delta is_representation_wrt equals of elements
  }.
Notation answers X := (option (answer_type X)).
Notation names X := ((questions X) -> (answers X)).

Lemma prod_rep (X Y : type):
  (fun (phipsi : (questions X + questions Y -> option(answer_type X + answer_type Y))) x =>
      delta (fun q => match phipsi (inl q) with
        | None => None
        | Some (inl a) => Some a
        | Some (inr b) => None
      end) x.1 /\ delta (fun q => match phipsi (inr q) with
        | None => None
        | Some (inl a) => None
        | Some (inr b) => Some b
      end) x.2)
    is_representation_wrt
  (fun x y => equals x.1 y.1 /\ equals x.2 y.2)
    of
  (fun x => elements x.1 /\ elements x.2).
Proof.
  move: (@representation_is_valid X) (@representation_is_valid Y)
    => [xsing [xeq xsur]] [ysing [yeq ysur]].
  - split.
    - move => phipsi [x y] [x' y'] /= [iex iey] [iex' iey'] [inx iny] [inx' iny'].
      split.
      apply: xsing => //.
      apply: inx.
      apply: inx'.
      apply: ysing => //.
      apply iny.
      apply iny'.
    - split. 
      - move => x y phi [xey1 xey2] [inx iny].
        split.
        apply: (xeq x.1) => //.
        apply: (yeq x.2) => //.
      - move => [x y] /= [iex iey].
        move: (xsur x iex) (ysur y iey) => [phi inx] [psi iny].
        exists (fun q => match q with
          | inl qx => match phi qx with
            | Some a => Some (inl a)
            | None => None
          end
          | inr qy => match psi qy with
            | Some a => Some (inr a)
            | None => None
          end
        end).
        split => /=.
        replace (fun q : questions X =>
        match
         match phi q with
          | Some a => Some (inl a)
          | None => None
         end
        with
         | Some (inl a) => Some a
         | Some (inr _) => None
         | None => None
        end) with phi.
        done.
        apply: functional_extensionality => q.
        elim (phi q).
        done.
        done.
        replace (fun q : questions Y =>
        match
         match psi q with
          | Some a => Some (inr a)
          | None => None
         end
        with
         | Some (inr a) => Some a
         | Some (inl _) => None
         | None => None
        end) with psi.
        done.
        apply: functional_extensionality => q.
        elim (psi q).
        done.
        done.
Qed.

(* This is the product of represented spaces. At some point I should prove that this
is the product in some category, but I am unsure what the morphisms are supposed to be. *)

Notation rep_space := type.
Notation "'rep'" := @delta (at level 2).
Notation "phi 'is_name_of' x" := (delta phi x) (at level 2).
Notation "x 'is_element'" := (elements x) (at level 2).
Notation "x 'is_from' X" := (@elements X x) (at level 2).
Notation "x 'equal' y" := (@equals x y) (at level 2).

Canonical rep_space_prod X Y := @make_rep_space
  (space X * space Y)
  (fun x => x.1 is_element /\ x.2 is_element)
  (fun x y => equals x.1 y.1 /\ equals x.2 y.2)
  (@questions X + @questions Y)
  (@answer_type X + @answer_type Y)
  (fun (phipsi : (questions X + questions Y -> option(answer_type X + answer_type Y))) x =>
      delta (fun q => match phipsi (inl q) with
        | None => None
        | Some (inl a) => Some a
        | Some (inr b) => None
      end) x.1 /\ delta (fun q => match phipsi (inr q) with
        | None => None
        | Some (inl a) => None
        | Some (inr b) => Some b
      end) x.2)
  (@prod_rep X Y).

Definition make_rep_space_from_sur
  (space : Type)
  (questions : Type)
  (answers : Type)
  (delta : (questions->option(answers)) ->> space) (representation_is_valid : is_rep delta) :=
  @make_rep_space space
    (fun x=> True)
    (fun x y => x= y)
    questions
    answers
    delta
    (sur_rep_sing (sur_rep representation_is_valid))
  .

Lemma fun_rep_on_range S X (f : S -> X) :
  (F2MF f) is_representation_of (range (F2MF f)).
Proof.
  split.
  - move => s t t' tfr t'fr fst fst'.
    by rewrite -fst -fst'.
  - by move => t tfrf.
Qed.

Definition make_rep_space_from_fun
  (space : Type)
  (questions : Type)
  (answers : Type)
  (delta: (questions->option answers) -> space) :=
    @make_rep_space
      space
      (range (F2MF delta))
      (fun x y => x = y)
      questions
      answers
      (F2MF delta)
      (sur_rep_sing (fun_rep_on_range delta))
    .

Lemma single_valued_rep_on_range S T (f : S ->> T) :
  f is_single_valued -> f is_representation_of (range f).
Proof.
  move => sing.
  split.
  - move => s t t' tfr t'fr.
    by apply sing.
  - done.
Qed.

Definition make_rep_space_from_mfun
  (space : Type)
  (questions : Type)
  (answers : Type)
  (delta: (questions -> option answers) ->> space)
  (sing: delta is_single_valued) :=
    @make_rep_space
      space
      (range delta)
      (fun x y => x = y)
      questions
      answers
      delta
      (sur_rep_sing (single_valued_rep_on_range sing)).

Definition is_mf_realizer (X Y : rep_space) F (f : (space X) ->> (space Y)) :=
  forall phi x y, delta phi x -> delta (F phi) (y) -> f x y.
(* One candidate for the morphisms: The multivalued realizable functions. *)

Definition is_realizer (X Y : rep_space) F (f: space X -> space Y) :=
  is_mf_realizer F (F2MF f).
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

Notation "X ~> Y" := (nat -> (names X) -> (questions Y) -> answers Y) (format "X ~> Y", at level 2).
(* I think about this type as a type of machines: For M : B ~> B' I "read M s n = nothing" as
"the Machine can't say anything about the return value yet" and "M s n = some t" as "after n
steps the machine considers t to be the best answer". Since no assumption about concurrency
have been made, in general a machine will produce an infinite list of return values. *)

Definition eval (X Y : rep_space) (M : X ~> Y) : ((names X) ->> (names Y)) :=
  fun (phi : names X) (psi : names Y) => forall (a : questions Y), exists n, M n phi a = psi a.
(* if M is a machine then eval M is the function the machine computes. Since no assumptions
about convergence or concurrency have been made, the computed multivalued function need
neither be singlevalued nor total. *)

Definition is_comput (X Y : rep_space) (F: (names X) ->> (names Y)):=
  exists M, forall phi, (exists psi, F phi psi) -> forall psi, (eval M phi psi -> F phi psi).
(* This is the best candidate for computability I have come up with so far: If there are eligible
return values then the machine produces one of these, but if there are none, the machine may behave
arbitrarily. I am not one hundred percent sure this is the right notion, but pretty confident. *)
Notation "F 'is_computable'" := (is_comput F) (at level 2).