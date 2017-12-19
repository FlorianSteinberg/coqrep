(* This file is supposed to be come a module for multivalued functions *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Notation "S ->> T" := (S -> T -> Prop) (format "S ->> T", at level 2).
(*This is the notation I use for multivalued functions *)

Definition mf_concat (R S T : Type) (f : R ->> S) (g : S ->> T) : R ->> T :=
  fun r t => forall s, f r s -> g s t.
(* Eventhough multivalued functions are relations, this is different from the relational
composition which would read "fun r t => exists s, f r s -> g s t." *)

Definition mf_sum (S S' T T' : Type) (f : S ->> T) (g : S' ->> T') : (S + S') ->> (T + T') :=
  fun c x => match c with
    | inl a => match x with
      | inl y => f a y
      | inr z => False
    end
    | inr b => match x with
      | inl y => False
      | inr z => g b z
    end
  end.

Definition mf_prod (S S' T T' : Type) (f : S ->> T) (g : S' ->> T') : (S * S') ->> (T * T') :=
  fun c x => f c.1 x.1 /\ g c.2 x.2.

Notation "f , g" := (mf_prod f g) (format "f , g", at level 50).
(*This is the notation for the tupling of multifunctions, it clashes with the pair notation *)

Definition is_sing S T (f: S ->> T) :=
  forall s t t', and (f s t) (f s t') -> t = t'.
(* a single valued function is still a partial function *)

Lemma prod_sing S S' T T' (f: S ->> T) (g : S' ->> T') :
  is_sing f /\ is_sing g -> is_sing (f , g).
Proof.
  move => [Fissing Gissing] a x y.
    move => [] [a0isxname a1isxname] [a0isyname a1isyname].
    apply: injective_projections.
    - apply: (Fissing (a.1) x.1 y.1).
      by split.
    - apply: (Gissing (a.2) x.2 y.2).
      by split.
Qed.

Definition is_sur S T (F: S ->> T) :=
  forall t, exists s, F s t.

Lemma prod_sur S S' T T' (f: S ->> T) (g : S' ->> T') :
  is_sur f /\ is_sur g -> is_sur (f , g).
Proof.
  move => [Fissur Gissur] x.
  move: (Fissur x.1) (Gissur x.2) => [c ciscode] [d discode].
  by exists (pair c d).
Qed.

Definition dom S T (f: S ->> T) s := exists t, f s t.

Definition is_total S T (f: S ->> T) := forall s, dom f s.

Lemma prod_total S T S' T' (f: S ->> T) (g: S' ->> T'):
  is_total f /\ is_total g -> is_total (f,g).
Proof.
  move => [istotalf istotalg] s.
  move: (istotalf s.1) (istotalg s.2) => [t fst] [t' gst'].
  by exists (pair t t').
Qed.

Notation "S ~> T" := (S -> nat -> option T) (format "S ~> T", at level 2).
(* I think about this type as a type of machines: For M : S ~> T I read M s n = nothing as
"the Machine can't say anything about the return value yet" and M s n = some t as "after n
steps the machine considers t to be the best answer". Since no assumption about concurrency
have been made, in general a machine will produce an infinite list of return values. *)

Definition eval S T (M : S ~> T) : (S ->> T) := fun a b => exists n b, M a n = some b.
(* if M is a machine then eval M is the function the machine computes. Since no assumptions
about convergence or concurrency have been made, the computed multivalued function need
neither be singlevalued nor total. *)

Definition is_comp S T (f: S ->> T):=
  exists M, forall s, (exists t, f s t) -> forall t, eval M s t -> f s t.
(* This is the best candidate for computability I have come up with so far: If there are eligible
return values then the machine produces one of these, but if there are not the machine may behave
arbitrarily. I am not one hundred percent sure this is the right notion, but pretty confident.
if it is a good one, though. *)