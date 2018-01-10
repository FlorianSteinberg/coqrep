(* This file is supposed to be come a module for multivalued functions *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Notation "S ->> T" := (S -> T -> Prop) (format "S ->> T", at level 2).
(*This is the notation I use for multivalued functions *)

Definition F2MF S T (f : S -> T) s t := f s = t.
(* I'd like this to be a Coercion but it won't allow me to do so. *)

Definition mf_concat (R S T : Type) (f : S ->> T) (g : R ->> S) : R ->> T :=
  fun r t => forall s, g r s -> f s t.
(* Eventhough multivalued functions are relations, this is different from the relational
composition which would read "fun r t => exists s, f r s -> g s t." *)
Notation "f 'o' g" := (mf_concat f g) (at level 2).

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
(* the sum of multivalued functions is not used anywhere so far. Probably because it the use of
sums is rather unusual for represented spaces. While infinite coproducts show up for some weird
spaces like polynomials or analytic functions I have not seen finite coproducts very often. *)

Definition mf_prod (S S' T T' : Type) (f : S ->> T) (g : S' ->> T') : (S * S') ->> (T * T') :=
  fun c x => f c.1 x.1 /\ g c.2 x.2.
(* in contrast to coproducts, products are very common and I have already included several lemmas
about them because I needed them. *)

Notation "f \, g" := (mf_prod f g) (at level 50).
(*This is the notation for the tupling of multifunctions*)

Definition is_sing_in S T (f: S ->> T) (P: T -> Prop) :=
  forall s t t', P t -> P t' -> (f s t) -> (f s t') -> t = t'.
Notation "f 'is_single_valued_in' P" := (is_sing_in f P) (at level 2).
Definition is_sing S T (f: S ->> T) := is_sing_in f (fun s=>True).
Notation "f 'is_single_valued'" := (is_sing f) (at level 2).
(* a single valued function is still a partial function *)

Lemma prod_sing S S' T T' (f: S ->> T) (g : S' ->> T') :
  f is_single_valued /\ g is_single_valued -> (f \, g) is_single_valued.
Proof.
  move => [Fissing Gissing] a x y _ _.
    move => [a0isxname a1isxname] [a0isyname a1isyname].
    apply: injective_projections.
    - by apply: (Fissing (a.1) x.1 y.1).
    - by apply: (Gissing (a.2) x.2 y.2).
Qed.

Lemma prod_sing_in S S' T T' (f:S ->> T) (g : S' ->> T') (P: T-> Prop) (Q: T' -> Prop) :
  f is_single_valued_in P /\ g is_single_valued_in Q
    -> (f \, g) is_single_valued_in (fun x => P x.1 /\ Q x.2).
Proof.
  move => [Fissing Gissing] a x y [px1 px2] [qx1 qx2].
    move => [a0isxname a1isxname] [a0isyname a1isyname].
    apply: injective_projections.
    - by apply: (Fissing (a.1) x.1 y.1).
    - by apply: (Gissing (a.2) x.2 y.2).
Qed.

Definition range S T (f: S ->> T) (t : T) := exists s, f s t.
Notation "t 'from_range' f" := (range f t) (at level 2).

Definition is_sur S T (f: S ->> T) :=
  forall t, range f t.
Notation "f 'is_surjective'" := (is_sur f) (at level 2).

Lemma prod_range S S' T T' (f: S ->> T) (g : S' ->> T') :
  forall s t, s from_range f /\ t from_range g -> (s,t) from_range (f \, g).
Proof.
  move => s t.
  move => [[s' fs's] [t' ft't]].
  by exists (s',t').
Qed.

Definition is_sur_on S T (f: S->> T) (A: T -> Prop) :=
  forall t, range f t -> A t.

Definition dom S T (f: S ->> T) s := exists t, f s t.
Notation "s 'from_dom' f" := (dom f s) (at level 2).

Definition is_tot S T (f: S ->> T) := forall s, dom f s.
Notation "f 'is_total'" := (is_tot f) (at level 2).

Lemma prod_total S T S' T' (f: S ->> T) (g: S' ->> T'):
  f is_total /\ g is_total ->(f \, g) is_total.
Proof.
  move => [istotalf istotalg] s.
  move: (istotalf s.1) (istotalg s.2) => [t fst] [t' gst'].
  by exists (pair t t').
Qed.