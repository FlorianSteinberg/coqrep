(* This file is supposed to be come a module for multivalued functions *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Notation "S ->> T" := (S -> T -> Prop) (format "S ->> T", at level 2).
(*This is the notation I use for multivalued functions *)

Definition F2MF S T (f : S -> T) s t := f s = t.
(* I'd like this to be a Coercion but it won't allow me to do so. *)

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
  forall t,  A t <-> range f t.
Notation "f 'is_surjective_on' A" := (is_sur_on f A) (at level 2).

Definition dom S T (f: S ->> T) s := exists t, f s t.
Notation "s 'from_dom' f" := (dom f s) (at level 2).

Definition is_tot S T (f: S ->> T) := forall s, s from_dom f.
Notation "f 'is_total'" := (is_tot f) (at level 2).

Lemma prod_total S T S' T' (f: S ->> T) (g: S' ->> T'):
  f is_total /\ g is_total ->(f \, g) is_total.
Proof.
  move => [istotalf istotalg] s.
  move: (istotalf s.1) (istotalg s.2) => [t fst] [t' gst'].
  by exists (pair t t').
Qed.

Definition mf_composition (R S T : Type) (f : S ->> T) (g : R ->> S) : R ->> T :=
  fun r t => (exists s, g r s /\ f s t) /\ (forall s, g r s -> s from_dom f).
(* Eventhough multivalued functions are relations, this is different from the relational
composition which would read "fun r t => exists s, f r s /\ g s t." *)
Notation "f 'o' g" := (mf_composition f g) (at level 2).

Lemma single_valued_composition R S T (f: S ->> T) (g : R ->> S) :
	f is_single_valued -> g is_single_valued_in (dom f) -> f o g is_single_valued.
Proof.
move => fsing gsing r t t' _ _ [[s] [grs fst]] prop [[s'] [grs' fs't'] ] _.
	apply: (fsing s t t') => //.
have: s = s'.
	apply: (gsing r s s') => //.
by apply (prop s).
by apply (prop s').
move => eq.
by rewrite eq.
Qed.

Lemma surjective_composition R S T (f: S ->> T) (g : R ->> S):
	f is_surjective -> g is_surjective_on (dom f) -> f o g is_surjective.
Proof.
move => fsur gsur t.
move: (fsur t) => [s] fst.
have: s from_range g.
	apply gsur.
	by exists t.
move => [r] grs.
exists r.
split.
	by exists s.
move => s0 grs0.
apply (gsur s0).
by exists r.
Qed.