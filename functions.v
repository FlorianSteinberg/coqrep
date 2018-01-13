(* This file is supposed to be come a module for multivalued functions *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Notation "S ->> T" := (S -> T -> Prop) (format "S ->> T", at level 2).
(*This is the notation I use for multivalued functions. The value f(s) of such
a function should be understood as the set of all elements t such that f s t is true. *)

Definition F2MF S T (f : S -> T) s t := f s = t.
(* I'd like this to be a Coercion but it won't allow me to do so. *)

Definition mf_sum (S S' T T' : Type) (f : S ->> T) (g : S' ->> T') :=
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
(* the sum of multivalued functions is not used anywhere so far. Probably because
it the use of sums is rather unusual for represented spaces. While infinite co-
products show up for some weird spaces like polynomials or analytic functions, I
have not seen finite coproducts very often. *)

Definition mf_prod (S S' T T' : Type)
	(f : S ->> T)
	(g : S' ->> T') :=
  	fun c x => f c.1 x.1 /\ g c.2 x.2.
(* in contrast to coproducts, products are very common and I have already included
several lemmas about them because I needed them. *)

Notation "f \, g" := (mf_prod f g) (at level 50).
(*This is the notation for the tupling of multifunctions*)

Definition is_sing_wrt S T (f: S ->> T) (R: T -> T -> Prop) :=
  forall s t t', (f s t) -> (f s t') -> R t t'.
Notation "f 'is_single_valued_wrt' P" := (is_sing_wrt f P) (at level 2).
(* To understand why this is called "single valued" see the special case that R i
the equality relation below. More generally, this means that f factors through the
relation R. *)
Definition is_sing S T (f: S ->> T) := is_sing_wrt f (fun s t=> s = t).
Notation "f 'is_single_valued'" := (is_sing f) (at level 2).
(* a single valued function is still a partial function *)

Lemma fun_to_sing S T (f: S-> T):
	(F2MF f) is_single_valued.
Proof.
by move => s t t' fst fst';rewrite -fst -fst'.
Qed.

Lemma prod_sing_wrt S S' T T' (f: S ->> T) (g : S' ->> T') R R' :
  f is_single_valued_wrt R /\ g is_single_valued_wrt R'
  	-> (f \, g) is_single_valued_wrt (fun p q => R p.1 q.1 /\ R' p.2 q.2).
Proof.
move => [Fsing Gsing] [a1 a2] [x1 x2] [y1 y2] [fv1 gv1] [fv2 gv2].
split.
	by apply (Fsing a1 x1 y1).
by apply (Gsing a2 x2 y2).
Qed.

Lemma prod_sing S S' T T' (f: S ->> T) (g: S' ->> T'):
  f is_single_valued /\ g is_single_valued -> (f \, g) is_single_valued.
Proof.
move => [fsing gsing] [a1 a2] [x1 x2] [y1 y2] [fv1 gv1] [fv2 gv2].
apply: injective_projections.
	by apply (fsing a1 x1 y1).
by apply (gsing a2 x2 y2).
Qed.

Definition range S T (f: S ->> T) (t : T) := exists s, f s t.
Notation "t 'from_range' f" := (range f t) (at level 2).
(* the range of a multivalued function is the union of all its value sets. *)

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

Definition is_sur_wrt S T (f: S->> T) (A: T -> Prop) :=
  forall t,  A t -> (exists s, f s t /\ forall s t', f s t -> f s t' -> A t').
Notation "f 'is_surjective_wrt' A" := (is_sur_wrt f A) (at level 2).
(* This says: a multivalued function is said to be surjective on a set X if whenever
one of its value sets f(s) has a nonempty intersection with X, then it is already
included in X. This notion has to be more elaborate to work well with composition
as defined below. It does kind of make sense if the value set is interpreted as the
set of "acceptable return values": It should either be the case that all acceptable
values are from X or that none is. *)

Definition dom S T (f: S ->> T) s := exists t, f s t.
Notation "s 'from_dom' f" := (dom f s) (at level 2).

Definition exte S T (f: S ->> T) (g: S ->> T) :=
	forall s, (exists t, f s t) -> (exists t, g s t) /\ forall t, g s t -> f s t.
Notation "g 'extends' f" := (exte f g) (at level 2).
(* The next two lemmas together prove, that the above definition of an extension
reduces to the usual notion of extension for single valued functions, namely a function
g extends f a function f if "forall s, (exists t, f(s) = t) -> g(s) = f(s)" which can
be rewriten as "forall s t, f(s) = t -> g(s) = t".
The generalization makes sense: for instance a Choice function of a multi valued funtion
is an extension of that funciton. Some people talk about tightenings for this reason
and to avoid confusion. *)
Lemma extension_of_single_valued S T (f: S ->> T) g:
	f is_single_valued -> g extends f -> forall s t, f s t -> g s t.
Proof.
move => fsing gef s t fst.
move: (gef s) => [].
	by exists t.
move => [] t' gst' cond.
rewrite (fsing s t t') => //.
by apply (cond t').
Qed.

Lemma single_valued_extension S T (f: S ->> T) g:
	g is_single_valued -> (forall s t, f s t -> g s t) -> g extends f.
Proof.
move => gsing gef s [] t fst.
split.
	exists t.
	by apply: (gef s t).
move => t' gst'.
rewrite -(gsing s t t') => //.
by apply gef.
Qed.

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
composition which would simply read "fun r t => exists s, f r s /\ g s t." *)
Notation "f 'o' g" := (mf_composition f g) (at level 2).

Lemma single_valued_composition_wrt R S T (f: S ->> T) (g : R ->> S) :
	f is_single_valued -> g is_single_valued_wrt (fun s s' => forall t, f s t -> f s' t)
		-> f o g is_single_valued.
Proof.
move => fsing gsing r t t' [][] s [] grs fst prop [][]s' [] grs' fs't' prop'.
move: (gsing r s s' grs grs' t fst) => fs't.
move: (fsing s t t') => eq.
move: (fsing s' t t') => eq''.
rewrite eq => //.
by rewrite -eq''.
Qed.

Lemma single_valued_composition R S T (f: S ->> T) (g : R ->> S) :
	f is_single_valued -> g is_single_valued -> f o g is_single_valued.
Proof.
move => fsing gsing r t t' [][] s [] grs fst prop [][]s' [] grs' fs't' prop'.
move: (gsing r s s' grs grs') => eq.
move: (fsing s t t') => eq'.
rewrite eq' => //.
by rewrite eq.
Qed.

Lemma surjective_composition_wrt R S T (f: S ->> T) (g : R ->> S):
	f is_surjective -> g is_surjective_wrt (dom f) -> f o g is_surjective.
Proof.
move => fsur gsur t.
move: (fsur t) => [s] fst.
have: s from_dom f.
	by exists t.
move => sdomf.
move: (gsur s sdomf) => [] r [] grs cond.
exists r.
split.
	by exists s.
move => s'.
by apply: (cond r s').
Qed.

(* Due to the definition of the composition there is no Lemma for surjectivity that
does not have additional assumptions. It is probably possible to prove:
Lemma surjective_composition R S T (f: S ->> T) (g: R ->> S):
	f is_surjective -> f is_total -> g is_surjective -> f o g is_surjective.
I did not try, though. *)