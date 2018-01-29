(* This file is supposed to be come a module for multivalued functions *)

From mathcomp Require Import all_ssreflect.
Require Import ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MULTIVALUED_FUNCTIONS.
Context (S T S' T': Type).
Notation "S ->> T" := (S -> T -> Prop) (format "S ->> T", at level 2).
(*This is the notation I use for multivalued functions. The value f(s) of such
a function should be understood as the set of all elements t such that f s t is true. *)

Definition F2MF S T (f : S -> T) s t := f s = t.
(* I'd like this to be a Coercion but it won't allow me to do so. *)

Definition mf_sum S T S' T' (f : S ->> T) (g : S' ->> T') :=
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

Definition mf_prod S T S' T' (f : S ->> T) (g : S' ->> T')
	:= fun c x => f c.1 x.1 /\ g c.2 x.2.
(* in contrast to coproducts, products are very common and I have already included
several lemmas about them because I needed them. *)

Notation "f \, g" := (mf_prod f g) (at level 50).
(*This is the notation for the tupling of multifunctions*)

Definition is_sing S T (f: S ->> T) :=
  (forall s t t', f s t -> f s t' -> t = t').
Notation "f 'is_single_valued'" := (is_sing f) (at level 2).
(* a single valued function is still a partial function *)

Lemma fun_to_sing (f: S-> T):
	(F2MF f) is_single_valued.
Proof.
by move => s t t' H H0; rewrite -H0.
Qed.

Lemma prod_sing (f: S ->> T) (g: S' ->> T'):
  f is_single_valued /\ g is_single_valued -> (f \, g) is_single_valued.
Proof.
move => [fsing gsing] s t t' [] fst gst [] fst' gst'.
apply: injective_projections.
	by apply (fsing s.1).
by apply (gsing s.2).
Qed.

Definition range S T (f: S ->> T) (t : T) := exists s, f s t.
Notation "t 'from_range' f" := (range f t) (at level 2).
(* the range of a multivalued function is the union of all its value sets. *)

Definition is_sur S T (f: S ->> T) :=
  forall t, range f t.
Notation "f 'is_surjective'" := (is_sur f) (at level 2).
(* this notion of surjectivity is only usefull in combination with single-valuedness *)

Lemma prod_range (f: S ->> T) (g : S' ->> T') :
  forall s t, s from_range f /\ t from_range g -> (s,t) from_range (f \, g).
Proof.
  move => s t.
  move => [[s' fs's] [t' ft't]].
  by exists (s',t').
Qed.

Definition dom S T (f: S ->> T) s := (exists t, f s t).
Notation "s 'from_dom' f" := (dom f s) (at level 2).

Definition tight S T (f: S ->> T) (g: S ->> T) :=
	forall s, (exists t, f s t) -> (exists t, g s t) /\ forall t, g s t -> f s t.
Notation "f 'is_tightened_by' g" := (tight f g) (at level 2).
Notation "g 'tightens' f" := (tight f g) (at level 2).

(* A thightening is a generalization of an extension of a single-valued function
to multivalued functions. It reduces to the usual notion of extension for single valued
functions: A single valued function g tightens a single valued function f if and only
if "forall s, (exists t, f(s) = t) -> g(s) = f(s)". This formula can also be written as
"forall s t, f(s) = t -> g(s) = t" and the equivalence is proven in the next lemmas.*)
Notation "g 'extends' f" := (forall s t, f s t -> g s t) (at level 2).

Lemma tight_ref (f: S ->> T):
	f tightens f.
Proof.
done.
Qed.

Lemma tight_trans (f g h: S ->> T):
	f tightens g -> g tightens h -> f tightens h.
Proof.
move => ftg gth s eh.
split.
	apply: (ftg s (gth s eh).1).1.
move => t fst.
apply: ((gth s eh).2 t).
by apply: ((ftg s (gth s eh).1).2 t).
Qed.

Lemma tightening_of_single_valued (f: S ->> T) g:
	f is_single_valued -> g tightens f -> g extends f.
Proof.
move => fsing gef s t fst.
move: (gef s) => [].
	by exists t.
move => [] t' gst' cond.
rewrite (fsing s t t') => //.
by apply (cond t').
Qed.

Lemma single_valued_tightening (f: S ->> T) g:
	g is_single_valued -> g extends f -> g tightens f.
Proof.
move => gsing gef s [] t fst.
split.
	exists t.
	by apply: (gef s t).
move => t' gst'.
rewrite -(gsing s t t') => //.
by apply gef.
Qed.

Lemma extension_and_tightening (f: S ->> T) g:
	f is_single_valued -> g is_single_valued -> (g extends f <-> g tightens f).
Proof.
split.
	exact: single_valued_tightening.
exact: tightening_of_single_valued.
Qed.

(* To extend to tightenings for multivalued functions makes sense: for instance a Choice
function of a multi valued funtion is a thightening of that funciton. *)
Definition icf S T (f: S ->> T) g := forall s, (exists t, f s t) -> f s (g s).
Notation "g 'is_choice_for' f" := (icf f g) (at level 2).

Lemma icf_tight (g: S -> T) f:
	g is_choice_for f <-> (F2MF g) tightens f.
Proof.
split.
	move => icf s ex.
	split.
		by exists (g s).
	move => t eq.
	by rewrite -eq; apply: icf s ex.
move => tight s ex.
move: (tight s ex) => [] _ prop.
by apply (prop (g s)).
Qed.

Lemma exists_choice (f: S ->> T):
	(exists (t:T), True) -> exists F, F is_choice_for f.
Proof.
move => [] t _.
set R := fun s t => s from_dom f -> f s t.
have cond: forall s, exists t, R s t.
	move => s.
	case: (classic (s from_dom f)).
		by move => [] t' fst; exists t'.
	move => false.
	exists t => sfd; by exfalso.
move: (choice R cond) => [] F prop.
rewrite /R in prop;move: R cond => _ _.
by exists F.
Qed.

Definition is_tot S T (f: S ->> T) := forall s, s from_dom f.
Notation "f 'is_total'" := (is_tot f) (at level 2).

Lemma fun_total (f: S -> T):
	(F2MF f) is_total.
Proof.
move => s; by exists (f s).
Qed.

Lemma prod_total (f: S ->> T) (g: S' ->> T'):
  f is_total /\ g is_total ->(f \, g) is_total.
Proof.
move => [istotalf istotalg] s.
move: (istotalf s.1) (istotalg s.2) => [t fst] [t' gst'].
by exists (pair t t').
Qed.

Definition mf_comp R S T (f : S ->> T) (g : R ->> S) :=
  fun r t => (exists s, g r s /\ f s t) /\ (forall s, g r s -> s from_dom f).
(* Eventhough multivalued functions are relations, this is different from the relational
composition which would simply read "fun r t => exists s, f r s /\ g s t." *)
Notation "f 'o' g" := (mf_comp f g) (at level 2).

Lemma mf_comp_assoc (f: S' ->> T') g (h: S ->> T) r q:
	(f o g) o h r q <-> f o (g o h) r q.
Proof.
split.
	move => [] [] s [] hrs [] [] t [] gst ftq prop cond.
	split.
		exists t.
		split => //.
		split.
			exists s.
			by split.
		move => s' hrs'.
		move: cond (cond s' hrs') =>
			_ [] q' [] [] t' [] gs't' ft'q' cond.
		by exists t'.
	move => t' [] [] s' [] hrs' gs't' cond'.
	move: (cond s' hrs') => [] q' [] [] t'' [] gs't'' ft''q'
		cond''.
	by apply (cond'' t').
move => [] [] t [] [] [] s [] hrt gst prop ftq cond.
split.
	exists s.
	split => //.
	split.
		exists t.
		by split.
	move => t' gst'.
	have ghrs: g o h r t'.
		split.
			exists s.
			by split.
		move => s' hrs'.
		by apply: (prop s' hrs').
	by apply (cond t' ghrs).
move => s' hrs'.
move: (prop s' hrs') => [] t' gs't'.
have ghrt': g o h r t'.
	split.
		exists s'.
		by split.
	move => s'' hrs''.
	by apply (prop s'' hrs'').
move: (cond t' ghrt') => [] q' ft'q'.
exists q'.
split.
	exists t'.
	by split.
move => t'' gs't''.
have ghrt'': g o h r t''.
	split.
		exists s'.
		by split.
	move => s'' hrs''.
	by apply (prop s'').
by apply (cond t'' ghrt'').
Qed.

Lemma sing_comp (f: T ->> T') (g : S ->> T) :
	f is_single_valued -> g is_single_valued -> f o g is_single_valued.
Proof.
move => fsing gsing.
move => r t t' [][] s [] grs fst prop [][] s' [] grs' fs't' prop'.
move: (gsing r s s' grs grs') (fsing s t t') => eq eq'.
by rewrite eq' => //; rewrite eq.
Qed.

Notation "f 'restricted_to' P" := (fun s t => P s /\ f s t) (at level 2).

Definition is_really_sur_wrt S T (f: S ->> T) (P: T -> Prop):=
	exists F, F is_choice_for f /\ forall t, (P t -> exists s, s from_dom f /\ F s = t).
(* Due to choice functions being involved, this notion is not nice to work with.
Since we are mostly interested in the case where the function is single valued,
we use the following notion instead, that can be proven equivalent in this case: *)

Definition is_sur_wrt S T (f: S ->> T) (P: T -> Prop) :=
  forall t,  P t -> (exists s, f s t /\ forall s t', f s t -> f s t' -> P t').
Notation "f 'is_surjective_wrt' A" := (is_sur_wrt f A) (at level 2).
(* This says: a multivalued function is said to be surjective on a set X if whenever
one of its value sets f(s) has a nonempty intersection with X, then it is already
included in X. This notion has to be more elaborate to work well with composition
as defined below. It does kind of make sense if the value set is interpreted as the
set of "acceptable return values": It should either be the case that all acceptable
values are from X or that none is. *)

Lemma sur_and_really_sur (f: S ->> T) P:
	(exists (t: T), True) -> f is_single_valued ->
		(is_really_sur_wrt f P <-> f is_surjective_wrt P).
Proof.
move => e sing.
split.
	move => []F [] icf prop t Pt.
	move: prop (prop t Pt) => _ [] s [] sfd Fst.
	exists (s); split.
		by rewrite -Fst; move: (icf s sfd).
	move => s0 t' fs0t fs0t'.
	by rewrite (sing s0 t t' fs0t fs0t') in Pt.
move: (exists_choice f e) => [] F prop sur.
exists F; split => //.
move => t Pt.
move: (sur t Pt) => [] s [] fst cond.
exists s; split.
	by exists t.
have ex: (exists t, f s t) by exists t.
move: (prop s ex) => fsFs.
by rewrite (sing s t (F s)).
Qed.

Lemma surjective_composition_wrt (f: T ->> T') (g : S ->> T):
	f is_surjective -> g is_surjective_wrt (dom f) -> f o g is_surjective.
Proof.
move => fsur gsur t.
move: (fsur t) => [s] fst.
have sdomf: s from_dom f by exists t.
move: (gsur s sdomf) => [] r [] grs cond.
exists r; split.
	by exists s.
by move => s'; apply: (cond r s').
Qed.

(* Due to the definition of the composition there is no Lemma for surjectivity that
does not have additional assumptions. It is probably possible to prove:
Lemma surjective_composition R S T (f: S ->> T) (g: R ->> S):
	f is_surjective -> f is_total -> g is_surjective -> f o g is_surjective.
I did not try, though. *)
End MULTIVALUED_FUNCTIONS.
Notation "S ->> T" := (S -> T -> Prop) (format "S ->> T", at level 2).
Notation "f \, g" := (mf_prod f g) (at level 50).
Notation "f 'is_single_valued'" := (is_sing f) (at level 2).
Notation "f 'restricted_to' P" := (fun s t => P s /\ f s t) (at level 2).
Notation "t 'from_range' f" := (range f t) (at level 2).
Notation "f 'is_surjective'" := (is_sur f) (at level 2).
Notation "s 'from_dom' f" := (dom f s) (at level 2).
Notation "f 'is_tightened_by' g" := (tight f g) (at level 2).
Notation "g 'tightens' f" := (tight f g) (at level 2).
Notation "g 'extends' f" := (forall s t, f s t -> g s t) (at level 2).
Notation "g 'is_choice_for' f" := ((F2MF g) tightens f) (at level 2).
Notation "f 'is_total'" := (is_tot f) (at level 2).
Notation "f 'o' g" := (mf_comp f g) (at level 2).
Notation "f 'restricted_to' P" := (fun s t => P s /\ f s t) (at level 2).
Notation "f 'is_surjective_wrt' A" := (is_sur_wrt f A) (at level 2).

