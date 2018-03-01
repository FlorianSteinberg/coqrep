(* This file contains basic definitions and Lemmas about multi-valued functions *)

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

(* The domain of a multifunctions is the set of all inputs such that the value set
is not empty. *)
Definition dom S T (f: S ->> T) s := (exists t, f s t).
Notation "s '\from_dom' f" := (dom f s) (at level 2).

Definition is_tot S T (f: S ->> T) := forall s, s \from_dom f.
Notation "f '\is_total'" := (is_tot f) (at level 2).

Lemma fun_total (f: S -> T):
	(F2MF f) \is_total.
Proof.
move => s; by exists (f s).
Qed.

(* The difference between multivalued functions and relations is how they are composed.
Compare the following definition with the usual one for relations where relations R and
Q are usually combined to "fun r t => exists s, R r s /\ Q s t.". Note that the composition
breaks the symmetry: it needs not be true that (f o g)^-1 = g^-1 o f^-1 *)
Definition mf_comp R S T (f : S ->> T) (g : R ->> S) :=
  fun r t => (exists s, g r s /\ f s t) /\ (forall s, g r s -> s \from_dom f).
Notation "f 'o' g" := (mf_comp f g) (at level 2).

(* The above operation is still associative and the composition in the category of sets
with multivalued functions as morphisms *)
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

(* The following should be considered to define equality as multivalued functions *)
Notation "f =~= g" := (forall s t, f s t <-> g s t) (at level 70).

Definition is_sur (f: S ->> T):= forall Q (g h: T ->> Q), g o f =~= h o f -> g =~= h.
Notation "f '\is_surjective'" := (is_sur f) (at level 2).

Definition is_inj (f: S ->> T):= forall Q (g h: Q ->> S), f o g =~= f o h -> g =~= h.
Notation "f '\is_injective'" := (is_inj f) (at level 2).

(* Definition mf_sum S T S' T' (f : S ->> T) (g : S' ->> T') :=
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
the sum of multivalued functions is not used anywhere so far. Probably because
it the use of sums is rather unusual for represented spaces. While infinite co-
products show up for some weird spaces like polynomials or analytic functions, I
have not seen finite coproducts very often. *)

(* For representations we should sieve out the single valued surjective partial functions. *)
Definition is_sing S T (f: S ->> T) :=
  (forall s t t', f s t -> f s t' -> t = t').
Notation "f '\is_single_valued'" := (is_sing f) (at level 2).

Lemma fun_to_sing (f: S-> T):
	(F2MF f) \is_single_valued.
Proof.
by move => s t t' H H0; rewrite -H0.
Qed.

Definition codom S T (f: S ->> T) (t : T) := exists s, f s t.
Notation "t '\from_codom' f" := (codom f t) (at level 2).
(* the codomain of a multi-valued function is the union of all its value sets. It should
not be understood as the range, as very few of its elements may be hit by a choice function. *)

Definition is_cotot S T (f: S ->> T) := forall s, s \from_codom f.
Notation "f '\is_cototal'" := (is_cotot f) (at level 2).

(* Being surjective implies being cototal*)
Lemma sur_cotot f:
f \is_surjective -> f \is_cototal.
Proof.
move => fsur t.
pose g t' b := t = t' /\ b = true.
pose h t' b := t = t' /\ b = false.
apply NNPP => notcodom.
suffices: g =~= h.
	move => eq.
	move: (eq t true) => ha.
	case: (classic (g t true)) => ass.
		by move: (ha.1 ass) => [] _ H.
	by apply ass.
apply (fsur bool g h).
move => s b.
by split => [] [] [] t' [] val1 val2 prop; by exfalso; apply notcodom; exists s; rewrite val2.1.
Qed.

(* The opposite implication does not hold in general but for single valued functions it is true. *)
Lemma sing_cotot_sur f:
f \is_single_valued -> (f \is_cototal <-> f \is_surjective).
Proof.
move => fsing.
split;last first.
	exact: sur_cotot.
move => fcotot Q g h eq t q.
split => ass.
	move: (fcotot t) => [] s fst.
	have gfsq: (g o f s q).
		split.
			by exists t.
		move => t' fst'.
		exists q.
		by rewrite (fsing s t' t).
	move: ((eq s q).1 gfsq) => [] [] t' [] fst' ht'q prop.
	by rewrite (fsing s t t').
move: (fcotot t) => [] s fst.
have hfsq: (h o f s q).
	split.
		by exists t.
	move => t' fst'.
	exists q.
	by rewrite (fsing s t' t).
move: ((eq s q).2 hfsq) => [] [] t' [] fst' ht'q prop.
by rewrite (fsing s t t').
Qed.

(* Thus, there is a very simple property that classifies being a partial surjective function.*)
Definition sur_par_fun S T (f: S ->> T) :=
  f \is_single_valued /\ f \is_cototal.
Notation "f '\is_surjective_partial_function'" := (sur_par_fun f) (at level 2).

(* the following is the construction is used to define the product of represented spaces *)
Definition mf_prod S T S' T' (f : S ->> T) (g : S' ->> T') :=
	fun c x => f c.1 x.1 /\ g c.2 x.2.
Notation "f \, g" := (mf_prod f g) (at level 50).
(*This is the notation for the tupling of multifunctions *)

Lemma prod_comp R R'
(f: S ->> T) (g: S' ->> T') (f': R ->> S) (g': R' ->> S'):
	forall x fx, (f \, g) o (f' \, g') x fx <-> (f o f' \, g o g') x fx.
Proof.
move => x ffggx.
split.
	move => [] [] fgx [] [] fxfgx gxfgx [] ffgxffggx gfgxffggx prop.
	split.
		split.
			by exists fgx.1.
		move => s f'xs.
		have temp: ((s, fgx.2) \from_dom (f \, g)) by apply: ((prop (s, fgx.2))).
		move: temp => [] [] x1 x2 [] /= fsx1.
		by exists x1.
	split.
		by exists fgx.2.
	move => s f'xs.
	have temp: ((fgx.1,s) \from_dom (f \, g)) by apply: ((prop (fgx.1, s))).
	move: temp => [] [] x1 x2 [] /= fsx1.
	by exists x2.
move => [] [] [] s1 [] fxs1 fs1ffggx prop [] [] s2 [] fxs2 fs2ffggx prop'.
split.
	by exists (s1,s2).
move => [] s'1 s'2 [] fs' gs'.
move: (prop s'1 fs') (prop' s'2 gs') => [] t fst [] t' fst'.
by exists (t,t').
Qed.

Lemma prod_sing (f: S ->> T) (g: S' ->> T'):
  f \is_single_valued /\ g \is_single_valued -> (f \, g) \is_single_valued.
Proof.
move => [fsing gsing] s t t' [] fst gst [] fst' gst'.
apply: injective_projections.
	by apply (fsing s.1).
by apply (gsing s.2).
Qed.

Lemma prod_dom (f: S ->> T) (g: S' ->> T'):
  forall s t, (s, t) \from_dom (f \, g) <-> s \from_dom f /\ t \from_dom g.
Proof.
split.
	by move => [] x [] /= fsx gty; split; [exists x.1| exists x.2].
by move => [[s' fs's] [t' ft't]]; exists (s',t').
Qed.

Lemma prod_tot (f: S ->> T) (g: S' ->> T'):
	f \is_total /\ g \is_total -> (f \, g) \is_total.
Proof.
move => [] ftot gtot [] t t'.
apply (prod_dom f g t t').2.
by split; [apply: ftot t| apply: gtot t'].
Qed.

Lemma tot_prod (f: S ->> T) (g: S' ->> T'):
	S -> S' -> (f \, g) \is_total -> f \is_total /\ g \is_total.
Proof.
split => s.
	by apply: ((prod_dom f g s X0).1 (H (s, X0))).1.
by apply: ((prod_dom f g X s).1 (H (X, s))).2.
Qed.

Lemma prod_codom (f: S ->> T) (g : S' ->> T') :
  forall s t, s \from_codom f /\ t \from_codom g -> (s,t) \from_codom (f \, g).
Proof.
by move => s t [[s' fs's] [t' ft't]]; exists (s',t').
Qed.

Definition tight S T (f: S ->> T) (g: S ->> T) :=
	forall s, s \from_dom f -> s \from_dom g /\ forall t, g s t -> f s t.
Notation "f '\is_tightened_by' g" := (tight f g) (at level 2).
Notation "g '\tightens' f" := (tight f g) (at level 2).

(* A thightening is a generalization of an extension of a single-valued function
to multivalued functions. It reduces to the usual notion of extension for single valued
functions: A single valued function g tightens a single valued function f if and only
if "forall s, (exists t, f(s) = t) -> g(s) = f(s)". This formula can also be written as
"forall s t, f(s) = t -> g(s) = t" and the equivalence is proven in the next lemmas.*)
Notation "g '\extends' f" := (forall s t, f s t -> g s t) (at level 2).

Lemma tight_ref (f: S ->> T):
	f \tightens f.
Proof.
done.
Qed.

Lemma tight_trans (f g h: S ->> T):
	f \tightens g -> g \tightens h -> f \tightens h.
Proof.
move => ftg gth s eh.
split.
	apply: (ftg s (gth s eh).1).1.
move => t fst.
apply: ((gth s eh).2 t).
by apply: ((ftg s (gth s eh).1).2 t).
Qed.

Lemma tightening_of_single_valued (f: S ->> T) g:
	f \is_single_valued -> g \tightens f -> g \extends f.
Proof.
move => fsing gef s t fst.
move: (gef s) => [].
	by exists t.
move => [] t' gst' cond.
rewrite (fsing s t t') => //.
by apply (cond t').
Qed.

Lemma single_valued_tightening (f: S ->> T) g:
	g \is_single_valued -> g \extends f -> g \tightens f.
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
	f \is_single_valued -> g \is_single_valued -> (g \extends f <-> g \tightens f).
Proof.
split.
	exact: single_valued_tightening.
exact: tightening_of_single_valued.
Qed.

(* To extend to tightenings for multivalued functions makes sense: for instance a choice
function of a multi valued funtion is a thightening of that funciton. *)
Definition icf S T (f: S ->> T) g := forall s t, f s t -> f s (g s).
Notation "g '\is_choice_for' f" := (icf f g) (at level 2).
(* A more comprehensible way to state icf would be "forall s, s \from_dom f -> f s (g s)"
or "forall s, (exists t, f s t) -> f s (g s)" but avoiding the existential quatification
makes the above more convenient. *)

Lemma icf_tight (g: S -> T) f:
	g \is_choice_for f <-> (F2MF g) \tightens f.
Proof.
split.
	move => icf s [] t fst.
	split.
		by exists (g s).
	move => gs eq.
	rewrite -eq.
	by apply: (icf s t).
move => tight s t fst.
have ex: s \from_dom f by exists t.
have [_ prop]:= (tight s ex).
by apply (prop (g s)).
Qed.

Lemma exists_choice (f: S ->> T):
	T -> exists F, F \is_choice_for f.
Proof.
move => t.
set R := fun s t => forall t', f s t' -> f s t.
have cond: forall s, exists t, R s t.
	move => s.
	case: (classic (s \from_dom f)).
		by move => [] t' fst; exists t'.
	move => false.
	exists t => t' fst'.
	by exfalso; apply false; exists t'.
move: (choice R cond) => [] F prop.
rewrite /R in prop;move: R cond => _ _.
by exists F.
Qed.

Lemma sing_comp (f: T ->> T') (g : S ->> T) :
	f \is_single_valued -> g \is_single_valued -> f o g \is_single_valued.
Proof.
move => fsing gsing.
move => r t t' [][] s [] grs fst prop [][] s' [] grs' fs't' prop'.
move: (gsing r s s' grs grs') (fsing s t t') => eq eq'.
by rewrite eq' => //; rewrite eq.
Qed.
End MULTIVALUED_FUNCTIONS.
Notation "S ->> T" := (S -> T -> Prop) (format "S ->> T", at level 2).
Notation "f \, g" := (mf_prod f g) (at level 50).
Notation "f '\is_single_valued'" := (is_sing f) (at level 2).
Notation "f '\restricted_to' P" := (fun s t => P s /\ f s t) (at level 2).
Notation "t '\from_codom' f" := (codom f t) (at level 2).
Notation "f '\is_surjective_partial_function'" := (sur_par_fun f) (at level 2).
Notation "s '\from_dom' f" := (dom f s) (at level 2).
Notation "f '\is_tightened_by' g" := (tight f g) (at level 2).
Notation "g '\tightens' f" := (tight f g) (at level 2).
Notation "g '\extends' f" := (forall s t, f s t -> g s t) (at level 2).
Notation "g '\is_choice_for' f" := (icf f g) (at level 2).
Notation "f '\is_total'" := (is_tot f) (at level 2).
Notation "f 'o' g" := (mf_comp f g) (at level 2).
Notation "f '\restricted_to' P" := (fun s t => P s /\ f s t) (at level 2).
