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

(* The following should be considered to define equality as multivalued functions *)
Notation "f =~= g" := (forall s t, f s t <-> g s t) (at level 70).

(* The domain of a multifunctions is the set of all inputs such that the value set
is not empty. *)
Definition dom S T (f: S ->> T) s := (exists t, f s t).
Notation "s '\from_dom' f" := (dom f s) (at level 2).

(* The difference between multivalued functions and relations is how they are composed.*)
Definition mf_comp R S T (f : S ->> T) (g : R ->> S) :=
  fun r t => (exists s, g r s /\ f s t) /\ (forall s, g r s -> s \from_dom f).
Notation "f 'o' g" := (mf_comp f g) (at level 2).

Lemma F2MF_comp R (f : S ->> T) (g : R -> S):
	f o (F2MF g) =~= (fun r t => f (g r) t).
Proof.
split => [[[r [grs fst]] prop] | fgrt ]; first by rewrite grs.
by split => [ | r eq]; [exists (g s) | exists t; rewrite -eq].
Qed.

(* This operation is associative *)
Lemma comp_assoc (f: S' ->> T') g (h: S ->> T) r q:
	(f o g) o h r q <-> f o (g o h) r q.
Proof.
split => [ [] [] s [] hrs [] [] t []| [] [] t [] [] [] s [] ].
	split => [ | t' [] [] s' [] hrs'].
		exists t;	split => //.
		split => [ | s' hrs']; first by exists s.
		by move: (b1 s' hrs') => [] x [] [] t' []; exists t'.
	by move: (b1 s' hrs') => [] q' comp gs't _; apply comp.2.
split => [ | s' hrs'].
	exists s; split => //.
	split => [ | t' gst']; first by exists t.
	suffices ghrs: g o h r t' by apply (b2 t' ghrs).
	by split => [ | s' hrs']; [exists s | apply b0].
move: (b0 s' hrs') => [] t' gs't'.
have ghrt': g o h r t'
	by split => [ | s'' hrs'']; [exists s' | apply b0].
move: (b2 t' ghrt') => [] q' ft'q'; exists q'.
split => [ | t'' gs't'']; first by exists t'.
suffices ghrt'': g o h r t'' by apply b2.
by split => [ | s'' hrs'']; [exists s' | apply b0].
Qed.

(* The composition breaks the symmetry between input and output, i.e. it needs not be true
that (f o g)^-1 = g^-1 o f^-1. This is in contrast to the following definition which pre-
serves the symmetry, is the usual one for relations, but not appropriate for our purpose. *)
Definition rel_comp R S T (f : S ->> T) (g : R ->> S) :=
  fun r t => exists s, g r s /\ f s t.
Notation "f 'o_R' g" := (rel_comp f g) (at level 2).

Definition is_tot S T (f: S ->> T) := forall s, s \from_dom f.
Notation "f '\is_total'" := (is_tot f) (at level 2).

Lemma F2MF_tot (f: S -> T):
	(F2MF f) \is_total.
Proof. move => s; by exists (f s). Qed.

(* For total multi valued functions, the relational composition is identical to the multi-
function composition.  *)
Lemma comp_tot R  (f : S ->> T) (g : R ->> S):
	f \is_total -> f o g =~= f o_R g.
Proof.
split => [[[r [grs fst]] prop] | [s' [gs0s eq]] ]; first by exists r.
by split => [ | r gs0r]; [exists s' | apply H].
Qed.

(* the following should be called "is_mono" and "is_epi", but we consider the multi
valued functions to be functions and thus call the notions surjective and injective.
This will be further justified below when choice functions are introduced. *)
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

Lemma F2MF_sing (f: S-> T):
	(F2MF f) \is_single_valued.
Proof. by move => s t t' H H0; rewrite -H0. Qed.

Lemma comp_sing (f: T ->> T') (g : S ->> T) :
	f \is_single_valued -> g \is_single_valued -> f o g \is_single_valued.
Proof.
move => fsing gsing r t t' [[] s [] grs fst _ [][] s' [] grs' fs't' _].
by rewrite (fsing s t t') => //; rewrite (gsing r s s').
Qed.

Lemma sing_comp R (f : S ->> T) (g : R ->> S):
	g \is_single_valued -> g \is_total -> f o g =~= (fun r t => forall y, g r y -> f y t).
Proof.
split => [[[r [grs fst]] prop] y gsy | fgrt ]; first by rewrite (H s y r).
split => [ | r gsr]; last by exists t; apply/ (fgrt r).
by have [r gsr]:= H0 s; by exists r; split; last by apply fgrt.
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
have eq: g =~= h.
	apply (fsur bool g h) => s b.
	split => [] [[t' [val1 val2]] prop];
	by exfalso; apply notcodom; exists s; rewrite val2.1.
case: (classic (g t true)) => ass; last by apply ass.
by case: ((eq t true).1 ass).
Qed.

(* The opposite implication does not hold in general*)
Lemma cotot_notsur (f: S ->> T) (s: S) (t t': T):
	~ t = t' -> exists f, f \is_cototal /\ ~ f \is_surjective.
Proof.
move => neq.
pose f' (x: S) (y: T) := (True: Prop).
exists f'; split => [ k | sur ].
	by exists s.
pose g k b := k = t /\ b = true.
pose h k b := k = t /\ b = false.
suffices eq: g o f' =~= h o f'.
	move: (((sur bool g h) eq) t false) => [] a b.
	by suffices htt: h t false by move: (b htt).2.
have tru: True by trivial.
by split; move => [ [] _ [] _ [] _ _ prop];
	move: (prop t' tru) => [] b' [] eq; exfalso; apply neq.
Qed.

(* but for single valued functions it is true. *)
Lemma sing_cotot_sur f:
f \is_single_valued -> (f \is_cototal <-> f \is_surjective).
Proof.
split => [fcotot Q g h eq t q| ]; last exact: sur_cotot.
split => ass; move: (fcotot t) => [] s fst.
	suffices gfsq: (g o f s q).
		by move: ((eq s q).1 gfsq) => [] [] t' [] fst'; rewrite (H s t t').
	by split => [ | t' fst']; [exists t | exists q; rewrite (H s t' t)].
have hfsq: (h o f s q).
	by split => [ | t' fst']; [ exists t| exists q; rewrite (H s t' t) ].
by move: ((eq s q).2 hfsq) => [] [] t' [] fst'; rewrite (H s t t').
Qed.

(* Due to the above, the following is named correctly.*)
Definition sur_par_fun S T (f: S ->> T) :=
  f \is_single_valued /\ f \is_cototal.
Notation "f '\is_surjective_partial_function'" := (sur_par_fun f) (at level 2).

(* the following is the construction is used to define the product of represented spaces *)
Definition mf_prod S T S' T' (f : S ->> T) (g : S' ->> T') :=
	fun c x => f c.1 x.1 /\ g c.2 x.2.
Notation "f \, g" := (mf_prod f g) (at level 50).
(*This is the notation for the tupling of multifunctions *)

Lemma prod_comp R R' (f: S ->> T) (g: S' ->> T') (f': R ->> S) (g': R' ->> S'):
	(f \, g) o (f' \, g') =~= (f o f' \, g o g').
Proof.
split => [[] [] fgx [] [] | [] [] [] s1 []]; last first.
	move => fxs1 fs1ffggx H [] [] s2 [] fxs2 fs2ffggx H'.
	split => [ | [] s'1 s'2 [] fs' gs']; first by exists (s1,s2).
	by move: (H s'1 fs') (H' s'2 gs') => [] t' fst [] t'' ; exists (t',t'').
move => fxfgx gxfgx [] ffgxffggx gfgxffggx H.
split; split => [ | s' f'xs]; [by exists fgx.1 | | by exists fgx.2 | ].
	have temp: ((s', fgx.2) \from_dom (f \, g)) by apply: ((H (s', fgx.2))).
	by move: temp => [] [] x1 x2 [] /= fsx1; exists x1.
have temp: ((fgx.1,s') \from_dom (f \, g)) by apply: ((H (fgx.1, s'))).
by move: temp => [] [] x1 x2 [] /= fsx1; exists x2.
Qed.

Lemma prod_sing (f: S ->> T) (g: S' ->> T'):
  f \is_single_valued /\ g \is_single_valued -> (f \, g) \is_single_valued.
Proof.
move => [fsing gsing] s t t' [] fst gst [] fst' gst'.
by apply: injective_projections; [apply (fsing s.1)| apply (gsing s.2)].
Qed.

Lemma prod_dom (f: S ->> T) (g: S' ->> T') s t:
  (s, t) \from_dom (f \, g) <-> s \from_dom f /\ t \from_dom g.
Proof.
split; last by move => [[s' fs's] [t' ft't]]; exists (s',t').
by move => [] x [] /= fsx gty; split; [exists x.1| exists x.2].
Qed.

Lemma prod_tot (f: S ->> T) (g: S' ->> T'):
	f \is_total /\ g \is_total -> (f \, g) \is_total.
Proof.
move => [ftot gtot] [t t']; apply (prod_dom f g t t').2.
by split; [apply: ftot t| apply: gtot t'].
Qed.

Lemma tot_prod (f: S ->> T) (g: S' ->> T'):
	S -> S' -> (f \, g) \is_total -> f \is_total /\ g \is_total.
Proof.
split => s; first by apply: ((prod_dom f g s X0).1 (H (s, X0))).1.
by apply: ((prod_dom f g X s).1 (H (X, s))).2.
Qed.

Lemma prod_codom (f: S ->> T) (g : S' ->> T') :
  forall s t, s \from_codom f /\ t \from_codom g -> (s,t) \from_codom (f \, g).
Proof. by move => s t [[s' fs's] [t' ft't]]; exists (s',t'). Qed.
End MULTIVALUED_FUNCTIONS.
Notation "f =~= g" := (forall s t, f s t <-> g s t) (at level 70).
Notation "S ->> T" := (S -> T -> Prop) (format "S ->> T", at level 2).
Notation "f \, g" := (mf_prod f g) (at level 50).
Notation "f '\is_single_valued'" := (is_sing f) (at level 2).
Notation "f '\restricted_to' P" := (fun s t => P s /\ f s t) (at level 2).
Notation "t '\from_codom' f" := (codom f t) (at level 2).
Notation "f '\is_surjective_partial_function'" := (sur_par_fun f) (at level 2).
Notation "s '\from_dom' f" := (dom f s) (at level 2).
Notation "f '\is_total'" := (is_tot f) (at level 2).
Notation "f 'o' g" := (mf_comp f g) (at level 2).
Notation "f '\restricted_to' P" := (fun s t => P s /\ f s t) (at level 2).

Section TIGHT_EXTENDS_ICF.
Context (S T: Type).
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

(* tight is almost an equivalence relation, it only fails to be symmetric *)
Lemma tight_ref (f: S ->> T):
	f \tightens f.
Proof. done. Qed.

Lemma tight_trans (f g h: S ->> T):
	f \tightens g -> g \tightens h -> f \tightens h.
Proof.
split => [ | t fst]; first by apply: (H s (H0 s H1).1).1.
by apply: ((H0 s H1).2 t); apply: ((H s (H0 s H1).1).2 t).
Qed.

Lemma tight_sing (f: S ->> T) g:
	f \is_single_valued -> g \tightens f -> g \extends f.
Proof.
move => fsing gef s t fst.
case: (gef s) =>[|[t' gst' cond]]; first by exists t.
by rewrite (fsing s t t'); [ | | apply (cond t') ].
Qed.

Lemma sing_tight (f: S ->> T) g:
	g \is_single_valued -> g \extends f -> g \tightens f.
Proof.
move => gsing gef s [t fst].
split => [ | t' gst']; first by exists t; apply: (gef s t).
by rewrite -(gsing s t t'); [ | apply gef | ].
Qed.

Lemma exte_tight (f: S ->> T) g:
	f \is_single_valued -> g \is_single_valued -> (g \extends f <-> g \tightens f).
Proof.
split; [exact: sing_tight | exact: tight_sing] .
Qed.

Lemma exte_comp R (f f': T ->> R) (g: S ->> T):
	f \extends f' -> (f o g) \extends (f' o g).
Proof.
move => fef s r [[t [gst ftr] prop]].
split => [ | t' gst']; first by exists t; split => //; apply fef.
specialize (prop t' gst').
have [r' f't'r']:= prop.
by exists r'; apply fef.
Qed.

Definition icf S T (f: S ->> T) g := forall s t, f s t -> f s (g s).
Notation "g '\is_choice_for' f" := (icf f g) (at level 2).
(* A more comprehensible way to state icf would be "forall s, s \from_dom f -> f s (g s)"
or "forall s, (exists t, f s t) -> f s (g s)" but avoiding the existential quatification
makes the above more convenient to use. *)

Lemma sing_tot_F2MF_icf (f: S ->> T) g:
	f \is_single_valued -> f \is_total -> (g \is_choice_for f <-> F2MF g =~= f).
Proof.
split => [icf s t| eq s t fst]; last by by rewrite ((eq s t).2 fst).
split => [ eq | fst ]; last by rewrite (H s t (g s)); last by apply (icf s t fst).
by have [t' fst']:= (H0 s); by rewrite -eq; apply (icf s t').
Qed.

Lemma icf_comp R f' (f: T ->> R) g' (g: S ->> T):
	f' \is_choice_for f -> g' \is_choice_for g
		-> (fun s => f' (g' s)) \is_choice_for (f o g).
Proof.
move => icff icfg s r [[t [gst ftr]] prop].
split => [ | t' gst']; last exact (prop t' gst'); exists (g' s).
have gsg's: g s (g' s) by apply/ (icfg s t).
have [r' fg'sr']:= (prop (g' s) gsg's).
by split; last apply/ (icff (g' s) r').
Qed.

Lemma icf_F2MF_tight (g: S -> T) f:
	g \is_choice_for f <-> (F2MF g) \tightens f.
Proof.
split => [ icf s [] t fst | tight s t fst].
	by split => [ | gs eq ]; [exists (g s) | rewrite -eq; apply: (icf s t)].
have ex: s \from_dom f by exists t.
by apply ((tight s ex).2 (g s)).
Qed.

Lemma tight_icf (g f: S ->> T):
	g \tightens f -> forall h, (h \is_choice_for g -> h \is_choice_for f).
Proof.
move => tight h icf.
apply/ icf_F2MF_tight.
apply/ tight_trans; last by apply tight.
by apply/ icf_F2MF_tight.
Qed.

Lemma exists_choice (f: S ->> T) (t: T):
	exists F, F \is_choice_for f.
Proof.
set R := fun s t => forall t', f s t' -> f s t.
suffices Rtot: R \is_total by move: (choice R Rtot) => [] F prop; exists F.
move => s.
case: (classic (s \from_dom f)) => [[] t' fst | false]; first by exists t'.
by exists t => t' fst'; exfalso; apply false; exists t'.
Qed.

(* For the next Lemma it would be very convenient if =~= was rewritable *)
Lemma F2MF_sing_tot (f: S ->> T) (t: T):
	f \is_single_valued /\ f \is_total <-> exists g, F2MF g =~= f.
Proof.
split => [ [sing tot] | [g eq] ].
	have [g icf]:= exists_choice f t.
	exists g; by apply/ sing_tot_F2MF_icf.
split.
	have gsing: (F2MF g) \is_single_valued by apply: F2MF_sing.
	by move => s r r' fsr fsr';rewrite (gsing s r r'); try apply eq.
have gtot: (F2MF g) \is_total by apply: (F2MF_tot g).
by move => s; have [t' gst]:= (gtot s); exists t'; apply eq.
Qed.

Lemma icf_tight (g f: S ->> T): (forall s, exists t', ~ f s t')
	-> (forall h, (h \is_choice_for g -> h \is_choice_for f)) -> (g \tightens f).
Proof.
move => ex prop s [t fst].
split => [ | t' gst'].
	have [t' nfst']:= (ex s).
	pose g' x y := (x <> s -> g x y) /\ (x = s -> y = t').
	have [h icf'] := (exists_choice g' t).
	apply NNPP => nex.
	have ngst': ~g s t' by move => gst'; apply nex; exists t'.
	have icf: h \is_choice_for g.
		move => s' t'' gs't''.
		case (classic (s' = s)) => [eq | neq].
			by exfalso; apply nex; exists t''; rewrite -eq.
		have g's't'': g' s' t'' by split => // eq; exfalso; apply neq.
		exact: ((icf' s' t'' g's't'').1 neq).
	suffices eq: h s = t' by apply nfst'; rewrite -eq; apply: (prop h icf s t).
	have g'st': g' s t' by trivial.
	by apply (icf' s t' g'st').2.
pose g' x y := g x y /\ (x = s -> y = t').
have gtg: g' \tightens g.
	move => x xfd.
	split => [ | y g'xy]; last by apply g'xy.1.
	case (classic (x = s)) => [ eq | neq ]; first by exists t'; rewrite eq.
	by have [y gxy]:= xfd; exists y; by split.
have [h icf']:= (exists_choice g' t).
have icf: h \is_choice_for g.
	apply icf_F2MF_tight.
	apply/ tight_trans; last by apply/ gtg.
	by apply icf_F2MF_tight; apply icf'.
suffices val: h s = t' by rewrite -val; apply/ (prop h icf s t).
have val': g s t' /\ (s = s -> t' = t') by split.
by apply: (icf' s t' val').2.
Qed.

End TIGHT_EXTENDS_ICF.
Notation "f '\is_tightened_by' g" := (tight f g) (at level 2).
Notation "g '\tightens' f" := (tight f g) (at level 2).
Notation "g '\extends' f" := (forall s t, f s t -> g s t) (at level 2).
Notation "g '\is_choice_for' f" := (icf f g) (at level 2).