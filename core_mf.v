(* This file contains basic definitions and Lemmas about multi-valued functions *)
From mathcomp Require Import all_ssreflect.
Require Import ClassicalChoice CRelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "S ->> T" := (S -> T -> Prop) (format "S ->> T", at level 2).
(*This is the notation I use for multivalued functions. The value f(s) of such
a function should be understood as the set of all elements t such that f s t is true. *)

(* The following should be considered to define equality as multivalued functions *)
Definition equiv S T (f g: S ->> T) := (forall s t, f s t <-> g s t).

Arguments equiv {S T}.

Global Instance eqiuv_equiv S T:
	Equivalence (@equiv S T).
Proof.
split => // [f g eq s t | f g h feg geh s t]; first by split => [gst | fst]; apply eq.
by split => [fst | hst]; [apply geh; apply feg | apply feg; apply geh].
Qed.
Notation "f =~= g" := (equiv f g) (at level 70).

Section MULTIVALUED_FUNCTIONS.
Context (S T S' T': Type).

Lemma bysym A (P: A ->> A) (Q: A -> Prop):
(forall f g, P f g -> Q f -> Q g) -> (forall f g, P g f -> P f g)
	-> (forall f g, P f g -> (Q f <-> Q g)).
Proof. firstorder. Qed.

Definition F2MF S T (f : S -> T) s t := f s = t.
(* I'd like this to be a Coercion but it won't allow me to do so. *)
Arguments F2MF {S T} f s t /.
Global Instance F2MF_prpr S T: Proper (eq ==> @equiv S T) (@F2MF S T).
Proof. by move => f g eq; rewrite eq. Qed.

(* The domain of a multifunctions is the set of all inputs such that the value set
is not empty. *)
Definition dom S T (f: S ->> T) s := (exists t, f s t).
Notation "s '\from_dom' f" := (dom f s) (at level 50).

Global Instance dom_prpr S T: Proper ((@equiv S T) ==> eq ==> iff) (@dom S T).
Proof.
move => f g equiv _ s ->; move: equiv.
apply/ (@bysym (S0 ->> T0) (equiv) (fun f => s \from_dom f)); last by symmetry.
by clear => f g equiv [t fst]; exists t; apply equiv.
Qed.

(* The difference between multivalued functions and relations is how they are composed:
The relational composition is given as follows.*)
Definition rel_comp R S T (f : S ->> T) (g : R ->> S) :=
  fun r t => (exists s, g r s /\ f s t).
Notation "f 'o_R' g" := (rel_comp f g) (at level 50).

Global Instance relcomp_prpr R S T:
Proper ((@equiv S T) ==> (@equiv R S) ==> (@equiv R T)) (@rel_comp R S T).
Proof.
move => f f' eqf g g' eqg s t; etransitivity; move: eqf.
apply: (@bysym _ (fun f f' => f =~= f') (fun f => (f o_R g) s t)); last by symmetry.
clear => f f' eqf [s' [gs't ftr]].
by exists s'; split => //; apply eqf.
by split => [[r [gsr frt]] | [r [gsr frt]]]; exists r; [rewrite -(eqg s r) | rewrite (eqg s r)].
Qed.

Lemma relcomp_assoc (f: S' ->> T') g (h: S ->> T):
	((f o_R g) o_R h) =~= (f o_R (g o_R h)).
Proof.
split; last by move => [t' [[s' []]]]; exists s'; split => //; exists t'.
by move => [t' [hst [s'[]]]]; exists s'; split => //; exists t'.
Qed.

(* The multi function composition adds an assumption that removes the symmetry of in- and output.
The additional condition is that g r is a subset of dom f. *)
Notation "P '\is_subset_of' Q" := (subset P Q) (at level 50).
Definition mf_comp R S T (f : S ->> T) (g : R ->> S) :=
  fun r t => (f o_R g) r t /\ (g r) \is_subset_of (dom f).
Notation "f 'o' g" := (mf_comp f g) (at level 50).

Lemma subs_trans R (P P' P'':  R -> Prop):
	P \is_subset_of P' -> P' \is_subset_of P'' -> P \is_subset_of P''.
Proof. by move => PsP' P'sP'' s Ps; apply/P'sP''/PsP'. Qed.

Global Instance comp_prpr R S T: Proper ((@equiv S T) ==> (@equiv R S) ==> (@equiv R T)) (@mf_comp R S T).
Proof.
move => f f' eqf g g' eqg s t; split; case.
	split; last by move => r g'sr; rewrite -eqf; apply/b/eqg.
	by move: a => [r stf]; exists r; rewrite -(eqf r t) -(eqg s r).
split; last by move => r g'sr; rewrite eqf; apply/b/eqg.
by move: a => [r stf]; exists r; rewrite (eqf r t) (eqg s r).
Qed.

Lemma dom_comp R Q Q' (f: Q ->> Q') (g: R ->> Q):
	dom (f o g) \is_subset_of dom g.
Proof. by move => r [s [[t[]]]]; exists t. Qed.

(* This operation is associative *)
Lemma comp_assoc (f: S' ->> T') g (h: S ->> T):
	((f o g) o h) =~= (f o (g o h)).
Proof.
move => r q.
split => [ [] [] s [] hrs [] [] t []| [] [] t [] [] [] s [] ].
	split => [ | t' [] [] s' [] hrs'].
		exists t;	split => //; split => [ | s' hrs']; first by exists s.
		by move: (b1 s' hrs') => [] x [] [] t' []; exists t'.
	by move: (b1 s' hrs') => [] q' comp gs't _; apply comp.2.
split => [ | s' hrs'].
	exists s; split => //.
	split => [ | t' gst']; first by exists t.
	suffices ghrs: (g o h) r t' by apply (b2 t' ghrs).
	by split => [ | s' hrs']; [exists s | apply b0].
move: (b0 s' hrs') => [] t' gs't'.
have ghrt': (g o h) r t'
	by split => [ | s'' hrs'']; [exists s' | apply b0].
move: (b2 t' ghrt') => [] q' ft'q'; exists q'.
split => [ | t'' gs't'']; first by exists t'.
suffices ghrt'': (g o h) r t'' by apply b2.
by split => [ | s'' hrs'']; [exists s' | apply b0].
Qed.

Lemma comp_id_l (f: S ->> T):
	(F2MF id) o f =~= f.
Proof.
split => [[[t' [fst <-]] _] | fst] //; by split => [ | t' fst']; [exists t | exists t'].
Qed.

Lemma comp_id_r (f: S ->> T):
	f o (F2MF id) =~= f.
Proof.
split => [[[t' [<- fst]] _] | fst] //; by split => [| t' <- ]; [exists s|exists t].
Qed.

Lemma F2MF_comp R (f: S ->> T) (g: R -> S):
	(f o (F2MF g)) =~= (fun r t => f (g r) t).
Proof.
split => [[[r [grs fst]] prop] | fgrt ]; first by rewrite grs.
by split => [ | r eq]; [exists (g s) | exists t; rewrite -eq].
Qed.
End MULTIVALUED_FUNCTIONS.
Notation "f =~= g" := (equiv f g) (at level 70).
Notation "S ->> T" := (S -> T -> Prop) (format "S ->> T", at level 2).
Notation "s '\from_dom' f" := (dom f s) (at level 2).
Notation "f 'o_R' g" := (rel_comp f g) (at level 2).
Notation "P '\is_subset_of' Q" := (subset P Q) (at level 50).
Notation "f 'o' g" := (mf_comp f g) (at level 2).

Section MFPROPERTIES.
Context (S T S' T': Type).

Definition mf_inv T S (f: S ->> T) t s := f s t.
Notation inv f := (mf_inv f).
Notation "f '\inverse'" := (mf_inv f) (at level 70).

Global Instance mfinv_prpr S T: Proper ((@equiv S T) ==> (@equiv T S)) (@mf_inv T S).
Proof. by split; intros; apply H. Qed.

Lemma id_inv:
	(F2MF (@id S)) \inverse =~= F2MF id.
Proof. done. Qed.

Definition empty_mf S T := (fun (s: S) (t: T) => False).

Lemma empty_inv:
	(@empty_mf S T) \inverse =~= (@empty_mf T S).
Proof. done. Qed.

Lemma relcomp_inv (f: T ->> S') (g: S ->> T):
	(f o_R g) \inverse =~= (g \inverse) o_R (f \inverse).
Proof. by split; case => r []; exists r. Qed.

Notation "f '\is_section_of' g" := (f o g =~= F2MF id) (at level 2).

Lemma sec_cncl (f: S -> T) g:
	(F2MF f) \is_section_of (F2MF g) <-> cancel g f.
Proof.
split; last by intros; rewrite F2MF_comp /F2MF => s t; split => <-.
by move => eq s; move: (eq s s); rewrite (F2MF_comp _ g _ s) /F2MF /= => ->.
Qed.

Definition is_tot S T (f: S ->> T) := forall s, s \from_dom f.
Notation "f '\is_total'" := (is_tot f) (at level 2).

Global Instance tot_prpr S T: Proper ((@equiv S T) ==> iff) (@is_tot S T).
Proof. by split => tot s; have [t xst]:= tot s; exists t; apply H. Qed.

Lemma comp_tot R (f: S ->> T) (g: T ->> R):
	f \is_total -> g \is_total -> (g o f) \is_total.
Proof.
move => ftot gtot s.
have [t fst]:= ftot s; have [r gtr]:= gtot t.
exists r; split; first by exists t.
by intros => a b; apply gtot.
Qed.

Lemma F2MF_tot (f: S -> T):
	(F2MF f) \is_total.
Proof. by move => s; exists (f s). Qed.

(* For total multi valued functions, the relational composition is identical to the multi-
function composition.  *)
Lemma tot_comp R  (f : S ->> T) (g : R ->> S):
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

(* For representations we should sieve out the single valued surjective partial functions. *)
Definition is_sing S T (f: S ->> T) :=
  (forall s t t', f s t -> f s t' -> t = t').
Notation "f '\is_single_valued'" := (is_sing f) (at level 2).

Global Instance sing_prpr S T: Proper ((@equiv S T) ==> iff) (@is_sing S T).
Proof.
move => f f'.
apply: (@bysym _ (fun f f' => f =~= f') (fun f => is_sing f)); last by symmetry.
by clear => f f' eq sing s t t' f'st f'st'; apply/ sing; apply eq; [apply f'st | apply f'st'].
Qed.

Lemma F2MF_sing (f: S-> T):
	(F2MF f) \is_single_valued.
Proof. by move => s t t' H H0; rewrite -H0. Qed.

Lemma comp_sing (f: T ->> T') (g : S ->> T) :
	f \is_single_valued -> g \is_single_valued -> (f o g) \is_single_valued.
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
Notation "t '\from_codom' f" := (codom f t) (at level 50).
(* the codomain of a multi-valued function is the union of all its value sets. It should
not be understood as the range, as very few of its elements may be hit by a choice function. *)
Lemma inv_dom_codom (f: S ->> T) t:
	t \from_codom f <-> t \from_dom (f \inverse).
Proof.
by split; case => s; exists s.
Qed.

Definition is_cotot S T (f: S ->> T) := forall s, s \from_codom f.
Notation "f '\is_cototal'" := (is_cotot f) (at level 2).

Lemma cotot_tot_inv (f: S ->> T):
	f \is_cototal <-> (f \inverse) \is_total.
Proof. by split; move => H t; move: (H t); case => s; exists s. Qed.

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
	have [a b]:= (((sur bool g h) eq) t false).
	by suffices htt: h t false by move: (b htt).2.
by split; move => [ [] _ [] _ [] _ _ prop];
	by have [ | b' [eq]]:= (prop t' _); last by exfalso; apply neq.
Qed.

(* but for single valued functions it is true. *)
Lemma sing_cotot_sur f:
f \is_single_valued -> (f \is_cototal <-> f \is_surjective).
Proof.
split => [fcotot Q g h eq t q| ]; last exact: sur_cotot.
split => ass; move: (fcotot t) => [] s fst.
	suffices gfsq: (g o f) s q.
		by move: ((eq s q).1 gfsq) => [] [] t' [] fst'; rewrite (H s t t').
	by split => [ | t' fst']; [exists t | exists q; rewrite (H s t' t)].
have hfsq: (h o f) s q.
	by split => [ | t' fst']; [ exists t| exists q; rewrite (H s t' t) ].
by move: ((eq s q).2 hfsq) => [] [] t' [] fst'; rewrite (H s t t').
Qed.

(* Due to the above, the following is named correctly.*)
Definition sur_par_fun S T (f: S ->> T) :=
  f \is_single_valued /\ f \is_cototal.
Notation "f '\is_surjective_partial_function'" := (sur_par_fun f) (at level 2).

Definition sur_fun (f: S -> T) := forall t, exists s, f s = t.
Notation "f '\is_surjective_function'" := (sur_fun f) (at level 2).

Lemma sur_fun_sur (f: S -> T):
	f \is_surjective_function <-> (F2MF f) \is_surjective.
Proof.
split => sur.
	move => R g h.
	rewrite !F2MF_comp => eq s t.
	have [r <-]:= sur s.
	exact: (eq r t).
move => t.
have cotot: (F2MF f) \is_cototal by apply sur_cotot.
have [s fst]:= cotot t.
by exists s.
Qed.

(* A modification of the following construction is used to define the product of represented spaces. *)
Definition mfpp S T S' T' (f : S ->> T) (g : S' ->> T') :=
	fun c x => f c.1 x.1 /\ g c.2 x.2.
Notation "f ** g" := (mfpp f g) (at level 50).

Definition mfpp_fun S T S' T' (f: S -> T) (g: S' -> T') :=
	fun p => (f p.1, g p.2).
Notation "f **_f g" := (mfpp_fun f g) (at level 50).

Lemma mfpp_fun_mfpp (f: S -> T) (g: S' -> T'):
	F2MF (mfpp_fun f g) =~= mfpp (F2MF f) (F2MF g).
Proof.
split; rewrite /F2MF; first by move <-.
by rewrite /mfpp_fun/mfpp => [[-> ->]]; rewrite -surjective_pairing.
Qed.

Definition ppp1 (fg: (S * S') ->> (T * T')) :=
	fun s t => exists s' p, fg (s,s') p /\ p.1 = t.

Definition ppp2 (fg: (S * S') ->> (T * T')) :=
	fun s' t' => exists s p, fg (s, s') p /\ p.2 = t'.

Lemma ppp1_proj (f: S ->> T) (g: S' ->> T'):
	(exists s', s' \from_dom g) -> ppp1 (f ** g) =~= f.
Proof.
move => [s' [t' gs't']].
by split => [[k [p [[/= eq _] eq']]] | ]; [rewrite -eq' | exists s'; exists (t, t')].
Qed.

Lemma ppp2_proj (f: S ->> T) (g: S' ->> T'):
	(exists s, s \from_dom f) -> ppp2 (f ** g) =~= g.
Proof.
move => [s [somet fst]].
by split => [[k [p [[/= _ eq] eq']]] | ]; [rewrite -eq' | exists s; exists (somet, t)].
Qed.

(* A modification of the following construction is used to define the sum of represented spaces. *)
Definition mfss S T S' T' (f : S ->> T) (g : S' ->> T') :=
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
Notation "f +s+ g" := (mfss f g) (at level 50).

Definition mfss_fun S T S' T' (f: S -> T) (g: S' -> T') :=
	fun ss' => match ss' with
		| inl s => inl (f s)
		| inr s' => inr (g s')
	end.
Notation "f +s+_f g" := (mfss_fun f g) (at level 50).

Lemma mfss_fun_mfss (f: S -> T) (g: S' -> T'):
	F2MF (mfss_fun f g) =~= mfss (F2MF f) (F2MF g).
Proof.
split; rewrite /F2MF; first by move <-; case s => /=.
by case: s => /=; case: t => //= s t ->.
Qed.

Lemma mfpp_comp R R' (f: S ->> T) (g: S' ->> T') (f': R ->> S) (g': R' ->> S'):
	(f ** g) o (f' ** g') =~= (f o f') ** (g o g').
Proof.
split => [[] [] fgx [] [] | [] [] [] s1 []]; last first.
	move => fxs1 fs1ffggx H [] [] s2 [] fxs2 fs2ffggx H'.
	split => [ | [] s'1 s'2 [] fs' gs']; first by exists (s1,s2).
	by move: (H s'1 fs') (H' s'2 gs') => [] t' fst [] t'' ; exists (t',t'').
move => fxfgx gxfgx [] ffgxffggx gfgxffggx H.
split; split => [ | s' f'xs]; [by exists fgx.1 | | by exists fgx.2 | ].
	have temp: ((s', fgx.2) \from_dom (f ** g)) by apply: ((H (s', fgx.2))).
	by move: temp => [] [] x1 x2 [] /= fsx1; exists x1.
have temp: ((fgx.1,s') \from_dom (f ** g)) by apply: ((H (fgx.1, s'))).
by move: temp => [] [] x1 x2 [] /= fsx1; exists x2.
Qed.

Lemma mfpp_sing (f: S ->> T) (g: S' ->> T'):
  f \is_single_valued /\ g \is_single_valued -> (f ** g) \is_single_valued.
Proof.
move => [fsing gsing] s t t' [] fst gst [] fst' gst'.
by apply: injective_projections; [apply (fsing s.1)| apply (gsing s.2)].
Qed.

Lemma mfpp_dom (f: S ->> T) (g: S' ->> T') s t:
  (s, t) \from_dom (f ** g) <-> s \from_dom f /\ t \from_dom g.
Proof.
split; last by move => [[s' fs's] [t' ft't]]; exists (s',t').
by move => [] x [] /= fsx gty; split; [exists x.1| exists x.2].
Qed.

Lemma mfpp_tot (f: S ->> T) (g: S' ->> T'):
	f \is_total /\ g \is_total -> (f ** g) \is_total.
Proof.
move => [ftot gtot] [t t']; apply (mfpp_dom f g t t').2.
by split; [apply: ftot t| apply: gtot t'].
Qed.

Lemma tot_mfpp (f: S ->> T) (g: S' ->> T'):
	S -> S' -> (f ** g) \is_total -> f \is_total /\ g \is_total.
Proof.
split => s; first by apply: ((mfpp_dom f g s X0).1 (H (s, X0))).1.
by apply: ((mfpp_dom f g X s).1 (H (X, s))).2.
Qed.

Lemma mfpp_codom (f: S ->> T) (g : S' ->> T') :
  forall s t, s \from_codom f /\ t \from_codom g -> (s,t) \from_codom (f ** g).
Proof. by move => s t [[s' fs's] [t' ft't]]; exists (s',t'). Qed.
End MFPROPERTIES.
Notation "f ** g" := (mfpp f g) (at level 50).
Notation "f **_f g" := (mfpp_fun f g) (at level 50).
Notation "f +s+ g" := (mfss f g) (at level 50).
Notation "f +s+_f g" := (mfss_fun f g) (at level 50).
Notation "f '\is_single_valued'" := (is_sing f) (at level 2).
Notation "f '\restricted_to' P" := (fun s t => P s /\ f s t) (at level 2).
Notation "t '\from_codom' f" := (codom f t) (at level 2).
Notation "f '\is_surjective_partial_function'" := (sur_par_fun f) (at level 2).
Notation "f '\is_surjective_function'" := (sur_fun f) (at level 2).
Notation "f '\is_total'" := (is_tot f) (at level 2).
Notation "f '\range_restricted_to' P" := (fun s t => f s t /\ P t) (at level 2).

Section TIGHT_EXTENDS_ICF.
Context (S T: Type).

Definition tight S T (f: S ->> T) (g: S ->> T) :=
	forall s, s \from_dom f -> s \from_dom g /\ forall t, g s t -> f s t.
Notation "f '\is_tightened_by' g" := (tight f g) (at level 2).
Notation "g '\tightens' f" := (tight f g) (at level 2).

Global Instance tight_prpr S T: Proper ((@equiv S T) ==> (@equiv S T) ==> iff) (@tight S T).
Proof.
move => f f' eqf g g' eqg.
etransitivity.
move: eqf.
apply: (@bysym _ (fun f f' => f =~= f') (fun f => tight f g)); last by symmetry.
clear => f f' eq gtf s [t fst].
have sfd': s \from_dom f by exists t; apply eq.
have [ex prop]:= (gtf s sfd').
by split => // t' gst'; apply eq; apply prop.
move: eqg; apply: (@bysym _ (fun f f' => f =~= f') (fun g => tight f' g)); last by symmetry.
clear => f g eq gtf' s sfd.
have [ex prop]:= gtf' s sfd.
split; first by have [t fst]:= ex; exists t; apply eq.
by move => t gst; apply prop; apply eq.
Qed.

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

Lemma tight_comp_r R (f: T ->> R) g (g': S ->> T):
	g \tightens g' -> (f o g) \tightens (f o g').
Proof.
move => gtg' s [r [[t [g'st ftr]] prop]].
have sfd: s \from_dom g' by exists t.
have [t' gst']:= (gtg' s sfd).1.
have g'st': g' s t' by apply (gtg' s sfd).2.
move: (prop t' g'st') => [r' fgsr'].
split; first exists r'.
	split => [ | t'' gst'']; first by exists t'.
	by apply prop; apply (gtg' s sfd).2.
move => r'' [[t'' [gst'' ft''r'']] prop'].
split => //; by exists t''; split => //; apply (gtg' s sfd).2.
Qed.

Lemma tight_comp_l R (f f': T ->> R) (g: S ->> T):
	f \tightens f' -> (f o g) \tightens (f' o g).
Proof.
move => ftf' s [r [[t [gst f'tr]] prop]].
have tfd: t \from_dom f' by exists r.
have [r' ftr']:= (ftf' t tfd).1.
have f'tr': f' t r' by apply (ftf' t tfd).2.
split; first exists r'.
	split => [ | t'' gst'']; first by exists t.
	by apply ftf'; apply prop.
move => r'' [[t'' [gst'' ft''r'']] prop'].
split => //; exists t''; split => //.
by apply ftf'; first by apply prop.
Qed.

Lemma mfpp_tight S' T' (f: S ->> T) (g: S' ->> T') (f': S ->> T) (g': S' ->> T'):
	f \tightens f' -> g \tightens g' -> (f ** g) \tightens (f' ** g').
Proof.
move => tigh tigh' [s s'] [[t t'] [/=f'st fs't']].
have sfd: s \from_dom f' by exists t.
have [[r fsr] prop] := tigh s sfd.
have s'fd: s' \from_dom g' by exists t'.
have [[r' gsr'] prop'] := tigh' s' s'fd.
split; first by exists (r, r').
move => [q q'] [/= fsq gs'q'].
by split; [apply prop | apply prop'].
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

Lemma F2MF_sing_tot (f: S ->> T) (t: T):
	f \is_single_valued /\ f \is_total <-> exists g, (F2MF g) =~= f.
Proof.
split => [ [sing tot] | [g eq] ].
	have [g icf]:= exists_choice f t.
	exists g; by apply/ sing_tot_F2MF_icf.
by split; rewrite -eq; [apply F2MF_sing | apply F2MF_tot].
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

Global Instance icf_prpr S T: Proper (@equiv S T ==> eq ==> iff) (@icf S T).
Proof. by move => f g feg f' g' f'eg'; rewrite !icf_F2MF_tight feg f'eg'. Qed.

Notation "f '\is_tightened_by' g" := (tight f g) (at level 2).
Notation "g '\tightens' f" := (tight f g) (at level 2).
Notation "g '\extends' f" := (forall s t, f s t -> g s t) (at level 2).
Notation "g '\is_choice_for' f" := (icf f g) (at level 2).

Lemma tight_comp S T R (f f': T ->> R) (g g': S ->> T):
	f \tightens f' -> g \tightens g' -> (f o g) \tightens (f' o g').
Proof.
intros; apply/tight_trans/tight_comp_l; last by apply H.
by apply/tight_trans/tight_comp_r; last by apply H0.
Qed.