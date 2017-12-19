From mathcomp Require Import all_ssreflect ssrnat.
Require Import Reals Lra Classical ClassicalFacts Psatz.
Require Import ClassicalChoice FunctionalExtensionality.
Load Compspaces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Definition is_size (Q A : SizeType) (s:(Q->A)-> nat -> nat) := forall phi q n, size q <= n -> size (phi q) <= s phi n.

Structure Parsp := Parspace
{
  elements :> Type;
  questions : SizeType;
  answers: SizeType;
  is_descr: (questions -> answers) -> elements -> Prop;
  rep_is_valid : is_rep is_descr;
}.

Definition descriptions (X : Parsp):Type := (questions X)-> (answers X).

Definition prod_rep (X Y : Parsp) := fun phi z =>
    (is_descr (fun c => 
      match phi(inl c) with
        | inl a => a
        | inr b => inh (answers X)
      end)  z.1)
    /\ (is_descr (fun c =>
      match phi(inr c) with
        | inr a => a
        | inl b => inh (answers Y)
      end) z.2).

Lemma prod_rep_is_rep (X Y : Parsp): is_rep (@prod_rep X Y).
Proof.
  split.
  - move => [a b].
    move: (rep_is_valid X) (rep_is_valid Y) => [issurx _] [issury _].
    move: (issurx a) (issury b) => [s sdes] [t tdes].
    exists (fun q => match q with
      | inl q => inl (s q)
      | inr q => inr (t q)
    end).
    done.
  - move: (rep_is_valid X) (rep_is_valid Y) => [_ issingx] [_ issingy].
    move => phi x y [] [xone xtwo] [yone ytwo].
    apply injective_projections.
    - apply (issingx (fun c : questions X => match phi (inl c) with
                                 | inl a => a
                                 | inr _ => inh (answers X)
                                 end) x.1 y.1).
      done.
    - apply (issingy (fun c : questions Y => match phi (inr c) with
                                 | inr a => a
                                 | inl _ => inh (answers Y)
                                 end) x.2 y.2).
      done.
Qed.

Canonical Parspace_prod X Y := @Parspace
  (elements X * elements Y)
  (SizeType_sum (questions X) (questions Y))
  (SizeType_sum (answers X) (answers Y))
  (fun phi z =>
    (is_descr (fun c => 
      match phi(inl c) with
        | inl a => a
        | inr b => inh (answers X)
      end)  z.1)
    /\ (is_descr (fun c =>
      match phi(inr c) with
        | inr a => a
        | inl b => inh (answers Y)
      end) z.2))
  (prod_rep_is_rep X Y).

Lemma not_to_rep (S X : Type) (is_code: S -> X -> Prop) :
  is_rep is_code -> is_rep (fun (phi : one -> S) (x : X) =>
    is_code (phi star) x).
Proof.
  move => [issur issing].
  split.
  - move => x.
    case: (issur x) => a aisnamex.
    by exists (fun b => a).
  - move => phi x y [isnamex isnamey].
    by apply: (issing (phi star) x y).
Qed.

Canonical Parspace_from_Compspace (M : Compsp) := @Parspace
  (elts M)
  (SizeType_one)
  (codes M)
  (fun phi x => is_code (phi star) x)
  (not_to_rep (not_is_valid M)).

Definition is_rlzr (X Y : Compsp) phi (f : X -> Y) :=
  forall a x, is_code a x -> is_code (phi a) (f x).

Lemma function_repsp (X Y : Compsp): is_rep (@is_rlzr X Y).
Proof.
  move: (not_is_valid X) (not_is_valid Y)
    => [Xsur Xsing] [Ysur Ysing].
  set C := codes X.
  set D := codes Y.
  split.
  - move => f.
    set R := fun c d => forall x, is_code c x -> is_code d (f x).
    apply: (@choice (codes X) (codes Y) R) => c.
    case: (classic (exists x, is_code c x)).
    - move => [x xisnameofc].
      move: (Ysur (f x)) => [d dinofx].
      exists d.
      move => x0 cinox0.
      have: x = x0.
      - by apply: (Xsing c x x0).
      move => xeqx0.
      by rewrite -xeqx0.
    - move => assump.
      exists (inh (codes Y)).
      move => x cisnox.
      exfalso.
      apply: assump.
      by exists x.
  - move => phi f g [isnamex isnamey].
    apply: functional_extensionality => x.
    move: (Xsur x) => [a ainox].
    apply (Ysing (phi a) (f x) (g x)).
    split.
    - by apply isnamex.
    - by apply isnamey.
Qed.

Canonical Parspace_fun (X Y : Compsp) := @Parspace
  (X -> Y)
  (codes X)
  (codes Y)
  (@is_rlzr X Y)
  ((@function_repsp X Y)).
