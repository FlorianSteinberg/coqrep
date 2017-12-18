From mathcomp Require Import all_ssreflect ssrnat.
Require Import Reals Lra Classical ClassicalFacts Psatz.
Require Import ClassicalChoice FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Definition prod_fun (S S' T T' : Type)
  (F : S -> T -> Prop) (G : S' -> T' -> Prop) : S * S' -> (T * T') -> Prop :=
  fun c x => F c.1 x.1 /\ G c.2 x.2.

Definition dom (S T : Type) (f : S -> T -> Prop) (s : S) := exists t, f s t.

Definition is_surjective S T (F: S -> T-> Prop) :=
  forall t, exists s, F s t.

Lemma prod_surj (S S' T T' : Type) (F: S -> T -> Prop) (G : S' -> T' -> Prop) :
  is_surjective F /\ is_surjective G -> is_surjective (prod_fun F G).
Proof.
  move => [Fissur Gissur] x.
  move: (Fissur x.1) (Gissur x.2) => [c ciscode] [d discode].
  by exists (c,d).
Qed.

Definition is_single_valued S T (F: S -> T -> Prop) :=
  forall s t t', and (F s t) (F s t') -> t = t'.

Lemma prod_single_valued
(S S' T T' : Type) (F: S -> T -> Prop) (G : S' -> T' -> Prop) :
  is_single_valued F /\ is_single_valued G -> is_single_valued (prod_fun F G).
Proof.
  move => [Fissing Gissing] a x y.
    move => [] [a0isxname a1isxname] [a0isyname a1isyname].
    apply: injective_projections.
    - apply: (Fissing (a.1) x.1 y.1).
      by split.
    - apply: (Gissing (a.2) x.2 y.2).
      by split.
Qed.

Definition is_rep S T (is_name: S -> T -> Prop) :=
  is_surjective is_name /\ is_single_valued is_name.

Lemma product_rep (S S' T T' : Type) (F : S -> T -> Prop) (G : S' -> T' -> Prop) :
  is_rep F -> is_rep G -> is_rep (prod_fun F G).
Proof.
  move => [Fissur Fissing] [Gissur Gissing].
  split.
  - exact : prod_surj.
  - exact : prod_single_valued.
Qed.

Lemma id_rep (S :Type) : is_rep (fun (a b : S) => a = b).
Proof.
  split.
  - move => a.
    by exists a.
  - move => c a b [cea ceb].
    by rewrite -cea -ceb.
Qed.

Structure SizeType := size_type {
  elems :> Type;
  size : elems -> nat;
  inh: elems
  }.

Canonical SizeType_sum X Y := @size_type
  (elems X + elems Y)
  (fun z => (match z with
    | inl x => size x
    | inr y => size y
   end))
   ( inl ( inh X ) ).

Canonical SizeType_prod X Y := @size_type
  (elems X * elems Y)
  (fun x => size x.1 + size x.2)
  ( (inh X, inh Y) ).

Inductive one : Type :=
  | star.

Canonical SizeType_one := @size_type
  one
  (fun x => 1)
  star.

Canonical SizeType_nat := @size_type 
  nat
  (fun n => n)
  0.

Fixpoint size_pos (n : positive) := match n with
  | xH => 0
  | xO m => S (size_pos m)
  | xI m => S (size_pos m)
end.

Canonical SizeType_pos := @size_type 
  positive
  size_pos
  xH
  .

Fixpoint size_Z (z : Z) := match z with
  | Z0 => 1
  | Zpos n => size_pos n + 1
  | Zneg n => size_pos n + 1
end.

Canonical SizeType_Z := @size_type 
  Z
  size_Z
  Z0
  .

Fixpoint size_Q (q : QArith_base.Q) :=
  size_Z (QArith_base.Qnum q) + size_pos (QArith_base.Qden q).

Canonical Q := @size_type
  QArith_base.Q
  size_Q
  (QArith_base.Qmake 0 1).

Structure Compsp := Compspace {
  elts :> Type;
  codes : SizeType;
  is_code : codes -> elts -> Prop;
  not_is_valid : is_rep is_code;
  }.

Canonical Compspace_nat := @Compspace
  nat
  SizeType_nat
  (fun n m => n = m)
  (id_rep nat).

Canonical Compspace_pos := @Compspace
  positive
  SizeType_pos
  (fun n m => n = m)
  (id_rep positive).

Canonical Compspace_Z := @Compspace
  Z
  SizeType_Z
  (fun n m => n = m)
  (id_rep Z).

Canonical Compspace_Q := @Compspace
  Q
  Q
  (fun n m => n = m)
  (id_rep Q).

Definition is_decoder
  (S T : Type) (get_name: T -> S) (is_name : S -> T -> Prop) :=
  forall x, is_name (get_name x) x.

Structure Codesp := Codespace {
  space :> Compsp;
  get_code : (elts space) -> (codes space);
  decoder_is_valid : is_decoder get_code (fun c x => is_code c x);
}.

Lemma id_decoder (S : Type) : 
  is_decoder (fun (n : S) => n) (fun (n : S) m => n = m).
Proof.
  done.
Qed.

Canonical Codespace_nat := @Codespace
  Compspace_nat
  (fun n=> n)
  (@id_decoder nat).

Canonical Codespace_pos := @Codespace
  Compspace_pos
  (fun n=> n)
  (@id_decoder positive).

Canonical Codespace_Z := @Codespace
  Compspace_Z
  (fun n=> n)
  (@id_decoder Z).

Canonical Codespace_Q := @Codespace
  Compspace_Q
  (fun n=> n)
  (@id_decoder Q).

Structure Repsp := Repspace
{
  elements :> Type;
  questions : SizeType;
  answers: SizeType;
  is_descr : (questions -> answers) -> elements -> Prop;
  representation_is_valid : is_rep is_descr;
}.

Definition prod_rep (X Y : Repsp) := fun phi z =>
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

Lemma prod_rep_is_rep (X Y : Repsp): is_rep (@prod_rep X Y).
Proof.
  split.
  - move => [a b].
    move: (representation_is_valid X) (representation_is_valid Y) => [issurx _] [issury _].
    move: (issurx a) (issury b) => [s sdes] [t tdes].
    exists (fun q => match q with
      | inl q => inl (s q)
      | inr q => inr (t q)
    end).
    done.
  - move: (representation_is_valid X) (representation_is_valid Y) => [_ issingx] [_ issingy].
    move => phi x y [] [xone xtwo] [yone ytwo].
    apply injective_projections.
    - apply (issingx (fun c : questions X => match phi (inl c) with
                                 | inl a => a
                                 | inr _ => inh (answers X)
                                 end) x.1 y.1).
      done.
    - apply (issingx (fun c : questions Y => match phi (inr c) with
                                 | inr a => a
                                 | inl _ => inh (answers Y)
                                 end) x.2 y.2).
      done.

Canonical Repspace_prod X Y := @Repspace
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
  (product_rep (@representation_is_valid X) (@representation_is_valid Y)).

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

Canonical Repspace_from_Compspace (M : Compsp) := @Repspace
  (elts M)
  (SizeType_one)
  (codes M)
  (fun phi x => is_code (phi star) x)
  (not_to_rep (not_is_valid M)).

Canonical Repspace_sum X Y := @Repspace
  (elements X + elements Y)
  (questions X + questions Y)
  (answers X + answers Y + SizeType_one)
  (fun phi z => match z with
    | inl x =>

Definition is_realizer (X Y : Repsp) phi (f : X -> Y) :=
  forall a x, is_name a x -> is_name (phi a) (f x).

Lemma function_representation (X Y : Repsp):
  (exists (d : (names Y)), True) -> is_rep (@is_realizer X Y).
Proof.
  move: (representation_is_valid X) (representation_is_valid Y)
    => [Xsur Xsing] [Ysur Ysing] [d' _].
  set C := names X.
  set D := names Y.
  split.
  - move => f.
    set R := fun c d => forall x, is_name c x -> is_name d (f x).
    apply: (@choice (names X) (names Y) R) => c.
    case: (classic (exists x, is_name c x)).
    - move => [x xisnameofc].
      move: (Ysur (f x)) => [d dinofx].
      exists d.
      move => x0 cinox0.
      have: x = x0.
      - by apply: (Xsing c x x0).
      move => xeqx0.
      by rewrite -xeqx0.
    - move => assump.
      exists d'.
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

Local Open Scope R_scope.

Coercion IZR : Z >-> R.

Definition C_rep_R : (nat -> Z) -> R -> Prop := fun phi x => forall n,
  Rabs(x-(phi n) / 2^n) <= (1/2^n).

Lemma approx : forall r, r - Int_part r <= 1.
Proof.
  move => r; move: (base_Int_part r) => [bipl bipr].
  lra.
Qed.

Lemma approx' : forall r, 0 <= r - Int_part r.
Proof.
  move => r; move: (base_Int_part r) => [bipl bipr].
  lra.
Qed.

Lemma cond_eq_nat : forall x y, (forall n, Rabs (x - y) <= / 2 ^ n) -> x = y.
Proof.
move=> x y H.
have [// | H1] : x = y \/ Rabs (x - y) > 0.
  split_Rabs; lra.
have H2 : Rabs (x - y) <= / 2.
  have := H 1%N.
  simpl.
  lra.
have H3 : 2 <= / Rabs (x - y).
  replace 2 with (/(/2))%R by field.
  apply Rinv_le_contravar; lra.
have H4 := ln_lt_2.
pose z := - ln (Rabs (x - y)) / ln 2.
have Pz : 0 <= z.
  replace 0 with (0 * /(ln 2)) by ring.
  apply Rmult_le_compat; try lra.
  suff : 0 < / ln 2 by lra.
  apply Rinv_0_lt_compat; try lra.
  replace 0 with (-0) by ring.
  rewrite - ln_1.
  apply Ropp_le_contravar.
  suff : ln (Rabs (x - y)) < ln 1 by lra.
  apply ln_increasing; lra.
pose u := Int_part  z.
pose n := Z.to_nat (1 + u).
suff : / 2 ^ n < Rabs (x - y).
  have := H n; lra.
replace (Rabs (x - y)) with (/ /(Rabs (x - y)))%R by (field; lra).
apply Rinv_1_lt_contravar.
  replace 1 with (/ / 1)%R by field.
  apply Rinv_le_contravar; lra.
apply ln_lt_inv; try lra.
  apply pow_lt; lra.
rewrite -Rpower_pow; try lra.
rewrite ln_exp.
rewrite INR_IZR_INZ.
rewrite ln_Rinv; try lra.
rewrite Z2Nat.id; last first.
  apply le_0_IZR.
  rewrite  plus_IZR.
  rewrite [IZR 1]/=.
  have := base_Int_part z.
  rewrite /u; lra.
rewrite  plus_IZR.
rewrite [IZR 1]/=.
replace (- ln (Rabs (x - y))) with (z * ln 2); last first.
  rewrite /z; field; lra.
have := base_Int_part z.
rewrite /u.
nra.
Qed.

Lemma CrepRisrep : is_rep C_rep_R.
Proof.
  split.
  - move => t.
    exists (fun n => Int_part(t*2^n)).
    move => n.
    set m := 2^n.
    rewrite Rabs_pos_eq.
    - apply: (Rmult_le_reg_l m).
      - apply: pow_lt.
        lra.
      rewrite Rmult_minus_distr_l -!Rmult_assoc !(Rmult_comm m) !Rmult_assoc.
      rewrite (Rinv_r m).
      - rewrite !Rmult_1_r.
        apply (approx (t * m)).
      apply Rlt_dichotomy_converse.
      right.
      apply: pow_lt.
      lra.
    apply: (Rmult_le_reg_l m).
    - apply: pow_lt.
      lra.
    rewrite Rmult_minus_distr_l -!Rmult_assoc Rmult_0_r
      !(Rmult_comm m) Rmult_assoc.
    rewrite (Rinv_r m).
    - rewrite Rmult_1_r.
      apply approx'.
    apply Rlt_dichotomy_converse.
    right.
    apply: pow_lt.
    lra.
  - move => phi t t' [noft noft'].
    apply: cond_eq_nat => n.
    move: Rle_trans => trans.
    apply: (trans _ (1/2^(n.+1) + 1/2^(n.+1)) (/2^n)).
    - rewrite -(Rplus_minus (phi (n.+1)/(2^n.+1)) t').
      rewrite /Rminus Ropp_plus_distr -Rplus_assoc.
      apply: (Rle_trans _ (Rabs(t + - ((phi ((n.+1))) / 2 ^ (n.+1)))
        + Rabs(- (t' + - ((phi ((n.+1))) / 2 ^ (n.+1)))))).
      - apply: Rabs_triang.
      apply: (Rplus_le_compat
      (Rabs (t + - ((phi ((n.+1))) / 2 ^ (n.+1)))) (1/2^(n.+1))
      (Rabs (- (t' + - ((phi ((n.+1))) / 2 ^ (n.+1))))) (1/2^(n.+1))).
      - by move: (noft ((n.+1))).
      - rewrite Rabs_Ropp.
        by move: (noft' ((n.+1))).
    rewrite /=.
    rewrite (Rmult_comm 2) /Rdiv Rinv_mult_distr.
    - rewrite Rmult_1_l eps2 -(Rmult_1_l (/ 2 ^ n)).
      by apply Rle_refl.
    apply: Rgt_not_eq.
    move: (pow_lt 2 n).
    lra.
  lra.
Qed.

Definition Q2R (q : QArith_base.Q) : R := QArith_base.Qnum q * / QArith_base.QDen q.

Coercion Q2R : QArith_base.Q >-> R.

Definition rep_R : (nat -> Q*Q) -> R -> Prop := fun phi x => forall n,
  Rabs(x-(phi n).1) <= (phi n).2 /\ forall eps, exists n, (phi n).2<= eps.

Canonical Repspace_R := @Repspace
  R
  (nat -> Z)
  C_rep_R
  CrepRisrep
  (fun phi l => forall n m, (size n <= m)%coq_nat
    -> (size (phi n) <= (l n))%coq_nat).

Definition is_computable (X Y: Repsp) (f: X -> Y):=
  exists phi, is_realizer phi f.

Lemma idiscomputable : is_computable (id : R -> R).
Proof.
  by exists (fun phi=>phi).
Qed.

Open Scope Z_scope.

Definition round_4 (d : Z) : Z := ((d / 2 + 1) / 2)%Z.

Lemma rounding (d : Z): (d-2<= 4*round_4(d) <= d+2)%Z.
Proof.
  rewrite /round_4.
  Search Z.div Z.modulo.
  rewrite  (Zdiv.Z_div_mod_eq d 4); try lia.
  replace (4*(d/4)) with (d/4*2*2) by ring.
  rewrite Zdiv.Z_div_plus_full_l; try lia.
  rewrite Zplus_assoc_reverse.
  rewrite Zdiv.Z_div_plus_full_l; try lia.
  have : d mod 4 = 0 \/ d mod 4 = 1 \/ d mod 4 = 2 \/ d mod 4 = 3.
  Search Z.modulo.
  have : 0 <= d mod 4 < 4.
  apply: Zdiv.Z_mod_lt; lia.
  lia.
  (case; [idtac|case;[idtac| case]]) => -> ;
  rewrite [(_/_ + _)/2] /=.
  change (1/2) with 0.
  lia.
  change (1/2) with 0.
  lia.
  change (2/2) with 1.
  lia.
  change (2/2) with 1.
  lia.
Qed.

Lemma rounding_R (d : Z) : (d-2<= 4*round_4(d) <= d+2)%R.
Admitted.

Open Scope R_scope.
Lemma additioniscomputable : is_computable (fun x => Rplus (x.1) (x.2)).
Proof.
  Definition addition_realizer (phi : names Repspace_R* names Repspace_R) n : Z :=
    round_4(phi.1 (n.+2) + phi.2 (n.+2)).
  exists addition_realizer.
  move => phi x [phi0 phi1] n.
  set r := phi.1 (n.+2)/4.
  set q := phi.2 (n.+2)/4.
  have round : (Rabs((addition_realizer phi n) -r-q) <= /2).
  rewrite /addition_realizer.
  move : (rounding_R (phi.1 (n.+2) + phi.2 (n.+2))) => stufffff.
  rewrite /r /q.
  rewrite plus_IZR in stufffff.
  split_Rabs; try lra.
  admit.
  have rapprox : Rabs(x.1 - r/2^n) <= 2^n.+2.
  move : phi0.
  rewrite /(is_name).
  Search _ "Int_part".
  admit.
  have qapprox : Rabs(x.2 - q/2^n) <= 2^n.+2.
  admit.
  set sum := Rabs( x.1 + x.2 - (r+q)/2^n) + Rabs(addition_realizer phi n -r-q)/2^n.
  have add : sum <= /2^n.
  admit.
  suff esti: Rabs(x.1 + x.2 -addition_realizer phi n /2^n) <= sum.
  apply : (Rle_trans _ sum) => //.
  by rewrite /Rdiv Rmult_1_l.
  admit.