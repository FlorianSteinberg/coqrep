(* This is example shows how to use a representation of the real numbers by means of rational
approximations to compute on the reals. Usually integers are prefered to avoid to many problems
that arise due to the possibility to use unnecessary high precission approximations. I tried
that approac in the other example file "example_approximating_reals_with_integers" but it lead
to extensive additional work so Igave up at some point. I feel that the approach in the present
file is more appropriate. *)

Load representations.

From mathcomp Require Import ssrnat.
Require Import Reals Lra Classical ClassicalFacts Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Local Open Scope Z_scope.
Import QArith.
Local Open Scope R_scope.

(* \begin{syntacticsuggar} *)
Fixpoint P2R n := match n with
  | xH => 1
  | xO m => 2* P2R m
  | xI k => 2* P2R k + 1
end.
(* It eludes my why this function is not provided under the name IPR in the standard Library *)
Fixpoint Z2R z := match z with
  | Z0 => 0
  | Zpos n => P2R n
  | Zneg m => - P2R m
end.
Coercion IZR : Z >-> R.
(* The translation IZR from the standard library translates to natural numbers in unary
and then to a real numbers. I think that is stuped so I tried to replace it. However, it turns
out that IZR is used in some lemmas, so I need to rely on it anyway. *)
Definition Q2R q := QArith_base.Qnum q / QArith_base.QDen q.
(* Coercion Q2R : Q >-> R. *)
(* This is not coerced since it leads to ambiguous paths. *)
(* \end{syntacticalsuggar} *)
(* It turns out that these coercions are not enough. To avoid heaps of burocracy I need to find
a way to also coerce the operators. Any hints about how to do this in a reasonable way are
appreciated *)

Load lemmas_rationals.
(* A set of lemmas that make it possible to work with rational numbers in the reals. The translation
is called Q2R and the most usefull tactic is Q2Rt which contains everyting that can be used to translate
operations on the rationals into operations on the reals. *)

Definition rep_R : (Q -> Q) -> R -> Prop :=
  fun phi x => forall eps, (0 < eps)%Q -> Rabs(x-Q2R(phi eps)) <= Q2R eps.
(* This is close to the standard definition of the chauchy representation. Usually integers
are prefered to avoid to many possible answers. I tried this in the other example file
"example_approximating_reals_with_integers" but it leads to extensive additional work so I
gave up at some point. I feel like the above is the most natural formulation of the Cauchy
representation. *)

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

Lemma rep_R_is_sur: rep_R is_surjective.
Proof.
  move => x.
  exists (fun eps => Qmult eps (Qmake(Int_part(x/(Q2R eps))) xH)).
  move => epsr eg0.
  rewrite !Q2Rt.
  rewrite Rabs_pos_eq.
  set eps := Q2R epsr.
  - set z := Int_part(x/eps).
    replace (x - eps * z) with (eps * (x / eps - z));first last.
    - field.
      by apply: Rlt_dichotomy_converse; right; apply lt0_Q2R.
    rewrite -{3}(Rmult_1_r eps).
    apply: Rmult_le_compat_l.
    - by left; apply lt0_Q2R.
    apply: (approx (x * /eps)).
  set eps := Q2R epsr.
  apply: (Rmult_le_reg_l (/eps)).
  - by apply: Rinv_0_lt_compat; apply: lt0_Q2R.
  rewrite Rmult_0_r.
  set z := Int_part(x/eps).
  replace (/eps*(x - eps * z)) with (x/eps - z);last first.
  - field.
    by apply: Rlt_dichotomy_converse; right; apply lt0_Q2R.
  apply (approx' (x * /eps)).
Qed.

(* The following is admitted here. However, it can probably be easily deduced from
the lemma cond_eq_nat that is proven in "example_approximating_reals_with_integers.v"
the biggest problem is type conversion... again. I'd prefer an independet and shorter proof. *)
Lemma cond_eq_rat : forall x y, (forall q, Q2R q > 0 -> Rabs (x - y) <= Q2R q) -> x = y.
Admitted.
(* TODO: give a proof of this. *)

Lemma rep_R_is_sing: is_sing rep_R.
Proof.
  move => phi x x' [pinox pinox'].
  apply: cond_eq_rat => q qg0.
  set r := Q2R (phi (Qdiv q (1+1))).
  replace (Rabs (x - x')) with (Rabs(x - r) + Rabs(r - x')).
  replace q with (Qplus (Qdiv q (1+1)) (Qdiv q (1+1))).
  rewrite plus_Q2R.
  apply: Rplus_le_compat.
  apply: pinox.
Admitted.

Lemma rep_R_is_rep: is_rep rep_R.
Proof.
  split.
  - exact: rep_R_is_sur.
  - exact: rep_R_is_sing.
Qed.

Canonical rep_space_R := @make_rep_space
  R
  (Q -> Q)
  (fun n => Qmake Z0 xH)
  rep_R
  rep_R_is_rep.

Lemma id_is_computable : (id : R -> R) is_computable.
Proof.
  by exists (fun phi=>phi).
Qed.
(* This is a trivial example. The proof looks nice, though... The next example uses the product
construction that was introduced in the file representations.v *)

Lemma triang r x y: (Rabs x) + (Rabs y) <= r -> Rabs(x + y) <= r.
Proof.
  move => ass.
Admitted.

Lemma Rplus_is_computable : (fun x => Rplus (x.1) (x.2)) is_computable.
Proof.
  Definition Rplus_realizer (phi : names rep_space_R * names rep_space_R) eps : Q :=
    (Qplus (phi.1 (Qdiv eps (1+1))) (phi.2(Qdiv eps (1+1)))).
  exists Rplus_realizer.
  move => phi x [phi0 phi1] eps eg0.
  rewrite /Rplus_realizer.
  rewrite plus_Q2R.
  set r := Q2R (phi.1 (Qdiv eps (1 + 1))).
  set q := Q2R (phi.2 (Qdiv eps (1 + 1))).
  replace (x.1 + x.2 - (r + q)) with (x.1 - r + x.2 - q); last first.
  - field.
  move: Rabs_triang.
Admitted.
