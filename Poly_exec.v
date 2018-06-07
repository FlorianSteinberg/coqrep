From mathcomp Require Import all_ssreflect all_algebra.
Require Import under Poly_complements.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

Section Poly_exec.
Variable R : ringType.
Implicit Type p : {poly R}.

Lemma Poly_cons (a: R) K:
	Poly (a :: K) = cons_poly a (Poly K).
Proof. done. Qed.

Definition lopp_poly : seq R -> seq R := map -%R.

Lemma lopp_poly_spec l : Poly (lopp_poly l) = - Poly l.
Proof.
elim: l => [|a l IH]; rewrite /= ?rm0 //.
by rewrite !cons_poly_def IH opprD polyC_opp mulNr.
Qed.

Definition lscal_poly (a : R) := map (fun i => a * i).

Lemma lscal_poly_spec a l : Poly (lscal_poly a l) = a *: Poly l.
Proof.
elim: l => [|b l IH]; rewrite /= ?rm0 //.
by rewrite !cons_poly_def IH scalerDr scalerAl polyC_mul mul_polyC.
Qed.

(* l1 + l2 *)
Fixpoint ladd_poly (l1 l2 : seq R) :=
 if l1 is a :: l3 then
   if l2 is b :: l5 then a + b :: ladd_poly l3 l5
   else l1
 else l2.

Lemma ladd_poly_spec l1 l2 : Poly (ladd_poly l1 l2) = Poly l1 + Poly l2.
Proof.
elim: l1 l2 => [l2| a l1 IH [|b l2]]; rewrite /= ?rm0 //.
rewrite !cons_poly_def IH  polyC_add mulrDl.
by rewrite -addrA [Poly l2 * _ + _]addrCA addrA.
Qed.

(* l1 - l2 *)
Fixpoint lsub_poly (l1 l2 : seq R) :=
 if l1 is a :: l3 then
   if l2 is b :: l5 then a - b :: lsub_poly l3 l5
   else l1
 else lopp_poly l2.

Lemma lsub_poly_spec l1 l2 : Poly (lsub_poly l1 l2) = Poly l1 - Poly l2.
Proof.
elim: l1 l2 => [l2| a l1 IH [|b l2]]; rewrite /= ?rm0 //.
  by rewrite lopp_poly_spec.
rewrite !cons_poly_def IH  polyC_sub mulrBl.
by rewrite -addrA [-_ + _]addrCA opprD !addrA.
Qed.
End Poly_exec.
