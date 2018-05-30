From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.


Definition rm0 :=
 (mulr0, mul0r, subr0, sub0r, add0r, addr0, mul0rn, mulr0n, oppr0,
  scale0r, scaler0).

Definition rm1 := (mulr1, mul1r, mulr1n).

Section Interp.

Variable R : fieldType.
Variable f : R -> R.

Definition prodl (l : seq R) : {poly R} :=
  \prod_(i <- undup l) ('X - i%:P).

Lemma prodl_root l : root (prodl l) =i l.
Proof.
elim: l => [i|a l IH i]; rewrite /prodl /=.
  by rewrite big_nil rootE hornerE oner_eq0.
have [aIl|aNIl] := boolP (a \in l).
  by rewrite IH inE; case: eqP => [->|].
by rewrite big_cons [LHS]rootM root_XsubC inE -IH.
Qed.

Lemma prodl_size l : (size (prodl l) <= (size l).+1)%N.
Proof.
elim: l => /= [|a l IH].
 by rewrite /prodl big_nil size_polyC; case: eqP.
rewrite /prodl /=; case: (boolP (_ \in _)) => H.
  by apply: leq_trans IH _.
rewrite big_cons.
apply: leq_trans (size_mul_leq _ _) _.
by rewrite size_XsubC.
Qed.

Fixpoint interp (l : seq R) : {poly R} :=
  if l is a :: l1 then
      let r := interp l1 in
      if a \in l1 then r else
        let q := prodl l1 in
        r + (f a - r.[a]) / q.[a] *: q
  else 0.

Lemma interp_nil : interp [::] = 0.
Proof. by []. Qed.

Lemma interpC a : interp [:: a] = (f a)%:P.
Proof. 
by rewrite /= [prodl _]big_nil !hornerC !rm0 divr1 alg_polyC.
Qed.

Lemma interp_cons a l :
  a \notin l -> 
  interp (a :: l) =
     interp l + (f a - (interp l).[a])/(prodl l).[a] *: prodl l.
Proof. by move=> /= /negPf->. Qed.

Lemma horner_interp l : all (fun i => (interp l).[i] == f i) l.
Proof.
elim: l => //= a l IH.
have [aIl|aNIl] := boolP (_ \in _).
  by rewrite IH (allP IH).
rewrite !hornerE divfK; last first.
  by rewrite -mem_root prodl_root.
rewrite addrC subrK eqxx /=.
apply/allP=> b bIl.
rewrite !hornerE (eqP (allP IH _ bIl)).
rewrite (_ : _.[b] = 0) ?rm0 //.
by apply/eqP; rewrite -mem_root prodl_root.
Qed.

Lemma interp_size l : (size (interp l) <= size l)%N.
Proof.
elim: l => /= [|a l IH].
  by rewrite size_poly0.
have [aIl|aNIl] := boolP (_ \in _).
  by apply: leq_trans IH _.
Search _ (size _) (_ + _) in poly.
apply: leq_trans (size_add _ _) _.
rewrite geq_max (leq_trans IH _) // 
                (leq_trans (size_scale_leq _ _)) //.
by exact: prodl_size.
Qed.

End Interp.

Require Import Rstruct.
Require Import Reals Coquelicot.Coquelicot Interval.Interval_tactic Psatz.

Search "der" in poly.

Lemma is_derive_horner p x :
  is_derive (horner p : R -> R) x (p^`()).[x].
Proof.
elim/poly_ind: p => [|p c IH].
  rewrite deriv0 hornerE.
  apply: (is_derive_ext (fun x => 0)) => [t|]; first by rewrite hornerE.
  by exact: is_derive_const.
rewrite derivMXaddC !hornerE.
apply: (is_derive_ext (fun x => p.[x] * x + c)) => [t|].
  by rewrite !hornerE.
auto_derive; first by exists p^`().[x].
rewrite Rmult_1_r Rmult_1_l Rplus_comm.
congr (_ + _ * _).
by apply: is_derive_unique.
Qed.
