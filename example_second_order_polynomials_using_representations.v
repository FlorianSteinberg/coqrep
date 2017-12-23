(*This file is supposed to contain the knowledge needed about second-order
polynomials to prove the closure of polynomial time computable operators
under composition. It is currently a mess and needs to be cleaned up. I want
to eventually make this another example of representations, but I do not yet
know how to use subtypes properly. *)

Load representations.

Require Import FunctionalExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Definition sof:Type := (nat -> nat) -> nat -> nat.
Module Sop.
Inductive term:Type :=
  |zero
  |one
  |sp
  |add (P:term) (Q:term)
  |mult (P:term) (Q:term)
  |appl (P:term).
Fixpoint eval (P : term) l n :=
  match P with
    | Sop.sp => n
    | Sop.zero => 0
    | Sop.one => 1
    | Sop.add Q R => (eval Q l n) + (eval R l n)
    | Sop.mult Q  R => (eval Q l n) * (eval R l n)
    | Sop.appl Q => l (eval Q l n)
  end.
Definition sop := @make_rep_space_from_fun sof term zero eval.
End Sop.

Notation sop := Sop.sop.
Delimit Scope sop_scope with sop.
Bind Scope sop_scope with sop.
Notation "0" := (Sop.zero): sop_scope.
Notation "1" := (Sop.one): sop_scope.
Notation "''n'" := (Sop.sp): sop_scope.
Notation "p + q" := (Sop.add p q): sop_scope.
Notation "p * q" := (Sop.mult p q): sop_scope.
Notation "''l' p" := (Sop.appl p) (format "''l'  p", at level 2): sop_scope.
Notation eval := Sop.eval.

Definition star (S T: sof) : sof := (fun l n => S l (T l n)).
Definition star_sop (PQ: (sop*sop)) : (space sop) :=
  star PQ.1 PQ.2.

Lemma star_is_computable:
  star_sop is_computable.
Proof.
  set F := fix F t1 t2 :=
  match t1 with
    | 0 => 0
    | 1 => 1
    | 'n => t2
    | R + T => (F R t2) + (F T t2)
    | R * T => (F R t2) * (F T t2)
    | 'l R => 'l (F R t2)
  end%sop.
  exists (fun PQ => F PQ.1 PQ.2).
  move => t1t2.
  rewrite {1}(surjective_pairing t1t2).
  move: t1t2.1 t1t2.2 => t1 t2.
  move: t1t2 => _.
  move: t1 t2.
  elim => //.
  - move => t1 PQ [ih1 _] [_ _].
    by rewrite /star_sop /star; rewrite -ih1.
  - move => t1 PQ [ih1 _] [_ _].
    by rewrite /star_sop /star; rewrite -ih1.
  - move => t1 PQ [ih1 ih2] [_ _].
    by rewrite /star_sop /star; rewrite -ih1 -ih2.
  - move => t1 ih1 t2 ih2 t3 PQ [noP noQ] _.
    move: (ih1 t3 (eval t1, eval t3)).
    move: ih1 => _ ih1.
    have: ((F t1 t3:(names sop)) is_name_of (star_sop (eval t1, eval t3))).
    apply: ih1.
    split => //.
    split.
    by exists t1.
    by exists t3.
    move: ih1 => _.
    move: (ih2 t3 (eval t2, eval t3)).
    move: ih2 => _ ih2.
    have: ((F t2 t3:(names sop)) is_name_of (star_sop (eval t2, eval t3))).
    apply: ih2.
    split => //.
    split.
    by exists t2.
    by exists t3.
    move: ih2 => _.
    rewrite /= /F2MF.
    move => ih1 ih2.
    rewrite -/eval /=.
    rewrite ih1 ih2.
    rewrite /star_sop /star /=.
    by rewrite -noP -noQ /=.
  - move => t1 ih1 t2 ih2 t3 PQ [noP noQ] _.
    move: (ih1 t3 (eval t1, eval t3)).
    move: ih1 => _ ih1.
    have: ((F t1 t3:(names sop)) is_name_of (star_sop (eval t1, eval t3))).
    apply: ih1.
    split => //.
    split.
    by exists t1.
    by exists t3.
    move: ih1 => _.
    move: (ih2 t3 (eval t2, eval t3)).
    move: ih2 => _ ih2.
    have: ((F t2 t3:(names sop)) is_name_of (star_sop (eval t2, eval t3))).
    apply: ih2.
    split => //.
    split.
    by exists t2.
    by exists t3.
    move: ih2 => _.
    rewrite /= /F2MF.
    move => ih1 ih2.
    rewrite -/eval /=.
    rewrite ih1 ih2.
    rewrite /star_sop /star /=.
    by rewrite -noP -noQ /=.
  - move => t1 ih1 t2 PQ [noP noQ] ie.
    move: (ih1 t2 (eval t1, eval t2)).
    move: ih1 => _ ih1.
    have: ((F t1 t2:(names sop)) is_name_of (star_sop (eval t1, eval t2))).
    apply: ih1.
    split => //.
    split.
    by exists t1.
    by exists t2.
    move: ih1 => _ ih1.
    rewrite /= /F2MF.
    rewrite -/eval /=.
    rewrite ih1.
    rewrite /star_sop /star /=.
    by rewrite -noP -noQ.
Qed.
(* This proof got considerably more complicated when I started using representations. I need to
understand why this is so. *)

Definition circ (P Q : sop) :sop := (fun l n => P (Q l) n).
Lemma circ_is_computable: (fun PQ => circ PQ.1 PQ.2) is_computable.
Proof.
  move: star_is_computable.
  case.
  move => F hypF.
  set G:= fix G P Q :=
  match P with
    | 0 => 0
    | 1 => 1
    | 'n => 'n
    | R + T => (G R Q) + (G T Q)
    | R * T => (G R Q) * (G T Q)
    | 'l R => F (Q,(G R Q))
  end%sop.
  exists (fun PQ => G PQ.1 PQ.2).
  move => [t1 t2] [P Q] [/= noP noQ] [_ _].
  move: t1 t2 noP noQ.
  rewrite /circ /F2MF.
  elim.
  - move => t1 ih noQ.
    by rewrite -ih.
  - move => t1 ih noQ.
    by rewrite -ih.
  - move => t1 ih noQ.
    by rewrite -ih.
  - move => t1 ih1 t2 ih2 t3 [noP noQ].
    move: (ih1 t3).
    move: ih1 => _ ih1.
    have: (eval (G t1 t3:(names sop)) = (fun l : nat -> nat => [eta P (Q l)])).
    apply: ih1 => //.
    split.
    by exists t1.
    by exists t3.
    move: ih1 => _.
    move: (ih2 t3 (eval t2, eval t3)).
    move: ih2 => _ ih2.
    have: ((F t2 t3:(names sop)) is_name_of (star_sop (eval t2, eval t3))).
    apply: ih2.
    split => //.
    split.
    by exists t2.
    by exists t3.
    move: ih2 => _.
    rewrite /= /F2MF.
    move => ih1 ih2.
    rewrite -/eval /=.
    rewrite ih1 ih2.
    rewrite /star_sop /star /=.
    by rewrite -noP -noQ /=.
  - move => t1 ih1 t2 ih2 t3 PQ [noP noQ] _.
    move: (ih1 t3 (eval t1, eval t3)).
    move: ih1 => _ ih1.
    have: ((F t1 t3:(names sop)) is_name_of (star_sop (eval t1, eval t3))).
    apply: ih1.
    split => //.
    split.
    by exists t1.
    by exists t3.
    move: ih1 => _.
    move: (ih2 t3 (eval t2, eval t3)).
    move: ih2 => _ ih2.
    have: ((F t2 t3:(names sop)) is_name_of (star_sop (eval t2, eval t3))).
    apply: ih2.
    split => //.
    split.
    by exists t2.
    by exists t3.
    move: ih2 => _.
    rewrite /= /F2MF.
    move => ih1 ih2.
    rewrite -/eval /=.
    rewrite ih1 ih2.
    rewrite /star_sop /star /=.
    by rewrite -noP -noQ /=.
  - by rewrite /circ /= - hypF /star -IHP.
Qed.
Fixpoint itrd P:=
  match P with
    |Sop.zero=> 0
    |Sop.one => 0
    |Sop.sp => 0
    |Sop.add P Q => maxn (itrd P) (itrd Q)
    |Sop.mult P Q => maxn (itrd P) (itrd Q)
    |Sop.appl P => (itrd P) .+1
  end.

Module Major.
Structure type:= Pack {sort :> Type ; _ : sort -> sort -> Prop}.
End Major.

Coercion Major.sort : Major.type >-> Sortclass.

Definition major {M : Major.type} : M -> M -> Prop :=
  match M with Major.Pack _ rel => rel end.

Canonical Major_nat := @Major.Pack nat leq.
Canonical Major_arrow M1 M2 := @Major.Pack
  (Major.sort M1 -> Major.sort M2)
    (fun l k => forall n m, major n m -> major (l n) (k m)).
Canonical Major_prod M1 M2 := @Major.Pack
  (Major.sort M1 * Major.sort M2)
    (fun m n => major m.1 n.1 /\ major m.2 n.2).

Implicit Types l k : nat -> nat.
Implicit Types n m : nat.
Implicit Types P : sop.
Notation "f \+ g" := (fun n => f n + g n) (at level 50, left associativity).

Lemma majsum l k l' k':
  major l k -> major l' k' ->
    major (l \+ l' : nat -> nat) (k \+ k').
Proof.
  move => lmajork mmajorn n0 m0 n0leqm0.
  rewrite /major /= leq_add //.
  - apply lmajork.
    apply n0leqm0.
  - apply mmajorn.
    apply n0leqm0.
Qed.

Lemma majmul l k l' k':
  major l k -> major l' k' ->
    major ((fun r => l r * l' r) : nat -> nat) (fun r => k r * k' r).
Proof.
  move => lmajork mmajorn n0 m0 n0leqm0.
  rewrite /major /= leq_mul //.
  - apply lmajork.
    apply n0leqm0.
  - apply mmajorn.
    apply n0leqm0.
Qed.

Notation ismon l := (major l l).

Lemma monotone l:
  ismon l = forall n m, n <= m -> l(n) <= l(m).
Proof.
  done.
Qed.

Lemma sumismon l k:
  ismon l -> ismon k -> ismon ((fun n=> l n + k n ) : nat -> nat).
Proof.
  exact: majsum.
Qed.

Lemma multismon l k:
  ismon l -> ismon k -> ismon ((fun n => l n * k n) : nat -> nat).
Proof.
  exact: majmul.
Qed.

Lemma sopmon: forall (P : sop), ismon (P : sof).
Proof.
  elim => [|||P IHP Q IHQ|P IHP Q IHQ|P IHP] //= l k major_lk //=.
  - apply majsum.
    - exact: IHP.
    - exact: IHQ.
  - apply majmul.
    - exact: IHP.
    - exact: IHQ.
  - by move=> n m nleqm; apply /major_lk /IHP.
Qed.

Lemma sopmonsecond P l : ismon l -> ismon (eval P l).
Proof.
  exact: sopmon.
Qed.

Notation pwleq l k := (forall (n:nat), l n <= k n).

Lemma ismon_nat n : ismon n. Proof. exact: leqnn. Qed.
Hint Resolve ismon_nat.

Lemma majvspwleq l k :
  ismon l -> ismon k -> pwleq l k <-> major l k.
Proof.
  move => lismon kismon.
  split.
  - move => lpwleqk n m nleqm;apply: (@leq_trans (k n)).
    - apply: lpwleqk.
    - exact: kismon nleqm.
  - by move => lmajork n; apply: lmajork.
Qed.

Lemma sopmonfirst P l k n :
  ismon l -> ismon k -> pwleq l k -> P l n <= P k n.
Proof.
  move => lismon kismon lsmallerk.
  by apply: sopmon => //; apply/majvspwleq.
Qed.