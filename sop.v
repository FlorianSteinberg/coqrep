(*This file is supposed to contain the knowledge needed about second-order
polynomials to prove the closure of polynomial time computable operators
under composition.*)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Definition sof:Type := (nat -> nat) -> nat -> nat.
Module Sop.
Inductive type:Type :=
  |zero
  |one
  |sp
  |add (P:type) (Q:type)
  |mult (P:type) (Q:type)
  |appl (P:type).
Fixpoint eval (P : type) l n :=
  match P with
    | Sop.sp => n
    | Sop.zero => 0
    | Sop.one => 1
    | Sop.add Q R => (eval Q l n) + (eval R l n)
    | Sop.mult Q  R => (eval Q l n) * (eval R l n)
    | Sop.appl Q => l (eval Q l n)
  end.

Definition sopeq (P Q : type) :=
  forall l n, eval P l n = eval Q l n.
End Sop.
Notation sop := Sop.type.
Delimit Scope sop_scope with sop.
Bind Scope sop_scope with sop.
Notation "0" := (Sop.zero): sop_scope.
Notation "1" := (Sop.one): sop_scope.
Notation "''n'" := (Sop.sp): sop_scope.
Notation "p + q" := (Sop.add p q): sop_scope.
Notation "p * q" := (Sop.mult p q): sop_scope.
Notation "''l' p" := (Sop.appl p) (format "''l'  p", at level 2): sop_scope.
Notation "p = q" := (Sop.sopeq p q): sop_scope.
Coercion Sop.eval : sop >-> Funclass.
Notation eval := Sop.eval.


Definition isrealizer (f : sof -> sof) (F : sop -> sop) :=
  forall (P : sop) l n, f P l n = F P l n.

Definition star (P Q : sof) (l : nat -> nat) (n : nat) := P l (Q l n).

Lemma stariscomputable:
  exists F : sop -> sop -> sop, forall P Q l n, 
  star (eval P) (eval Q) l n = eval (F P Q) l n.
Proof.
  set F := fix F P Q :=
  match P with
    | 0 => 0
    | 1 => 1
    | 'n => Q
    | R + T => (F R Q) + (F T Q)
    | R * T => (F R Q) * (F T Q)
    | 'l R => 'l (F R Q)
  end%sop.
  exists F.
  elim =>//.
  - move => P indhypP Q indhypQ Q0 l n.
    by rewrite /star /= - indhypQ - indhypP.
  - move => P indhypP Q indhypQ Q0 l n.
    by rewrite /star /= - indhypQ - indhypP.
  - move => P indhypP Q0 l n.
  - by rewrite /star /= - indhypP.
Qed.

Definition circ (P Q : sof) (l : nat -> nat) (n : nat) := P (Q l) n.
Lemma circiscomputable l n : exists G:sop -> sop -> sop,
  forall P Q, circ (eval P) (eval Q) l n = eval (G P Q) l n.
Proof.
  move: stariscomputable.
  case.
  move => F hypF.
  set G:= fix G P Q :=
  match P with
    | 0 => 0
    | 1 => 1
    | 'n => 'n
    | R + T => (G R Q) + (G T Q)
    | R * T => (G R Q) * (G T Q)
    | 'l R => F Q (G R Q)
  end%sop.
  exists G.
  elim => // P IHP Q.
  - move => IHQ Q0.
    by rewrite /circ /= - IHQ - IHP.
  - move => IHQ Q0.
    by rewrite /circ /= - IHQ - IHP.
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