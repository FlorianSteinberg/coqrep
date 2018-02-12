(*This file contains the knowledge needed about second-order polynomials to prove
the closure of polynomial time computable operators under composition. It is
currently being changed to rely on representations and therefore not fully
functional. As an example for a represented space, the second-order polynomials
are a nice counterpoint to the real numbers because in this case the
representation is a total mapping on the name space but it is neither injective
nor surjective on the natural space of interpretations of the element, i.e. the
type (nat -> nat) -> nat -> nat. *)

From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions representations par_spaces.

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

Lemma star_is_computable:
   (fun (PQ: space (rep_space_prod sop sop)) => (star PQ.1 PQ.2):(space sop)) is_computable.
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
  (* The idea, why this is inside of the proof is that its only important property
    is that it computes the start operation. This way it is impossible for a user
    to rely on other properties of the mapping. *)
  exists (fun PQ => F PQ.1 PQ.2).
  move => [t1 t2] [P Q] [/= noP noQ] [_ _].
  move: t1 t2 P Q noP noQ; rewrite /F2MF.
  (* This decodes the pair given as input into its components. *)
  elim.
  (* the first three cases were removed by the // when no representations where used. *)
  - move => t1 P Q noP; by rewrite -noP.
  - move => t1 P Q noP; by rewrite -noP.
  - move => t1 P Q noP; by rewrite -noP.
  - move => t1 ih1 t2 ih2 t3 P Q noP noQ.
    move: ih1 (ih1 t3 (eval t1) Q) => _ /= ih1.
    move: ih2 (ih2 t3 (eval t2) Q) => _ /= ih2.
    (* due to the use of representations, the induction hypothesises need some work
      before we can actually use them. *)
    have: ((F t1 t3:(names sop)) is_name_of (star (eval t1) Q)).
    apply: ih1 => //.
    move: ih1 => _.
    have: ((F t2 t3:(names sop)) is_name_of (star (eval t2) Q)).
    apply: ih2 => //.
    move: ih2 => _ ih1 ih2.
    (* The rest of the proof is similar to what had to be done without
      representations *)
    rewrite ih1 ih2 /star.
    by rewrite -noP -noQ.
  - move => t1 ih1 t2 ih2 t3 P Q noP noQ.
    move: ih1 (ih1 t3 (eval t1) Q) => _ /= ih1.
    move: ih2 (ih2 t3 (eval t2) Q) => _ /= ih2.
    (* due to the use of representations, the induction hypothesises need some work
      before we can actually use them. *)
    have: ((F t1 t3:(names sop)) is_name_of (star (eval t1) Q)).
    apply: ih1 => //.
    move: ih1 => _.
    have: ((F t2 t3:(names sop)) is_name_of (star (eval t2) Q)).
    apply: ih2 => //.
    move: ih2 => _ ih1 ih2.
    (* The rest of the proof is similar to what had to be done without
      representations *)
    rewrite ih1 ih2 /star.
    by rewrite -noP -noQ.
  - move => t1 ih1 t2 P Q noP noQ.
    move: ih1 (ih1 t2 (eval t1) Q) => _ ih1.
    have: (eval(F t1 t2:(names sop)) = (star (eval t1) Q)).
    apply: ih1 => //.
    move: ih1 => _ ih1.
    rewrite /= ih1 /star.
    by rewrite -noP -noQ.
Qed.
(* When compared to the original proof in the other example file about second-order polynom-
ials this is considerably more complicated when using representations. That is for two
reasons: Firstly, one has to code and decode pairs to be able to use the product construction
of representations for reasoning about multivariate functions. The second problem is that
representations are meant to still work in a setting that is a lot more general. For instance
it is not usually possible to evaluate the representation. This leads to additional
bureaucracy. *)

Definition circ (P Q : sof) :sof := (fun l n => P (Q l) n).
Lemma circ_is_computable: (fun (PQ:space (rep_space_prod sop sop)) => (circ PQ.1 PQ.2):space sop) is_computable.
Proof.
  move: star_is_computable => [F] hypF.
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
  move: t1 t2 P Q noP noQ; rewrite /F2MF.
  elim.
  - move => t1 P Q noP; by rewrite -noP.
  - move => t1 P Q noP; by rewrite -noP.
  - move => t1 P Q noP; by rewrite -noP.
  - move => t1 ih1 t2 ih2 t3 P Q noP noQ.
    move: ih1 (ih1 t3 (eval t1) Q) => _ /= ih1.
    move: ih2 (ih2 t3 (eval t2) Q) => _ /= ih2.
    have: ((G t1 t3:(names sop)) is_name_of (circ (eval t1) Q)).
    apply: ih1 => //.
    move: ih1 => _.
    have: ((G t2 t3:(names sop)) is_name_of (circ (eval t2) Q)).
    apply: ih2 => //.
    move: ih2 => _ ih1 ih2.
    rewrite ih1 ih2 /circ.
    by rewrite -noP -noQ.
  - move => t1 ih1 t2 ih2 t3 P Q noP noQ.
    move: ih1 (ih1 t3 (eval t1) Q) => _ /= ih1.
    move: ih2 (ih2 t3 (eval t2) Q) => _ /= ih2.
    have: ((G t1 t3:(names sop)) is_name_of (circ (eval t1) Q)).
    apply: ih1 => //.
    move: ih1 => _.
    have: ((G t2 t3:(names sop)) is_name_of (circ (eval t2) Q)).
    apply: ih2 => //.
    move: ih2 => _ ih1 ih2.
    rewrite ih1 ih2 /circ.
    by rewrite -noP -noQ.
  - move => t1 ih1 t2 P Q noP noQ.
    move: ih1 (ih1 t2 (eval t1) Q) => _ ih1.
    have: (eval(G t1 t2:(names sop)) = (circ (eval t1) Q)).
    apply: ih1 => //.
    move: ih1 => _ ih1 /=.
    have: (F (t2, (G t1 t2))) is_name_of (star Q (circ (eval t1) Q)).
    apply (hypF (t2, (G  t1 t2)) (Q, circ (eval t1) Q)) => //=.
    split.
    - by exists t2.
    - by exists (G t1 t2).
    move: hypF => _ hypF.
    rewrite hypF /circ /star.
    by rewrite -noP -noQ.
Qed.

(*
Load size_types.
The rest of this file reasons about majorization and monotonicity. The concepts it
relies on are also provided by means of the major type from "size_types.v". Unfortunatelly
there is a clash since both the "size_type.v" as well as "representations.v" load the
file "functions.v". I should really get rid of the load stuff... but for now I'll just
reintroduce the notions.  *)
(* TODO: use size_types here *)

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
Implicit Types P : space sop.
Notation "f \+ g" := (fun n => f n + g n) (at level 50, left associativity).
Notation "f \* g" := (fun n => f n * g n) (at level 50, left associativity).
Lemma majsum l k l' k':
  major l k -> major l' k' -> major (l \+ l' : nat -> nat) (k \+ k').
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

Lemma sopmon: forall P, P is_element -> ismon P.
Proof.
  move => P [ie];rewrite /F2MF => noP.
  rewrite -noP.
  move: ie P noP.
  elim => t1 //.
  - by move => /=.
  - move => ih1 t2 ih2 P noP l k lmk.
    apply: majsum.
    - by apply (ih1 (eval t1)).
    - by apply (ih2 (eval t2)).
  - move => ih1 t2 ih2 P noP l k lmk.
    apply: majmul.
    - by apply (ih1 (eval t1)).
    - by apply (ih2 (eval t2)).
  - move=> ih P noP l k lmk /= n m nmm.
    have: (ismon (eval t1)).
    apply (ih (eval t1)) => //.
    move => im.
    by apply /lmk /im.
Qed.

Lemma sopmonsecond P l : P is_from sop -> ismon l -> ismon (P l).
Proof.
  move => ie.
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
  P is_from sop -> ismon l -> ismon k -> pwleq l k -> P l n <= P k n.
Proof.
  move => ie lismon kismon lsmallerk.
  by apply: sopmon => //; apply/majvspwleq.
Qed.