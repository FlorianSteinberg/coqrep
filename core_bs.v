(* This file provides basic notions for spaces of the form Q -> A for some arbitrary types Q and A.*)
From mathcomp Require Import all_ssreflect.
Require Import core_mf.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BAIRE_SPACE.
Context (Q A : Type).
(* Q is for questions, A is for answers*)
Notation B := (Q -> A).
(* B is for Baire space. The topology is the product topology, the convergence relation can be
described as follows.*)

(* The topology on Baire space is the topology of pointwise convergence the following are
the basic open ets (in the sens that for each finite list L and each element phi of Baire
space the set {psi | coin phi psi L} is a basic open set *)
Fixpoint coin (phi psi: B) L :=
  match L with
    | nil => True
    | cons s K => (phi s = psi s) /\ (coin phi psi K)
  end.
Notation "phi '\and' psi '\coincide_on' L" := (coin phi psi L) (at level 2).

(* The convergence relation belonging to the topology is given as follows *)
Definition conv phin psi :=
	forall L, exists n, forall m, m <= n -> psi \and (phin m) \coincide_on L.

(* coinciding on a finite list is an equivalence relation on the elemets of Baire space. *)
Lemma coin_ref (phi: B):
	forall L, phi \and phi \coincide_on L.
Proof. by elim. Qed.

Lemma coin_sym phi psi L:
	phi \and psi \coincide_on L -> psi \and phi \coincide_on L.
Proof. by elim L => //; split; [by rewrite H0.1| by apply/ H; apply H0.2]. Qed.

Lemma coin_trans phi psi psi' L:
	phi \and psi \coincide_on L -> psi \and psi' \coincide_on L -> phi \and psi' \coincide_on L.
Proof.
elim: L => // q L ih [] eq1 c1 [] eq2 c2.
by split; [rewrite eq1 eq2| apply: ih].
Qed.

Lemma coin_lstn (phi psi: B) L:
	phi \and psi \coincide_on L <-> (forall q, List.In q L -> phi q = psi q).
Proof.
elim L => //; split => [ [ass1 ass2] q' listin | ass ].
	by case listin => ass'; [ rewrite -ass' | apply H.1 => //].
by split; [ apply ass; left | apply H.2 => q' listin; apply ass; right].
Qed.

Lemma coin_app (phi psi: B) L K:
	phi \and psi \coincide_on (L ++ K) <-> (phi \and psi \coincide_on L /\ phi \and psi \coincide_on K).
Proof.
split.
	elim: L => [| a L ih]; first by replace (nil ++ K) with (K).
	replace ((a :: L) ++ K) with ((a :: L)%SEQ ++ K)%list by trivial.
	rewrite -(List.app_comm_cons L K a).
	by move => [ass1 ass2];	split; [ split => // | ]; apply ih; apply ass2.
elim: L => [[_ coin]| a L ih [[ass1 ass2] ass3]]; first by replace (nil ++ K) with (K).
replace ((a :: L) ++ K) with ((a :: L)%SEQ ++ K)%list by trivial.
by rewrite -(List.app_comm_cons L K a); split => //; apply ih.
Qed.

Notation "L '\is_sublist_of' K" := (forall q, List.In q L -> List.In q K) (at level 2).

Lemma coin_mon phi psi L K:
	L \is_sublist_of K -> phi \and psi \coincide_on K -> phi \and psi \coincide_on L.
Proof.
move => subl coin; apply/ coin_lstn => q listin.
by rewrite ((coin_lstn phi psi K).1 coin q) => //; apply subl.
Qed.

End BAIRE_SPACE.
Notation "L '\is_sublist_of' K" := (forall q, List.In q L -> List.In q K) (at level 2).
Notation "phi '\and' psi '\coincide_on' L" := (coin phi psi L) (at level 2).

Section BAIRE_SPACE_SETS.
Context (Q A : Type).
Notation B := (Q -> A).
Definition closure (P: B -> Prop) phi :=
	forall L, exists psi, phi \and psi \coincide_on L /\ P psi.

Lemma P_cP (P: B -> Prop) phi:
	P phi -> closure P phi.
Proof. exists phi; split => //; exact: coin_ref. Qed.

Lemma ccP_cP (P: B -> Prop) phi:
	closure (closure P) phi -> closure P phi.
Proof.
move => ccPphi L.
move: (ccPphi L) => [] psi [] coin cPphi.
move: (cPphi L) => [] psi' [] coin' Pphi.
by exists psi'; split => //; apply: coin_trans coin coin'.
Qed.

Lemma conv_cP (P: B -> Prop) phin psi:
	conv phin psi -> (forall n, P (phin n)) -> closure P psi.
Proof.
move => conv elts L.
move: (conv L) => [] n prop.
by exists (phin n); split => //; apply (prop n).
Qed.
End BAIRE_SPACE_SETS.
