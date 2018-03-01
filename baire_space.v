(* This file provides basic notions for spaces of the form Q -> A for some arbitrary types Q and A.*)
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions.
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

Fixpoint coin (phi psi: B) L :=
  match L with
    | nil => True
    | cons s K => (phi s = psi s) /\ (coin phi psi K)
  end.
Notation "phi '\and' psi '\coincide_on' L" := (coin phi psi L) (at level 2).

Definition conv phin psi :=
	forall L, exists n, forall m, m <= n -> psi \and (phin m) \coincide_on L.

Lemma coin_ref (phi: B):
	forall L, phi \and phi \coincide_on L.
Proof. by elim. Qed.

Lemma coin_and_list_in (phi psi: B):
	forall L, phi \and psi \coincide_on L <-> (forall q, List.In q L -> phi q = psi q).
Proof.
elim=>// q L [] ih1 ih2.
split => ass.
	move: ass => [] ass1 ass2 q' listin.
	by case listin => ass'; [ rewrite -ass' | apply ih1 => //].
split; first by apply ass;left.
by apply ih2 => q' listin; apply ass; right.
Qed.

Lemma coin_listin (phi psi: B):
	forall L, phi \and psi \coincide_on L <-> (forall q, List.In q L -> phi q = psi q).
Proof. exact: coin_and_list_in. Qed.

Lemma coin_to_listin (phi psi: B):
	forall L, phi \and psi \coincide_on L -> (forall q, List.In q L -> phi q = psi q).
Proof. by move => L; apply: (coin_and_list_in phi psi L).1. Qed.

Lemma listin_to_coin (phi psi: B):
	forall L, (forall q, List.In q L -> phi q = psi q) -> phi \and psi \coincide_on L .
Proof. by move => L; apply: (coin_and_list_in phi psi L).2. Qed.

Lemma coin_sym phi psi L:
	phi \and psi \coincide_on L -> psi \and phi \coincide_on L.
Proof. by elim L => //; split; [by rewrite H0.1| by apply/ H; apply H0.2]. Qed.

Lemma coin_trans phi psi psi' L:
	phi \and psi \coincide_on L -> psi \and psi' \coincide_on L -> phi \and psi' \coincide_on L.
Proof.
elim: L => // q L ih [] eq1 c1 [] eq2 c2.
by split; [rewrite eq1 eq2| apply: ih].
Qed.

Lemma coin_app L K (phi psi: B):
	phi \and psi \coincide_on (L ++ K) <-> (phi \and psi \coincide_on L /\ phi \and psi \coincide_on K).
Proof.
split; elim: L.
			by replace (nil ++ K) with (K); split.
		move => a L ih.
		replace ((a :: L) ++ K) with ((a :: L)%SEQ ++ K)%list by trivial.
		rewrite -(List.app_comm_cons L K a).
		move => [ass1 ass2].
		split; try apply ih; try apply ass2.
		by split => //; apply ih; apply ass2.
	by move => [_ coin]; replace (nil ++ K) with (K).
move => a L ih [[ass1 ass2] ass3].
replace ((a :: L) ++ K) with ((a :: L)%SEQ ++ K)%list by trivial.
rewrite -(List.app_comm_cons L K a).
by split => //; apply ih.
Qed.

Notation "L '\is_sublist_of' K" := (forall q, List.In q L -> List.In q K) (at level 2).

Lemma coin_mon phi psi L K:
	L \is_sublist_of K -> phi \and psi \coincide_on K -> phi \and psi \coincide_on L.
Proof.
move => subl coin.
apply listin_to_coin => q listin.
by apply/ (coin_to_listin); [apply coin | apply subl].
Qed.

End BAIRE_SPACE.
Notation "L '\is_sublist_of' K" := (forall q, List.In q L -> List.In q K) (at level 2).
Notation "phi '\and' psi '\coincide_on' L" := (coin phi psi L) (at level 2).

Section BAIRE_SPACE_SETS.
Context (Q A : Type).
Notation B := (Q -> A).
Definition closure (P: B -> Prop) phi :=
	forall L, exists psi, phi \and psi \coincide_on L /\ P psi.

Lemma P_cP (P: B -> Prop):
	forall phi, P phi -> closure P phi.
Proof.
move => phi Pphi L.
exists phi; split => //.
exact: coin_ref.
Qed.

Lemma ccP_cP (P: B -> Prop):
	forall phi, closure (closure P) phi -> closure P phi.
Proof.
move => phi ccPphi L.
move: (ccPphi L) => [] psi [] coin cPphi.
move: (cPphi L) => [] psi' [] coin' Pphi.
by exists psi'; split => //; apply: coin_trans coin coin'.
Qed.

Lemma conv_cP (P: B -> Prop) phin psi:
	conv phin psi /\ (forall n, P (phin n)) -> closure P psi.
Proof.
move => [] conv elts L.
move: (conv L) => [] n prop.
by exists (phin n); split => //; apply (prop n).
Qed.
End BAIRE_SPACE_SETS.
