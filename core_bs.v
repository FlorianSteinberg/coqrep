(* This file provides basic notions for spaces of the form Q -> A for some arbitrary types Q and A.*)
From mathcomp Require Import all_ssreflect.
Require Import core_mf.
Require Import FunctionalExtensionality ClassicalChoice.
Require Import CRelationClasses.

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

(* coinciding on a finite list is an equivalence relation on the elemets of Baire space. *)
Lemma coin_ref L (phi: B):
	phi \and phi \coincide_on L.
Proof. by elim: L. Qed.

Lemma coin_sym L phi psi:
	phi \and psi \coincide_on L -> psi \and phi \coincide_on L.
Proof. by elim: L => //; split; [by rewrite H0.1| by apply/ H; apply H0.2]. Qed.

Lemma coin_trans L phi psi psi':
	phi \and psi \coincide_on L -> psi \and psi' \coincide_on L -> phi \and psi' \coincide_on L.
Proof.
by elim: L => // q L ih [] eq1 c1 [] eq2 c2; split; [rewrite eq1 eq2| apply: ih].
Qed.

Lemma coin_equiv L:
	Equivalence (fun phi psi => (coin phi psi L)).
Proof. by split; [apply/ coin_ref | apply/ coin_sym | apply/ coin_trans]. Qed.

Lemma coin_lstn (phi psi: B) L:
	phi \and psi \coincide_on L <-> (forall q, List.In q L -> phi q = psi q).
Proof.
elim: L => //; split => [ [ass1 ass2] q' [<- | listin] | ass ] //; first by apply H.1.
by split; last (apply H.2; intros); apply ass; [left | right].
Qed.

Lemma coin_app (phi psi: B) L K:
	phi \and psi \coincide_on (L ++ K) <-> (phi \and psi \coincide_on L /\ phi \and psi \coincide_on K).
Proof.
split; first by elim: L => [| a L ih] //=; case => eq b; have []:= ih b; do 2 try split.
by elim: L => [[_ coin]| a L ih [/=[/=ass1 ass2] ass3]] => //=; split => //; apply ih.
Qed.

Notation "L '\is_sublist_of' K" := (forall q, List.In q L -> List.In q K) (at level 2).

Lemma coin_mon phi psi L K:
	L \is_sublist_of K -> phi \and psi \coincide_on K -> phi \and psi \coincide_on L.
Proof. by rewrite !coin_lstn; intros; apply/H0/H. Qed.

End BAIRE_SPACE.
Notation "L '\is_sublist_of' K" := (forall q, List.In q L -> List.In q K) (at level 2).
Notation "phi '\and' psi '\coincide_on' L" := (coin phi psi L) (at level 2).

Section BAIRE_SPACE_SETS.
Context (Q A : Type).
Notation B := (Q -> A).

Definition closure (P: B -> Prop) phi :=
	forall L, exists psi, phi \and psi \coincide_on L /\ P psi.

Notation "P '\is_subset_of' Q" := (subset P Q) (at level 50).

Lemma subs_clos P:
	P \is_subset_of (closure P).
Proof. by move => phi; exists phi; split => //; apply: coin_ref. Qed.

Lemma clos_mon P P':
	P \is_subset_of P' -> (closure P) \is_subset_of (closure P').
Proof.
move => subs phi cPphi L; have [psi [coin Ppsi]]:= cPphi L.
by exists psi; split => //; apply subs.
Qed.

Lemma ccP_cP (P: B -> Prop):
	closure (closure P) \is_subset_of closure P.
Proof.
move => phi ccPphi L; have [psi [coin cPpsi]] := ccPphi L; have [psi' [coin' Ppsi']] := cPpsi L.
by exists psi'; split => //; apply: coin_trans coin coin'.
Qed.
End BAIRE_SPACE_SETS.
Notation "P '\is_subset_of' Q" := (subset P Q) (at level 50).

Section SEQUENCES.
Context (Q A: Type).
Notation B := (Q -> A).
Notation sequence:= (nat -> B).

Definition image (phin: sequence) phi := exists n, phi = phin n.

Lemma img_subs phin P:
	(image phin \is_subset_of P) <-> (forall n, P (phin n)).
Proof. by split => H m; [apply/ H; exists m | move => [n ->]; apply H]. Qed.

(* The convergence relation belonging to the topology is given as follows *)
Definition lim phin (psi: B) :=
	forall L, exists n, forall m, n <= m -> psi \and (phin m) \coincide_on L.
Notation "psi '\is_limit_of' phin" := (lim phin psi) (at level 50).

Lemma conv_cP (P: B -> Prop) phin psi:
	lim phin psi /\ (image phin \is_subset_of P) -> closure P psi.
Proof.
rewrite img_subs; case => conv elts L; have [n prop]:= conv L.
by exists (phin n); split => //; apply (prop n).
Qed.

End SEQUENCES.
