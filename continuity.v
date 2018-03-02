(* This file provides a definition of continuity of functions between spaces of the form
Q -> A for some arbitrary types Q and A. It also proves some basic Lemmas about this notion.*)
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions baire_space.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CONTINUITY_DEFINITION.
Context (Q A Q' A' : Type).
(* Q is for questions, A is for answers*)
Notation B := (Q -> A).
Notation B' := (Q' -> A').
(* B is for Baire space. *)

(* It is sometimes hepfull thing of B as a language: An element of B is a - notneccessarily
meaningful - conversation: when a question q: Q, is asked in such a conversation, some
information phi(q): I is returned as answer. Usually the questions and answers can be encoded
as natural numbers, which will give the usual Baire space nat -> nat. *)

(* The set of meaningful conversations in a language is a subset of the Baire space corre-
sponding to that language. It is instructive to think about each meaningful conversation
as description of an abstract object. *)
Context (F: B ->> B').
(* F is a multivalued function and a good example of such a function is a translation languages.
Such a translation should assing to each meaningful description of an object in the input
language, i.e. element of (dom F) a description of the same object in the output language. *)

(* For such a translation to exists, it should at least be the case that each property of an
object that each question q' asked about an object in the output language can be answered by
asking questions from a finit list L about the object in the input lanuage. This property is called
continuity of the translation. *)

Definition determines phi q' a' := forall Fphi, F phi Fphi -> a' = Fphi q'.

Definition eligible phi q' a' := exists Fphi, F phi Fphi /\ a' = Fphi q'.

Definition cert L phi q' a' := forall psi, phi \and psi \coincide_on L -> determines psi q' a'.

Lemma cert_det phi q' a':
	(exists L, cert L phi q' a') -> determines phi q' a'.
Proof. by move => [] L crt elg; apply/ crt; apply coin_ref. Qed.

Lemma cert_mon L K phi q' a':
	L \is_sublist_of K -> cert L phi q' a' -> cert K phi q' a'.
Proof. by move => subl det psi coin; apply: det; apply (coin_mon subl). Qed.

Lemma cert_cons L phi psi q' a':
	phi \and psi \coincide_on L -> cert L phi q' a' -> cert L psi q' a'.
Proof.
move => coin det psi' coin' Fpsi' Fpsi'Fpsi'.
apply/ det; last by apply Fpsi'Fpsi'.
by apply (coin_trans coin coin').
Qed.

Definition mf_mod phiq L:= forall Fphi, F phiq.1 Fphi -> cert L phiq.1 phiq.2 (Fphi phiq.2).
(* Such a translation is continuous if for each question about an object in the second
language, an answer can be found from a dscription in the first language by asking a finite
number of questions. *)

Lemma mod_elig_cert phiq L:
	mf_mod phiq L <-> forall a', eligible phiq.1 phiq.2 a' -> cert L phiq.1 phiq.2 a'.
Proof.
split => [eligcert a' [] Fphi [] FphiFhi eq | mod Fphi FphiFphi psi coin].
	by rewrite eq; apply /eligcert.
by apply: (mod (Fphi phiq.2)); [ exists Fphi; split | apply coin ].
Qed.

Lemma mod_mon phiq L K:
	L \is_sublist_of K -> mf_mod phiq L -> mf_mod phiq K.
Proof. by move => sl mod Fphi FphiFphi; apply/ cert_mon; [ apply sl | apply mod ]. Qed.

Definition is_cont_in phi := forall q', phi \from_dom F -> (phi, q') \from_dom mf_mod.
Definition is_cont := forall phi, is_cont_in phi.
End CONTINUITY_DEFINITION.

Notation "F '\is_continuous'" := (is_cont F) (at level 2).
Notation "F '\is_continuous_in' phi" := (is_cont_in F phi) (at level 2).

Section CONTINUITY_LEMMAS.
Context (Q A Q' A' : Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').

Lemma elig_exte (F G: B ->> B') phi q' a':
	F \extends G -> eligible G phi q' a' -> eligible F phi q' a'.
Proof.
move => GeF [] Gphi [] GphiGphi eq.
by exists Gphi; split => //; apply/ GeF.
Qed.

Lemma det_exte (F G: B ->> B') phi q' a':
	G \extends F -> determines G phi q' a' -> determines F phi q' a'.
Proof.
move => GeF det Fpsi FpsiFpsi.
by apply det; apply GeF.
Qed.

Lemma cert_exte (F G: B ->> B') L phi q' a':
	G \extends F -> cert G L phi q' a' -> cert F L phi q' a'.
Proof.
move => GeF certi psi coin.
by apply/ det_exte; [apply GeF | apply certi].
Qed.

Definition c_dom (F: B ->> B') phi :=
	closure (dom F) phi.

Lemma dom_cdom (F: B ->> B') phi:
	phi \from_dom F -> c_dom F phi.
Proof. exact: P_cP. Qed.

Lemma cert_cdom (F: B ->> B') phi q' a':
	~ c_dom F phi -> exists L, cert F L phi q' a'.
Proof.
move => neg.
have [L Lprop]: exists L, forall psi, ~ (phi \and psi \coincide_on L /\ psi \from_dom F).
	apply NNPP => ex; apply neg => L; apply NNPP => negi.
	exfalso; apply ex; exists L => psi [] coin val.
	by apply negi; exists psi.
exists L => psi coin Fpsi FpsiFpsi.
exfalso; apply (Lprop psi).
by split; last by exists Fpsi.
Qed.

Definition is_mod (F: B ->> B') mf:= forall phi q', phi \from_dom F ->  mf_mod F (phi, q') (mf phi q').
Notation "mf '\is_modulus_of' F" := (is_mod F mf) (at level 2).

Lemma cont_mod (F: B ->> B'):
	F \is_continuous <-> exists mf, mf \is_modulus_of F.
Proof.
split => [ cont | [] mf mprop phi q']; last by exists (mf phi q'); apply / mprop.
move: (exists_choice (mf_mod F) nil) => [] mf mprop.
exists (fun phi q' => mf (phi,q')) => phi q' phifd.
have [L Lprop]:= (cont phi q' phifd).
by apply: (mprop (phi, q') L).
Qed.

Lemma elig_restr P (F: B ->> B') phi q' a':
	eligible (F \restricted_to P) phi q' a' -> P phi /\ eligible F phi q' a'.
Proof. by move => [] Fphi [] []; split => //; exists Fphi. Qed.

Lemma restr_elig (P: B -> Prop) (F: B ->> B') phi q' a':
	P phi -> eligible F phi q' a' -> eligible (F \restricted_to P) phi q' a'.
Proof. by move => Pphi [] Fphi []; exists Fphi. Qed.

Lemma det_restr P (F: B ->> B') phi q' a':
	determines (F \restricted_to P) phi q' a' <-> (P phi -> determines F phi q' a').
Proof.
split; first by move => det Pphi Fphi val; apply det.
by move => prop Fphi [] Pphi; apply: (prop Pphi).
Qed.

Definition dom_cont (F: B ->> B') phi := (forall q', (phi, q') \from_dom (mf_mod F)).

Lemma dom_domc (F: B ->> B'):
	F \is_continuous -> forall phi, phi \from_dom F -> dom_cont F phi.
Proof. move => cont phi fd q'; by apply cont. Qed.

Lemma domc_cont (F: B ->> B'):
	(forall phi, phi \from_dom F -> dom_cont F phi ) <-> F \is_continuous.
Proof.
split => [ domc phi dom q' | ]; [exact: (domc phi q' dom) | exact: dom_domc ].
Qed.

Lemma cont_domc (F: B ->> B'):
	(F \restricted_to (dom_cont F)) \is_continuous.
Proof.
move => phi q' [] Fphi [] domc.
have [L Lprop]:= (domc q'); exists L => Fphi' [] /= _ val psi coin.
apply/ det_restr => domcpsi.
by apply/ Lprop.
Qed.

Lemma cont_to_sing (F: B ->> B'):
	F \is_continuous -> F \is_single_valued.
Proof.
move => cont phi Fphi Fpsi FphiFphi FphiFpsi.
apply functional_extensionality => q'.
have fd: phi \from_dom F by exists Fphi.
have [L Lprop]:= (cont phi q' fd).
by apply/ Lprop; [ | apply coin_ref | apply FphiFpsi ].
Qed.

Lemma cont_exte (F G: B ->> B'):
	G \tightens F -> G \is_continuous -> F \is_single_valued -> F \is_continuous.
Proof.
move => GtF Gcont Fsing phi q' [] Fphi FphiFphi.
have GeF:= (tightening_of_single_valued Fsing GtF).
have fdG: phi \from_dom G by exists Fphi; apply GeF.
have [L Lprop]:= (Gcont phi q' fdG).
exists L => Fphi' /= FphiFphi' psi coin Fpsi FpsiFpsi.
by apply/ Lprop; [ apply GeF | apply coin | apply: GeF ].
Qed.
End CONTINUITY_LEMMAS.
Notation "mf '\is_modulus_of' F" := (is_mod F mf) (at level 2).
