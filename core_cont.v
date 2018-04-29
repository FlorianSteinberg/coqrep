(* This file provides a definition of continuity of functions between spaces of the form
Q -> A for some arbitrary types Q and A. It also proves some basic Lemmas about this notion.*)
From mathcomp Require Import all_ssreflect.
Require Import core_mf core_bs.
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

(* Note that we start from an arbitrary multivalued function F for which the return value on input
phi need not even be unique. Thus, before we start talking about finite lists determining the return
value, we first express wha it means for an input to determine the value. *)
Definition determines phi q' a' := forall Fphi, F phi Fphi -> a' = Fphi q'.

(* determines is closely connected to being single valued. *)
Lemma det_sing:
	(forall phi, phi \from_dom F -> forall q', exists a', determines phi q' a') <-> F \is_single_valued.
Proof.
split => [detall | sing].
	move => phi Fphi Fphi' FphiFphi FphiFphi'.
	apply functional_extensionality => q'.
	have [ | a' det] := (detall phi _ q'); first by exists Fphi.
	by rewrite -(det Fphi); first rewrite -(det Fphi').
move => phi [Fphi FphiFphi] q'.
exists (Fphi q') => Fphi' FphiFphi'.
by rewrite (sing phi Fphi Fphi').
Qed.

(* There is a dual concept that will also be usefull *)
Definition eligible phi q' a' := exists Fphi, F phi Fphi /\ a' = Fphi q'.
(* eligible is closely connected to being total *)

Lemma dom_elig:
	F \is_total -> forall phi q', exists a', eligible phi q' a'.
Proof.
move => tot phi q'; have [Fphi FphiFphi]:= tot phi.
by exists (Fphi q'); exists Fphi.
Qed.

Lemma elig_dom:
	inhabited Q' -> F \is_total <-> forall phi q', exists a', eligible phi q' a'.
Proof.
move => [q']; split; first exact dom_elig; move => eligall phi.
by have [_ [Fphi [FphiFphi _]]]:= eligall phi q'; exists Fphi.
Qed.

(* For being determined from a finite list we use the notion of functions conciding
on lists from core_bs.v *)
Definition cert L phi q' a' := forall psi, phi \and psi \coincide_on L -> determines psi q' a'.
(* cert is for certificate and cert L phi q' a' means that the values of phi on the list L
is enough to determine the return value a' on input q'. *)

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

(* We define a multivalued modulus function that makes sense even if F is not continuous. *)
Definition mf_mod phiq L:= phiq.1 \from_dom F /\ forall Fphi, F phiq.1 Fphi -> cert L phiq.1 phiq.2 (Fphi phiq.2).
(* The following Lemma gives a good specification for mf_mod: L is a value if whenever there
exists an eligible return value, then L is a certificate for that value. *)

Lemma mod_elig_cert phiq L:
	mf_mod phiq L <-> phiq.1 \from_dom F /\ forall a', eligible phiq.1 phiq.2 a' -> cert L phiq.1 phiq.2 a'.
Proof.
split => [[phifd mod] | ]; first by split => // a' [Fphi [FphiFphi ->]]; apply/ mod.
by move => [phifd eligcert]; split => // Fphi FphiFphi; apply eligcert; exists Fphi.
Qed.

Lemma mod_mon phiq L K:
	L \is_sublist_of K -> mf_mod phiq L -> mf_mod phiq K.
Proof. by move => sl [phifd mod]; split => //; intros; apply/(cert_mon sl)/mod. Qed.

Definition cont_xtndbl_to phi := forall q', (phi, q') \from_dom mf_mod.
Definition is_cont_in phi := phi \from_dom F /\ cont_xtndbl_to phi.
Definition is_cont := forall phi, phi \from_dom F -> cont_xtndbl_to phi.

Lemma cont_cont_in:
	is_cont <-> (forall phi, phi \from_dom F -> is_cont_in phi).
Proof.
split => [cont | cntn].
	by move => phi phifd; split => // q'; exact/ cont.
by move => phi phifd; exact/ (cntn phi phifd).2.
Qed.
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

Definition c_dom (F: B ->> B') phi := closure (dom F) phi.

Lemma dom_cdom (F: B ->> B') phi:
	phi \from_dom F -> c_dom F phi.
Proof. exact: subs_clos. Qed.

(* The following is the reason why the phi \from_dom F is part of many definitions *)
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

Definition is_mod (F: B ->> B') mf:= forall phi q', phi \from_dom F -> mf_mod F (phi, q') (mf phi q').
Notation "mf '\is_modulus_of' F" := (is_mod F mf) (at level 2).

Lemma mod_cont F mf:
	is_mod F mf <-> forall phi Fphi, F phi Fphi -> forall q', cert F (mf phi q') phi q' (Fphi q').
Proof.
split => [mod phi Fphi FphiFphi q' | ]; last by move => prop; split => //=; intros; apply prop.
by have phifd: phi \from_dom F; [exists Fphi | have [/=_ prop]:= (mod phi q' phifd); apply prop].
Qed.

Lemma cont_mod (F: B ->> B'):
	F \is_continuous <-> exists mf, mf \is_modulus_of F.
Proof.
split => [cont | [mf mprop] phi phifd q']; last by exists (mf phi q'); apply mprop.
have [mf mprop] := exists_choice (mf_mod F) nil.
exists (fun phi q' => mf (phi, q')); move => phi q' phifd.
by have [L Lprop]:= (cont phi phifd q'); exact (mprop _ _ Lprop).
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
Proof. by split => ass phi phifd; apply ass. Qed.

Lemma cont_domc (F: B ->> B'):
	(F \restricted_to (dom_cont F)) \is_continuous.
Proof.
move => phi [Fphi [domc FphiFphi]] q'.
have [L [/= phifd Lprop]]:= domc q'; exists L; split; first by exists Fphi.
move => Fphi' [/= _ val] psi coin.
by apply/ det_restr => domcpsi; apply/ Lprop.
Qed.

Lemma cont_sing (F: B ->> B'):
	F \is_continuous -> F \is_single_valued.
Proof.
move => cont; apply det_sing; intros.
have [L [[Fphi FphiFphi] /=Lprop]]:= cont phi H q'.
by exists (Fphi q'); apply cert_det; exists L; apply Lprop.
Qed.

Lemma cont_exte (F G: B ->> B'):
	G \tightens F -> G \is_continuous -> F \is_single_valued -> F \is_continuous.
Proof.
move => GtF Gcont Fsing phi; case; have GeF:= (tight_sing Fsing GtF); intros => q'.
have [ | L [_ /=Lprop]]:= (Gcont phi _ q'); first by exists x; apply GeF.
by exists L; split; [exists x | intros; apply/ (cert_exte GeF)/ Lprop/GeF].
Qed.

Lemma cont_comp Q'' A'' (F: B ->> B') (G: B' ->> (Q'' -> A'')):
	F \is_continuous -> G \is_continuous -> G o F \is_continuous.
Proof.
move => Fcont Gcont phi phifd q''.
have [mf ismod]:= ((cont_mod F).1 Fcont).
case (classic (phi \from_dom F)) => [[Fphi FphiFphi]| nfd]; last first.
	exists nil; split => // GFpsi [[Fphi [/= FphiFphi]]].
	by exfalso; apply nfd; exists Fphi.
have FphifdG: Fphi \from_dom G by have [_ [_ prop]]:= phifd; apply prop.
have [L [/=_ Lprop]]:= (Gcont Fphi FphifdG q'').
set gather := fix gather K := match K with
	| nil => nil
	| cons q' K' => app (mf phi q') (gather K')
end.
exists (gather L); split => //= GFphi [] [] Fphi' [] FphiFphi' GFphi'GFphi _ psi coing.
move => GFpsi [] [] Fpsi [] FpsiFpsi GFpsiGFpsi _.
have gprop: forall K, phi \and psi \coincide_on (gather K) -> Fphi \and Fpsi \coincide_on K.
	elim => // a K ih coin.
	have [coin1 coin2]:= ((coin_app phi psi (mf phi a) (gather K)).1 coin).
	split; last by apply ih.
	by apply/ ((ismod _ a _).2 _ _ _ coin1) => //; exists Fphi.
by apply /Lprop; [rewrite ((cont_sing Fcont) phi Fphi Fphi') | apply (gprop L) | ].
Qed.

Lemma comp_cont Q'' A'' (F: B ->> B') (G: B' ->> (Q'' -> A'')):
	F \is_continuous -> G \is_continuous -> G o F \is_continuous.
Proof.
exact: cont_comp.
Qed.

Lemma cnst_cont (Fphi: B'):
	(fun (phi: B) (Fphi': B') => forall q, Fphi' q = Fphi q) \is_continuous.
Proof.
by move => phi phifd q; exists nil; split => // Fphi' ->/= psi _ Fpsi ->.
Qed.
End CONTINUITY_LEMMAS.
Notation "mf '\is_modulus_of' F" := (is_mod F mf) (at level 2).
