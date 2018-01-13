(* This file provides a definition of continuity of functions between spaces of the form
Q -> A for some arbitrary types Q and A. It also proves some basic Lemmas about this notion.*)
Load functions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

(* Context Q A Q' A' (F: (Q-> A) ->> (Q'-> A')). *)

Fixpoint equal_on Q A (phi psi : Q -> A) L :=
  match L with
    | nil => True
    | cons s K => (phi s = psi s) /\ (equal_on phi psi K)
  end.
Notation "phi 'and' psi 'coincide_on' L" := (equal_on phi psi L) (at level 2).

Lemma coin_ref Q A (phi: Q -> A):
	forall L, phi and phi coincide_on L.
Proof.
	by elim.
Qed.

Lemma app_coincide Q A (L K: list Q) (phi psi: Q -> A):
	phi and psi coincide_on (L ++ K) <-> (phi and psi coincide_on L /\ phi and psi coincide_on K).
Proof.
split.
	move: L.
	elim.
		by replace (nil ++ K) with (K); split.
	move => a L ih.
	replace ((a :: L) ++ K) with ((a :: L)%SEQ ++ K)%list by trivial.
	rewrite -(List.app_comm_cons L K a).
	move => [ass1 ass2].
	split; try apply ih; try apply ass2.
	by split => //; apply ih; apply ass2.
move: L.
elim.
	move => [_ coin].
	by replace (nil ++ K) with (K).
move => a L ih [[ass1 ass2] ass3].
replace ((a :: L) ++ K) with ((a :: L)%SEQ ++ K)%list by trivial.
rewrite -(List.app_comm_cons L K a).
by split; try apply ih; try apply ass2.
Qed.

Definition is_cont (Q A Q' A' : Type) (F : (Q -> A) ->> (Q'-> A')) :=
  forall phi q', exists (L : list Q),
  	forall psi, phi and psi coincide_on L ->
  	 forall Fphi, F phi Fphi -> forall Fpsi, F psi Fpsi ->
  	 	Fphi q' = Fpsi q'.
Notation "F 'is_continuous'" := (is_cont F) (at level 2).

Require Import FunctionalExtensionality.

Lemma cont_to_sing Q A Q' A' (F: (Q-> A) ->> (Q'-> A')):
	F is_continuous -> F is_single_valued.
Proof.
move => cont phi Fpsi Fpsi' v1 v2.
apply functional_extensionality => a.
move: cont (cont phi a) => _ [L] cont.
have: (forall K, phi and phi coincide_on K) by elim.
move => equal.
by rewrite -((cont phi (equal L) Fpsi') v2).
Qed.

Definition is_mod Q A Q' A' (F:(Q -> A) ->> (Q' -> A')) mf :=
  forall phi q', forall (psi : Q -> A), phi and psi coincide_on (mf phi q') ->
  	forall Fphi : Q' -> A', F phi Fphi -> (forall Fpsi, F psi Fpsi -> Fphi q' = Fpsi q').
Notation "mf 'is_modulus_of' F" := (is_mod F mf) (at level 2).

Require Import Classical.

Lemma continuous_extension Q A Q' A' (F: (Q -> A) ->> (Q' -> A')) G:
	G extends F -> G is_continuous -> F is_single_valued -> F is_continuous.
Proof.
move => GeF Gcont Fsing phi q'.
move: (Gcont phi q') => [] L Lprop.
exists L => psi pep Fphi FphiFphi Fpsi FpsiFpsi.
move: GeF (@extension_of_single_valued (Q->A) (Q'->A') F G Fsing GeF) => _ GeF.
apply: (Lprop psi pep Fphi _ Fpsi _).
	by apply: (GeF phi Fphi).
by apply: (GeF psi Fpsi).
Qed.

Require Import ClassicalChoice.

Lemma exists_modulus Q A Q' A' (F: (Q-> A) ->> (Q'-> A')):
	F is_continuous -> exists mf, mf is_modulus_of F.
Proof.
move => cont.
set R:= fun phiq L => forall psi, phiq.1 and psi coincide_on L -> forall Fphi, F phiq.1 Fphi -> 
	(forall Fpsi, F psi Fpsi -> Fphi phiq.2 = Fpsi phiq.2).
have: forall phiq, exists L, R phiq L.
	move => [phi q'].
	move: (cont phi q') => [L] prop.
	exists L.
		move => psi H.
	 	by apply (prop psi H).
move => cond.
move: cond (choice R cond) => _ [mf] cond.
exists (fun phi q => mf (phi, q)).
move => phi q.
by apply (cond (phi, q)).
Qed.


Lemma continuous_composition
	Q A Q' A' (F: (Q-> A) ->> (Q'-> A'))
	Q'' A'' (G: (Q' -> A') ->> (Q'' -> A'')):
		F is_continuous -> G is_continuous -> G o F is_continuous.
Proof.
move => Fcont Gcont.
move => phi q''.
move: (exists_modulus Fcont) => [mf] ismod.
case (classic (exists Fphi, F phi Fphi)).
	move => [] Fphi FphiFphi.
	set gather := fix gather K := match K with
		| nil => nil
		| cons q' K' => app (mf phi q') (gather K')
	end.
	move: (Gcont Fphi q'') => [L] Lprop.
	exists (gather L).
	move => psi.
	case: (classic (exists Fpsi, F psi Fpsi)).
		move => [] Fpsi FpsiFpsi coin GFphi [] [] Fphi' [] FphiFphi' GFphi'GFphi cond'.
		have: Fphi and Fpsi coincide_on L.
			specialize (Lprop Fpsi).
			move: L Fphi FphiFphi Fpsi FpsiFpsi Lprop coin .
			elim=> //.
			move => a L ih Fphi FphiFphi Fpsi FpsiFpsi assump coin.
			move: coin ((app_coincide (mf phi a) (gather L) phi psi).1 coin) => _ [coin1 coin2].
			split.
				by apply: (ismod phi a psi) => //.
			apply ih => //.
			move => coin'.
			apply assump.
			split.
				by apply (ismod phi a psi).
			done.
		move => coin' GFpsi [] [] Fpsi' [] FpsiFpsi' GFpsi'GFpsi cond.
		apply (Lprop Fpsi) => //.
		rewrite ((cont_to_sing Fcont) phi Fphi Fphi') => //.
		rewrite ((cont_to_sing Fcont) psi Fpsi Fpsi') => //.
	move => false coin a b c [][]Fpsi [] FpsiFpsi .
	exfalso; apply false.
	by exists Fpsi.
move => false.
exists nil.
move => a b c [][] Fphi [] FphiFphi.
exfalso; apply false.
by exists Fphi.
Qed.