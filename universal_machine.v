(* This file contains the definition of a universal machine and the proof that the machine
is actually universal. The universal machine is a machine of type two and it should work
for any continuous function from B -> B. Here, B is usually the Baire space i.e. the set
of all mappings from strings to strings. However, since I don't want to rely on a
handwritten type of strings I use more generaly a space of the form Q -> A for some types
Q and A as substitute for B. The assumptions needed about Q and A are that they are
countable and that A is inhabited. *)
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions continuity initial_segments machines.
Require Import ClassicalChoice Psatz FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section UNIVERSAL_MACHINE.

(* Q: Questions, A: Answers *)
Context (Q A Q' A' : Type).
(* B: Baire space *)
Notation B := (Q -> A).
Notation B' := (Q' -> A').

Definition U_step (psi : list (Q * A) * Q' -> Q + A') phi q' L :=
match psi (L, q') with
  | inr a' => inl a'
  | inl q => inr ((q, phi q) :: L)
end.

Fixpoint U_rec n (psi: list (Q * A) * Q' -> Q + A') phi q' :=
match n with
	|	0 => U_step psi phi q' nil
	|	S n' => match U_rec n' psi phi q' with
	  | inl a' => inl a'
		| inr L => U_step psi phi q' L
	end
end.

(* This is the definition of the universal machine: *)
Definition U
	(n: nat)
	(psi: list (Q * A) * Q' -> Q + A')
	(phi: Q -> A)
	(q' : Q') :=
match U_rec n psi phi q' with
	| inl a' => Some a'
	| inr L => None
end.

(* List to multi function *)
Notation L2MF L := (fun q a => List.In (q, a) L).

Section FLST.
Context (phi: B).
Definition flst L:= zip L (map phi L).

Lemma flst_cons_elts qa L:
	List.In qa (flst L) -> phi (qa.1) = qa.2.
Proof.
case: qa => /= eq1 eq2.
by elim: L => // q L ih [] // [<-].
Qed.

Lemma list_in_to_flst_in q L:
	(List.In q L -> List.In (q, phi q) (flst L)).
Proof.
elim: L => //= q' L ih [H|H]; first by left; rewrite H.
by right; apply: ih.
Qed.

Lemma flst_in_to_list_in qa L:
	List.In qa (flst L) -> List.In qa.1 L.
Proof.
case: qa => eq1 eq2 /=.
elim: L => //= a L ih []; first by case => eq _; left.
by move => stuff; right; apply: ih.
Qed.

Lemma icf_flst L:
	phi \is_choice_for (L2MF (flst L)).
Proof.
move => q [] a listin.
split=> [|a' phiqa'].
	exists a; apply: flst_cons_elts listin.
by rewrite -phiqa'; apply: list_in_to_flst_in (flst_in_to_list_in listin).
Qed.

Lemma flst_sing L : (L2MF (flst L)) \is_single_valued.
Proof.
by move=> s t1 t2 /flst_cons_elts /= <- /flst_cons_elts /= <-.
Qed.

Lemma coin_icf_flst psi L:
	psi \is_choice_for (L2MF (flst L))
	<->
	psi \and phi \coincide_on L.
Proof.
elim: L => [|q L [ih hi]]; first by split => // _ /= q [] _ [].
split => [icf|/= coin q' [a inlist]].
  split.
    have [|[a psiqa] prop] := icf q.
      by exists (phi q); apply: (list_in_to_flst_in); left.
    by rewrite psiqa (flst_cons_elts  (prop a psiqa)).
	apply ih => q' [] a inlist.
  have /= eq := flst_cons_elts inlist.
  have [|[a' psiq'a'] prop] := icf q'.
    by exists a; right.
  have /= [[] eq1 eq2|/flst_cons_elts /= phiq'a'] := prop a' psiq'a'.
    split=> [|a'' psiq'a'']; first by exists a'.
    by rewrite -psiq'a'' psiq'a' -eq2 eq1 eq.
  split=> [|a'' psiq'a'']; first by by exists a'.
  by rewrite -psiq'a'' psiq'a' -phiq'a' eq.
split => [|a' psiq'a']; first by exists (psi q').
have /= [eq1|listin] /= := @flst_in_to_list_in _ (q :: L) (inlist).
  by left; rewrite -psiq'a' -eq1 coin.1.
right.
have listin2 : List.In q' (q::L) by right.
have eq' := (coin_and_list_in psi phi (q::L)).1 coin q' listin2.
by rewrite - psiq'a' eq'; apply: (list_in_to_flst_in).
Qed.

Lemma icf_flst_coin psi L:
	psi \is_choice_for (L2MF(flst L)) <-> psi \and phi \coincide_on L.
Proof. exact: coin_icf_flst. Qed.

Lemma length_flst_in_seg cnt n:
	length (flst (in_seg cnt n)) = n.
Proof. by elim: n => // n ih; rewrite -{2}ih. Qed.

Lemma extend_list:
	A -> exists listf, forall (L: list (Q * A)), (listf L) \is_choice_for (L2MF L).
Proof.
move => i.
pose R (L : Q * list(Q * A)) (a: A) := 
  forall b, (L2MF L.2) L.1 b -> (L2MF L.2) L.1 a.
have cond L : exists b, R L b.
  case: L => q L.
  have [[a inlist]|H] :=  classic (exists a, List.In (q,a) L).
  	by exists a.
  exists i => a inList.
  by case: H; exists a.
have [listf listfprop]  := choice R cond.
exists (fun L q => listf (q, L)) => L q [a inlist].
rewrite /F2MF.
split=> [|b v]; first by exists (listf (q,L)).
rewrite -v.
by apply: listfprop (_, _) _ inlist.
Qed.
End FLST.

Section MINIMAL_MODULI.
Context (cnt: nat -> Q) (sec: Q -> nat) (F: B ->> B').
Notation init_seg := (in_seg cnt).
Notation size := (size sec).

Definition is_min_mod mf :=
	(fun phi q' => init_seg (mf phi q')) \is_modulus_of F
	/\
	forall phi q' K, determines F K phi q' -> mf phi q' <= size K.

Lemma minimal_mod_function:
  F \is_continuous -> sec \is_minimal_section_of cnt -> exists mf, is_min_mod mf.
Proof.
move => cont ims.
pose P n phiq := determines F (init_seg n) phiq.1 phiq.2.
pose R phiq n := P n phiq /\ (forall K, P (size K) phiq ->  n <= size K).
have cond phiq : exists n, R phiq n.
	have cond: exists n : nat, P n phiq.
		have [L Lprop] := cont phiq.1 phiq.2.
		exists (size L).
		move => psi coin.
		apply/ Lprop.
		apply/ (coin_and_list_in phiq.1 psi L) => q listin.
		apply/ (coin_and_list_in phiq.1 psi (init_seg (size L))).1 => //.
		apply: (inseg q ims (size L)).2.
		by apply: listin_sec_size.
  have [n [p nprop]] := well_order_nat cond.
  exists n.
  split => // K p'. by apply: nprop.
have [mf mfprop] := choice R cond.
rewrite {cond}/R in mfprop.
exists (fun phi q' => mf (phi, q')).
split => phi q'; first by apply: (mfprop (phi, q')).1.
move => K det.
apply: (mfprop (phi, q')).2 => psi /= coin.
apply det.
apply/ (coin_and_list_in phi psi K) => q listin.
apply/ (coin_and_list_in phi psi (init_seg (size K))).1 => //.
apply/ (inseg q ims (size K)).
exact: listin_sec_size.
Qed.
End MINIMAL_MODULI.

(*This should at some point go into an appropriate section: *)

Definition is_count Q :=
	exists cnt: nat -> Q, cnt \is_surjective.
Notation "T 'is_countable'" := (is_count T) (at level 2).

Context (cnt : nat -> Q) (F: B ->> B').
Notation init_seg := (in_seg cnt).

Lemma listsf (a : A) :
	exists phi',
		forall L, ((exists phi, (exists psi, F phi psi) /\ phi \is_choice_for (L2MF L)) ->
			exists psi, F (phi' L) psi) /\ (phi' L) \is_choice_for (L2MF L).
Proof.
have [listf listfprop] := extend_list a.
pose R L psi := 
  ((exists phi, phi \from_dom F /\ phi \is_choice_for (L2MF L)) -> psi \from_dom F)
	/\ psi \is_choice_for (L2MF L).
have cond L : exists psi, R L psi.
  have [[psi [psifd psic]]|NE] := classic (exists phi, phi \from_dom F /\ phi \is_choice_for (L2MF L)).
    by exists psi.
  by exists (listf L).
have [phi' phi'prop] := choice R cond.
by exists phi'.
Qed.

Lemma U_mon n psi phi q' a:
	forall m, n <= m -> U n psi phi q' = some a -> U m psi phi q' = some a.
Proof.
elim.
	move => ineq.
	have n0: n = 0 by lia.
	by rewrite n0.
move => m ih ineq eq.
case: ((PeanoNat.Nat.le_succ_r n m).1 ineq) => ass.
	have eq' := (ih ass eq).
	case E: (U_rec m psi phi q') => [b|k].
		rewrite /U_rec in E.
		by rewrite -eq' /U /U_rec E.
	by rewrite /U E in eq'.
by case E: (U_rec m.+1 psi phi q') => [b|k]; rewrite -eq ass /U E.
Qed.

Lemma U_is_universal (None : A) (None' : A') (sur: cnt \is_surjective) (Fcont : F \is_continuous) :
  exists psiF, (fun n phi q' => U n psiF phi q') \type_two_computes F.
Proof.
pose R phi psi := (exists psi', F phi psi') -> F phi psi.
have cond phi : exists psi, R phi psi.
  have [[psi prop]|Nprop] := classic (exists psi' , F phi psi').
    by exists psi.
  by exists (fun a => None').
have [Ff Fprop] := choice R cond.
rewrite {cond}/R /= in Fprop.
have [sec isminsec] := minimal_section sur.
have [mf mprop] := minimal_mod_function Fcont isminsec.
have [phi' phi'prop] := listsf None.
set size := size sec.

have coin phi q' :
    (phi' (flst phi (init_seg (mf phi q')))) \and phi \coincide_on (init_seg (mf phi q')).
	apply/icf_flst_coin.
	by apply: (phi'prop (flst phi (init_seg (mf phi q')))).2.

have ineq phi q' n : (exists psi, F phi psi) -> mf phi q' <= n ->
	mf (phi' (flst phi (init_seg n))) q' <= mf phi q'.
  move=> [Fphi FphiFphi] ass.
  set K := mf (phi' _) _.
  have coin'': (phi' (flst phi (init_seg n))) \and phi \coincide_on (init_seg (mf phi q')).
    have coin'' := (coin_icf_flst phi (phi' (flst phi (init_seg n))) (init_seg n)).1
			(phi'prop (flst phi (init_seg n))).2.
		have elts := (coin_and_list_in (phi' (flst phi (init_seg n))) phi (init_seg n)).1 coin''.
		apply/coin_and_list_in=> q listin.
		apply: elts.
	  by apply: mon_inseg listin.
	have coin''':
		(phi' (flst phi (init_seg n))) \and (phi' (flst phi (init_seg (mf phi q')))) \coincide_on (init_seg (mf phi q')).
		apply: coin_trans coin'' _.
		have coin''' := (coin_icf_flst phi (phi' (flst phi (init_seg (mf phi q')))) (init_seg (mf phi q'))).1
			(phi'prop (flst phi (init_seg (mf phi q')))).2.
		by apply/coin_sym.
	suffices: K <= size (init_seg (mf phi q')).
		move: (size_inseg isminsec (mf phi q')) => ineq ineq'.
		by rewrite -/size in ineq; lia.
	apply: (mprop.2 (phi' (flst phi (init_seg n))) q' (init_seg (mf phi q'))) =>
		  psi coin' FphiL Fpsi FphiLFphiL FpsiFpsi.
  apply: etrans (_ :  Fphi q' = _); last first.
  	apply: (mprop.1 phi _ psi) => //.
    apply: coin_trans; first by apply/coin_sym/coin.
    apply: coin_trans coin'.
		by apply/coin_sym/coin'''.
	apply/esym/ (mprop.1 phi) => //.
    by apply/coin_sym/coin''.
  exact: FphiLFphiL.

pose psiF L :=
  if (mf (phi' L.1) L.2 <= length L.1)%N
  then
    (inr (Ff (phi' L.1) L.2))
  else
    (inl (cnt (length L.1))).

have U_step_prop phi q' n :
	phi \from_dom F -> mf phi q' <= n ->
	U_step psiF phi q' (flst phi (init_seg n)) = inl(Ff (phi' (flst phi (init_seg n))) q').
	move => phifd ass.
	rewrite /U_step/psiF/=.
	rewrite (length_flst_in_seg phi cnt n).
	have toeroe := ineq phi q' n phifd ass.
	case E: (mf (phi' (flst phi (init_seg n))) q' <= n)%N => //.
  case/idP: E.
  by apply /leP; lia.

have Ffprop n phi q':
	phi \from_dom F -> mf (phi' (flst phi (init_seg n))) q' <= n ->
			Ff (phi' (flst phi (init_seg n))) q' = Ff phi q'.
	move => phifd leq.
	pose m := mf (phi' (flst phi (init_seg n))) q'.
	apply: (mprop.1 (phi' (flst phi (init_seg n))) q' phi).
			apply/ coin_and_list_in => q listin.
	  	have coin' :=
    	  (icf_flst_coin phi (phi' (flst phi (init_seg n))) (init_seg n)).1
					(phi'prop (flst phi (init_seg n))).2.
    	apply : ((coin_and_list_in (phi' (flst phi (init_seg n))) phi (init_seg n)).1 coin').
    	apply/ (inseg q isminsec n).
    	suffices: sec q < mf (phi' (flst phi (init_seg n))) q' by lia.
    	by apply/ (inseg q isminsec).
 		apply Fprop.
		apply: (phi'prop (flst phi (init_seg n))).1.
		exists phi.
		split => //.
		apply/ (icf_flst_coin).
		by apply coin_ref.
	by apply Fprop.

have U_rec_prop n :
	forall phi q', (exists psi, F phi psi) ->
		U_rec n psiF phi q' = inl(Ff phi q')
		\/
		U_rec n psiF phi q' = inr(flst phi (init_seg (S n))).
  elim: n => [phi q' phifd|n ih phi q' phifd /=].
    rewrite /U_rec /U_step /psiF /=.
    case E : (mf (phi' [::]) q' <= 0)%N.
      left.
      congr inl.
      have Fphi1 : F (phi' [::]) (Ff (phi' [::])).
				apply: Fprop.
				apply: (phi'prop [::]).1.
				exists phi.
				by split => // q [] a [].
      have Fphi : F phi (Ff phi) by apply: Fprop.
			apply: (mprop.1) Fphi1 Fphi.
      move: ((icf_flst_coin phi (phi' nil) (nil)).1 (phi'prop (flst phi nil)).2) => coin'.
      have t : mf (phi' nil) q' <= 0
		    by apply /leP; rewrite E.
			have eq : mf (phi' nil) q' = 0 by lia.
			by rewrite eq.
    by right.
  have {ih}[eq|eq] := ih phi q' phifd.
    by rewrite eq /=; left.
	rewrite eq /= /U_step/psiF.
	rewrite (length_flst_in_seg phi cnt (S n)) /=.
	case E :  (mf (phi' (flst phi (cnt n :: init_seg n))) q' <= n.+1)%N.
		left.
		have leq: mf (phi' (flst phi (cnt n :: init_seg n))) q' <= n.+1 by apply /leP.
		by rewrite (Ffprop (S n) phi q' phifd leq).
 	by right.

have U_rec_prop' n :
	forall phi q', (exists psi, F phi psi) -> mf phi q' <= n ->
		U_rec n psiF phi q' = inl (Ff phi q').
	elim: n => [phi q' phifd leq /=|n ih phi q' phifd leq /=].
		rewrite (U_step_prop _ _ _ _ leq) //.
		have eq : mf phi q' = 0 by lia.
		have leq' := ineq phi q' 0 phifd leq.
		rewrite eq in leq'.
		by rewrite Ffprop.
	case: (U_rec_prop n phi q' phifd) => [->//|->/=].
	rewrite (U_step_prop _ _ _ _ leq) //.
	have leq' := ineq phi q' (S n) phifd leq.
	have leq'':mf (phi' (flst phi (init_seg n.+1))) q' <= S n by lia.
	by rewrite Ffprop.

exists psiF => phi [Fphi FphiFphi].
split=> [|Mphi MphiMphi].
	exists Fphi => q'.
	exists (mf phi q').
	rewrite /U.
	rewrite (U_rec_prop' (mf phi q') phi q')=>//;last first.
		by exists Fphi.
  congr Some.
	apply: mprop.1  (FphiFphi).
  	by apply/ (coin_ref phi).
  apply: Fprop.
  by exists Fphi.
replace Mphi with Fphi => //.
apply: functional_extensionality => q'.
apply: Some_inj.
have [n eq] := MphiMphi q'.
rewrite -eq /U.
have [|ass|ass] := U_rec_prop n phi q'.
		by exists Fphi.
	rewrite ass.
	congr Some.
	apply/ (mprop.1); last first.
			apply Fprop.
			by exists Fphi.
		by apply FphiFphi.
	by apply/(coin_ref phi).
by rewrite /U ass in eq.
Qed.

(* Lemma comp_cont:
  (exists psiF, (fun n phi q' => U n psiF phi q') \type_two_computes F) -> F \is_continuous.
Proof.
move => [] psiF comp phi q'.
case: (classic (phi \from_dom F)) => [] phifd.
move: (comp phi phifd) => [] [] psi ev prop.
move: (ev q') => [] n eq.
Admitted.
*)
End UNIVERSAL_MACHINE.
Notation "T '\is_countable'" := (is_count T) (at level 2).