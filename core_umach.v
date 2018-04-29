(* This file contains the definition of a universal machine and the proof that the machine
is actually universal. The universal machine is a machine of type two and it should work
for any continuous function from B -> B. Here, B is usually the Baire space i.e. the set
of all mappings from strings to strings. However, since I don't want to rely on a
handwritten type of strings I use more generaly a space of the form Q -> A for some types
Q and A as substitute for B. The assumptions needed about Q and A are that they are
countable and that A is inhabited. *)
From mathcomp Require Import all_ssreflect.
Require Import core_mf core_bs core_cont core_inseg core_omach core_count.
Require Import ClassicalChoice Psatz FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope coq_nat_scope.
Section UNIVERSAL_MACHINE.

(* Q: Questions, A: Answers *)
Context (Q Q': Type) (A A' : Type).
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
	(psi: list (Q * A) * Q' -> Q + A')
	(n: nat)
	(phi: Q -> A)
	(q' : Q') :=
match U_rec n psi phi q' with
	| inl a' => Some a'
	| inr L => None
end.

Lemma U_mon psi:
	(U psi) \is_monotone_oracle_machine.
Proof.
move => /= n m phi q' a'; rewrite /pickle /=.
elim: m => [| m ih] ineq eq; first by replace 0 with n by lia.
case: ((PeanoNat.Nat.le_succ_r n m).1 ineq) => ass.
	have eq' := (ih ass eq).
	case E: (U_rec m psi phi q') => [b|k]; last by rewrite /U E in eq'.
	by rewrite /U_rec in E; rewrite -eq' /U /U_rec E.
by case E: (U_rec m.+1 psi phi q') => [b|k]; rewrite -eq ass /U E.
Qed.

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
apply icf_F2MF_tight.
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
rewrite (icf_F2MF_tight psi (L2MF (flst L))).
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
have eq' := (coin_lstn psi phi (q::L)).1 coin q' listin2.
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
exists (fun L q => listf (q, L)) => L.
rewrite (icf_F2MF_tight (fun q => listf (q, L)) (L2MF L)) => q [a inlist].
rewrite /F2MF.
split=> [|b v]; first by exists (listf (q,L)).
rewrite -v.
by apply: listfprop (_, _) _ inlist.
Qed.

End FLST.

Section MINIMAL_MODULI.
Context (F: B ->> B').
Definition listfprop listf :=
	listf \is_choice_for (fun L phi => phi \from_dom F /\ phi \is_choice_for (L2MF L)).

Context (cnt: nat -> Q).
Notation init_seg := (in_seg cnt).

Lemma phi'prop listf phi n:
	listfprop listf -> phi \from_dom F ->
	(listf (flst phi (init_seg n))) \from_dom F
	/\
	(listf (flst phi (init_seg n))) \is_choice_for (L2MF (flst phi (init_seg n))).
Proof.
move => listfprop phifd.
have prop: phi \from_dom F/\ phi \is_choice_for (L2MF (flst phi (init_seg n))).
	by split; last exact: icf_flst.
by apply: (listfprop (flst phi (init_seg n)) phi).
Qed.

Context (sec: Q -> nat).

Notation size := (max_elt sec).

Definition is_min_mod mf :=
	(fun phi q' => init_seg (mf phi q')) \is_modulus_of F
	/\
	forall phi q' K, phi \from_dom F -> mf_mod F (phi, q') K -> mf phi q' <= size K.

Context (ims: sec \is_minimal_section_of cnt).

Lemma exists_minmod: cnt \is_surjective_function -> F \is_continuous ->
	exists mf, is_min_mod mf.
Proof.
move => sur cont.
pose P phiq n := mf_mod F phiq (init_seg n).
have Pdom: forall phi, phi \from_dom F -> forall q', (phi, q') \from_dom P.
	move => phi fd q'.
	move : (cont phi q' fd) => [] L Lprop.
	exists (size L) => Fphi FphiFphi.
	apply: cert_mon; first exact: inseg_melt.
	by apply/ Lprop; first by apply FphiFphi.
pose R phiq n := P phiq n /\ (forall K, P phiq (size K) ->  n <= size K).
have Rdom: forall phi, phi \from_dom F -> forall q', (phi, q') \from_dom R.
	move => phi fd q'.
  have [n [p nprop]] := well_order_nat (Pdom phi fd q').
  by exists n; split => // K p'; apply/leP/nprop.
have [mf mfprop] := exists_choice R 0.
exists (fun phi q' => mf (phi, q')).
split => phi q' X.
	by move: (Rdom phi X q') => [] n Rn; apply: (mfprop (phi, q') n Rn).1.
move => fd Xprop.
move: (Rdom phi fd q') => [] n Rn.
apply: (mfprop (phi, q') n Rn).2=> Fphi FphiFphi.
apply/ cert_mon; first exact: inseg_melt.
by apply Xprop.
Qed.

Lemma minmod_ineq mf listf phi:
	listfprop listf ->	is_min_mod mf -> phi \from_dom F
		-> forall q' m, mf phi q' <= m -> mf (listf (flst phi (init_seg m))) q' <= m.
Proof.
move => listfprop [] mod min phifd q' m ineq.
pose L := flst phi (init_seg m).
pose phi' := listf L.
move: (phi'prop m listfprop phifd) => phi'prop.
rewrite -/L -/phi'.
have coin: phi' \and phi \coincide_on (init_seg m).
	by apply icf_flst_coin; apply: phi'prop.2.
move: phifd => [] Fphi FphiFphi.
have ineq': size (init_seg m) <= m by exact/leP/(melt_inseg ims).
suffices: mf phi' q' <= size (init_seg m) by lia.
apply/ min; first by apply: phi'prop.1.
move => Fphi' /= Fphi'Fphi'.
suffices eq: (Fphi q' = Fphi' q').
	rewrite -eq.
	apply/ cert_cons; first by apply coin_sym; apply coin.
	apply/ cert_mon; first by apply inseg_mon; apply/leP/ineq.
	by apply /mod; first by exists Fphi.
apply /mod; [ by exists Fphi; apply FphiFphi | done | | apply Fphi'Fphi' ].
by apply coin_sym; apply/ coin_mon; first by apply inseg_mon; apply/leP/ineq.
Qed.

End MINIMAL_MODULI.

Context (cnt : nat -> Q) (F: B ->> B').
Notation init_seg := (in_seg cnt).

Lemma listsf (a : A) :
	exists listf, listf \is_choice_for (fun L phi => phi \from_dom F /\ phi \is_choice_for (L2MF L)).
Proof. exact: exists_choice. Qed.

Definition psiF mf listf (Ff: B -> B') (L: seq (Q * A) * Q') :=
	if (mf (listf L.1) L.2 <= length L.1)%N
	then
		(inr (Ff (listf L.1) L.2))
	else
		(inl (cnt (length L.1))).

Lemma psiFprop sec mf listf Ff phi q':
	is_min_sec cnt sec ->
	is_min_mod F cnt sec mf ->
	listfprop F listf ->
	phi \from_dom F ->
	forall n,
		(exists m,
		mf (listf (flst phi (init_seg m))) q' <= m
		/\
		U_rec n (psiF mf listf Ff) phi q' = inl (Ff (listf (flst phi (init_seg m))) q'))
	\/
	forall m, m <= n -> 
	U_rec m (psiF mf listf Ff) phi q' = inr (flst phi (init_seg (S m))).
Proof.
move => ims imm listfprop phifd.
pose phin m := listf (flst phi (init_seg m)).
have phinfd: forall m, (phin m) \from_dom F.
	by move => m; apply: (phi'prop cnt m listfprop phifd).1.

elim => [ | n ih].
	rewrite /U_rec/U_step/psiF/=.
	case E: (mf (listf [::]) q' <= 0)%N; last first.
		right => m ineq.
		have eq: m = 0 by lia.
		by rewrite eq /= E.
	left; exists 0; split => //.
	replace 0 with (max_elt sec nil) by trivial.
	apply: imm.2; replace (max_elt sec nil) with 0 by trivial; first by apply phinfd.
	move: (imm.1 (phin 0) q' (phinfd 0)).
	apply/ mod_mon.
	replace nil with (init_seg 0) by trivial; apply/ inseg_mon; rewrite / phin.
	by replace (flst phi (init_seg 0)) with (nil: seq (Q * A)) by trivial.
case: ih => [[] m [] ineq eq | eq].
	by rewrite /U_rec; left; exists m; split; [apply ineq | rewrite /U_rec in eq; rewrite /U_rec eq].
case E: (mf (listf (flst phi (init_seg n.+1), q').1) (flst phi (init_seg n.+1), q').2 <= n.+1)%N.
	left; exists (n.+1);rewrite /U_rec in eq;rewrite /U_rec eq =>//; rewrite /U_step/psiF length_flst_in_seg.
	by split; [ apply /leP| rewrite E].
right => m ineq.
case: ((PeanoNat.Nat.le_succ_r m n).1 ineq) => le; first by rewrite -eq.
have eq': U_rec n (psiF mf listf Ff) phi q' = inr (flst phi (init_seg n.+1)).
	by apply eq.
by rewrite /U_rec in eq'; rewrite /U_rec le eq'/U_step/psiF length_flst_in_seg E.
Qed.

Lemma U_is_universal (somea: A) (somephi : B') (sur: cnt \is_surjective_function) (Fcont : F \is_continuous) :
  exists psiF, (U psiF) \ocomputes F.
Proof.
have [Ff Fprop] := (exists_choice F somephi).
have [sec isminsec] := minimal_section sur.
have [mf [mprop minmod]] := exists_minmod isminsec sur Fcont.
have [listf listfprop] := listsf somea.
set psi_F := psiF mf listf Ff.

exists psi_F => phi phifd.

pose phin m := listf (flst phi (init_seg m)).
have phinprop m:= (phi'prop cnt m listfprop phifd).
have coin: forall m, (phin m) \and phi \coincide_on (init_seg m).
	by move => m; apply icf_flst_coin; apply: (phinprop m).2.
pose phi' q' := phin (mf phi q').

have Ffprop q': forall m, mf (phin m) q' <= m -> Ff (phin m) q' = Ff phi q'.
	move => m ineq.
	move: phifd (phinprop m).1 => [] Fphi FphiFphi [] Fphin FphinFphin.
	apply/ mprop => /=; [ exists Fphin | apply/ Fprop; apply FphinFphin | | apply/Fprop; apply FphiFphi ] => //.
	by apply/coin_mon; [ apply/inseg_mon | apply coin]; apply /leP.

have U_step_prop q': U_step psi_F phi q' (flst phi (init_seg (mf phi q'))) = inl (Ff phi q').
	rewrite /U_step/psi_F/psiF/=length_flst_in_seg.
	case E: (mf (listf (flst phi (init_seg (mf phi q')))) q' <= mf phi q')%N.
		by rewrite (Ffprop q' (mf phi q')); last by apply: (@minmod_ineq F cnt sec isminsec mf listf phi listfprop).
	suffices: (mf (listf (flst phi (init_seg (mf phi q')))) q' <= mf phi q')%N by rewrite E.
	by apply /leP; apply/ (@minmod_ineq F cnt sec isminsec mf listf phi listfprop).

have U_stops q': U psi_F (mf phi q') phi q' = some (Ff phi q').
	rewrite /U.
	case: (@psiFprop sec mf listf Ff phi q' isminsec _ listfprop phifd (mf phi q'))=> [ | [] m []ineq eq | eq].
			by split.
		by rewrite eq; congr some; rewrite (Ffprop q' m).
	case: (PeanoNat.Nat.zero_or_succ (mf phi q')) => [null | [] m sm].
		have eq': flst phi (init_seg (mf phi q')) = nil by rewrite null.
		by rewrite null /= -eq' U_step_prop.
	have ineq: m <= mf phi q' by lia.
	specialize (eq m ineq).
	by rewrite sm /= eq -sm U_step_prop.

move: phifd => [] Fphi FphiFphi.
have eq' q': U psi_F (mf phi q') phi q' = Some (Fphi q').
	rewrite U_stops.
	congr Some.
	by apply: mprop (FphiFphi); [ exists Fphi | apply: Fprop; apply FphiFphi | apply/ (coin_ref _ phi)].
split => [|Mphi MphiMphi]; first by exists Fphi => q'; exists (mf phi q'); rewrite eq'.
replace Mphi with Fphi => //.
apply: functional_extensionality => q'.
apply: Some_inj.
have [n eq] := MphiMphi q'.
case: (PeanoNat.Nat.le_ge_cases n (mf phi q')) => ineq.
	by rewrite -(U_mon ineq eq) eq'.
by rewrite -(U_mon ineq (eq' q')) eq.
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
Notation L2MF L := (fun q a => List.In (q, a) L).