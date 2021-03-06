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
move => /= n m phi q' a'; elim: m => [| m].
	by intros; have /eqP <-: n == 0 by rewrite -leqn0.
rewrite /pickle/= [_ <= S m]leq_eqVlt=> ih; case/orP => [/eqP ass | ass eq].
	by case E: (U_rec m.+1 psi phi q') ih => [b|k]// _ <-; rewrite ass.
have:= (ih ass eq); rewrite /U; case E: (U_rec m psi phi q') => //.
by rewrite /U_rec in E; rewrite /U_rec E => <-.
Qed.

Lemma U_rec_step n psi phi q':
	U_rec n.+1 psi phi q' = match U_rec n psi phi q' with
	  | inl a' => inl a'
		| inr L => U_step psi phi q' L
	end.
Proof. done. Qed.

Lemma U_rec_length n psi phi q' L:
	(U_rec n psi phi q') = inr L -> length L = n.+1.
Proof.
elim: n L; first by move => L; rewrite /U_rec/U_step; case: (psi (nil, q')) => [q [<-]|].
move => n ih L; rewrite U_rec_step.
case E: (U_rec n psi phi q') => [ | K] => //; rewrite /U_step.
by case: (psi (K, q')) => // q [<-] /=; rewrite ih.
Qed.

(* List to multivalued function *)
Notation L2MF L := (fun q a => List.In (q, a) L).

Section FLST.
Context (phi: B).
Definition flst L:= zip L (map phi L).

Lemma flst_cons_elts qa L:
	List.In qa (flst L) -> phi (qa.1) = qa.2.
Proof.
by case: qa => q a; elim: L => // p L ih [] // [<-].
Qed.

Lemma lstn_flst q L:
	(List.In q L -> List.In (q, phi q) (flst L)).
Proof.
by elim: L => //= q' L ih [H|H]; [left; rewrite H | right; apply: ih].
Qed.

Lemma flst_lstn qa L:
	List.In qa (flst L) -> List.In qa.1 L.
Proof.
by case: qa => q a; elim: L => //= p L ih []; [case; left | right; apply: ih].
Qed.

Lemma icf_flst L:
	phi \is_choice_for (L2MF (flst L)).
Proof.
apply icf_F2MF_tight => q [a listin].
split => [ |a' <-]; first by exists a; apply: flst_cons_elts listin.
by apply /lstn_flst/(flst_lstn listin).
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
rewrite coin_lstn; split => [icf q lstn | prp q a /flst_lstn lstn].
	by rewrite (@flst_cons_elts (q, psi q) L); last by apply/icf/lstn_flst.
by rewrite prp; first apply /lstn_flst.
Qed.

Lemma icf_flst_coin psi L:
	psi \is_choice_for (L2MF(flst L)) <-> psi \and phi \coincide_on L.
Proof. exact: coin_icf_flst. Qed.

Lemma length_flst_in_seg cnt n:
	length (flst (in_seg cnt n)) = n.
Proof. by elim: n => // n ih; rewrite -{2}ih. Qed.

Lemma extend_list (a: A):
	exists listf, forall (L: list (Q * A)), (listf L) \is_choice_for (L2MF L).
Proof.
pose R (L : list(Q * A)) (phi: Q -> A) := phi \is_choice_for (L2MF L).
by have /choice Rtot : R \is_total by move => L; exact: exists_choice (L2MF L) a.
Qed.
End FLST.

Section MINIMAL_MODULI.
Context (F: B ->> B').

Definition listfprop listf :=
	listf \is_choice_for (fun L phi => phi \from_dom F /\ phi \is_choice_for (L2MF L)).

Lemma exists_lstf (a : A) :
	exists listf, listfprop listf.
Proof. exact: exists_choice. Qed.

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
	move => phi fd q'; have [L [/=_ Lprop]]:= (cont phi fd q').
	exists (size L); split => // Fphi FphiFphi.
	apply: cert_mon; first exact: inseg_melt.
	by apply/ Lprop; first by apply FphiFphi.
pose R phiq n := P phiq n /\ (forall K, P phiq (size K) ->  n <= size K).
have Rdom: forall phi, phi \from_dom F -> forall q', (phi, q') \from_dom R.
	move => phi fd q'.
  have [n [p nprop]] := well_order_nat (Pdom phi fd q').
  by exists n; split => // K p'; apply/nprop.
have [mf mfprop] := exists_choice R 0.
exists (fun phi q' => mf (phi, q')).
split => phi q' X.
	by have [n Rn]:= (Rdom phi X q'); apply: (mfprop (phi, q') n Rn).1.
move => fd Xprop; have [n Rn]:= (Rdom phi fd q').
apply: (mfprop (phi, q') n Rn).2; split => // Fphi FphiFphi.
by apply/ cert_mon; [apply: inseg_melt | apply Xprop].
Qed.

Definition compat mf listf:= forall phi, phi \from_dom F ->
	forall (q': Q') m, mf phi q' <= m -> mf (listf (flst phi (init_seg m))) q' <= m.

Lemma minmod_compat mf listf:
	listfprop listf -> is_min_mod mf -> compat mf listf.
Proof.
move => listfprop [mod min] phi phifd q' m ineq.
have [/=_ mod'] := mod phi q' phifd.
pose L := flst phi (init_seg m).
pose phi' := listf L.
have [phi'fd icf]:= (phi'prop m listfprop phifd).
rewrite -/L -/phi' in phi'fd icf.
have coin: phi \and phi' \coincide_on (init_seg m)
	by apply/coin_sym/ icf_flst_coin/icf.
move: phifd => [Fphi FphiFphi].
have ineq': size (init_seg m) <= m by exact/(melt_inseg ims).
suffices ineq'': mf phi' q' <= size (init_seg m) by apply /(leq_trans ineq'').
apply/ min => //; split => // Fphi' /= Fphi'Fphi'.
suffices <-: (Fphi q' = Fphi' q').
	by apply/(cert_cons coin)/cert_mon; [apply/inseg_mon/ineq | apply /mod'].
apply /mod' => //; last apply Fphi'Fphi'.
by apply /coin_mon; [apply /inseg_mon/ineq | apply /coin ].
Qed.

End MINIMAL_MODULI.


Section PSIF.
Context (cnt: nat -> Q).
Notation init_seg := (in_seg cnt).
Notation "mf '\is_modulus_for' F" :=
	((fun phi q' => init_seg (mf phi q')) \is_modulus_of F) (at level 2).
Context (F: B ->> B') (mf: B -> Q' -> nat) (listf: seq (Q * A) -> B) (Ff: B -> B').
Notation L phi m:= (flst phi (init_seg m)).

Definition psiF (L: seq (Q * A) * Q') :=
	if (mf (listf L.1) L.2 <= length L.1)%N
	then
		(inr (Ff (listf L.1) L.2))
	else
		(inl (cnt (length L.1))).

Lemma psiFprop phi q':
	forall n,
		(exists m,
		mf (listf (flst phi (init_seg m))) q' <= m
		/\
		U_rec n psiF phi q' = inl (Ff (listf (flst phi (init_seg m))) q'))
	\/
	forall m, m <= n ->
	U_rec m psiF phi q' = inr (flst phi (init_seg (S m))).
Proof.
pose phin m := listf (L phi m).
elim => [ | n ih].
	rewrite /U_rec/U_step/psiF/=.
	case E: (mf (listf [::]) q' <= 0); first by left; exists 0; split.
	by right => m ineq; have /eqP ->: m == 0; [rewrite -leqn0 | rewrite E].
case: ih => [[] m [] ineq | eq].
	by rewrite /U_rec; left; exists m; split; [apply ineq | rewrite /U_rec b].
case E: (mf (listf (flst phi (init_seg n.+1), q').1) (flst phi (init_seg n.+1), q').2 <= n.+1).
	left; exists (n.+1);rewrite /U_rec in eq;rewrite /U_rec eq =>//.
	by rewrite /U_step/psiF length_flst_in_seg; split; last rewrite E.
right => m; rewrite  leq_eqVlt; case/orP => [/eqP nm | le]; last by rewrite -eq.
have eq': U_rec n psiF phi q' = inr (flst phi (init_seg n.+1)) by apply eq.
by rewrite /U_rec in eq'; rewrite /U_rec nm eq'/U_step/psiF length_flst_in_seg E.
Qed.

Definition Ff_mod phi q' := forall m, mf (listf (L phi m)) q' <= m -> Ff (listf (L phi m)) q' = Ff phi q'.

Lemma Ffprop
	(icf: Ff \is_choice_for F)
	(mod: mf \is_modulus_for F)
	(lstprp: listfprop F listf):
		forall phi q', phi \from_dom F -> Ff_mod phi q'.
Proof.
move => phi q' phifd m.
have phinprop:= (phi'prop cnt m lstprp phifd).
have coin: (listf (L phi m)) \and phi \coincide_on (init_seg m) by apply/icf_flst_coin/(phinprop).2.
move: mod (mod (listf (L phi m)) q' (phinprop).1) => _ [/=_ mprop] ineq.
move: phifd (phinprop).1 => [] Fphi FphiFphi [] Fphin FphinFphin.
apply/mprop; [ apply/ (icf _ Fphin) | | apply/(icf _ Fphi) ] => //.
by apply/coin_mon; [apply/inseg_mon | apply coin].
Qed.

Lemma U_step_compat phi q' (cmpt: compat F cnt mf listf):
	phi \from_dom F -> Ff_mod phi q' -> U_step psiF phi q' (L phi (mf phi q')) = inl (Ff phi q').
Proof.
move => phifd Ffprop.
rewrite /U_step/psiF/=length_flst_in_seg; case: ifP => [|/negP eq].
	by rewrite Ffprop; last by apply/cmpt.
by exfalso; apply eq; apply/cmpt.
Qed.

Lemma U_psiF_cmpt_F
	(sur: cnt \is_surjective_function)
	(icf: Ff \is_choice_for F)
	(mod: (fun phi q' => init_seg (mf phi q')) \is_modulus_of F)
	(lstprp: listfprop F listf)
	(cmpt: compat F cnt mf listf):
		(U psiF) \ocomputes F.
Proof.
move => phi phifd.
pose phin m := listf (L phi m).
have phinprop m:= (phi'prop cnt m lstprp phifd).
have coin m: (phin m) \and phi \coincide_on (init_seg m) by apply/icf_flst_coin/(phinprop m).2.
pose phi' q' := phin (mf phi q').

have U_stops q': U psiF (mf phi q') phi q' = some (Ff phi q').
	rewrite /U.
	case: (psiFprop phi q'(mf phi q'))=> [ [] m []ineq eq | eq].
		by rewrite eq; congr some; rewrite (Ffprop).
	case E: (mf phi q') => [ | m].
		have eq': flst phi (init_seg (mf phi q')) = nil by rewrite E.
		by rewrite /= -eq' U_step_compat => //; apply/ Ffprop.
	have /eq eqn: m <= mf phi q' by rewrite E leqnSn.
	by rewrite /= eqn -E U_step_compat => //; apply/ Ffprop.

have [Fphi FphiFphi]:= phifd.
have eq' q': U psiF (mf phi q') phi q' = Some (Fphi q').
	rewrite U_stops; congr Some.
	by apply: (mod _ _ phifd).2; [ apply/icf/FphiFphi | apply/ coin_ref | ].
split => [|Mphi MphiMphi]; first by exists Fphi => q'; exists (mf phi q'); rewrite eq'.
have ->: Mphi = Fphi => //.
apply: functional_extensionality => q'; apply Some_inj.
have [n eq] := MphiMphi q'.
case/orP: (leq_total n (mf phi q')) => ineq.
	by rewrite -(U_mon ineq eq).
by rewrite -(U_mon ineq (eq' q')).
Qed.
End PSIF.

Lemma U_universal (someq: Q) (somea : A) (somephi': B') (count: Q \is_countable):
	forall F, F \is_continuous -> exists psiF, (U psiF) \ocomputes F.
Proof.
have [ | cnt sur]:= (count_sur Q).2.
	by split; [apply (inhabits someq) | apply count].
move => F Fcont.
have [Ff Fprop] := exists_choice F somephi'.
have [sec isminsec] := minimal_section sur.
have [mf [mprop minmod]] := exists_minmod isminsec sur Fcont.
have [listf listfprop] := exists_lstf F somea.
exists (psiF cnt mf listf Ff).
apply/U_psiF_cmpt_F => //.
exact: (minmod_compat isminsec).
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