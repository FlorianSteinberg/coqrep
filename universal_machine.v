(* This file is supposed to contain the definition of a universal machine and the proof
that the machine is actually universal. The universal machine is a machine of type two
and it should work for any continuous function from B -> B. Usually B is the Baire space,
here, i.e. the set of all mappings from strings to strings. However, since I don't want
to rely on a handwritten type of strings as I attempted in the file "operators.v" I use
more generaly a space S -> T as substitute for B. *)
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions continuity initial_segments machines.
Require Import ClassicalChoice Psatz FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section UNIVERSAL_MACHINE.

Context (Q I Q' I' : Type).
(* Answer *)
Notation A := (option I).
Notation A' := (option I').
(* Baire space *)
Notation B := (Q -> I).
Notation B' := (Q' -> I').

Definition U_step (psi : list (Q * I) * Q' -> Q + I') phi q' L :=
match psi (L, q') with
  | inr a' => inl a'
  | inl q => inr ((q, phi q) :: L)
end.

Fixpoint U_rec n (psi: list (Q * I) * Q' -> Q + I') phi q' :=
match n with
	|	0 => U_step psi phi q' nil
	|	S n' => match U_rec n' psi phi q' with
	  | inl a' => inl a'
		| inr L => U_step psi phi q' L
	end
end.

(* This is what I want to prove to be a universal machine: *)
Definition U
	(n: nat)
	(psi: list (Q * I) * Q' -> Q + I')
	(phi: Q -> I)
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
	phi is_choice_for (L2MF (flst L)).
Proof.
move => q [] a listin.
split=> [|a' phiqa'].
	exists a; apply: flst_cons_elts listin.
by rewrite -phiqa'; apply: list_in_to_flst_in (flst_in_to_list_in listin).
Qed.

Lemma flst_sing L : (L2MF (flst L)) is_single_valued.
Proof.
by move=> s t1 t2 /flst_cons_elts /= <- /flst_cons_elts /= <-.
Qed.

Lemma coin_icf_flst psi L:
	psi is_choice_for (L2MF (flst L))
	<->
	psi and phi coincide_on L.
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
	psi is_choice_for (L2MF(flst L)) <-> psi and phi coincide_on L.
Proof. exact: coin_icf_flst. Qed.

Lemma length_flst_in_seg cnt n:
	length (flst (in_seg cnt n)) = n.
Proof. by elim: n => // n ih; rewrite -{2}ih. Qed.

End FLST.

Section MINIMAL_MODULI.
Context (cnt: nat -> Q) (sec: Q -> nat) (F: B ->> B').
Notation init_seg := (in_seg cnt).
Notation size := (size sec).

Definition is_min_mod mf :=
	mf is_modulus_of F /\ forall phi q' K, (forall psi, phi and psi coincide_on K
    -> forall Fphi, F phi Fphi -> forall Fpsi, F psi Fpsi -> Fphi q' = Fpsi q') ->
     exists m, m <= size K /\ mf phi q'= init_seg m.

Lemma minimal_mod_function:
  F is_continuous -> sec is_minimal_section_of cnt ->
  exists mf, is_min_mod mf.
Proof.
move => cont [] issec ismin.
pose P phiq L := forall psi, 
                    phiq.1 and psi coincide_on L -> 
                 forall Fphi, F phiq.1 Fphi -> 
                 forall Fpsi, F psi Fpsi -> Fphi phiq.2 = Fpsi phiq.2.
pose R phiq L := P phiq L /\
  	(forall K, P phiq K ->  exists m, m <= size K /\ L = init_seg m).
have cond phiq : exists L, R phiq L.
  have cond : exists n, exists L, P phiq L /\ size L = n.
    have [L Lprop] := cont phiq.1 phiq.2.
    by exists (size L); exists L.
  have [n [[L [Lprop Leqn]] nprop]] := well_order_nat cond.
  exists (in_seg cnt (size L)).
  split=> [psi /(list_size issec) coin|K Pfi].
    by apply: Lprop.
  rewrite -Leqn in nprop.
  exists (size L).
  split => //.
  have e : exists L : seq Q, P phiq L /\ size L = (size K) by exists K.
  by apply: nprop.
have [mf mfprop] := choice R cond.
rewrite {cond}/R in mfprop.
exists (fun phi q' => mf (phi, q')).
split => [phi q' psi|phi q' K mod].
  by have [/(_ psi) /=] := mfprop (phi, q').
have [_ /(_ K)] := mfprop (phi,q').
apply=> psi coin Fphi FphiFphi Fpsi FpsiFpsi.
by apply: (mod psi).
Qed.

End MINIMAL_MODULI.

(*This should at some point go into an appropriate section: *)
Lemma extend_list:
	I -> exists listf, forall (L: list (Q * I)), (listf L) is_choice_for (L2MF L).
Proof.
move => i.
pose R (L : Q * list(Q * I)) (a: I) := 
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

Context (cnt : nat -> Q).
Notation init_seg := (in_seg cnt).

Lemma length_in_seg n : length (init_seg n) = n.
Proof. by elim: n => // n ih; rewrite -{2}ih. Qed.

Context (F: B ->> B').

Lemma listsf (i : I) :
	exists phi',
		forall L, ((exists phi, phi from_dom F /\ phi is_choice_for (L2MF L)) ->
			(phi' L) from_dom F) /\ (phi' L) is_choice_for (L2MF L).
Proof.
have [listf listfprop] := extend_list i.
pose R L psi := 
  ((exists phi, phi from_dom F /\ phi is_choice_for (L2MF L)) -> psi from_dom F)
	/\ psi is_choice_for (L2MF L).
have cond L : exists psi, R L psi.
  have [[psi [psifd psic]]|NE] := 
     classic (exists phi, phi from_dom F /\ phi is_choice_for (L2MF L)).
    by exists psi.
  by exists (listf L).
have [phi' phi'prop] := choice R cond.
by exists phi'.
Qed.

Context (sec: Q -> nat) (isminsec: is_min_sec cnt sec).
Notation size := (size sec).

Lemma min_mod_in_seg mf:
	is_min_mod cnt sec F mf ->
	forall phi q', in_seg cnt (size (mf phi q')) = mf phi q'.
Proof.
move => mprop phi q'.
have [m [ineq eq']] := mprop.2 phi q' (mf phi q') (mprop.1 phi q').
have ineq' := size_in_seg isminsec m.
rewrite -eq' in ineq'.
rewrite -/size in ineq ineq'.
have eq'': (size (mf phi q')) = m by lia.
by rewrite eq'' eq'.
Qed.

Definition is_count Q :=
	exists cnt: nat -> Q, (F2MF cnt) is_surjective.
Notation "T 'is_countable'" := (is_count T) (at level 2).
Notation "B ~> B'" := (nat -> B -> Q'-> A') (at level 2).

Context (sur: (F2MF cnt) is_surjective).

Lemma mon_in_seg q n m:
	  n <= m -> List.In q (init_seg n) -> List.In q (init_seg m).
Proof.
elim: m => [l0|m ih ass].
  by rewrite (_ : n = 0) //; lia.
have [/ih H1 H2|<- //] := (PeanoNat.Nat.le_succ_r n m).1 ass.
by right; apply: H1.
Qed.

Lemma U_is_universal (None : I) (None' : I') (Fcont : F is_continuous) :
  exists psiF, (fun n phi q' => U n psiF phi q') computes F.
Proof.
pose R phi psi := (exists psi', F phi psi') -> F phi psi.
have cond phi : exists psi, R phi psi.
  have [[psi prop]|Nprop] := classic (exists psi' , F phi psi').
    by exists psi.
  by exists (fun a => None').
have [Ff Fprop] := choice R cond.
rewrite {cond}/R /= in Fprop.
have [mf mprop] := minimal_mod_function Fcont isminsec.
have [phi' phi'prop] := listsf None.
have coin phi q' :
    (phi' (flst phi (mf phi q'))) and phi coincide_on (mf phi q').
	apply/icf_flst_coin.
	by apply: (phi'prop (flst phi (mf phi q'))).2.
have ineq phi q' n : phi from_dom F -> size (mf phi q') <= n ->
  	size (mf (phi' (flst phi (init_seg n))) q') <= size (mf phi q').
  move=> [Fphi FphiFphi] ass.
  set K := mf (phi' _) _.
  have coin'': (phi' (flst phi (init_seg n))) and phi coincide_on (mf phi q').
    have coin'' := (coin_icf_flst phi (phi' (flst phi (init_seg n))) (init_seg n)).1
			(phi'prop (flst phi (init_seg n))).2.
		have elts := (coin_and_list_in (phi' (flst phi (init_seg n))) phi (init_seg n)).1 coin''.
		apply/coin_and_list_in=> q listin.
		apply: elts.
		rewrite -(min_mod_in_seg mprop phi q') in listin.
	  by apply: mon_in_seg listin.
	have coin''':
		(phi' (flst phi (init_seg n))) and (phi' (flst phi (mf phi q'))) coincide_on (mf phi q').
		apply: coin_trans coin'' _.
		have coin''' := (coin_icf_flst phi (phi' (flst phi (mf phi q'))) (mf phi q')).1
			(phi'prop (flst phi (mf phi q'))).2.
		by apply/coin_sym.
	suffices [m [leq eq]]: exists m : nat, m <= size (mf phi q') /\ K = in_seg cnt m.
		rewrite eq.
    have ineq := size_in_seg isminsec m.
		by lia.
	apply: mprop.2 =>
		  psi coin' FphiL FphiLFphiL Fpsi FpsiFpsi.
  apply: etrans (_ :  Fphi q' = _); last first.
  	apply: (mprop.1 phi _ psi) => //.
    apply: coin_trans; first by apply/coin_sym/coin.
    apply: coin_trans  coin'.
		by apply/coin_sym/coin'''.
	apply/esym/ (mprop.1 phi) => //.
    by apply/coin_sym/coin''.
  exact: FphiLFphiL.
pose psiF L :=
  if (size (mf (phi' L.1) L.2) <= length L.1)%N
  then
    (inr (Ff (phi' L.1) L.2))
  else
    (inl (cnt (length L.1))).

have length_size: forall phi q', size (mf phi q') = length (mf phi q').
	move => phi q'.
	rewrite -{2}(min_mod_in_seg mprop phi q').
	by rewrite length_in_seg.

have U_step_prop phi q' n :
	phi from_dom F -> size (mf phi q') <= n ->
	U_step psiF phi q' (flst phi (init_seg n)) = inl(Ff (phi' (flst phi (init_seg n))) q').
	move => phifd ass.
	rewrite /U_step/psiF/=.
	rewrite (length_flst_in_seg phi cnt n).
	have tada := size_in_seg isminsec n.
	have toeroe := ineq phi q' n phifd ass.
	case E: (size (mf (phi' (flst phi (init_seg n))) q') <= n)%N => //.
  case/idP: E.
  by apply /leP; lia.
	
have Ffprop n phi q':
	 phi from_dom F -> size (mf (phi' (flst phi (init_seg n))) q') <= n ->
			Ff (phi' (flst phi (init_seg n))) q' = Ff phi q'.
	move => phifd leq.
	pose m := size (mf (phi' (flst phi (init_seg n))) q').
	have eq := min_mod_in_seg mprop (phi' (flst phi (init_seg n))) q'.
	rewrite -/m in leq eq.
	apply: (mprop.1 (phi' (flst phi (init_seg n))) q' phi).
	- rewrite -eq.
		apply/ coin_and_list_in => q listin.
	  have coin' :=
      (icf_flst_coin phi (phi' (flst phi (init_seg n))) (init_seg n)).1
				(phi'prop (flst phi (init_seg n))).2.
    have cond := ((coin_and_list_in (phi' (flst phi (init_seg n))) phi (init_seg n)).1
				coin').
    apply: cond.
	  by apply: mon_in_seg listin.
  - apply Fprop.
		apply: (phi'prop (flst phi (init_seg n))).1.
		exists phi.
		split => //.
		apply/ (icf_flst_coin).
		by apply coin_ref.
	by apply Fprop.

have U_rec_prop n :
	forall phi q', phi from_dom F ->
		U_rec n psiF phi q' = inl(Ff phi q')
		\/
		U_rec n psiF phi q' = inr(flst phi (init_seg (S n))).
  elim: n => [phi q' phifd|n ih phi q' phifd /=].
    rewrite /U_rec /U_step /psiF /=.
    case E : (size (mf (phi' [::]) q') <= 0)%N.
      left.
      congr inl.
      have Fphi1 : F (phi' [::]) (Ff (phi' [::])).
				apply: Fprop.
				apply: (phi'prop [::]).1.
				exists phi.
				by split => // q [] a [].
      have Fphi : F phi (Ff phi) by apply: Fprop.
			apply: (mprop.1) Fphi1 _ Fphi.
      move: ((icf_flst_coin phi (phi' nil) (nil)).1 (phi'prop (flst phi nil)).2).
      have t : size (mf (phi' nil) q') <= 0
		    by apply /leP; rewrite E.
			have eq : size (mf (phi' nil) q') = 0 by lia.
			have isnil: mf (phi' nil) q' = nil.
			  suffices [m [leq eq']] :
				     exists m : nat, m <= size (mf (phi' nil) q')
								/\ mf (phi' [::]) q' = init_seg m.
				  have m0 : m=0 by lia.
					by rewrite eq' m0.
			  apply: (mprop.2 (phi' nil) q' (mf (phi' nil) q')).
				by apply: (mprop.1 (phi' nil) q').
			rewrite -isnil => equal.
			by apply: equal.
    by right.
  have {ih}[eq|eq] := ih phi q' phifd.
    by rewrite eq /=; left.
	rewrite eq /= /U_step/psiF.
	rewrite (length_flst_in_seg phi cnt (S n)) /=.
	case E :  (size (mf (phi' (flst phi (cnt n :: init_seg n))) q') <= n.+1)%N.
		left.
		have leq: size (mf (phi' (flst phi (cnt n :: init_seg n))) q') <= n.+1 by apply /leP.
		by rewrite (Ffprop (S n) phi q' phifd leq).
 	by right.

have U_rec_prop' n :
	forall phi q', phi from_dom F -> size (mf phi q') <= n ->
		U_rec n psiF phi q' = inl (Ff phi q').
	elim: n => [phi q' phifd leq /=|n ih phi q' phifd leq /=].
		rewrite (U_step_prop _ _ _ _ leq) //.
		have eq : size (mf phi q') = 0 by lia.
		have leq' := ineq phi q' 0 phifd leq.
		rewrite eq in leq'.
		by rewrite Ffprop.
	case: (U_rec_prop n phi q' phifd) => [->//|->/=].
	rewrite (U_step_prop _ _ _ _ leq) //.
	have leq' := ineq phi q' (S n) phifd leq.
	have leq'':size (mf (phi' (flst phi (init_seg n.+1))) q') <= S n by lia.
	by rewrite Ffprop.

exists psiF => phi [Fphi FphiFphi].
split=> [|Mphi MphiMphi].
	exists Fphi => q'.
	exists (size (mf phi q')).
	rewrite /U.
	rewrite (U_rec_prop' (size (mf phi q')) phi q')=>//;last first.
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
- by exists Fphi.
- rewrite ass.
  congr Some.
	apply/ (mprop.1); last first.
	- apply Fprop.
		by exists Fphi.
  - by apply FphiFphi.
	by apply/(coin_ref phi).
by rewrite /U ass in eq.
Qed.
End UNIVERSAL_MACHINE.
Notation "T 'is_countable'" := (is_count T) (at level 2).