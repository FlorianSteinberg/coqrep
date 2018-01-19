(* This file is supposed to contain the definition of a universal machine and the proof
that the machine is actually universal. The universal machine is a machine of type two
and it should work for any continuous function from B -> B. Usually B is the Baire space,
here, i.e. the set of all mappings from strings to strings. However, since I don't want
to rely on a handwritten type of strings as I attempted in the file "operators.v" I use
more generaly a space S -> T as substitute for B. *)
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions continuity initial_segments.
Require Import ClassicalChoice Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section UNIVERSAL_MACHINE.

Context (Q I Q' I' : Type).
Notation A := (option I).
Notation A' := (option I').
Notation B := (Q -> A).
Notation B' := (Q' -> A').

Definition U_step (psi: list(Q * A) * Q' -> Q + A') phi q' L :=
match psi (L, q') with
  | inr a' => inl a'
  | inl q => inr (cons (q, phi q) L)
end.

Fixpoint U_rec
n (psi: list(Q * A) * Q' -> Q + A') phi q' :=
match n with
	|	0 => match U_step psi phi q' nil with
		| inl a' => inl a'
		| inr L => inr L
	end
	|	S n' => match (U_rec n' psi phi q') with
		| inl a' => inl a'
		| inr L => U_step psi phi q' L
	end
end.

(* This is what I want to prove to be a universal machine: *)
Definition U
	(n: nat)
	(psi: list (Q * A) * Q' -> Q + A')
	(phi: Q -> A)
	(q' : Q') :=
match (U_rec n psi phi q') with
	| inl a' => a'
	| inr L => None
end.

Context (F: B ->> B').

Notation L2MF L := (fun q a => List.In (q, a) L).

Definition flst (phi: B) L := zip L (map phi L).
Notation function_list phi L := (flst phi L).

Lemma in_function_list phi qa:
	forall L, List.In qa (function_list phi L) -> phi (qa.1) = qa.2.
Proof.
elim => // q L ih ass.
case: ass => //; rewrite (surjective_pairing qa).
by case => eq1 eq2 /=; rewrite -eq1.
Qed.

Lemma function_list_in phi q:
	forall L, (List.In q L -> List.In (q, phi q) (function_list phi L)).
Proof.
elim => // q' L ih ass.
case: ass => H.
	by left; rewrite H.
by move; right; apply: ih.
Qed.

Lemma function_in_list phi qa:
	forall L, List.In qa (function_list phi L) -> List.In qa.1 L.
Proof.
elim => // a L ih [].
	by rewrite (surjective_pairing qa); case => eq _; left.
by move => stuff; right; apply: ih.
Qed.

Lemma choice_function_list phi L:
	phi is_choice_for (L2MF (function_list phi L)).
Proof.
move => q [] a listin.
split.
	exists a; apply: (in_function_list listin).
move => a' phiqa'.
by rewrite -phiqa'; apply: (function_list_in phi (function_in_list listin)).
Qed.

Lemma coin_choice_flst phi psi:
	forall L, phi is_choice_for (L2MF (function_list psi L))
	<->
	phi and psi coincide_on L.
Proof.
elim.
	by split => // _ /= q [] a false; exfalso.
move => q L.
split.
	move: H => [] ih _ icf.
	split.
		case: (icf q).
			by exists (psi q); apply: (function_list_in psi); left.
		move => [] a phiqa prop.
		move: (in_function_list (prop a phiqa)) => /= psiqa.
		by rewrite psiqa -phiqa.
	apply ih => q' [] a inlist.
	move: (in_function_list inlist) => /= eq.
	split.
		exists a; case: (icf q') => /=.
			by exists a; right.
		move => [] a' phiq'a' prop.
		case: (prop a' phiq'a').
			move: prop => _ [] eq1 eq2.
			by rewrite -eq -{2}eq1 eq2.
		move: prop => _ listin.
		move: (in_function_list listin) => /= eq'.
		by rewrite -eq eq'.
	move: (function_in_list inlist) => /= listin a' phiq'a'.
	case: (icf q').
		by exists a; right.
	move => _ prop.
	case: (prop a' phiq'a').
		move => [] eq1 eq2.
		by rewrite -eq2 eq1; apply: function_list_in.
	by move => stuff.
move => coin q' [] a inlist.
split.
	by exists (phi q').
move: coin.1 => eq a' phiq'a'.
rewrite -phiq'a'.
case: (function_in_list inlist) => /=.
	move => eq'.
	by left; rewrite -eq' eq.
move => listin;right.
have: List.In q' (q::L) by right.
move => listin2.
move: ((coin_and_list_in phi psi (q::L)).1 coin q' listin2) => eq'.
by rewrite eq'; apply: (function_list_in psi).
Qed.

(*This should at some point go into an appropriate section: *)
Lemma extend_list:
	exists listf, forall (L: list (Q * A)), (listf L) is_choice_for (L2MF L).
Proof.
set R := (fun (L : Q * list(Q * A)) (a: A) =>
	forall b, (L2MF L.2) L.1 b -> (L2MF L.2) L.1 a).
have : forall L, exists b, R L b.
	move => [q L].
	case: (classic (exists a, List.In (q,a) L)).
		move => [a] inlist.
		by exists a.
	move => false.
	exists None.
	move => a inlist.
	exfalso; apply: false.
	by exists a.
move => cond.
move: ((@choice (Q*list(Q * A)) A R) cond) => [listf] listfprop.
exists (fun L => (fun q => listf (q,L))).
move => L q e.
split.
	by exists (listf (q,L)).
rewrite /F2MF.
move: e => [] a inlist b v.
move: (listfprop (q, L) a inlist) => /= asdf.
by rewrite v in asdf.
Qed.

Lemma continuous_lists:
	F is_continuous ->
		exists phi', forall L: list (Q*A),
		((exists phi, phi from_dom F /\ phi is_choice_for (L2MF L)) ->
			(phi' L) from_dom F)
    /\ (phi' L) is_choice_for (L2MF L).
Proof.
move: extend_list => [] listf listfprop.
set R := (fun L (psi: B) =>
	((exists phi, phi from_dom F /\ phi is_choice_for (L2MF L)) -> psi from_dom F)
	/\ psi is_choice_for (L2MF L)).
have : forall L, exists psi, R L psi.
	move => L.
  case: (classic (exists phi, phi from_dom F /\ phi is_choice_for (L2MF L))).
  	move => [psi] [] psifd psic.
    by exists psi.
  move => false.
  exists (listf L).
  by split => //.
move => cond.
move: ((@choice (list(Q * A)) (Q -> A) R) cond) => [phi'] phi'prop.
by exists phi'.
Qed.

Definition is_count T :=
	exists cnt: nat -> T, (F2MF cnt) is_surjective.
Notation "T 'is_countable'" := (is_count T) (at level 2).

Notation "B ~> B'" := (nat -> B -> B') (at level 2).

Definition F_computed_by (M: B ~> B'):=
  (forall phi Fphi, F phi Fphi -> forall q', exists n, M n phi q' = Fphi q')
    /\
  (forall phi n q' a', M n phi q' = Some a' -> exists Fphi, F phi Fphi /\ Fphi q' = Some a').

Lemma icf_coin_flst (phi psi:B) L:
	phi is_choice_for (L2MF(flst psi L)) <-> phi and psi coincide_on L.
Proof.
split.
	move => icf.
	apply/ (coin_and_list_in phi psi L) => q listin.
	have ex: (exists t : A, List.In (q, t) (function_list psi L)).
			exists (psi q).
			by apply: (function_list_in).
	have inlist: List.In (q, phi q) (flst psi L) by apply: (icf q ex).2.
	by move: (in_function_list inlist).
move => coin q []a listin.
move: (function_in_list listin) => inlist.
move: coin ((coin_and_list_in phi psi L).1 coin q) => _ coin .
split.
	exists a.
	move: (in_function_list listin) => /= eq.
	by rewrite -eq -coin.
move => a' eq.
rewrite -eq coin => //.
by apply: (function_list_in).
Qed.

Lemma U_is_universal:
	Q is_countable -> F is_continuous ->
  	exists psiF, F_computed_by (fun n phi q' => U n psiF phi q').
Proof.
move => [cnt sur] cont.
move: sur (minimal_section sur) => _ [] sec isminsec.
set init_seg := in_seg cnt.
set size := size sec.

set R := fun phi psi => ((exists psi', F phi psi') -> F phi psi).
have cond: forall phi, exists psi, R phi psi.
  move => phi.
  case: (classic (exists psi' , F phi psi')).
    move => [psi prop].
    by exists psi.
  move => false.
  by exists (fun a => None).
move: ((@choice ((Q -> A)) (Q' -> A') R) cond) => [Ff] Fprop.
rewrite /R /= in Fprop; move: R cond => _ _.

move: (@minimal_mod_function Q A Q' A' cnt sec F cont isminsec) => [] mf mprop.
move: (continuous_lists cont) => [] phi' phi'prop.

have coin: forall phi q', (phi' (flst phi (mf phi q'))) and phi coincide_on (mf phi q').
	move => phi q'.
	apply/ icf_coin_flst.
	by apply: (phi'prop (flst phi (mf phi q'))).2.

have mfinseg: forall phi q', init_seg (size (mf phi q')) = mf phi q'.
	move => phi q'.
	move: (mprop.2 phi q' (mf phi q') (mprop.1 phi q')) => [] m [] ineq eq'.
	move: (size_in_seg isminsec m) => ineq'.
	rewrite -eq' in ineq'.
	rewrite -/size in ineq ineq'.
	have eq'': (size (mf phi q')) = m by lia.
	by rewrite eq'' eq'.

have ineq: forall phi q', phi from_dom F -> size (mf (phi' (flst phi (init_seg (size (mf phi q'))))) q') <= size (mf phi q').
	move => phi q' [] Fphi FphiFphi.
	set L := init_seg (size (mf phi q')).
	set K := mf (phi' (flst phi L)) q'.
	suffices: exists m : nat, m <= size (mf phi q') /\ K = in_seg cnt m.
		move => [] m [] leq eq.
		rewrite eq.
		move: (size_in_seg isminsec m) => ineq.
		rewrite -/size in ineq.
		by lia.
	apply: (mprop.2 (phi' (flst phi L)) q' (mf phi q')) => psi coin' FphiL FphiLFphiL Fpsi FpsiFpsi.
	replace (FphiL q') with (Fphi q').
	apply: (mprop.1 phi q' psi) => //.
		apply/ (coin_trans).
			by apply: ((coin_sym phi (phi' (flst phi (mf phi q'))) (mf phi q')).2 (coin phi q')).
		by rewrite -{1}mfinseg.
	apply: (mprop.1 phi q' (phi' (flst phi L))) => //.
	move: ((coin_sym phi (phi' (flst phi (mf phi q'))) (mf phi q')).2 (coin phi q')).
	by rewrite -{1}mfinseg.

set psiF := (fun L =>
  if
    (leq (size (mf (phi' L.1) L.2)) (length L.1))
  then
    (inr (Ff (phi' L.1) L.2))
  else
    (inl (cnt (length L.1)))).

have: forall phi q' n a', phi from_dom F -> U_step psiF phi q' (flst phi (init_seg n)) = inl a' 
	-> U_step psiF phi q' (flst phi(init_seg n.+1)) = inl a'.
	move => phi q' n a' phifd H.
	replace (flst phi (init_seg n.+1)) with ((cnt n, phi (cnt n))::(flst phi (init_seg n))) by trivial.
	rewrite /U_step/psiF/=.

have: forall n phi q', phi from_dom F -> size (mf phi q') <= n -> U_step psiF phi q' (flst phi (init_seg n)) = inl (Ff phi q').
	elim.
  	move => phi q' phifd ass.
  	rewrite /U_step/psiF/=.
  	have isnil: flst phi (init_seg 0) = nil by trivial.
  	rewrite isnil.
  	have isnil': (mf phi q' = nil).
 			move: (mprop.2 phi q' (mf phi q') (mprop.1 phi q')) => [] m [];rewrite -/size /leqP.
 			move => leq.
 			have null: m = 0 by lia.
 			by rewrite null.
 		have eq : 0 = size (mf phi q') by lia.
 		have sizenil: size nil = 0 by trivial.
 		case_eq (size (mf (phi' nil) q') <= 0)%N => truth;last first.
 			exfalso.
 			case (classic (size (mf (phi' nil) q') <= 0)%N).
 				by rewrite truth.
 			move => false; apply false; apply/ leP.
			move: (ineq phi q' phifd).
			by rewrite isnil' isnil sizenil => ineq'.
		replace (Ff (phi' [::]) q') with (Ff phi q') => //.
		have phi'fd : (phi' nil) from_dom F.
			have ex: (exists phi0 : B, phi0 from_dom F /\ phi0 is_choice_for (L2MF [::])).
				exists phi.
				split => //.
				have triv: forall phi, flst phi nil = nil by trivial.
				move: (@choice_function_list phi nil).
				by rewrite triv.
			by move: ((phi'prop nil).1 ex).
		move: (Fprop phi phifd) (Fprop (phi' nil) phi'fd) => val1 val2.
		apply: (mprop.1 phi q' (phi' [::]) _ (Ff phi) val1 (Ff (phi' [::])) val2).
		by rewrite isnil'.
	move => n ih phi q' phifd ass.
	case: ((PeanoNat.Nat.le_succ_r (size (mf phi q')) n).1 ass) => ass'.
		move: (ih phi q' phifd ass').
		rewrite /U_step/psiF/=.

	move: (mfinseg phi q').
	
	Search _ le S (_ \/ _).
	case_eq (size (mf (phi' (flst phi (mf phi q'))) q') <= n.+1)%N => truth;last first.
		exfalso.
	case (classic (size (mf (phi' nil) q') <= 0)%N).
		by rewrite truth.
	move => false; apply false; apply/ leP.
	move: (ineq phi q' phifd).
	by rewrite isnil' isnil sizenil => ineq'.
replace (Ff (phi' [::]) q') with (Ff phi q') => //.
have phi'fd : (phi' nil) from_dom F.
	have ex: (exists phi0 : B, phi0 from_dom F /\ phi0 is_choice_for (L2MF [::])).
		exists phi.
		split => //.
		have triv: forall phi, flst phi nil = nil by trivial.
		move: (@choice_function_list phi nil).
		by rewrite triv.
	by move: ((phi'prop nil).1 ex).
move: (Fprop phi phifd) (Fprop (phi' nil) phi'fd) => val1 val2.
apply: (mprop.1 phi q' (phi' [::]) _ (Ff phi) val1 (Ff (phi' [::])) val2).
by rewrite isnil'.
  
  		
  		move: true'.
  		apply /eqP.

  			done.
  		rewrite ineq'.
  		apply /leqP. => //.
  	rewrite -eq.

  	set K := mf (phi' L) q'.
		have isnil: K = nil.
		move: (mprop.2 phi q' K).
		move: (mprop.1 (phi' L) q').
		) => [] m [];rewrite -/size-/init_seg.
		move => leq.
		have null: m = 0 by lia.
		by rewrite null.
  	have ineq: size (mf (phi' [::]) q') <= 0.
  		have prop: forall psi : B,
  	  	(phi' [::]) and psi coincide_on [::] ->
  	  	forall Fphi0 : B',
  	  	F (phi' [::]) Fphi0 -> forall Fpsi : B', F psi Fpsi -> Fphi0 q' = Fpsi q'.
  			move => psi _ Fphi0 Fphi0Fphi0 Fpsi FpsiFpsi.
 				have coin1: phi and psi coincide_on (mf phi q').
 					rewrite isnil.
  	  		by apply: (coin_and_list_in phi (phi' nil) nil).2.
 				have coin2: phi and (phi' nil) coincide_on (mf phi q').
 					rewrite isnil.
  	  		by apply: (coin_and_list_in phi (phi' nil) nil).2.
  	  	replace (Fpsi q') with (Fphi q').
  	  		by rewrite (mprop.1 phi q' (phi' nil) coin2 Fphi FphiFphi Fphi0).
  	  	by rewrite (mprop.1 phi q' psi coin1 Fphi FphiFphi Fpsi FpsiFpsi).
  	  move: (mprop.2 (phi' nil) q' nil prop); rewrite -/size.
  	  move => /= [] m [] le a.
  	  have isnull: (size nil = 0) by trivial.
  	  rewrite isnull in le.
  	  have m0: m=0 by lia.
  	  rewrite m0 in a.
  	  have snil: (in_seg cnt 0 = nil) by trivial.
  	  rewrite snil in a.
  	  by rewrite a isnull.
  	replace (size (mf (phi' nil) q')<= 0)%N with true.
  	replace (Ff (phi' [::]) q') with (Fphi q') => //.
  	apply: (mprop.1 phi q' (phi' nil) _ Fphi _ ) => //.
  	by rewrite isnil.
  	apply: Fprop.
  	have ex: (exists phi0 : B,
    	phi0 from_dom F /\
    	phi0 is_choice_for (L2MF [::])).
    	exists phi.
    	split.
    		by exists Fphi.
    	move => q [] a false.
    	by exfalso.
  	by move: ((phi'prop nil).1 ex).

Definition U_step (psi: list(Q * A) * Q' -> Q + A') phi q' L :=
match psi (q', L) with
  | inr a' => inl a'
  | inl q => inr (cons (q, phi q) L)
end.

exists psiF.
move => phi Fphi FphiFphi q'.
exists (size (mf phi q')).
have: forall m, m = size (mf phi q') ->
	U (size (mf phi q')) psiF phi q' = Some (Fphi q').
	elim.
 		move => eq.
  	rewrite -eq /U/U_rec/U_step/psiF/=.
  	have ineq: size (mf (phi' [::]) q') <= 0.
  		have prop: forall psi : B,
  	  	(phi' [::]) and psi coincide_on [::] ->
  	  	forall Fphi0 : B',
  	  	F (phi' [::]) Fphi0 -> forall Fpsi : B', F psi Fpsi -> Fphi0 q' = Fpsi q'.
  			move => psi _ Fphi0 Fphi0Fphi0 Fpsi FpsiFpsi.
 				have coin1: phi and psi coincide_on (mf phi q').
 					rewrite isnil.
  	  		by apply: (coin_and_list_in phi (phi' nil) nil).2.
 				have coin2: phi and (phi' nil) coincide_on (mf phi q').
 					rewrite isnil.
  	  		by apply: (coin_and_list_in phi (phi' nil) nil).2.
  	  	replace (Fpsi q') with (Fphi q').
  	  		by rewrite (mprop.1 phi q' (phi' nil) coin2 Fphi FphiFphi Fphi0).
  	  	by rewrite (mprop.1 phi q' psi coin1 Fphi FphiFphi Fpsi FpsiFpsi).
  	  move: (mprop.2 (phi' nil) q' nil prop); rewrite -/size.
  	  move => /= [] m [] le a.
  	  have isnull: (size nil = 0) by trivial.
  	  rewrite isnull in le.
  	  have m0: m=0 by lia.
  	  rewrite m0 in a.
  	  have snil: (in_seg cnt 0 = nil) by trivial.
  	  rewrite snil in a.
  	  by rewrite a isnull.
  	replace (size (mf (phi' nil) q')<= 0)%N with true.
  	replace (Ff (phi' [::]) q') with (Fphi q') => //.
  	apply: (mprop.1 phi q' (phi' nil) _ Fphi _ ) => //.
  	by rewrite isnil.
  	apply: Fprop.
  	have ex: (exists phi0 : B,
    	phi0 from_dom F /\
    	phi0 is_choice_for (L2MF [::])).
    	exists phi.
    	split.
    		by exists Fphi.
    	move => q [] a false.
    	by exfalso.
  	by move: ((phi'prop nil).1 ex).
  	admit.
	move => n ih ass.
  move: (size_in_seg isminsec 0);rewrite -/size.
  lia.
  move: .

  rewrite -/size.
  rewrite /U /U_rec /U_step /psiF /=.

Fixpoint cons_check S T S' T' (psi : S'*list T -> S + T') (s': S') (L : list (S*T)) :=
match L with
  | nil =>
  match (psi (s',nil)) with
    | inl s => Some False
    | inr t => None
  end
  | cons a K =>
  match (psi (s',map snd K)) with
    | inl s =>
    match (cons_check psi s' K) with
      | None => None
      | Some b => Some (a.1 = s /\ b)
    end
    | inr t => None
   end
end.