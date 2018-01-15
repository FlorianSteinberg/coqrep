(* This file is supposed to contain the definition of a universal machine and the proof
that the machine is actually universal. The universal machine is a machine of type two
and it should work for any continuous function from B -> B. Usually B is the Baire space,
here, i.e. the set of all mappings from strings to strings. However, since I don't want
to rely on a handwritten type of strings as I attempted in the file "operators.v" I use
more generaly a space S -> T as substitute for B. *)
Load initial_segments.

Section UNIVERSAL_MACHINE.

Context (Q I Q' I' : Type).
Notation A := (option I).
Notation A' := (option I').
Notation B := (Q -> A).
Notation B' := (Q' -> A').

Definition U_step (psi: Q'* list(Q*A) -> Q + A') phi q' L :=
match psi (q', L) with
  | inr a' => inl a'
  | inl q => inr (cons (q, phi q) L)
end.

Fixpoint U_rec
n (psi: Q'* list(Q*A) -> Q + A') phi q' :=
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
	(psi:Q' * list (Q * A) -> Q + A')
	(phi: Q -> A)
	(q' : Q') :=
match (U_rec n psi phi q') with
	| inl a' => Some a'
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
	by exists a; apply (in_function_list listin).
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

Lemma U_is_universal:
	Q is_countable -> F is_continuous ->
  	exists psi, forall phi, (exists Fphi, F phi Fphi) ->
    forall (Fphi: Q'->A') a, exists n, U n psi phi a = Some (Fphi a).
Proof.
  move => [cnt sur] cont.
  move: sur (minimal_section sur) => _ [] sec [] issec smin.
  set init_seg := fun m => in_seg cnt m.

  set R := fun phi psi => ((exists psi', F phi psi') -> F phi psi).
  have: forall phi, exists psi, R phi psi.
  - move => phi.
    case: (classic (exists psi' , F phi psi')).
    - move => [psi prop].
      by exists psi.
    move => false.
    by exists (fun a => None).
  move => cond.
  move: ((@choice ((Q -> A)) (Q' -> A') R) cond) => [Ff] Fprop.
  rewrite /R /= in Fprop.
  move: R cond => _ _.

move: (minimal_mod_function sec cont) => [mf] mprop.
move: (continuous_lists cont) => [] phi' phi'prop.
have: forall phi L,
	(phi' (flst phi L)) and phi coincide_on L.
	move => phi L.
	apply: (coin_choice_flst (phi' (flst phi L)) phi L).1.
	apply phi'prop.
move => phi'prop'.
have: forall phi q'' psi, phi and psi coincide_on (mf phi q'') ->
	size sec (mf psi q'') <= size sec (mf phi q'').

set psiF := (fun L =>
  if
    (leq (size sec (mf (phi' L.2) L.1)) (length L.2))
  then
    (inr (Ff (phi' L.2) L.1))
  else
    (inl (cnt (length L.2).+1))).
exists psiF.
move => phi [Fphi FphiFphi] Fphi' q'.
exists (size sec (mf phi q')).
set QA := fun m => function_list phi (init_seg m).
have: size sec (mf (phi' (QA (size sec (mf phi q')))) q') <= size sec (mf phi q').
	apply mprop.
	move => psi coin Fphi'L val Fpsi FpsiFpsi.
	replace (Fpsi q') with (Fphi q').
	apply: (mprop.1 (phi' (QA (size sec (mf phi q')))) q' psi) => //.
  apply: (listf_prop 
  (phi' (QA (size sec (mf phi q'))))
  psi
  (mf (phi' (QA (size sec (mf phi q')))) q')).1.
	move: (phi'prop (function_list psi (mf (phi' (QA (size sec (mf phi q')))) q'))).2.
	have:
  	forall m, m < size sec (mf phi q') ->
  	U_step psiF phi q' (QA m) = inr (QA m.+1).
  elim.
  	move => ineq.
  		rewrite /U_step.
  		rewrite /psiF /=.
  		replace (QA 0) with (@nil (Q*A)).

(* This is probably not true without further assumptions... also, instead of arbitrary
certificates, the function f should probably use minimal certificates for it to work
even in special cases. *)

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