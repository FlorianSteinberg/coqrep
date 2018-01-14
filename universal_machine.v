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

Definition is_fun_for (phi :B) L :=
forall q a, List.In (q, a) L -> List.In (q, phi q) L.
Notation "phi 'is_function_for' L" := (if_fun_for phi L) (at level 2).

(*This should at some point go into an appropriate section: *)
Lemma extend_list:
		exists listf, forall (L : list (Q*A)) (q:Q) b, List.In (q, b) L ->
    	List.In (q, (listf L) q) L.
Proof.
set R := (fun (L : Q * list(Q * A)) (a: A) =>
	forall b, List.In (L.1,b) L.2 -> List.In (L.1,a) L.2).
have : forall L, exists b, R L b.
	move => [q L].
	case: (classic (exists a, List.In (q,a) L)).
		move => [a] inlist.
		by exists a.
	move => false.
	exists None.
	move => /= a inlist.
	exfalso; apply: false.
	by exists a.
move => cond.
move: ((@choice (Q*list(Q * A)) A R) cond) => [listf] listfprop.
exists (fun L => (fun q => listf (q,L))).
move => L q.
apply: (listfprop (q, L)).
Qed.

Lemma continuous_lists:
	F is_continuous ->
		exists phi', forall L: list (Q*A), ((exists phi, phi from_dom F
			/\ forall s, List.In s (unzip1 L) -> List.In (s,phi s) L) ->
    	(phi' L) from_dom F)
    /\ forall s, List.In s (unzip1 L) -> List.In (s,(phi' L) s) L.
Proof.
move: extend_list => [] listf listfprop.

set R := (fun (L : list(Q * A)) (psi:Q -> A) =>
	((exists phi Fphi, F phi Fphi 
		/\ forall s, List.In s (unzip1 L) -> List.In (s,phi s) L) ->
		psi from_dom F)
	/\ forall s, List.In s (unzip1 L) -> List.In (s,psi s) L).
have : forall L, exists psi, R L psi.
	move => L.
    case: (classic (exists phi Fphi, F phi Fphi
    	 /\ forall s, List.In s (unzip1 L) -> List.In (s,phi s) L)).
    	move => [psi] [Fpsi] [v prop].
      exists psi.
      split => //.
      by exists Fpsi.
    move => false.
    exists (listf L).
    split.
    	move => stuff.
    	by exfalso; apply false.
    move => s inlist.
    have: exists a, List.In (s,a) L.
    	move: s inlist.
    	elim L => //.
    	move => p K ih q' ass.
    	case ass.
   		exists p.2.
   		rewrite -H.
    	left.
    	by rewrite -surjective_pairing.
    	move => q'inlist.
    	move: (ih q' q'inlist) => [] a ainlist.
    	exists a.
    	by right.
    move => [] a ainlist.
		by apply: (listfprop L s a).
  move => cond.
  move: ((@choice (list(Q * A)) (Q -> A) R) cond) => [phi'] phi'prop.
  by exists phi'.
Qed.

Definition is_count T :=
	exists cnt: nat -> T, (F2MF cnt) is_surjective.
Notation "T 'is_countable'" := (is_count T) (at level 2).

Lemma U_is_universal:
	Q is_countable ->
  (exists a: A, True) ->
  (exists a':A', True) ->
  F is_continuous ->
  	exists psi, forall phi, (exists Fphi, F phi Fphi) ->
    forall (Fphi: Q'->A') a, exists n, U n psi phi a = Some (Fphi a).
Proof.
  move => [cnt sur] [t _] [t' _] cont.
  move: sur (minimal_section sur) => _ [] sec [] issec sprop.
  set init_seg := fun m => in_seg cnt m.

  set R := fun phi psi => ((exists psi', F phi psi') -> F phi psi).
  have: forall phi, exists psi, R phi psi.
  - move => phi.
    case: (classic (exists psi' , F phi psi')).
    - move => [psi prop].
      by exists psi.
    move => false.
    by exists (fun a => t').
  move => cond.
  move: ((@choice ((Q -> A)) (Q' -> A') R) cond) => [Ff] Fprop.
  rewrite /R /= in Fprop.
  move: t' R cond => _ _ _.


	move: (minimal_mod_function sec cont) => [mf] mprop.
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
  move: Fphi'.

  set QA := fun m => zip (init_seg m) (map phi (init_seg m)).
  have:
  	size sec (mf (phi' (QA (size sec (mf phi q')))) q')
  	<= size sec (mf phi q').
  apply: (mprop).2.
  move => psi coin Fphi' Fphi'Fphi' Fpsi FpsiFpsi.
  replace (Fpsi q') with (Fphi q').
  apply: (mprop.1 phi q' (phi' (QA (size sec (mf phi q'))))) => //.
  have: 
  	forall m, m < size sec (mf phi q') ->
  	step psiF phi q' (QA m) = inr (QA m.+1).
  elim.
  	move => ineq.
  	rewrite /step.
  	rewrite /psiF /QA /=.
  have: forall m< size sec (mf phi q') ->
  	rec m psiF phi q' = inr (zip (init_seg m.+1) (map phi (init_seg m.+1))).
  	elim.
  		move => ineq.
  		rewrite /rec.
  		rewrite /step.
    move => ineq /=.
    have: ( size sec (mf (phi' nil) q')) <= 0.
   		rewrite eq.
    	apply: (mprop.2).
    	move => psi pep Fphi' val Fpsi FpsiFpsi.
    	replace (Fphi' q') with (Fphi q');last first.
    	apply: (mprop.1 (phi) q' (phi' nil) _ ) => //.
    		move => .
    		apply: (mprop.1 (phi' nil) q' (psi)) => //.
    		apply: (@list_size Q A cnt sec issec (mf (phi' nil) q')).
    		rewrite -eq //.
    		have: F (phi' nil) Fphi.
    	move: (mprop.1).
    	split.
    	have: (mf (phi' nil) q') = nil.
    		move: (fprop (phi, s') (phi' nil)).
    replace (Ff (phi' [::]) s') with (Fphi' s') => //.
      have: f (phi' nil, s') = 0.
      case: (classic (exists Fpsi, F (phi' nil) Fpsi)).
      - move => [Fpsi] v1.
        move: (fprop (phi, s') (phi' nil)) => stuff.
        have: (forall m : nat, m < f (phi, s')
        	-> (phi, s').1 (cnt m) = phi' [::] (cnt m)).
        move => m ml0.
        exfalso.
        apply (PeanoNat.Nat.nlt_0_r m).
        by rewrite zero.
        move => ass.
        move: stuff ass (stuff ass Fphi v) => _ _ [] [] Fpsi' v3 lala.
        move: lala (lala Fpsi v1) => _ /= v4.
      - done.
      apply (fprop (phi,s') (phi' nil)).
      rewrite zero.
      move => m H.
      exfalso.
      by apply: (PeanoNat.Nat.nlt_0_r m).
      by replace ((phi,s').1) with phi.
      - apply: (Fprop (phi' nil)).
        apply phiprop.
        exists phi.
        exists Fphi.
        split.
        - done.
        done.
    - move => n ih two.
      have: f(phi,s') = n.+1.
      - move: (Minus.pred_of_minus (f(phi,s')).+1) => H.
        by rewrite -{2}two /= in H.
      move: two => _ one.
      rewrite /U /U' /psiF /=.
      replace (Ff (phi' [::]) s') with (Fphi s').
      - done.
      apply (fprop (phi,s') (phi' nil)).
      rewrite one.
      move => m H /=.
      exfalso.
      by apply: (PeanoNat.Nat.nlt_0_r m).
      by replace ((phi,s').1) with phi.
      - apply: (Fprop (phi' nil)).
        apply phiprop.
        exists phi.
        exists Fphi.
        split.
        - done.
        done.
      
      exists Fphi'.
      case: (classic ((exists (Fphi : S' -> T'),
        F (phi' nil) Fphi /\
        (forall (s : S) (c : T),
         List.In (s, c) [::] -> List.In (s, (phi' nil) s) [::])))).
      move => [Fpsi] [v3 c].
      by exists Fpsi.
      move => false.
      exists (Fphi).
      apply NNPP.
      move => nv.
      apply false.
      exists (phi' nil).
      exists Fphi.
      split.
      split; last first.
      replace Fphi with Fpsi => //.
      apply functional_extensionality.
      move => x.
      move: (cont (phi' nil) x) => [L] stuff.
      apply (stuff (phi' nil)).
      done.
      move: (cont_to_sing cont) => sing.
      move: (sing (phi' nil) Fphi Fpsi).
      apply: cont.
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