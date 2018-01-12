(* This file is supposed to contain the definition of a universal machine and the proof
that the machine is actually universal. The universal machine is a machine of type two
and it should work for any continuous function from B -> B. Usually B is the Baire space,
here, i.e. the set of all mappings from strings to strings. However, since I don't want
to rely on a handwritten type of strings as I attempted in the file "operators.v" I use
more generaly a space S -> T as substitute for B. *)
Load initial_segments.

Fixpoint U' Q A Q' A'
  (n: nat)
  (psi: Q' * list (Q * A) -> Q + A')
  (phi: Q -> A)
  (L: Q' * list (Q * A)) :=
match n with
  | 0 => None
  | S n => match psi L with
    | inr c => Some c
    | inl b => U' n psi phi (L.1, cons (b,phi b) L.2)
  end
end.

Definition U Q A Q' A' n (psi: Q'* list(Q*A) -> Q + A') phi a :=
U' n.+1 psi phi (a,nil).
(* This is what I want to prove to be a universal machine. *)

Lemma U_is_universal Q A Q' A' (F:(Q -> A) ->> (Q' -> A')):
  (exists cnt: nat -> Q, (F2MF cnt) is_surjective)
    -> (exists a: A, True)
    -> (exists a':A', True)
    -> F is_continuous
      -> exists psi, forall phi, (exists Fphi, F phi Fphi)
      -> forall (Fphi: Q'->A') a, exists n, U n psi phi a = Some (Fphi a).
Proof.
  move => [cnt sur] [t _] [t' _] cont.
  move: sur (minimal_section sur) => _ [] sec [] issec sprop.

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

  set R := (fun (L : Q*list(Q * A)) (b:A) =>
      forall c, List.In (L.1,c) L.2 -> List.In (L.1,b) L.2).
    have : forall L, exists b, R L b.
    move => L.
    case: (classic (exists c, List.In (L.1, c) L.2)).
    - move => [c] inlist.
      by exists c.
    move => false.
    exists (t).
    move => c inlist.
    exfalso.
    apply: false.
    by exists c.
  move => cond.
  move: ((@choice (Q*list(Q * A)) (A) R) cond) => [temp] tprop.
  rewrite /R /= in tprop.
  move: R cond => _ _.

  set R := (fun (L : list(Q * A)) (psi:Q -> A) =>
     ((exists phi Fphi, F phi Fphi /\ forall s c, List.In (s,c) L -> List.In (s,phi s) L)
    -> (exists Fpsi, F psi Fpsi)) /\ forall s c, List.In (s,c) L -> List.In (s,psi s) L).
  have : forall L, exists psi, R L psi.
    move => L.
    case: (classic (exists phi Fphi, F phi Fphi /\ forall s c, List.In (s,c) L -> List.In (s,phi s) L)).
    - move => [psi] [Fpsi] [v prop].
      exists psi.
      split.
      - move => stuff.
        by exists Fpsi.
      - done.
    move => false.
    exists (fun s => temp (s,L)).
    split.
    move => stuff.
    exfalso.
    by apply false.
    move => s.
    apply (tprop (s,L)).
    move => cond.
    move: ((@choice (list(Q * A)) (Q -> A) R) cond) => [phi'] phiprop.
    rewrite /R /= in phiprop.
    move: R cond => _ _.

		move: (minimal_mod_function sec cont) => [mf] mprop.
    set psiF := (fun L =>
      if
        (leq (size sec (mf (phi' L.2) L.1)) (length L.2))
      then
        (inr (Ff (phi' L.2) L.1))
      else
        (inl (cnt (length L.2).+1))).
    exists psiF.
    move => phi [Fphi v] Fphi' q'.
    exists (size sec (mf phi q')).
    have: forall m, m = size sec (mf phi q') -> U m psiF phi q' = Some (Fphi' q').
    	elim.
    	rewrite /U /U' /psiF /=.
    	move => eq.
    	have: forall psi Fphi Fpsi, F (phi' nil) Fphi -> F psi Fpsi ->
    		(phi' nil) and psi coincide_on nil -> Fphi q' = Fpsi q'.
    		move => psi a b c d e.
    		apply: (mprop.1 (phi' nil) q' psi) => //.
    	have: (size sec (mf (phi' [::]) q') <= 0).
    		rewrite eq.
    		apply mprop.2 => //.
    		move => psi _ Fphi'nil Fphi'nilFphi'nil Fpsi FpsiFpsi.
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
        have: (forall m : nat, m < f (phi, s') -> (phi, s').1 (cnt m) = phi' [::] (cnt m)).
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
(* This is probably not true without further assumptions... also, instead of arbitrary certificates,
the function f should probably use minimal certificates for it to work even in special cases. *)

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