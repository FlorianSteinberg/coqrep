(* This file is supposed to contain the definition of a universal machine and the proof
that the machine is actually universal. The universal machine is a machine of type two
and it should work for any continuous function from B -> B. Usually B is the Baire space,
here, i.e. the set of all mappings from strings to strings. However, since I don't want
to rely on a handwritten type of strings as I attempted in the file "operators.v" I use
more generaly a space S -> T as substitute for B. *)
Load functions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Fixpoint equal_on (S T : Type) (phi psi : S -> T) (L : list S) :=
  match L with
    | nil => True
    | cons s K => (phi s = psi s) /\ (equal_on phi psi K)
  end.
Notation "phi 'and' psi 'coincide_on' L" := (equal_on phi psi L) (at level 2).

Definition is_cont (S T S' T' : Type) (F : (S -> T) ->> (S'-> T')) :=
      forall phi (s': S'), exists (L : list S), forall psi, phi and psi coincide_on L ->
          forall Fphi : S' -> T', F phi Fphi -> ((exists Fpsi, F psi Fpsi) /\
            forall Fpsi, (F psi Fpsi -> Fphi s' = Fpsi s')).
Notation "F 'is_continuous'" := (is_cont F) (at level 2).

Require Import FunctionalExtensionality.
Lemma cont_to_sing (S T S' T' : Type) F: @is_cont S T S' T' F -> F is_single_valued.
Proof.
  move => cont phi Fpsi Fpsi' _ [v1 v2].
  apply functional_extensionality => a.
  move: cont (cont phi a) => _ [L] cont.
  have: (forall K, phi and phi coincide_on K).
  by elim.
  move => equal.
  move: cont (cont phi (equal L) Fpsi') => _ cond.
  move: cond (cond v2) => _ [[Fphi]] v cond.
  by rewrite ((cond Fpsi) v1).
Qed.

Definition iscont (S T S' T': Type) (F: (S-> T) -> S' -> T') :=
  forall phi (s': S'), exists (L : list S), forall psi,
    phi and psi coincide_on L -> F phi s' = F psi s'.

Lemma continuity S T S' T' (F: (S-> T) -> S' -> T') :  iscont F <-> is_cont (F2MF F).
Proof.
  split.
  - move => cont psi s'.
    move: cont (cont psi s') => _ [L cond].
    exists L => phi coin Fpsi iv.
    split.
    - by exists (fun s' => F phi s').
    - move => Fphi iv'.
      rewrite -iv -iv'.
      by apply (cond phi).
  - move => cont phi s'.
    move: cont (cont phi s') => _ [L cond].
    exists L => psi coin.
    move: cond (cond psi coin (F phi)) => _ cond.
    have: forall psi', (F2MF F psi' (F psi')).
    - done.
    move => triv.
    move: cond (cond (triv phi)) => _ [] [Fphi] v cond.
    by apply: (cond (fun s' => F psi s')).
Qed.

Fixpoint U' (S T S' T' : Type)
  n
  (psi: S' * list (S * T) -> S + T')
  (phi: S -> T)
  (L: S' * list (S * T)) :=
match n with
  | 0 => None
  | S n => match psi L with
    | inr c => Some c
    | inl b => U' n psi phi (L.1, cons (b,phi b) L.2)
  end
end.

Definition U (S T S' T' : Type) n (psi: S' * list (S * T) -> S + T') (phi: S -> T) a :=
U' n.+1 psi phi (a,nil).
(* This is what I want to prove to be a universal machine. *)

Require Import ClassicalChoice FunctionalExtensionality.

Inductive one := star.

Local Open Scope coq_nat_scope.

Lemma example: is_cont (fun phi Fphi => phi (Fphi star) = 0 /\ forall m, m < Fphi star -> phi m <> 0).
Proof.
  move => phi star.
  set L := fix L m := match m with
    | 0 => cons 0 nil
    | S n => cons (S n) (L n)
  end.
  case: (classic (exists m, phi m = 0)); last first.
  - move => false.
    exists nil => psi _ fp1 [v1] cond.
    exfalso; apply false.
    by exists (fp1 Top.star).
  - move => [m me0].
    exists (L m).
    move => psi pep.
    have: (forall k,phi and psi coincide_on (L k) -> forall n, n <= k -> phi n = psi n).
    elim.
    - move => [p0 _] n nl0.
      replace n with 0 => //.
      by apply Le.le_n_0_eq.
    - move => n ihn.
      replace (L n.+1) with (cons n.+1 (L n)).
      case.
      move => eqp1 stuff n0.
      move: stuff ihn (ihn stuff) => _ _ ihn nln0.
      case: (classic (n0 = S n)).
      move => kack.
      by rewrite kack.
      move => neq.
      apply ihn.
      apply Lt.lt_n_Sm_le.
      move: (PeanoNat.Nat.le_neq n0 n.+1) => [_ stuff].
      by apply stuff.
      done.
    - move => cond.
      move: cond pep (cond m pep) => _ _ cond Fphi [v1 c1].
      have: m >= Fphi Top.star.
      - apply NNPP => ge1.
        apply (c1 m);last first.
        replace (psi m) with (phi m) =>//.
        - by apply (cond m).
        apply Compare_dec.not_ge.
        done.
      move => ge1.
      move: ge1 (cond (Fphi Top.star) ge1).
      rewrite v1.
      move => zero1.
      split.
      - exists (fun star => Fphi Top.star).
        split => //.
        move => m0 co.
        replace (psi m0) with (phi m0).
        - by apply (c1 m0).
        apply (cond m0).
        apply PeanoNat.Nat.lt_le_incl.
        by apply: (PeanoNat.Nat.lt_le_trans m0 (Fphi Top.star) m).
      - move => Fpsi [v2 c2].
      have: m >= Fpsi Top.star.
      apply NNPP => ge2.
      apply (c2 m);last first.
      replace (psi m) with (phi m) =>//.
      by apply (cond m).
      apply Compare_dec.not_ge.
      done.
      move => ge2.
      move: ge2 (cond (Fpsi Top.star) ge2) => _.
      rewrite v2.
      move => zero2.
      have: (~ Fphi star > Fpsi star).
      move => gt1.
      apply (c1 (Fpsi star)).
      replace Top.star with star => //.
      by elim star.
      replace star with Top.star => //.
      by elim star.
      move => gt1.
      have: (~ Fpsi star > Fphi star).
      move => gt2.
      apply (c2 (Fphi star)).
      replace Top.star with star => //.
      by elim star.
      replace star with Top.star => //.
      by elim star.
      move => gt2.
      apply NNPP=> neq.
      move: (PeanoNat.Nat.lt_trichotomy (Fphi star) (Fpsi star)).
      case.
      apply gt2.
      case.
      apply neq.
      apply gt1.
Qed.
(* This was a pain to prove... Why? *)

Lemma dec S (equ : S -> S -> bool):
  forall s t, (equ s t = true \/ equ s t = false).
Proof.
  move => s t.
  elim (equ s t).
  by left.
  by right.
Qed.

Lemma minimal_section S (cnt : nat -> S) (equ : S -> S -> bool):
  (F2MF cnt) is_surjective -> (forall s s', is_true (equ s s') <-> (s = s'))
    -> exists sec: S -> nat, forall s, cnt (sec s) = s /\ (forall m, m < sec s -> cnt m <> s).
Proof.
  move => sur eprop.
  set R := fun s n => cnt n = s /\ (forall m, m < n -> cnt m <> s).
  have: forall s, exists n, R s n.
  - move => s.
    move: (sur s) => [m] mprop.
    set n := fix n m k:= match k with
      | 0 => m
      | S k' => if equ (cnt (m - (k'.+1))) s then (m-(k'.+1)) else n m k'
    end.

    have: forall k, cnt (n m k) = s.
    - elim => //.
      move => n0 ih /=.
      set l:=m - n0.+1.
      case: (dec equ (cnt l) s) => eq /=.
      - replace (equ (cnt l) s) with true => //.
        - move: (eprop (cnt l) s) => [temp _].
          by rewrite (temp eq).
      - by rewrite eq.
    move => prp.

    have: forall k k', k'<= m -> m <= (k' + k)%coq_nat -> (cnt k' = s -> n m k <= k').
    - elim.
      - move =>k' k'u k'l eq.
        rewrite (PeanoNat.Nat.add_0_r k') in k'l.
        case: (PeanoNat.Nat.eq_dec m 0).
        - move => me0.
          rewrite me0 /=.
          apply le_0_n.
        move => neq.
        move: (PeanoNat.Nat.zero_or_succ m).
        case.
        - move => a.
          by exfalso.
        by move => [] k succ.
      move => k ih k' k'u k'l eq /=.
      have: (m - k.+1)%coq_nat <= k'.
      - rewrite -(PeanoNat.Nat.add_0_r k').
        rewrite (Minus.minus_diag_reverse k.+1).
        rewrite (PeanoNat.Nat.add_sub_assoc).
        - by apply PeanoNat.Nat.sub_le_mono_r.
        done.
      move => k'2.
      case (dec equ (cnt (m-k.+1)) s).
      - move => true.
        by rewrite true.
      move => false.
      rewrite false.
      apply ih => //.
      set l:=(m - k.+1)%coq_nat.
      have: (k' + k.+1 <> m).
        move => meq.
        rewrite PeanoNat.Nat.add_comm in meq.
        move: (PeanoNat.Nat.add_sub_eq_l m k.+1 k' meq) => neq.
        rewrite -neq in eq.
        move: (eprop (cnt l) s) => [t1 t2].
        move: (t2 eq).
        by rewrite false.
      move: (PeanoNat.Nat.lt_eq_cases m (k'+k.+1)%coq_nat) => [te1 _] beq.
      move: (te1 k'l).
      case.
      - move => ineq.
        rewrite -plus_n_Sm in ineq.
        by apply Lt.lt_n_Sm_le.
      move => keq.
      by exfalso; by apply beq.
    move => eqk.
  
    exists (n m m).
    split.
    - by apply (prp m).
    move => m0 ineq eq.
    have: m0 < m.
    - apply: (PeanoNat.Nat.lt_le_trans m0 (n m m) m) => //.
      apply (eqk m m) => //.
      by apply (Plus.le_plus_l m m).
    move => ineq2.
    move: ineq.
    apply Lt.le_not_lt.
    - - apply eqk.
    - by apply PeanoNat.Nat.lt_le_incl.
      by apply (Plus.le_plus_r m0 m).
    done.
  move => cond.
  move: ((@choice (S) (nat) R) cond) => [sec] issec.
  by exists sec.
Qed.

Lemma U_is_universal S T S' T' (F:(S -> T) ->> (S' -> T')):
  (exists cnt: nat -> S, (F2MF cnt) is_surjective)
    -> (exists equ: S -> S -> bool, forall s s', is_true (equ s s') <-> (s = s'))
    -> (exists t: T, True)
    -> (exists t':T', True)
    -> F is_continuous -> exists psi, forall phi, (exists Fphi, F phi Fphi)
      -> forall (Fphi: S'->T') a, exists n, U n psi phi a = Some (Fphi a).
Proof.
  move => [cnt sur] [equ] eprop [t _] [t' _] cont.

  set size := (fix size K := match K with
    | nil => 0
    | cons s K' => max ((sec s).+1) (size K')
  end).
  have: forall K phi (psi:S -> T),
    (forall m: nat, m < size K -> phi (cnt m) = psi (cnt m))
      -> (phi and psi coincide_on K).
  - elim => //.
    move => a K ih phi psi H.
    split.
    - replace a with (cnt (sec a)) by apply (issec a).
      apply: (H (sec a)).
      move: (PeanoNat.Nat.le_succ_l (sec a) ((size (a :: K)))) => [lt_max_l _].
      apply: lt_max_l.
      by apply: (PeanoNat.Nat.le_max_l).
    apply ih => m si.
    apply H.
    apply (PeanoNat.Nat.lt_le_trans m (size K)) => //.
    apply PeanoNat.Nat.le_max_r.
  move => init.
  set R := fun phi psi => ((exists psi', F phi psi') -> F phi psi).
  have: forall phi, exists psi, R phi psi.
  - move => phi.
    case: (classic (exists psi' , F phi psi')).
    - move => [psi prop].
      by exists psi.
    move => false.
    by exists (fun a => t').
  move => cond.
  move: ((@choice ((S -> T)) (S' -> T') R) cond) => [Ff] Fprop.
  rewrite /R /= in Fprop.
  move: t' R cond => _ _ _.

  set R := fun p n => forall (psi : S -> T), (forall m,
      m < n -> (p.1) (cnt m) = psi (cnt m)) ->
      forall Fphi : S' -> T', F p.1 Fphi -> (exists Fpsi, F p.1 Fpsi) /\
        (forall Fpsi, F psi Fpsi -> Fphi p.2 = Fpsi p.2).
  have: forall p, exists n, R p n.
  - move => p.
    move: (cont p.1 p.2) => [L] cond.
    exists (size L).
    move => psi kack Fpsi v1.
    split.
    - by exists Fpsi.
    move => Fphi v2.
    apply (cond psi) => //.
    by apply (init L p.1 psi).
    move => cond.
    move: ((@choice ((S->T)*S') (nat) R) cond) => [f] fprop.
    rewrite /R /= in fprop.
    move: R cond => _ _.
    set R := (fun (L : S*list(S * T)) (b:T) =>
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
  move: ((@choice (S*list(S * T)) (T) R) cond) => [temp] tprop.
  rewrite /R /= in tprop.
  move: R cond => _ _.

  set R := (fun (L : list(S * T)) (psi:S -> T) =>
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
    move: ((@choice (list(S * T)) (S -> T) R) cond) => [phi'] phiprop.
    rewrite /R /= in phiprop.
    move: R cond => _ _.
    set psiF := (fun L =>
      if
        (leq (f (phi' L.2,L.1)) (length L.2))
      then
        (inr (Ff (phi' L.2) L.1))
      else
        (inl (cnt (length L.2).+1))).
    exists psiF.
    move => phi [Fphi v] Fphi' s'.
    move: (cont phi s') => [L] prop.
    exists (size L).
    have: forall m, m = size L -> U m psiF phi s' = Some (Fphi' s').
    elim.
    rewrite /U /U' /psiF /=.
    move => eq.
    have: f(phi' nil, s') <= 0.
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