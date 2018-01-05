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
          forall Fphi Fpsi : S' -> T', F phi Fphi -> F psi Fpsi -> Fphi s' = Fpsi s'.
Notation "F 'is_continuous'" := (is_cont F) (at level 2).

Require Import FunctionalExtensionality.
Lemma cont_to_sing (S T S' T' : Type) F: @is_cont S T S' T' F -> F is_single_valued.
Proof.
  move => cont phi psi psi' _ [psivphi psi'vphi].
  apply functional_extensionality => a.
  move: cont (cont phi a) => _ [L] cont.
  have: (forall K, phi and phi coincide_on K).
  by elim.
  move => equal.
  by apply: (cont phi (equal L) psi psi').
Qed.

Definition iscont (S T S' T': Type) (F: (S-> T) -> S' -> T') :=
  forall phi (s': S'), exists (L : list S), forall psi,
    phi and psi coincide_on L -> F phi s' = F psi s'.

Lemma continuity S T S' T' (F: (S-> T) -> S' -> T') :  iscont F <-> is_cont (F2MF F).
Proof.
  split.
  - move => cont phi s'.
    move: cont (cont phi s') => _ [L cond].
    exists L => psi coin Fphi Fpsi iv iv'.
    rewrite -iv -iv'.
    by apply (cond psi).
  - move => cont phi s'.
    move: cont (cont phi s') => _ [L cond].
    exists L => psi coin. 
    by apply: (cond psi coin (F phi) (F psi)).
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
U' n psi phi (a,nil).
(* This is what I want to prove to be a universal machine. *)

Require Import ClassicalChoice FunctionalExtensionality.

Inductive one := star.

Local Open Scope coq_nat_scope.

Definition F phi Fphi := phi (Fphi star) = 0 /\ forall m, m < Fphi star -> phi m <> 0.

Lemma example: is_cont F.
Proof.
  move => phi star.
  set L := fix L m := match m with
    | 0 => cons 0 nil
    | S n => cons (S n) (L n)
  end.
  case: (classic (exists m, phi m = 0)); last first.
  - move => false.
    exists nil => psi _ fp1 fp2 [v1 c1] .
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
      move: cond pep (cond m pep) => _ _ cond Fphi Fpsi [v1 c1] [v2 c2].
      have: m >= Fphi Top.star.
      apply NNPP => ge1.
      apply (c1 m);last first.
      replace (psi m) with (phi m) =>//.
      by apply (cond m).
      apply Compare_dec.not_ge.
      done.
      move => ge1.
      move: ge1 (cond (Fphi Top.star) ge1) => _.
      rewrite v1.
      move => zero1.
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

Lemma U_is_universal S T S' T' (F:(S -> T) ->> (S' -> T')):
  (exists t: T, True) -> (exists t':T', True) -> F is_continuous ->
    exists psi, forall phi Fphi, F phi Fphi -> forall a, exists n, U n psi phi a = Some (Fphi a).
Proof.
  move => [t _] [t' _] cont.
  set R := fun phi psi => ((exists psi', F phi psi') -> F phi psi).
  have: forall phi, exists psi, R phi psi.
  move => phi.
  case: (classic (exists psi' , F phi psi')).
  - move => [psi prop].
    by exists psi.
  - move => false.
    by exists (fun a => t').
  move => cond.
  move: ((@choice ((S -> T)) (S' -> T') R) cond) => [Ff] Fprop.
  rewrite /R /= in Fprop.
  move: t' R cond => _ _ _.
  - set R := fun p L => forall psi : S -> T,
      (p.1) and psi coincide_on L ->
      forall Fphi Fpsi : S' -> T',
      F p.1 Fphi -> F psi Fpsi -> Fphi p.2 = Fpsi p.2.
    have: forall p, exists L, R p L.
    move => p.
    apply: cont p.1 p.2.
    move => cond.
    move: ((@choice ((S->T)*S') (list(S)) R) cond) => [f] fprop.
    rewrite /R /= in fprop.
    move: R cond => _ _.
    set R := (fun (L : S*list(S * T)) (b:T) => 
      forall c, List.In (L.1,c) L.2 -> List.In (L.1,b) L.2).
    have : forall L, exists b, R L b.
    move => L.
    case: (classic (exists c, List.In (L.1, c) L.2)).
    - move => [c] inlist.
      by exists c.
    - move => false.
      exists t.
      move => c inlist.
      exfalso.
      apply: false.
      by exists c.
    move => cond.
    move: ((@choice (S*list(S * T)) (T) R) cond) => [phi'] phiprop.
    rewrite /R /= in phiprop.
    move: R cond => _ _.
    set R := (fun (L : (list S) *  list(S * T)) (b : option S) =>
      match b with
        | None => forall c, List.In c L.1 -> List.In c (map fst L.2)
        | Some s => List.In s L.1 /\ ~ List.In s (map fst L.2)
      end).
    have : forall L, exists b, R L b.
    - move => L.
      case: (classic (exists s, List.In s L.1 /\ ~ List.In s (map fst L.2))).
      - move => [s] [list false].
        exists (Some s) => //=.
      - move => false.
        exists None => //=.
        move => s list.
        apply: NNPP.
        move => notnot.
        apply: false.
        by exists s.
    move => cond.
    move: ((@choice ((list S)*list(S * T)) (option S) R) cond) => [cf] cfprop.
    rewrite /R /= in cfprop.
    move: R cond => _ _.
    set psiF := (fun L => match (cf (f (fun s => phi' (s , L.2) , L.1), L.2)) with
      | Some s => inl s
      | None => inr (Ff (fun s => phi' (s, L.2)) L.1)
    end).
    exists psiF.
    move => phi Fphi v s'.
    apply: NNPP.
    move => false.
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