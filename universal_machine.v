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

Section CONTINUITY.
Context Q A Q' A' (F: (Q-> A) ->> (Q'-> A')).

Fixpoint equal_on Q A (phi psi : Q -> A) L :=
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
Lemma cont_to_sing: is_cont F -> F is_single_valued.
Proof.
  move => cont phi Fpsi Fpsi' _ [v1 v2].
  apply functional_extensionality => a.
  move: cont (cont phi a) => _ [L] cont.
  have: (forall K, phi and phi coincide_on K) by elim.
  move => equal.
  move: ((cont phi (equal L) Fpsi') v2) => [[Fphi]] v cond.
  by rewrite ((cond Fpsi) v1).
Qed.

Definition iscont (G: (Q-> A) -> Q' -> A') :=
  forall phi (q': Q'), exists (L : list Q), forall psi,
    phi and psi coincide_on L -> G phi q' = G psi q'.

Lemma continuity (G: (Q-> A) -> Q' -> A') :  iscont G <-> is_cont (F2MF G).
Proof.
  split.
  - move => cont psi s'.
    move: cont (cont psi s') => _ [L cond].
    exists L => phi coin Fpsi iv.
    split.
    - by exists (fun s' => G phi s').
    move => Fphi iv'.
    rewrite -iv -iv'.
    by apply (cond phi).
  move => cont phi s'.
  move: cont (cont phi s') => _ [L cond].
  exists L => psi coin.
  have: forall psi', (F2MF G psi' (G psi')) by trivial.
  move => triv.
  move: cond (cond psi coin (G phi) (triv phi)) => _ [] [Fphi] v cond.
  by apply: (cond (fun s' => G psi s')).
Qed.

Fixpoint U'
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

Definition U n psi phi a :=
U' n.+1 psi phi (a,nil).
(* This is what I want to prove to be a universal machine. *)

From Coq.micromega Require Import Psatz.
Open Scope coq_nat_scope.

Section MINIMIZATION.
(* The code from this section was provided by Vincent *)
Context (p: nat -> bool) (bound: nat) (bound_ok: p bound).

Fixpoint searchU m k : nat :=
  match k with
  | 0 => m
  | k'.+1 => let n := m - k in if p n then n else searchU m k'
  end.

Lemma searchU_correct m k :
  p m -> p (searchU m k).
Proof.
move => hm.
by elim: k => // n ih /=; case: ifP.
Qed.

Lemma searchU_le m k :
  le (searchU m k) m.
Proof.
elim: k => // n ih /=; case: ifP => // _.
rewrite /subn /subn_rec; lia.
Qed.

Lemma searchU_minimal m k :
  (forall n, n < m - k -> ~ p n) ->
  forall n, n < searchU m k -> ~ p n.
Proof.
elim: k.
- move => h n /=; rewrite -(subn0 m); exact: h.
move => k ih h n /=; case: ifP.
- move => _; exact: h.
move => hk; apply: ih => i hi.
case: (i =P m - k.+1).
- by move ->; rewrite hk.
move => hik; apply: h; move: hi hik.
rewrite /subn /subn_rec; lia.
Qed.

End MINIMIZATION.

Require Import ClassicalChoice.

Lemma well_order_nat (P : nat -> Prop):
	(exists n, P n) -> exists n, P n /\ forall m, P m -> n <= m.
Proof.
	set R:= fun n b => P n <-> is_true b.
	have: forall n, exists b, R n b.
	-	move => n.
		case: (classic (P n)) => pn.
		exists true.
		by split.
		exists false.
		by split.
	move => cond.
	move: cond (choice R cond) => _ [p] prop.
	rewrite /R in prop;move: R => _.
  set n := searchU p.
	move => [m] Pm.
  exists (n m m).

	split.
  - apply: (prop (n m m)).2 (@searchU_correct p m m ((prop m).1 Pm)).
  - have: forall k, k< n m m -> ~ p k.
    apply: (@searchU_minimal p m m).
    move => k; rewrite subnn; lia.
  move => neg k Pk.
  case: (leqP (n m m) k) => // /leP stuff //.
  elim: (neg k) => //.
  by apply ((prop k).1 Pk).
Qed.

Lemma minimal_section (cnt : nat -> Q):
  (F2MF cnt) is_surjective ->
    exists sec, (forall s, cnt (sec s) = s) /\ forall s,(forall m, cnt m = s -> sec s <= m).
Proof.
  move => sur.
  set R := fun s n => cnt n = s /\ (forall m, cnt m = s -> n <= m).
  have: forall s, exists n, R s n.
  - move => s.
  	move: (@well_order_nat (fun n => cnt n = s) (sur s)) => [] n [np1 np2].
  	by exists n.
  move => cond.
  move: (choice R cond) => [sec] sprop.
  exists sec.
  split => s.
  	by move: (sprop s) => [a _].
	by move: (sprop s) => [ _ a].
Qed.

Definition is_min_sec S (cnt: nat -> S) (sec : S -> nat) :=
  (forall s, cnt (sec s) = s) /\ forall s,(forall m, m < sec s -> cnt m <> s).
Notation "sec 'is_minimal_section_of' cnt" := (is_min_sec S cnt sec) (at level 2).

Fixpoint in_seg S (cnt: nat -> S) m := match m with
  | 0 => cons (cnt 0) nil
  | S n => cons (cnt n.+1) (in_seg cnt n)
end.

Lemma initial_segments S T (cnt: nat -> S) (phi psi : S -> T):
  forall m, (forall n, n <= m -> phi (cnt n) = psi (cnt n)) <-> phi and psi coincide_on (in_seg cnt m).
Proof.
  split; last first.
  - move: m.
    elim.
    - move => [p0 _] n nl0.
      by replace n with 0 by lia.
    move => n ihn.
    replace (in_seg cnt n.+1) with (cons (cnt n.+1) (in_seg cnt n)) by trivial.
    case.
    move => eqp1 stuff n0.
    move: stuff ihn (ihn stuff) => _ _ ihn nln0.
    case: (classic (n0 = n.+1)).
    - move => kack.
      by rewrite kack.
    move => neq.
    apply ihn;lia.
  move: m.
  elim.
  - move => stuff /=.
    split; last first => //.
    by apply: (stuff 0).
  move => n ihn ass.
    split.
    - by apply (ass n.+1).
    apply ihn => n0 ineq.
    apply (ass n0);lia.
Qed.

Fixpoint size S (sec: S -> nat) K := match K with
  | nil => 0
  | cons s K' => max ((sec s).+1) (size sec K')
end.

Lemma list_size S T (cnt : nat -> S) (sec: S -> nat):
  (forall s, cnt (sec s) = s)
    -> forall K (phi psi : S -> T), phi and psi coincide_on (in_seg cnt (size sec K)) -> (phi and psi coincide_on K).
Proof.
  move => issec.
  elim => //.
  move => a L IH phi psi ci'.
  move: IH (IH phi psi) => _ IH.
  move: (initial_segments cnt phi psi (size sec (cons a L))) => [_ d2].
  move: d2 (d2 ci') => _ ci.
  have: (sec a <= size sec (a :: L)).
  - replace (size sec (a :: L)) with (max (sec a).+1 (size sec L)) by trivial; lia.
  move => ineq.
  split.
  - replace a with (cnt (sec a)) by apply (issec a).
    by apply: (ci (sec a)).
  apply (IH).
  move: (initial_segments cnt phi psi (size sec L)) => [d1 _].
  apply d1 => n ine.
  apply ci.
  apply: (PeanoNat.Nat.le_trans n (size sec L) (size sec (a :: L))) => //.
  replace (size sec (a :: L)) with (max (sec a).+1 (size sec L)) by trivial;lia.
Qed.

Inductive one := star.

Lemma example: is_cont (fun phi Fphi => phi (Fphi star) = 0 /\ forall m, m < Fphi star -> phi m <> 0).
Proof.
  move => phi star.
  set cnt := (fun n:nat => n).
  set sec := (fun n:nat => n).
  set L := in_seg cnt.
  replace CONTINUITY.star with star; last first.
  - by elim star.
  case: (classic (exists m, phi m = 0)); last first.
  - move => false.
    exists nil => psi _ fp1 [v1] cond.
    exfalso; apply false.
    by exists (fp1 star).
  move => [m me0].
  exists (L m).
  move => psi pep.
  move: (initial_segments cnt phi psi m) => [_ cond].
  move: cond pep (cond pep) => _ _ cond Fphi [v1 c1].
  have: m >= Fphi star.
  - apply NNPP => ge1.
    apply (c1 m).
    - by apply Compare_dec.not_ge.
    replace (psi m) with (phi m) => //.
    by apply (cond m).
  move => ge1.
  move: ge1 (cond (Fphi star) ge1).
  rewrite v1.
  move => zero1.
  split.
  - exists (fun star => Fphi star).
    split => //.
    move => m0 co.
    replace (psi m0) with (phi m0).
    - by apply (c1 m0).
    apply (cond m0); lia.
  move => Fpsi [v2 c2].
  have: m >= Fpsi star.
  - apply NNPP => ge2.
    apply (c2 m);last first.
    replace (psi m) with (phi m) =>//.
    - by apply (cond m).
    by apply Compare_dec.not_ge.
  move => ge2.
  move: ge2 (cond (Fpsi star) ge2) => _.
  rewrite v2 => zero2.
  have: (~ Fphi star > Fpsi star).
  - move => gt1.
    by apply (c1 (Fpsi star)).
  move => gt1.
  have: (~ Fpsi star > Fphi star).
  - move => gt2.
    by apply (c2 (Fphi star)).
  move => gt2.
  apply NNPP=> neq.
  move: (PeanoNat.Nat.lt_trichotomy (Fphi star) (Fpsi star)) => //.
  case => //.
  by case.
Qed.
(* This was a pain to prove... Why? *)

Definition is_mod S T S' T' (F:(S -> T) ->> (S' -> T')) mf :=
  forall phi s', forall (psi : S -> T), phi and psi coincide_on (mf phi s') ->
    forall Fphi : S' -> T', F phi Fphi -> (exists Fpsi, F psi Fpsi) /\
      (forall Fpsi, F psi Fpsi -> Fphi s' = Fpsi s').
Notation "mf 'is_modulus_of' F" := (is_mod F mf) (at level 2).

Lemma minimal_mod_function (sec : Q -> nat):
  F is_continuous
    -> exists mf, mf is_modulus_of F /\ forall nf, nf is_modulus_of F -> forall phi q', size sec (mf phi q') <= size sec (nf phi q').
Proof.
  move => cont.
  set P := fun phiq L => forall psi, phiq.1 and psi coincide_on L
    -> forall Fphi, F phiq.1 Fphi -> (exists Fpsi, F psi Fpsi) /\
      (forall Fpsi, F psi Fpsi -> Fphi phiq.2 = Fpsi phiq.2).
  set R := fun phiq L => P phiq L /\ forall K, P phiq K -> size sec L <= size sec K.
  have: forall phiq, exists L, R phiq L.
  - move => phiq.
  	have: exists n, exists L, P phiq L/\ size sec L = n.
  		move: (cont phiq.1 phiq.2) => [L] Lprop.
  		exists (size sec L).
  		by exists L.
  	move => cond.
  	move: (@well_order_nat (fun n => exists L, P phiq L/\ size sec L = n) cond) => [n] [ [L] [Lprop Leqn]] nprop.
  	exists L.
  	split.
  		apply: Lprop.
  	rewrite -Leqn in nprop.
  	move => K Pfi.
 		apply: (nprop (size sec K)).
 		by exists K.
 	move => cond.
 	move: (@choice ((Q -> A)*Q') (list Q) R cond) => [mf] mfprop.
 	rewrite /R in mfprop.
 	move: R cond => _ _.
 	exists (fun phi q' => mf (phi, q')).
 	split.
 		move => phi q' psi.
 		apply (mfprop (phi, q')).
 	move => nf mod phi q'.
 	move: (mfprop (phi,q')) => [_ b].
 	apply: (b (nf phi q')).
 	apply: mod.
Qed.

Lemma U_is_universal:
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
    have: (size sec (mf (phi' [::]) q') <= 0).
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