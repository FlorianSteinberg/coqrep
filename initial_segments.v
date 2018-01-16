From Coq.micromega Require Import Psatz.
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions continuity.
Open Scope coq_nat_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Definition is_min_sec Q (cnt: nat -> Q) (sec : Q -> nat) :=
  (forall s, cnt (sec s) = s) /\ forall s,(forall m, cnt m = s -> sec s <= m).
Notation "sec 'is_minimal_section_of' cnt" := (is_min_sec cnt sec) (at level 2).

Lemma minimal_section Q (cnt : nat -> Q):
  (F2MF cnt) is_surjective ->
    exists sec, sec is_minimal_section_of cnt.
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

Fixpoint in_seg S (cnt: nat -> S) m := match m with
  | 0 => nil
  | S n => cons (cnt n) (in_seg cnt n)
end.

Lemma initial_segments S T (cnt: nat -> S) (phi psi : S -> T):
  forall m, (forall n, n < m -> phi (cnt n) = psi (cnt n))
  	<-> phi and psi coincide_on (in_seg cnt m).
Proof.
  split; last first.
  - move: m.
    elim.
    - move => coin n false.
    	exfalso; lia.
    move => n ihn.
    replace (in_seg cnt n.+1) with (cons (cnt n) (in_seg cnt n)) by trivial.
    move => coin n0 ltn.
    case: (classic (n0 = n)).
    	move => eq.
    	rewrite eq.
    	apply coin.1.
    move => neq.
    apply ihn.
    	apply coin.2.
    lia.
  move: m.
  elim => //.
  move => n ihn ass.
    split.
    - by apply (ass n).
    apply ihn => n0 ineq.
    apply (ass n0);lia.
Qed.

Fixpoint size S (sec: S -> nat) K := match K with
  | nil => 0
  | cons s K' => max (sec s).+1 (size sec K')
end.

Lemma size_app S (sec: S -> nat):
	forall L K, size sec (L ++ K) = max (size sec L) (size sec K).
Proof.
elim => //.
move => a L ih K.
replace ((a :: L) ++ K) with ((a :: L)%SEQ ++ K)%list by trivial.
rewrite -List.app_comm_cons.
replace (size sec (a :: (L ++ K)%list))
	with (max ((sec a).+1) (size sec (L ++ K))) by trivial.
rewrite (ih K).
apply: PeanoNat.Nat.max_assoc.
Qed.

Lemma size_in_seg S (cnt: nat -> S) (sec: S -> nat):
	is_min_sec cnt sec -> forall n, size sec (in_seg cnt n) <= n.
Proof.
move => [issec min].
elim => //.
move => n ih.
replace (in_seg cnt n.+1) with (cons (cnt n) (in_seg cnt n)) by trivial.
replace (size sec (cnt n :: in_seg cnt n))
	with (max (sec (cnt n)).+1 (size sec (in_seg cnt n))) by trivial.
	have: (cnt n = cnt n) by trivial.
	move => eq.
	move: (min (cnt n) n eq) => leq.
	lia.
Qed.

Lemma list_size S T (cnt : nat -> S) (sec: S -> nat):
  (forall s, cnt (sec s) = s)
    -> forall K (phi psi : S -> T), phi and psi coincide_on (in_seg cnt (size sec K))
    -> (phi and psi coincide_on K).
Proof.
  move => issec.
  elim => //.
  move => a L IH phi psi ci'.
  move: IH (IH phi psi) => _ IH.
  move: (initial_segments cnt phi psi (size sec (cons a L))) => [_ d2].
  move: d2 (d2 ci') => _ ci.
  have: (sec a < size sec (a :: L)).
  - replace (size sec (a :: L)) with (max (sec a).+1 (size sec L)) by trivial; lia.
  move => ineq.
  split.
  - replace a with (cnt (sec a)) by apply (issec a).
    by apply: (ci (sec a)).
  apply (IH).
  move: (initial_segments cnt phi psi (size sec L)) => [d1 _].
  apply d1 => n ine.
  apply ci.
  apply: (PeanoNat.Nat.lt_le_trans n (size sec L) (size sec (a :: L))) => //.
  replace (size sec (a :: L)) with (max (sec a).+1 (size sec L)) by trivial; lia.
Qed.

Definition is_min_mod Q A Q' A' (sec: Q -> nat) (F: (Q -> A) ->> (Q' -> A')) mf :=
	mf is_modulus_of F /\ forall phi q' K, (forall psi, phi and psi coincide_on K
    -> forall Fphi, F phi Fphi -> forall Fpsi, F psi Fpsi -> Fphi q' = Fpsi q') ->
     size sec (mf phi q') <= size sec K.

Notation "mf 'is_minimal_modulus_of' F 'wrt' sec" := (is_min_mod sec F mf) (at level 2).

Lemma minimal_mod_function Q A Q' A' (F: (Q -> A) ->> (Q' -> A')) (sec: Q -> nat):
  F is_continuous -> exists mf, mf is_minimal_modulus_of F wrt sec.
Proof.
  move => cont.
  set P := fun phiq L => forall psi, phiq.1 and psi coincide_on L
    -> forall Fphi, F phiq.1 Fphi -> forall Fpsi, F psi Fpsi -> Fphi phiq.2 = Fpsi phiq.2.
  set R := fun phiq L => P phiq L /\
  	(forall K, P phiq K -> size sec L <= size sec K).
  have: forall phiq, exists L, R phiq L.
  - move => phiq.
  	have: exists n, exists L, P phiq L/\ size sec L = n.
  		move: (cont phiq.1 phiq.2) => [L] Lprop.
  		exists (size sec L).
  		by exists L.
  	move => cond.
  	move: (@well_order_nat (fun n => exists L, P phiq L
  		/\ size sec L = n) cond) => [n] [ [L] [Lprop Leqn]] nprop.
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
 	move => phi q' K mod.
 	move: (mfprop (phi,q')) => [_ b].
 	apply: (b K).
 	move => psi coin Fphi FphiFphi Fpsi FpsiFpsi.
 	apply: (mod psi) =>//.
Qed.
