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

Section SECTIONS.
Context Q (cnt: nat -> Q).

Definition is_min_sec (sec : Q -> nat) :=
  (forall s, cnt (sec s) = s) /\ forall s,(forall m, cnt m = s -> sec s <= m).

Notation "sec 'is_minimal_section'" := (is_min_sec sec) (at level 2).

Definition is_sur S T f:=
	forall (t: T), exists (s: S), f s = t.
Notation "f 'is_surjective'" := (is_sur f) (at level 2).

Lemma minimal_section:
  cnt is_surjective -> exists sec, sec is_minimal_section.
Proof.
  move => sur.
  set R := fun s n => cnt n = s /\ (forall m, cnt m = s -> n <= m).
  have: forall s, exists n, R s n
  	by move => s; move: (@well_order_nat (fun n => cnt n = s) (sur s)) => [] n [np1 np2]; exists n.
  move => cond.
  move: (choice R cond) => [sec] sprop.
  by exists sec; split => s;move: (sprop s) => [a b].
Qed.
End SECTIONS.

Notation "sec 'is_section_of' cnt" := (forall s, cnt (sec s) = s) (at level 2).
Notation "sec 'is_minimal_section_of' cnt" := (is_min_sec cnt sec) (at level 2).


Section INITIAL_SEGMENTS_AND_SIZES.
Context Q (cnt: nat -> Q).

Fixpoint in_seg m := match m with
  | 0 => nil
  | S n => cons (cnt n) (in_seg n)
end.

Lemma initial_segments A (phi psi : Q -> A):
  forall m, (forall n, n < m -> phi (cnt n) = psi (cnt n))
  	<-> phi and psi coincide_on (in_seg m).
Proof.
  split; last first.
  - move: m.
    elim.
    - move => coin n false.
    	exfalso; lia.
    move => n ihn.
    replace (in_seg n.+1) with (cons (cnt n) (in_seg n)) by trivial.
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

Context (sec: Q -> nat).

Fixpoint size K := match K with
  | nil => 0
  | cons s K' => max (sec s).+1 (size K')
end.

Lemma size_app:
	forall L K, size (L ++ K) = max (size L) (size K).
Proof.
elim => //.
move => a L ih K.
replace ((a :: L) ++ K) with ((a :: L)%SEQ ++ K)%list by trivial.
rewrite -List.app_comm_cons.
replace (size (a :: (L ++ K)%list))
	with (max ((sec a).+1) (size (L ++ K))) by trivial.
rewrite (ih K).
apply: PeanoNat.Nat.max_assoc.
Qed.

Lemma list_size A:
  sec is_section_of cnt
    -> forall K (phi psi : Q -> A), phi and psi coincide_on (in_seg (size K))
    -> (phi and psi coincide_on K).
Proof.
  move => issec.
  elim => //.
  move => a L IH phi psi ci'.
  move: IH (IH phi psi) => _ IH.
  move: (initial_segments phi psi (size (cons a L))) => [_ d2].
  move: d2 (d2 ci') => _ ci.
  have: (sec a < size (a :: L)).
  - replace (size (a :: L)) with (max (sec a).+1 (size L)) by trivial; lia.
  move => ineq.
  split.
  - replace a with (cnt (sec a)) by apply (issec a).
    by apply: (ci (sec a)).
  apply (IH).
  move: (initial_segments phi psi (size L)) => [d1 _].
  apply d1 => n ine.
  apply ci.
  apply: (PeanoNat.Nat.lt_le_trans n (size L) (size (a :: L))) => //.
  replace (size (a :: L)) with (max (sec a).+1 (size L)) by trivial; lia.
Qed.

Lemma size_in_seg:
	is_min_sec cnt sec -> forall n, size (in_seg n) <= n.
Proof.
move => [issec min].
elim => // n ih.
replace (in_seg n.+1) with (cons (cnt n) (in_seg n)) by trivial.
replace (size (cnt n :: in_seg n))
	with (max (sec (cnt n)).+1 (size (in_seg n))) by trivial.
have eq: (cnt n = cnt n) by trivial.
by move: (min (cnt n) n eq) => leq; lia.
Qed.
End INITIAL_SEGMENTS_AND_SIZES.
Notation "f 'is_surjective'" := (is_sur f) (at level 2).
