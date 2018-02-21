From Coq.micromega Require Import Psatz.
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions continuity.
Require Import ClassicalChoice.
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

Lemma well_order_nat (P : nat -> Prop):
	(exists n, P n) -> exists n, P n /\ forall m, P m -> n <= m.
Proof.
set R:= fun n b => P n <-> is_true b.
have cond: forall n, exists b, R n b.
	move => n.
	by case: (classic (P n)) => pn; [exists true|exists false]; split.
move: cond (choice R cond) => _ [p] prop.
rewrite /R in prop;move: R => _.
set n := searchU p.
move => [m] Pm.
exists (n m m); split.
	apply: (prop (n m m)).2 (@searchU_correct p m m ((prop m).1 Pm)).
	have neg: forall k, k< n m m -> ~ p k.
    apply: (@searchU_minimal p m m).
    by move => k; rewrite subnn; lia.
	move => k Pk.
  case: (leqP (n m m) k) => // /leP stuff //.
  by elim: (neg k) => //; apply ((prop k).1 Pk).
Qed.

Section SECTIONS.
Definition is_sur S T f:=
	forall (t: T), exists (s: S), f s = t.
Notation "f '\is_surjective'" := (is_sur f) (at level 2).

Context Q (cnt: nat -> Q) (sur: cnt \is_surjective).

Definition is_min_sec (sec : Q -> nat) :=
  (forall s, cnt (sec s) = s) /\ forall s,(forall m, cnt m = s -> sec s <= m).

Notation "sec '\is_minimal_section'" := (is_min_sec sec) (at level 2).

Lemma minimal_section:
  exists sec, sec \is_minimal_section.
Proof.
set R := fun s n => cnt n = s /\ (forall m, cnt m = s -> n <= m).
have cond: forall s, exists n, R s n
	by move => s; move: (@well_order_nat (fun n => cnt n = s) (sur s)) => [] n [np1 np2]; exists n.
move: (choice R cond) => [sec] sprop.
by exists sec; split => s;move: (sprop s) => [a b].
Qed.
End SECTIONS.

Notation "sec '\is_section_of' cnt" := (forall s, cnt (sec s) = s) (at level 2).
Notation "sec '\is_minimal_section_of' cnt" := (is_min_sec cnt sec) (at level 2).

Section INITIAL_SEGMENTS_AND_SIZES.
Context Q (cnt: nat -> Q).

Fixpoint in_seg m := match m with
  | 0 => nil
  | S n => cons (cnt n) (in_seg n)
end.

Lemma length_inseg n : length (in_seg n) = n.
Proof. by elim: n => // n ih; rewrite -{2}ih. Qed.

Lemma mon_inseg q n m:
	  n <= m -> List.In q (in_seg n) -> List.In q (in_seg m).
Proof.
elim: m => [l0|m ih ass].
  by rewrite (_ : n = 0) //; lia.
have [/ih H1 H2|<- //] := (PeanoNat.Nat.le_succ_r n m).1 ass.
by right; apply: H1.
Qed.

Lemma inseg_ex a:
	forall n, List.In a (in_seg n.+1) <-> exists m, m <= n /\ cnt m = a.
Proof.
elim.
	split => /=.
		by case => ass //; exists 0.
	move => [] m [] eq p; left.
	have m0: m=0 by lia.
	by rewrite -m0.
move => n ih.
case (classic (a = cnt (S n))) => ass.
	split => ass'; [by exists (S n)|by left].
split.
	move => [] stuff.
		by exfalso; apply ass.
	move: (ih.1 stuff) => [] m [] ineq eq.
	exists m.
	by split; first by lia.
move => [] m [] ineq eq.
right.
apply ih.2.
exists m.
split => //.
case: (classic (m = S n)) => ass'.
	by exfalso; apply ass; rewrite -ass'.
by lia.
Qed.

Lemma inseg_coin A (phi psi : Q -> A) m:
  	(forall n, n < m -> phi (cnt n) = psi (cnt n))
  	<->
  	phi \and psi \coincide_on (in_seg m).
Proof.
split.
  move: m; elim => // n ihn ass.
  split; first by apply (ass n).
  apply ihn => n0 ineq.
  by apply (ass n0);lia.
move: m.
elim; first by move => coin n false; exfalso; lia.
move => n ihn.
replace (in_seg n.+1) with (cons (cnt n) (in_seg n)) by trivial.
move => coin n0 ltn.
case: (classic (n0 = n)) => eq.
	by rewrite eq; apply coin.1.
apply ihn.
  by apply coin.2.
by lia.
Qed.

Context (sec: Q -> nat).

Lemma inseg a:
	is_min_sec cnt sec -> forall n, List.In a (in_seg n.+1) <-> sec a <= n.
Proof.
move => issec n.
split => ass.
	move: ((inseg_ex a n).1 ass) => [] m [] ineq eq.
	suffices: sec a <= m by lia.
	by apply: (issec.2 a m).
apply: ((inseg_ex a n).2).
exists (sec a).
split => //.
by apply (issec.1 a).
Qed.

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
  sec \is_section_of cnt
    -> forall K (phi psi : Q -> A), phi \and psi \coincide_on (in_seg (size K))
    -> (phi \and psi \coincide_on K).
Proof.
move => issec.
elim => //.
move => a L IH phi psi ci'.
specialize (IH phi psi).
have [_ d2]:= (inseg_coin phi psi (size (cons a L))).
move: d2 (d2 ci') => _ ci.
have ineq: (sec a < size (a :: L)).
	replace (size (a :: L)) with (max (sec a).+1 (size L)) by trivial; lia.
split; first by replace a with (cnt (sec a)) by apply (issec a); apply: (ci (sec a)).
apply (IH).
have [d1 _]:= (inseg_coin phi psi (size L)).
apply d1 => n ine.
apply ci.
apply: (PeanoNat.Nat.lt_le_trans n (size L) (size (a :: L))) => //.
by replace (size (a :: L)) with (max (sec a).+1 (size L)) by trivial; lia.
Qed.

Lemma inseg_sec a:
	is_min_sec cnt sec -> List.In a (in_seg (sec a).+1).
Proof.
move => ims; apply/ (inseg a) => //.
Qed.

Lemma size_inseg:
	is_min_sec cnt sec -> forall n, size (in_seg n) <= n.
Proof.
move => [issec min].
elim => // n ih.
replace (in_seg n.+1) with (cons (cnt n) (in_seg n)) by trivial.
replace (size (cnt n :: in_seg n)) with (max (sec (cnt n)).+1 (size (in_seg n))) by trivial.
have eq: (cnt n = cnt n) by trivial.
by move: (min (cnt n) n eq) => leq; lia.
Qed.

Lemma inseg_size a K:
	is_min_sec cnt sec -> List.In a K -> List.In a (in_seg (size K).+1).
Proof.
move => ims listin.
apply/ (inseg a) => //.
move: K a listin.
elim => // a K ih a' listin.
replace (size (a::K)) with (max (sec a).+1 (size K)) by trivial.
suffices: sec a' <= (sec a).+1 \/ sec a' <= size K by lia.
case: listin => ass.
	by left; rewrite ass; lia.
by right; apply ih.
Qed.
End INITIAL_SEGMENTS_AND_SIZES.
Notation "f '\is_surjective'" := (is_sur f) (at level 2).