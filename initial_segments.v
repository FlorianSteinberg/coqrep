From Coq.micromega Require Import Psatz.
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions baire_space continuity.
Require Import ClassicalChoice.
Open Scope coq_nat_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "L '\is_sublist_of' K" := (forall q, List.In q L -> List.In q K) (at level 2).

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
Notation "f '\is_surjective'" := (is_sur f) (at level 2).
Notation "sec '\is_minimal_section_of' cnt" := (is_min_sec cnt sec) (at level 2).

Section INITIAL_SEGMENTS.
Context Q (cnt: nat -> Q).

Fixpoint in_seg m := match m with
  | 0 => nil
  | S n => cons (cnt n) (in_seg n)
end.

Lemma length_inseg n : length (in_seg n) = n.
Proof. by elim: n => // n ih; rewrite -{2}ih. Qed.

Lemma inseg_mon n m:
	  n <= m -> (in_seg n) \is_sublist_of (in_seg m).
Proof.
elim: m => [l0|m ih ass].
  by rewrite (_ : n = 0) //; lia.
have [/ih H1 H2|<- //] := (PeanoNat.Nat.le_succ_r n m).1 ass.
by right; apply: H1.
Qed.

Lemma inseg_ex a n:
	 List.In a (in_seg n) -> exists m, m < n /\ cnt m = a.
Proof.
elim: n => [ listin | n ih /= listin ]; first by trivial.
case: listin => [eq | listin ]; first by exists n; split.
by move: (ih listin) => [] m [ineq eq]; exists m; split; try lia.
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
	is_min_sec cnt sec -> forall n, List.In a (in_seg n) -> sec a < n.
Proof.
move => issec n listin.
move: (inseg_ex listin) => [] m [] ineq eq.
suffices: sec a <= m by lia.
by apply/ issec.2.
Qed.

Fixpoint max_elt K := match K with
  | nil => 0
  | cons s K' => max (sec s).+1 (max_elt K')
end.

Lemma melt_app:
	forall L K, max_elt (L ++ K) = max (max_elt L) (max_elt K).
Proof.
elim => //.
move => a L ih K.
replace ((a :: L) ++ K) with ((a :: L)%SEQ ++ K)%list by trivial.
rewrite -List.app_comm_cons.
replace (max_elt (a :: (L ++ K)%list))
	with (max ((sec a).+1) (max_elt (L ++ K))) by trivial.
rewrite (ih K).
apply: PeanoNat.Nat.max_assoc.
Qed.

Lemma list_melt A:
  sec \is_section_of cnt
    -> forall K (phi psi : Q -> A), phi \and psi \coincide_on (in_seg (max_elt K))
    -> (phi \and psi \coincide_on K).
Proof.
move => issec.
elim => //.
move => a L IH phi psi ci'.
specialize (IH phi psi).
have [_ d2]:= (inseg_coin phi psi (max_elt (cons a L))).
move: d2 (d2 ci') => _ ci.
have ineq: (sec a < max_elt (a :: L)).
	replace (max_elt (a :: L)) with (max (sec a).+1 (max_elt L)) by trivial; lia.
split; first by replace a with (cnt (sec a)) by apply (issec a); apply: (ci (sec a)).
apply (IH).
have [d1 _]:= (inseg_coin phi psi (max_elt L)).
apply d1 => n ine.
apply ci.
apply: (PeanoNat.Nat.lt_le_trans n (max_elt L) (max_elt (a :: L))) => //.
by replace (max_elt (a :: L)) with (max (sec a).+1 (max_elt L)) by trivial; lia.
Qed.

Lemma inseg_sec a:
	cnt \is_surjective -> sec \is_minimal_section_of cnt -> List.In a (in_seg (sec a).+1).
Proof.
move => sur [] issec min.
case: (sur a).
elim => [eq | n ih eq]; by left.
Qed.

Lemma melt_inseg:
	is_min_sec cnt sec -> forall n, max_elt (in_seg n) <= n.
Proof.
move => [issec min].
elim => // n ih.
replace (in_seg n.+1) with (cons (cnt n) (in_seg n)) by trivial.
replace (max_elt (cnt n :: in_seg n)) with (max (sec (cnt n)).+1 (max_elt (in_seg n))) by trivial.
have eq: (cnt n = cnt n) by trivial.
by move: (min (cnt n) n eq) => leq; lia.
Qed.

Lemma lstn_sec_melt:
forall (K : seq Q) (a : Q), List.In a K -> sec a < max_elt K.
Proof.
elim => // a K ih a' listin.
replace (max_elt (a::K)) with (max (sec a).+1 (max_elt K)) by trivial.
suffices: sec a' <= (sec a) \/ sec a' < max_elt K by lia.
case: listin => ass.
	by left; rewrite ass; lia.
by right; apply ih.
Qed.

Lemma melt_mon L K:
	L \is_sublist_of K -> max_elt L <= max_elt K.
Proof.
elim: L => [ _ | a L ih /= sl ]; first by rewrite /=; lia.
have inlist: List.In a K by apply sl; left.
have ineq: sec a < max_elt K by apply lstn_sec_melt.
suffices sl': max_elt L <= max_elt K by case E: (max_elt L); rewrite /=; by lia.
by apply ih => q listin; apply sl; right.
Qed.

Lemma inseg_melt K:
	cnt \is_surjective -> is_min_sec cnt sec -> K \is_sublist_of (in_seg (max_elt K)).
Proof.
move => sur ims a listin.
apply/ inseg_mon.
	suffices ineq: sec a < max_elt K by apply: ineq.
	move: listin; elim K => [ | k L ih listin ]; first by trivial.
	rewrite /= in listin; case: listin => [ eq | listin ].
		by case E: (max_elt L); rewrite /= E eq; lia.
	move: (ih listin) => ineq.
	suffices mon: max_elt L <= max_elt (k::L) by lia.
	by apply/ melt_mon; first by move => q lstn; right.
left; apply ims.1.
Qed.
End INITIAL_SEGMENTS.
Notation "L '\is_sublist_of' K" := (forall q, List.In q L -> List.In q K) (at level 2).
Notation "f '\is_surjective'" := (is_sur f) (at level 2).