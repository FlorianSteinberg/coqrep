From mathcomp Require Import all_ssreflect.
Require Import core_mf core_bs core_cont.
Require Import ClassicalChoice Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "L '\is_sublist_of' K" := (forall q, List.In q L -> List.In q K) (at level 2).

Section MINIMIZATION.
(* Most code from this section was provided by Vincent *)
Context (p: nat -> bool).

Let Fixpoint searchU m k : nat :=
  match k with
  | 0 => m
  | k'.+1 => let n := m - k in if p n then n else searchU m k'
  end.

Let searchU_correct m k :
  p m -> p (searchU m k).
Proof.
move => hm.
by elim: k => // n ih /=; case: ifP.
Qed.

Let searchU_le m k :
  searchU m k <= m.
Proof.
elim: k => // n ih /=; case: ifP => // _.
rewrite /subn /subn_rec; apply /leP; lia.
Qed.

Let searchU_minimal m k :
  (forall n, p n -> m - k <= n) -> forall n, p n -> searchU m k <= n.
Proof.
elim: k.
- move => h n /=; rewrite -(subn0 m); exact: h.
move => k ih h n /=; case: ifP.
- move => _; exact: h.
move => hk; apply: ih => i hi.
case: (i =P m - k.+1).
move => eq.
rewrite -eq in hk.
by rewrite hk in hi.
move: (h i hi).
rewrite /subn /subn_rec => /leP prp cnd; apply/leP; lia.
Qed.

Definition search n := searchU n n.

Lemma search_correct n:
	p n -> p (search n).
Proof.
exact: searchU_correct.
Qed.

Lemma search_le n:
	search n <= n.
Proof.
exact: searchU_le.
Qed.

Lemma search_min n m:
	p m -> search n <= m.
Proof.
apply searchU_minimal.
move => k pk.
rewrite /subn/subn_rec; apply/leP; lia.
Qed.
End MINIMIZATION.

Section SECTIONS.
Lemma worder_nat (p : nat -> bool):
	(exists n, p n) -> exists n, p n /\ forall m, p m -> n <= m.
Proof.
move => [m pm].
exists (search p m ).
split; first exact: search_correct.
exact: search_min.
Qed.

Lemma well_order_nat (P : nat -> Prop):
	(exists n, P n) -> exists n, P n /\ forall m, P m -> n <= m.
Proof.
set R:= fun n b => P n <-> is_true b.
have Rtot: R \is_total.
	by move => n; case: (classic (P n)) => pn; [exists true|exists false]; split.
have [p prop]:= choice R Rtot.
move => [m Pm].
have ex: exists n, p n by exists m; apply prop.
have [n [pn min]]:= (worder_nat ex).
by exists n; split => [ | k Pk ]; [ | apply min]; apply prop.
Qed.

Notation "f '\is_surjective'" := (f \is_surjective_function) (at level 2).

Context Q (cnt: nat -> Q) (sur: cnt \is_surjective).

Definition is_min_sec (sec : Q -> nat) :=
  cancel sec cnt /\ forall s,(forall m, cnt m = s -> sec s <= m).

Notation "sec '\is_minimal_section'" := (is_min_sec sec) (at level 2).

Lemma minimal_section:
  exists sec, sec \is_minimal_section.
Proof.
set R := fun s n => cnt n = s /\ (forall m, cnt m = s -> n <= m).
have Rtot: R \is_total by move => s; have [n]:= well_order_nat (sur s); exists n.
by have [sec]:= (choice R Rtot); exists sec; split => s; have []:= p s.
Qed.
End SECTIONS.
Notation "sec '\is_minimal_section_of' cnt" := (is_min_sec cnt sec) (at level 2).

Section INITIAL_SEGMENTS.
Context (Q A: Type) (cnt: nat -> Q).
Notation B := (Q -> A).

Fixpoint in_seg m := match m with
  | 0 => nil
  | S n => cons (cnt n) (in_seg n)
end.

Lemma size_inseg n : size (in_seg n) = n.
Proof. by elim: n => // n {2}<-. Qed.

Lemma length_inseg n : length (in_seg n) = n.
Proof. exact: size_inseg. Qed.

Lemma inseg_mon n m:
	  n <= m -> (in_seg n) \is_sublist_of (in_seg m).
Proof.
elim: m => [l0|m ih /=ass]; first by rewrite (_ : n = 0) //; apply /eqP; rewrite -leqn0.
by rewrite leq_eqVlt in ass; case: (orP ass); [move /eqP -> | right; apply ih].
Qed.

Lemma inseg_ex a n:
	 List.In a (in_seg n) -> exists m, m < n /\ cnt m = a.
Proof.
elim: n => // n ih /=; case => listin; first by exists n.
by have [m []]:= ih listin; exists m; split; first apply/ (ltn_trans _ (ltnSn n)).
Qed.

Lemma inseg_coin (phi psi : Q -> A) m:
  	(forall n, n < m -> phi (cnt n) = psi (cnt n))
  	<->
  	phi \and psi \coincide_on (in_seg m).
Proof.
split; elim: m => // n ihn; [ | move => /= []].
	by split; [apply/H | apply ihn => n0 ineq; apply /H/(ltn_trans _ (ltnSn n))].
by intros; rewrite ltnS leq_eqVlt in H; case (orP H); [move /eqP -> | apply ihn].
Qed.

Context (sec: Q -> nat).

Lemma inseg a:
	is_min_sec cnt sec -> forall n, List.In a (in_seg n) -> sec a < n.
Proof.
move => [cncl min] n listin.
have [m [/(leq_ltn_trans _) ineq eq]]:= (inseg_ex listin).
by apply /ineq/min.
Qed.

Fixpoint max_elt K := match K with
  | nil => 0
  | cons s K' => maxn (sec s).+1 (max_elt K')
end.

Lemma melt_app L K:
	max_elt (L ++ K) = maxn (max_elt L) (max_elt K).
Proof.
by elim: L K; [move => K; rewrite max0n | intros; rewrite /= (H K) maxnA].
Qed.

Lemma list_melt K (phi psi: B): cancel sec cnt ->
	phi \and psi \coincide_on (in_seg (max_elt K)) -> phi \and psi \coincide_on K.
Proof.
move => cncl.
elim: K => //= q L; rewrite -!inseg_coin -[q]cncl; split.
by apply /H0/leq_ltn_trans; last apply leq_maxl; first rewrite cncl leqnn.
by apply H; intros; apply /H0/leq_trans; last by apply leq_maxr.
Qed.

Lemma inseg_sec: cnt \is_surjective_function -> sec \is_minimal_section_of cnt ->
	forall a, List.In a (in_seg (sec a).+1).
Proof. by move => sur [cncl min] a; case: (sur a); elim; left. Qed.

Lemma melt_inseg: is_min_sec cnt sec ->
	forall n, max_elt (in_seg n) <= n.
Proof.
case; intros; elim: n => // n ih /=; rewrite geq_max; apply/ andP.
by split; [apply b | apply /leq_trans; last exact: leqnSn].
Qed.

Lemma lstn_sec_melt K a:
	List.In a K -> sec a < max_elt K.
Proof.
elim: K a => // a K ih a'/=.
by case => [<- | lstn]; apply/leq_trans; [|exact: leq_maxl|apply ih|exact: leq_maxr].
Qed.

Lemma melt_mon L K:
	L \is_sublist_of K -> max_elt L <= max_elt K.
Proof.
elim: L => // a L ih /= sl; rewrite geq_max; apply/andP.
by split; [apply /lstn_sec_melt/sl; left | apply /ih; intros; apply sl; right].
Qed.

Lemma inseg_melt K: cnt \is_surjective_function -> is_min_sec cnt sec ->
	K \is_sublist_of (in_seg (max_elt K)).
Proof.
intros; apply/ (@inseg_mon (S (sec q)) (max_elt K)); last exact: inseg_sec.
move: H1; elim K => //=; intros; case: H2 => [-> | lstn]; first by apply leq_maxl.
by apply /leq_trans; [apply H1 | apply leq_maxr].
Qed.
End INITIAL_SEGMENTS.
Notation "L '\is_sublist_of' K" := (forall q, List.In q L -> List.In q K) (at level 2).
