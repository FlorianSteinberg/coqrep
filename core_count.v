From mathcomp Require Import all_ssreflect.
Require Import core_mf core_inseg.
Require Import Psatz ClassicalChoice FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope coq_nat_scope.
Section COUNTABILITY.
Definition is_count Q :=
	exists cnt: nat -> Q, cnt \is_surjective_function.
Notation "T '\is_countable'" := (is_count T) (at level 2).

Lemma count_countType Q:
	Q \is_countable -> exists P:Countable.class_of Q, true.
Proof.
move => [cnt sur].
have [sec [issec min]]:= minimal_section sur.
pose eq' (q: Q * Q) b := (q.1 = q.2) <-> (b = true).
have eqtot: eq' \is_total.
	move => [q q'].
	case: (classic (q = q')) => ass.
		by exists true.
	by exists false.
have [eq'' eqprop]:= choice eq' eqtot.
pose eq q q' := eq'' (q, q').
split => //.
split.
	split; first  by exists (eq) => q q'; apply Bool.iff_reflect; apply (eqprop (q, q')).
	exists (fun p n => if p (cnt n):bool then some (cnt (search (fun n => p (cnt n)) n)) else None).
			move => p n q; case E: (p (cnt n)) => // equ.
			have <-:= Some_inj equ.
			by apply/ (@search_correct (fun n => p (cnt n)) n).
		move => p [q pq].
		exists (sec q); case: ifP => //; by rewrite issec pq.
	by move => p p' pep' n; have <-: p = p' by apply functional_extensionality.
apply (@Countable.Mixin _ sec (fun q => some (cnt q))).
move => q; congr Some; apply issec.
Qed.

Lemma option_count T:
	T \is_countable -> (option T) \is_countable.
Proof.
move => [cnt sur].
exists (fun n => match n with
	| 0 => None
	| S n' => Some (cnt n')
end).
move => x.
case x; last by exists 0.
move => a.
have [n cntna]:= sur a.
by exists (S n); rewrite cntna.
Qed.

Lemma sum_count Q Q':
  Q \is_countable -> Q' \is_countable -> (Q + Q') \is_countable.
Proof.
move => [cnt1] sur1 [cnt2] sur2.
set cnt' := fix cnt' n acc := match n with
	| 0 => inl (cnt1 acc) 
	| 1 => inr (cnt2 acc)
	| S (S n') => (cnt' n' (S acc))
end.

have prop: forall n k, cnt' (2 * n) k = inl(cnt1 (n + k)).
	elim => // n ih k.
	replace (2*n.+1) with ((2*n).+2) by by rewrite /muln/muln_rec; lia.
	rewrite /= (ih (k.+1)).
	by replace (n + k.+1) with (n.+1 + k) by by rewrite /addn/addn_rec; lia.
have prop2: forall n k, cnt' (2 * n + 1) k = inr(cnt2 (n + k)).
	elim => // n ih k.
	replace (2*n.+1 + 1) with ((2*n).+2 + 1) by by rewrite /muln/muln_rec; lia.
	rewrite /= (ih (k.+1)).
	by replace (n + k.+1) with (n.+1 + k) by by rewrite /addn/addn_rec; lia.

exists (fun n => cnt' n 0).
rewrite /sur_fun.
apply sum_rect => s.
	move: (sur1 s) => [n] idx.
	exists (2*n).
	move: n s idx.
	elim => [s idx | n ih s idx]; first by rewrite -idx.
	replace (2 * n.+1) with ((2 * n).+2) by by rewrite /muln/muln_rec; lia.
	rewrite -idx /= prop.
	by replace (S n) with (n + 1) by by rewrite /addn/addn_rec; lia.
move: (sur2 s) => [n] idx.
exists (2*n + 1).
move: n s idx.
elim => [s idx | n ih s idx]; first by rewrite -idx.
replace (2 * n.+1 + 1) with ((2 * n).+2 + 1) by by rewrite /muln/muln_rec; lia.
rewrite -idx /= prop2.
by replace (S n) with (n + 1) by by rewrite /addn/addn_rec; lia.
Qed.

Lemma prod_count Q Q':
  Q \is_countable -> Q' \is_countable -> (Q * Q') \is_countable.
Proof.
move => Qcount Q'count.
have [ctQ _] := count_countType Qcount.
have [ctQ' _] := count_countType Q'count.
have [Qcnt Qsur]:= Qcount.
have [Q'cnt Q'sur]:= Q'count.
have issec:= (@pickleK_inv (prod_countType (Countable.Pack ctQ Q) (Countable.Pack ctQ' Q'))).
pose cnt n := match (@pickle_inv (prod_countType (Countable.Pack ctQ Q) (Countable.Pack ctQ' Q'))) n with
	| Some q => q
	| None => (Qcnt 0,Q'cnt 0)
end.
exists cnt.
move => q.
exists (@pickle (prod_countType (Countable.Pack ctQ Q) (Countable.Pack ctQ' Q')) q).
by rewrite /cnt (issec q).
Qed.

Lemma list_count Q:
	Q \is_countable -> (list Q) \is_countable.
Proof.
move => Qcount.
have [ctQ _] := count_countType Qcount.
have [Qcnt Qsur]:= Qcount.
have issec:= (@pickleK_inv (seq_countType (Countable.Pack ctQ Q))).
pose cnt n := match (@pickle_inv (seq_countType (Countable.Pack ctQ Q))) n with
	| Some q => q
	| None => nil
end.
exists cnt.
move => q.
exists (@pickle (seq_countType (Countable.Pack ctQ Q)) q).
by rewrite /cnt (issec q).
Qed.
End COUNTABILITY.
Notation "T '\is_countable'" := (is_count T) (at level 2).