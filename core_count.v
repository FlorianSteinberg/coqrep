From mathcomp Require Import all_ssreflect.
Require Import core_mf core_inseg.
Require Import Psatz ClassicalChoice FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope coq_nat_scope.
Section COUNTABILITY.
Definition is_count Q :=
	exists cnt: nat -> option Q, cnt \is_surjective_function.
Notation "T '\is_countable'" := (is_count T) (at level 2).

Lemma classic_eqClass Q : exists P : Equality.class_of Q, True.
Proof.
have /choice[eq eqP]: (fun q b => (q.1 = q.2 :> Q) <-> (b = true)) \is_total.
  by move=> q; case: (classic (q.1 = q.2)) => ass; [exists true|exists false].
unshelve eexists (@Equality.Mixin _ (fun x y => eq (x, y)) _) => //.
by move=> x y; apply: (iffP idP) => [/eqP//|->]; apply/eqP.
Qed.

Lemma count_countMixin Q : Q \is_countable ->
  exists P : Countable.mixin_of Q, True.
Proof.
move => [cnt sur]; have [sec [issec min]] := minimal_section sur.
unshelve eexists (@Countable.Mixin _ (sec \o some) cnt _) => //.
by move=> x /=; rewrite issec.
Qed.

Lemma count_countClass Q  : Q \is_countable ->
  exists P : Countable.class_of Q, True.
Proof.
move=> /count_countMixin[cmQ _]; have [eqQ _] := classic_eqClass Q.
set QeqType := EqType Q eqQ.
set QchoiceType := ChoiceType QeqType (CountChoiceMixin cmQ).
by exists (Countable.class (CountType QchoiceType cmQ)).
Qed.

Lemma countMixin_count T : Countable.mixin_of T -> T \is_countable.
Proof.
move=> [pickle unpickle pickleK].
exists (fun n => if n isn't n.+1 then None else unpickle n).
move=> [x|]; last by exists 0.
by exists (pickle x).+1; rewrite pickleK.
Qed.

Lemma countType_count (T : countType) : T \is_countable.
Proof. by apply: countMixin_count; case: T => [?[]]. Qed.

Lemma nat_count: nat \is_countable.
Proof. exact: countType_count. Qed.

Lemma option_count T : T \is_countable -> (option T) \is_countable.
Proof.
move=> /count_countClass [cT _]; set T' : Type := Countable.Pack cT T.
by rewrite -[T]/T'; apply: countType_count.
Qed.

Lemma sum_count Q Q': Q \is_countable -> Q' \is_countable ->
  (Q + Q') \is_countable.
Proof.
move=> /count_countClass [cQ _]; set QC : Type := Countable.Pack cQ Q.
move=> /count_countClass [cQ' _]; set Q'C : Type := Countable.Pack cQ' Q'.
by rewrite -[Q]/QC -[Q']/Q'C; apply: countType_count.
Qed.

Lemma prod_count Q Q':
  Q \is_countable -> Q' \is_countable -> (Q * Q') \is_countable.
Proof.
move=> /count_countClass [cQ _]; set QC : Type := Countable.Pack cQ Q.
move=> /count_countClass [cQ' _]; set Q'C : Type := Countable.Pack cQ' Q'.
by rewrite -[Q]/QC -[Q']/Q'C; apply: countType_count.
Qed.

Lemma list_count Q: Q \is_countable -> (list Q) \is_countable.
Proof.
move=> /count_countClass [cQ _]; set QC : Type := Countable.Pack cQ Q.
by rewrite -[Q]/QC; apply: countType_count.
Qed.

Lemma count_sur Q: (exists cnt: nat -> Q, cnt \is_surjective) <-> inhabited Q /\ Q \is_countable.
Proof.
split => [ [cnt sur] | [[someq [cnt sur]]]].
	split; first exact (inhabits (cnt 0)).
	exists (fun n => match n with
		| 0 => None
		| S n' => Some (cnt n')
	end).
	move => q.
	case: q; last by exists 0.
	move => q.
	have [n val] := sur (q).
	by exists (S n); rewrite val.
exists (fun n => match cnt n with
	| None => someq
	| Some q => q
end) => q.
have [n val] := sur (some q).
by exists n; rewrite val.
Qed.

End COUNTABILITY.
Notation "T '\is_countable'" := (is_count T) (at level 2).