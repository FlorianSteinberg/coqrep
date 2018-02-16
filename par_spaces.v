(* This file provides an alternative formulation of represented spaces that saves
the input and output types of the names *)
From mathcomp Require Import all_ssreflect.
Require Import continuity universal_machine multi_valued_functions machines.
Require Import FunctionalExtensionality ClassicalChoice Psatz ProofIrrelevance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section REPRESENTED_SPACES.

Definition is_rep S T (delta: S ->> T):=
	delta is_surjective_partial_function.
Notation "delta 'is_representation'" := (is_rep delta) (at level 2).

(* To construct a represented space it is necessary to provide a proof that the
representation is actually a representation. The names can be an arbitrary type
but will usually be something that can be computed on, i.e. Baire space or something.
At some point I will probably change the names to be a size_type. The type of names
must be inherited for the rather irrelevant full function-space construction to
work. This may change depending on whether other function space constructions also
need this or not. *)
Structure rep_space := make_rep_space {
  space :> Type;
  questions: Type;
  answers: Type;
  delta: (questions -> answers) ->> space;
	some_answer: answers;
  countable_questions: questions is_countable;
  countable_answers: answers is_countable;
  representation_is_valid : delta is_representation
}.
Notation names X := ((questions X) -> (answers X)).
Notation "'rep'" := @delta (at level 2).
Notation "phi 'is_name_of' x" := (delta phi x) (at level 2).
Notation "'rep_valid' X" := (@representation_is_valid X) (at level 2).

Definition prod_rep X Y :=
	(fun (phipsi : (questions X + questions Y -> answers X + answers Y)) x =>
      delta (fun q => match phipsi (inl q) with
        | inl a => a
        | inr b => some_answer X
      end) x.1 /\ delta (fun q => match phipsi (inr q) with
        | inl a => some_answer Y
        | inr b => b
      end) x.2).

Lemma prod_rep_is_rep (X Y: rep_space):
	(@prod_rep X Y) is_representation.
Proof.
split.
	move => phipsi x x' [] phinx1 psinx2 [] phinx'1 psinx'2.
	apply: injective_projections.
		apply/ (rep_valid X).1.
			by apply phinx1.
		done.
	apply/ (rep_valid Y).1.
		by apply psinx2.
	done.
move => x.
move: ((rep_valid X).2 x.1) ((rep_valid Y).2 x.2) => [] phi phinx1 [] psi psinx2.
by exists (fun q => match q with
	| inl q' => inl (phi q')
	| inr q' => inr (psi q')
end).
Qed.

(* This is the product of represented spaces. At some point I should prove that this
is the product in some category, but I am unsure what the morphisms are supposed to be. *)

Lemma sum_count Q Q':
  Q is_countable -> Q' is_countable -> (Q + Q') is_countable.
Proof.
move => [cnt1] sur1 [cnt2] sur2.
set cnt' := fix cnt' n acc := match n with
	| 0 => inl (cnt1 acc) 
	| 1 => inr (cnt2 acc)
	| S (S n') => (cnt' n' (S acc))
end.

have prop: forall n k, cnt' (2 * n) k = inl(cnt1 (n + k)).
	elim => //.
	move => n ih k.
	replace (2*n.+1) with ((2*n).+2) by by rewrite /muln/muln_rec; lia.
	rewrite /= (ih (k.+1)).
	by replace (n + k.+1) with (n.+1 + k) by by rewrite /addn/addn_rec; lia.
have prop2: forall n k, cnt' (2 * n + 1) k = inr(cnt2 (n + k)).
	elim => //.
	move => n ih k.
	replace (2*n.+1) with ((2*n).+2) by by rewrite /muln/muln_rec; lia.
	rewrite /= (ih (k.+1)).
	by replace (n + k.+1) with (n.+1 + k) by by rewrite /addn/addn_rec; lia.

exists (fun n => cnt' n 0).
rewrite /initial_segments.is_sur.
apply sum_rect.
	move => s.
	move: (sur1 s) => [n] idx.
	exists (2*n).
	move: n s idx.
	rewrite /F2MF.
	elim.
		move => s idx.
		by rewrite -idx.
	move => n ih s idx.
	replace (2 * n.+1) with ((2 * n).+2) by by rewrite /muln/muln_rec; lia.
		rewrite -idx /=.
		rewrite prop.
		by replace (S n) with (n + 1) by by rewrite /addn/addn_rec; lia.
	move => s.
	move: (sur2 s) => [n] idx.
	exists (2*n + 1).
	move: n s idx.
	rewrite /F2MF.
	elim.
		move => s idx.
		by rewrite -idx.
	move => n ih s idx.
	replace (2 * n.+1) with ((2 * n).+2) by by rewrite /muln/muln_rec; lia.
		rewrite -idx /=.
		rewrite prop2.
		by replace (S n) with (n + 1) by by rewrite /addn/addn_rec; lia.
Qed.

Canonical rep_space_prod X Y := @make_rep_space
  ((space X) * (space Y))
  (@questions X + @questions Y)
  (@answers X + @answers Y)
  (@prod_rep X Y)
  (inl (some_answer X))
  (sum_count (countable_questions X) (countable_questions Y))
  (sum_count (countable_answers X) (countable_answers Y))
  (@prod_rep_is_rep X Y).

Lemma prod_count Q Q':
  Q is_countable -> Q' is_countable -> (Q * Q') is_countable.
Proof.
admit.
Admitted.

Lemma list_count Q:
	Q is_countable -> (list Q) is_countable.
Proof.
admit.
Admitted.

Definition is_mf_rlzr (X Y: rep_space) (F: (names X) ->> (names Y)) (f: X ->> Y) :=
	(rep Y) o F tightens (f o (rep X)).

Definition is_rlzr (X Y: rep_space) (F: (names X) -> option (names Y)) (f: X -> Y) :=
	forall phi x, (rep X) phi x -> (exists psi, (F phi) = some psi /\ (rep Y) psi (f x)).
Notation "f 'is_realized_by' F" := (is_rlzr F f) (at level 2).
Notation "F 'is_realizer_of' f" := (is_rlzr F f) (at level 2).

Lemma is_rlzr_is_rep X Y:
  (@is_rlzr X Y) is_representation.
Proof.
split.
	move => F f g Frf Frg.
	apply functional_extensionality => x.
	move: ((rep_valid X).2 x) => [] phi phinx.
	move: (Frf phi x phinx) => [] psi [] eq psinfx.
	move: (Frg phi x phinx) => [] psi' [] eq' psi'nfx.
	have pep: psi = psi'.
		apply Some_inj.
		by rewrite -eq -eq'.
	apply/ (rep_valid Y).1.
		by apply psinfx.
	by rewrite pep.
move => f.
set R :=(fun phi psi => phi from_dom (rep X) -> forall x, (rep X) phi x -> (rep Y) psi (f x)).
have cond: forall phi, exists psi, R phi psi.
	move => phi.
	case: (classic (phi from_dom (rep X))).
		move => [] x phinx.
		move: ((rep_valid Y).2 (f x)) => [] psi psiny.
		exists psi.
		move => _ x' phinx'.
		by rewrite -((rep_valid X).1 phi x x').
	move => ass.
	exists (fun q => some_answer Y).
	move => phifd.
	by exfalso;apply ass.
move: (choice R cond) => [] F Fcond.
exists (fun phi => some (F phi)).
move => phi x phinx.
exists (F phi).
split => //.
apply Fcond => //.
by exists x.
Qed.

Fact eq_sub T P (a b : {x : T | P x}) : a = b <-> projT1 a = projT1 b.
Proof.
split=> [->//|]; move: a b => [a Pa] [b Pb] /= eqab.
case: _ / eqab in Pb *; congr (exist _ _ _).
exact: Classical_Prop.proof_irrelevance.
Qed.

Definition has_cont_rlzr (X Y : rep_space) (f : X -> Y) :=
	exists F, is_rlzr F f /\ @is_cont (questions X) (answers X) (questions Y) (answers Y) F.

Notation "X c-> Y" := {f: X -> Y | has_cont_rlzr f} (at level 2).

Definition is_ass (X Y: rep_space) psi (f: X c-> Y) := 
	exists F,  (fun n phi q' => U n psi phi q') type_two_computes F /\ F is_realizer_of (projT1 f).

Lemma is_ass_is_rep (X Y : rep_space):
  (@is_ass X Y) is_representation.
Proof.
split.
	move => psiF f g [] F [] psinF Frf [] G [] psinG Grg.
	apply/ eq_sub.
	apply/ (is_rlzr_is_rep X Y).1.
		by apply Frf.
	move => phi x phinx.
	move: (Grg phi x phinx) => [] Gphi [] GphiGphi Gphingx.
	move: (Frf phi x phinx) => [] Fphi [] FphiFphi Fphinfx.
	exists Gphi.
	split => //.
	have ex: exists psi, F phi = some psi by exists Fphi.
	move: (psinF phi ex) => [] [] Uphi prop cond.
	rewrite (cond Uphi prop).
	rewrite -GphiGphi.
	have ex': exists psi, G phi = some psi by exists Gphi.
	move: (psinG phi ex') => [] [] Uphi' prop' cond'.
	by rewrite (cond' Uphi prop).
move => f.
move: (countable_questions X) => [] cnt sur.
move: (initial_segments.minimal_section sur) => [] sec ismin.
set F := fun phi psi => exists x, (rep X) phi x -> (rep Y) psi (projT1 f x).
move: exists_choice.
move: (@U_is_universal (questions X) (answers X) (questions Y) (answers Y)
	cnt).
Qed.

Canonical rep_space_cont_fun X Y := @make_rep_space
  (Space_from_rep (@is_ass_is_rep X Y))
  (seq (questions X * answers X) * questions Y)
  (questions X + answers Y)
  (@is_ass X Y)
  (inr (No_answer Y))
  (prod_count
  	(list_count (prod_count
  		(countable_questions X)
  		(countable_answers X)))
  	(countable_questions Y))
  (sum_count (countable_questions X) (countable_answers Y))
  (rep_of_space_from_rep (@is_ass_is_rep X Y)).

Definition has_comp_name (X: rep_space) (x: X):=
	{M | exists phi, M computes (F2MF phi) /\ phi is_name_of x}.
Definition has_prim_rec_name (X: rep_space) (x: X) :=
	{phi| phi is_name_of x}.

Lemma prim_rec_elt_comp_elt (X: rep_space) (x: X): has_prim_rec_name x -> has_comp_name x.
Proof.
move => [] phi phinx.
exists (fun n q => some (phi q)).
exists phi.
split => //.
move => q _.
split.
	exists (phi q).
	by exists 0.
move => a  [] n ev.
by apply Some_inj.
Qed.

Definition is_comp_fun (X Y: rep_space) (f: X -> Y) :=
	{M | exists F, M type_two_computes F /\ F is_realizer_of f}.

Definition is_prim_rec_fun (X Y: rep_space) (f: X -> Y) :=
	{F | (F2MF F) is_realizer_of f}.

Lemma prim_rec_fun_comp_fun (X Y: rep_space) (f:X -> Y) : is_prim_rec_fun f -> is_comp_fun f.
Proof.
move => [] F Frf.
exists (fun n phi q => some (F phi q)).
exists (F2MF F).
split => //.
move => phi _.
split.
	exists (F phi).
	move => q'.
	by exists 0.
move => Fphi ev.
apply: functional_extensionality => q'.
move: (ev q') => [] _ eq.
by apply Some_inj.
Qed.

End REPRESENTED_SPACES.
Notation "delta 'is_representation'" := (is_rep delta) (at level 2).
Notation "delta 'is_representation_of' X" := (@is_rep_of _ X delta) (at level 2).
Notation names X := ((questions X) -> (answers X)).
Notation "'rep'" := @delta (at level 2).
Notation "phi 'is_name_of' x" := (delta phi x) (at level 2).
Notation "x 'equals' y" := (equal x y) (at level 2).
Notation "x 'is_element'" := (equal x x) (at level 2).
Notation "x 'is_from' X" := (@equal X x x) (at level 2).
Notation "x 'equals' y" := (equal x y) (at level 2).
Notation "'rep_valid' X" := (@representation_is_valid X) (at level 2).
Notation "f 'is_realized_by' F" := (is_rlzr F f) (at level 2).
Notation "F 'is_realizer_of' f" := (is_rlzr F f) (at level 2).
Notation opU psi:=(eval (fun n phi q' => U n psi phi q')).
Notation "x 'is_computable_element'" := (has_comp_name x) (at level 2).
Notation "x 'is_primitive_recursive_element'" := (has_prim_rec_name x) (at level 2).
Notation "f 'is_computable_function'" := (is_comp_fun f) (at level 2).
(*

Lemma eval_comp X Y:
	is_cmptbl (fun (p: space (rep_space_prod (rep_space_cont_fun X Y) X)) => p.1 p.2).
Proof.
exists (e val (fun n psi q' => U n (psi.1) psi.2 q')).

Lemma cont_fun_equal X Y (f g: space X -> space Y):
	f equals g <-> has_cont_rlzr f /\ has_cont_rlzr g
		/\ forall x y, x equals y -> (f x) equals (g y).
Proof.
split.
	move=> [] psi []psinf psing.
	split.
		exists (opU psi).
		split => //.
		admit.
	split.
		exists (opU psi).
		split => //.
		admit.
	move => x y xey.
	apply/ equal_trans.
		by apply: (psinf.2 x y).
	admit.
move => [] [] F [] Frf Fcont [][] G [] Grg Gcont prop.
*)