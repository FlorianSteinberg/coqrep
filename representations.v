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
	delta \is_surjective_partial_function.
Notation "delta '\is_representation'" := (is_rep delta) (at level 2).

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
  countable_questions: questions \is_countable;
  countable_answers: answers \is_countable;
  representation_is_valid : delta \is_representation
}.
Notation names X := ((questions X) -> (answers X)).
Notation "'\rep'" := @delta (at level 2).
Notation "phi '\is_name_of' x" := (delta phi x) (at level 2).
Notation "'\rep_valid' X" := (@representation_is_valid X) (at level 2).

Definition prod_rep X Y :=
	(fun (phipsi : (questions X + questions Y -> answers X * answers Y)) x =>
      delta (fun q => (phipsi (inl q)).1) x.1 /\ delta (fun q => (phipsi (inr q)).2) x.2).

Lemma prod_rep_is_rep (X Y: rep_space):
	(@prod_rep X Y) \is_representation.
Proof.
split.
	move => phipsi x x' [] phinx1 psinx2 [] phinx'1 psinx'2.
	apply: injective_projections.
		apply/ (\rep_valid X).1.
			by apply phinx1.
		done.
	apply/ (\rep_valid Y).1.
		by apply psinx2.
	done.
move => x.
move: ((\rep_valid X).2 x.1) ((\rep_valid Y).2 x.2) => [] phi phinx1 [] psi psinx2.
by exists (fun q => match q with
	| inl q' => (phi q', some_answer Y)
	| inr q' => (some_answer X, psi q')
end).
Qed.

(* This is the product of represented spaces. At some point I should prove that this
is the product in some category, but I am unsure what the morphisms are supposed to be. *)

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

Lemma prod_count Q Q':
  Q \is_countable -> Q' \is_countable -> (Q * Q') \is_countable.
Proof.
admit.
Admitted.

Canonical rep_space_prod X Y := @make_rep_space
  ((space X) * (space Y))
  (@questions X + @questions Y)
  (@answers X * @answers Y)
  (@prod_rep X Y)
  ((some_answer X, some_answer Y))
  (sum_count (countable_questions X) (countable_questions Y))
  (prod_count (countable_answers X) (countable_answers Y))
  (@prod_rep_is_rep X Y).

Lemma list_count Q:
	Q \is_countable -> (list Q) \is_countable.
Proof.
admit.
Admitted.

Definition is_mf_rlzr (X Y: rep_space) (F: (names X) ->> (names Y)) (f: X ->> Y) :=
	(\rep Y) o F \tightens (f o (\rep X)).

Definition is_rlzr (X Y: rep_space) (F: (names X) -> (names Y)) (f: X -> Y) :=
	forall phi x, (\rep X) phi x -> ((\rep Y) (F phi) (f x)).
Notation "f '\is_realized_by' F" := (is_rlzr F f) (at level 2).
Notation "F '\is_realizer_of' f" := (is_rlzr F f) (at level 2).

Lemma is_rlzr_is_rep X Y:
  (@is_rlzr X Y) \is_representation.
Proof.
split.
	move => F f g Frf Frg.
	apply functional_extensionality => x.
	move: ((\rep_valid X).2 x) => [] phi phinx.
	move: (Frf phi x phinx) => Fphinfx.
	move: (Frg phi x phinx) => Fphingx.
	apply/ (\rep_valid Y).1.
		by apply Fphinfx.
	by apply Fphingx.
move => f.
set R :=(fun phi psi => phi \from_dom (\rep X) -> forall x, (\rep X) phi x -> (\rep Y) psi (f x)).
have cond: forall phi, exists psi, R phi psi.
	move => phi.
	case: (classic (phi \from_dom (\rep X))).
		move => [] x phinx.
		move: ((\rep_valid Y).2 (f x)) => [] psi psiny.
		exists psi.
		move => _ x' phinx'.
		by rewrite -((\rep_valid X).1 phi x x').
	move => ass.
	exists (fun q => some_answer Y).
	move => phifd.
	by exfalso;apply ass.
move: (choice R cond) => [] F Fcond.
exists (F) => phi x phinx.
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
	exists F, is_rlzr F f /\ @is_cont (questions X) (answers X) (questions Y) (answers Y) (F2MF F).

Definition is_ass (X Y: rep_space) psi (f: X -> Y) := 
	exists F,  (fun n phi q' => U n psi phi q') \type_two_computes (F2MF F) /\ F \is_realizer_of f.

Notation "X c-> Y" := {f: space X -> space Y | has_cont_rlzr f} (at level 2).

Definition is_fun_name (X Y: rep_space) psi (f: X c-> Y) := 
	exists F,  (fun n phi q' => U n psi phi q') \type_two_computes (F2MF F) /\ F \is_realizer_of (projT1 f).

Lemma is_fun_name_is_rep (X Y : rep_space):
  (@is_fun_name X Y) \is_representation.
Proof.
split.
	move => psiF f g [] F [] psinF Frf [] G [] psinG Grg.
	apply/ eq_sub.
	apply/ (is_rlzr_is_rep X Y).1.
		by apply Frf.
	move => phi x phinx.
	have eq: G phi = F phi.
		have ex: exists psi, F2MF F phi psi by exists (F phi).
		move: (psinF phi ex) => [] [] Uphi prop cond.
		rewrite (cond Uphi prop).
		have ex': exists psi, F2MF G phi psi by exists (G phi).
		move: (psinG phi ex') => [] [] Uphi' prop' cond'.
		by rewrite (cond' Uphi prop).
	rewrite -eq.
	by apply (Grg phi x phinx).
move => f.
move: (countable_questions X) => [] cnt sur.
move: (some_answer X) (some_answer Y) => a a'.
move: (projT2 f) => [] F [] Frf Fcont.
move: (U_is_universal a a' sur Fcont) => [] psiF psinF.
exists psiF.
by exists F.
Qed.

Canonical rep_space_cont_fun X Y := @make_rep_space
	({f: space X -> space Y | has_cont_rlzr f})
	(seq (questions X * answers X) * questions Y)
	(questions X + answers Y)
	(@is_fun_name X Y)
	(inr (some_answer Y))
  (prod_count
  	(list_count (prod_count
  		(countable_questions X)
  		(countable_answers X)))
  	(countable_questions Y))
  (sum_count (countable_questions X) (countable_answers Y))
  (@is_fun_name_is_rep X Y).

Definition is_comp (X: rep_space) (x: X) :=
	{phi| phi \is_name_of x}.

Definition is_comp_fun X Y (f: space X -> space Y) :=
	{G | exists F, is_rlzr F f/\ comptt G (F2MF F)}.

Definition is_prim_rec X Y (f: space X -> space Y) :=
	{F | is_rlzr F f}.

Lemma prim_rec_comp_fun X Y (f: space X -> space Y):
	is_prim_rec f -> is_comp_fun f.
Proof.
move => [] F Fir.
exists (fun n phi q => some (F phi q)).
exists F.
split => //.
move => phi _.
split.
	exists (F phi).
	move => q'.
	by exists 0.
move => Fphi ev.
apply functional_extensionality => q'.
move: (ev q') => [] _ seq.
by apply Some_inj.
Qed.

(*
Lemma comp_cont (X Y: rep_space) (f:X -> Y):
	is_comp_fun f -> has_cont_rlzr f.
Proof.
rewrite /is_comp_fun.
rewrite /is_ass.
Admitted.*)

Lemma id_prim_rec (X: rep_space) :
	@is_prim_rec X X (fun x => x).
Proof.
by exists id.
Qed.

Lemma id_comp_fun (X: rep_space) :
	@is_comp_fun X X id.
Proof.
exact: (prim_rec_comp_fun (id_prim_rec X)).
Qed.

(*
Lemma eval_comp_fun X Y:
	is_comp_fun (fun (p:((X c-> Y) * X)) => (projT1 p.1) p.2).
Proof.
rewrite /is_comp_fun.
pose G n (phi: names(rep_space_prod (rep_space_cont_fun X Y) X)) q' :=
	U n (fun q =>  (phi (inl q)).1) (fun q => (phi (inr q)).2) q'.
exists G.
move: ((exists_choice (evaltt G)) (fun q => some_answer Y)) => [] F FcG.
exists F.
split.
	move => phi x phinx.
	suffices: (exists t : names Y, evaltt G phi t).
		move => ex.
		have ev:= (FcG phi ex).
		rewrite /evaltt in ev.
		rewrite /rep.
Admitted.
*)

End REPRESENTED_SPACES.
Notation "delta '\is_representation'" := (is_rep delta) (at level 2).
Notation names X := ((questions X) -> (answers X)).
Notation "'\rep'" := @delta (at level 2).
Notation "phi '\is_name_of' x" := (delta phi x) (at level 2).
Notation "'\rep_valid' X" := (@representation_is_valid X) (at level 2).
Notation "f '\is_realized_by' F" := (is_rlzr F f) (at level 2).
Notation "F '\is_realizer_of' f" := (is_rlzr F f) (at level 2).
Notation opU psi:=(eval (fun n phi q' => U n psi phi q')).
Notation "X c-> Y" := {f: space X -> space Y | has_cont_rlzr f} (at level 2).
Notation "x '\is_computable'" := (is_comp x) (at level 2).
Notation "f '\is_computable_function'" := (is_comp_fun f) (at level 2).
