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
representation is actually a representation. The names have to be of the formulation
Q -> A where Q and A are countable and A is inhabited. This must also be proven. *)
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
split => [phipsi x x' [] phinx1 psinx2 [] phinx'1 psinx'2 | x].
	apply: injective_projections.
		by apply/ (\rep_valid X).1; first apply phinx1.
	by apply/ (\rep_valid Y).1; first apply psinx2.
have [phi phinx1]:= ((\rep_valid X).2 x.1).
have [psi psinx2]:= ((\rep_valid Y).2 x.2).
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
	elim => // n ih k.
	replace (2*n.+1) with ((2*n).+2) by by rewrite /muln/muln_rec; lia.
	rewrite /= (ih (k.+1)).
	by replace (n + k.+1) with (n.+1 + k) by by rewrite /addn/addn_rec; lia.
have prop2: forall n k, cnt' (2 * n + 1) k = inr(cnt2 (n + k)).
	elim => // n ih k.
	replace (2*n.+1) with ((2*n).+2) by by rewrite /muln/muln_rec; lia.
	rewrite /= (ih (k.+1)).
	by replace (n + k.+1) with (n.+1 + k) by by rewrite /addn/addn_rec; lia.

exists (fun n => cnt' n 0).
rewrite /initial_segments.is_sur.
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
replace (2 * n.+1) with ((2 * n).+2) by by rewrite /muln/muln_rec; lia.
rewrite -idx /= prop2.
by replace (S n) with (n + 1) by by rewrite /addn/addn_rec; lia.
Qed.

Lemma prod_count Q Q':
  Q \is_countable -> Q' \is_countable -> (Q * Q') \is_countable.
Proof.
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
Admitted.

Definition is_mf_rlzr (X Y: rep_space) (F: (names X) ->> (names Y)) (f: X ->> Y) :=
	(\rep Y) o F \tightens (f o (\rep X)).

Definition is_rlzr (X Y: rep_space) (F: (names X) -> (names Y)) (f: X -> Y) :=
	forall phi x, (\rep X) phi x -> ((\rep Y) (F phi) (f x)).
Notation "f '\is_realized_by' F" := (is_rlzr F f) (at level 2).
Notation "F '\is_realizer_of' f" := (is_rlzr F f) (at level 2).

Lemma rlzr_mfrlzr (X Y: rep_space) F (f: X -> Y):
	F \is_realizer_of f <-> is_mf_rlzr (F2MF F) (F2MF f).
Proof.
split => [rlzr phi [fx [[x [phinx eq]] prop]] | mfrlzr phi x phinx].
	split => [ | y [[Fphi [FphiFphi Fphiny]] prop']].
		exists (f x).
		split => [ | Fphi FphiFphi]; first by exists (F phi); split => //; apply rlzr.
		by exists (f x); rewrite -FphiFphi; exact: rlzr.
	rewrite comp_tot; last exact: F2MF_tot; exists x.
	split => //; rewrite -FphiFphi in Fphiny.
	by apply: (representation_is_valid Y).1; [apply rlzr | apply/ Fphiny ].
have exte: ((delta (r:=Y)) o (F2MF F)) \extends ((F2MF f) o (delta (r:=X))).
	apply/ exte_tight => //; apply: comp_sing; try exact: F2MF_sing.
		exact: (representation_is_valid X).1.
	exact: (representation_is_valid Y).1.
have Fphinfx: ((F2MF f) o (delta (r:=X))) phi (f x) by apply comp_tot; [exact: F2MF_tot | exists x].
have [Fphi [eq Fphifx]]:= (exte phi (f x) Fphinfx).1.
by rewrite eq.
Qed.

Lemma mfrlzr_rlzr (X Y: rep_space) F (f: X ->> Y) (somey: Y): f \is_single_valued -> f \is_total
	-> (exists g, g \is_choice_for f /\ F \is_realizer_of g) <-> is_mf_rlzr (F2MF F) f.
Proof.
move => sing tot.
split => [ [g [icf rlzr]] | mfrlzr].
	move: ((@sing_tot_F2MF_icf X Y f g sing tot).1 icf) => eq.
	suffices: is_mf_rlzr (F2MF F) (F2MF g) by admit.
	exact/ rlzr_mfrlzr.
have ass: f \is_single_valued /\ f \is_total by split.
have [g eq]:= ((F2MF_sing_tot f (somey)).1 ass).
exists g; split; first by apply sing_tot_F2MF_icf.
apply/ rlzr_mfrlzr.
admit.
Admitted.

Lemma is_rlzr_is_rep X Y:
  (@is_rlzr X Y) \is_representation.
Proof.
split => [F f g Frf Frg | f].
	apply functional_extensionality => x.
	have [phi phinx]:= ((\rep_valid X).2 x).
	apply/ (\rep_valid Y).1.
		by apply (Frf phi x phinx).
	by apply (Frg phi x phinx).
set R :=(fun phi psi => phi \from_dom (\rep X) -> forall x, (\rep X) phi x -> (\rep Y) psi (f x)).
have Rtot: R \is_total.
	move => phi.
	case: (classic (phi \from_dom (\rep X))) => [[x phinx] | nfd].
		have [psi psiny]:= ((\rep_valid Y).2 (f x)).
		by exists psi => _ x' phinx'; rewrite -((\rep_valid X).1 phi x x').
	by exists (fun q => some_answer Y) => fd; exfalso;apply nfd.
have [F Fcond]:= (choice R Rtot).
by exists F => phi x phinx; apply Fcond => //; exists x.
Qed.

Fact eq_sub T P (a b : {x : T | P x}) : a = b <-> projT1 a = projT1 b.
Proof.
split=> [->//|]; move: a b => [a Pa] [b Pb] /= eqab.
case: _ / eqab in Pb *; congr (exist _ _ _).
exact: Classical_Prop.proof_irrelevance.
Qed.

Definition has_cont_rlzr (X Y : rep_space) (f : X ->> Y) :=
	exists F, is_mf_rlzr (F2MF F) f /\ @is_cont (questions X) (answers X) (questions Y) (answers Y) (F2MF F).

Definition is_ass (X Y: rep_space) psi (f: X ->> Y) :=
	exists F, (evaltt (fun n phi q' => U n psi phi q')) =~= (F2MF F) /\ is_mf_rlzr F f.

Notation "X c-> Y" := {f: space X -> space Y | has_cont_rlzr (F2MF f)} (at level 2).

Definition is_fun_name (X Y: rep_space) psi (f: X c-> Y) :=
	exists F, (fun n phi q' => U n psi phi q') \type_two_computes (F2MF F) /\ F \is_realizer_of (projT1 f).

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
move: (U_is_universal a (fun q => a') sur Fcont) => [] psiF psinF.
exists psiF.
by exists F; split; last by apply rlzr_mfrlzr.
Qed.

Canonical rep_space_cont_fun X Y := @make_rep_space
	({f: space X -> space Y | has_cont_rlzr (F2MF f)})
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
move => [F Fir]; exists (fun n phi q => some (F phi q)).
exists F; split => // phi _.
split => [ | Fphi ev]; first by exists (F phi) => q'; exists 0.
apply functional_extensionality => q'.
by have [_ seq]:= (ev q'); exact: Some_inj.
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
Proof. exact: (prim_rec_comp_fun (id_prim_rec X)). Qed.

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
