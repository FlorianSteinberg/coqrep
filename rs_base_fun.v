From mathcomp Require Import all_ssreflect.
Require Import all_core rs_base rs_base_sub.
Require Import FunctionalExtensionality ClassicalFacts ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FUNCTIONSPACES.
Definition is_ass (X Y: rep_space) psi (f: X ->> Y) :=
	(oeval (U psi)) \is_realizer_of f.

Notation "X c-> Y" :=
	{f: X ->> Y | (f \is_single_valued /\ f \is_total) /\ f \has_continuous_realizer} (at level 2).

Definition exist_c (X Y: rep_space) F sing tot Fhcr :=
exist (fun f => (f \is_single_valued /\ f \is_total) /\ @hcr X Y f)
	F (conj (conj sing tot) Fhcr).

Definition exist_fun (X Y: rep_space) (g: X -> Y) ghcr:=
exist (fun f => (f \is_single_valued /\ f \is_total) /\ @hcr X Y f)
	(F2MF g) (conj (conj (@F2MF_sing X Y g) (F2MF_tot g)) ghcr).

Definition is_fun_name (X Y: rep_space) psi (f: X c-> Y) :=
	(eval (U psi)) \is_realizer_of (projT1 f).

Axiom prop_ext: prop_extensionality.

Lemma is_fun_name_is_rep (X Y : rep_space):
	(@is_fun_name X Y) \is_representation.
Proof.
case (classic (exists y: Y, true)) => [[somey _] | nex];last first.
split => [psi f g psinf psing | ].
	apply eq_sub.
	apply functional_extensionality => x.
	exfalso; apply nex.
	have [[_ tot] _] := projT2 f.
	have [y _] := tot x.
	by exists (y).
move => f.
exists (fun p => inr (some_answer Y)) => ka [y asd].
exfalso; apply nex; by exists y.
split => [psi f g psinf psing | f].
	move: (projT2 f) (projT2 g) => [[fsing ftot] hasrlzrf] [[gsing gtot] hastrlzrg].
	have [hf eqf]:= ((@F2MF_sing_tot X Y (projT1 f) somey).1 (conj fsing ftot)).
	have [hg eqg]:= ((@F2MF_sing_tot X Y (projT1 g) somey).1 (conj gsing gtot)).
	apply/ eq_sub.
	apply functional_extensionality => x;	apply functional_extensionality => y; apply prop_ext; move: x y.
	suffices: F2MF hf =~= F2MF hg by rewrite eqf eqg.
	suffices: hf = hg by move => <-.
	have [F icf]:= exists_choice (eval (U psi)) (fun q => some_answer Y).
	apply/ (frlzr_is_rep X Y).1.
		apply frlzr_rlzr.
		apply/ tight_rlzr.
			apply/ icf_F2MF_tight.
			by apply icf.
		by rewrite /rlzr eqf.
	apply frlzr_rlzr.
	apply/ tight_rlzr.
		apply/ icf_F2MF_tight.
		by apply icf.
	by rewrite /rlzr eqg.
have [cnt sur]:= (countable_questions X).
have [[ftot fsing] [F [Frf Fcont]]]:= (projT2 f).
have [psiF psinF]:= (U_is_universal (some_answer X) (fun q => (some_answer Y)) sur Fcont).
exists psiF.
rewrite /is_fun_name.
apply/ tight_trans; last by apply Frf.
by apply tight_comp_r.
Qed.

Canonical rep_space_cont_fun X Y := @make_rep_space
	((space X) c-> (space Y))
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
End FUNCTIONSPACES.
Notation "X c-> Y" := (rep_space_cont_fun X Y) (at level 2).
