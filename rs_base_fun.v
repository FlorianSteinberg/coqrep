From mathcomp Require Import all_ssreflect.
Require Import all_core rs_base rs_base_sub rs_base_prod rs_base_facts.
Require Import FunctionalExtensionality ClassicalFacts ClassicalChoice Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FUNCTIONSPACES.
Definition is_ass (X Y: rep_space) psi (f: X -> Y) :=
	(oeval (U psi)) \is_realizer_of (F2MF f).

Notation "X c-> Y" :=
	{f: X -> Y | (F2MF f) \has_continuous_realizer} (at level 2).

Check exist.
Definition exist_c (X Y: rep_space) F Fhcr :=
exist (fun f => @hcr X Y (F2MF f))
	F (Fhcr).

Definition is_fun_name (X Y: rep_space) psi (f: X c-> Y) :=
	(eval (U psi)) \is_realizer_of (F2MF (projT1 f)).

Lemma is_fun_name_is_rep (X Y : rep_space):
	(@is_fun_name X Y) \is_representation.
Proof.
case (classic (exists y: Y, true)) => [[somey _] | nex];last first.
	split => [_ [f  fhcr] g _ _ | f].
		apply /eq_sub/functional_extensionality => x.
		by exfalso; apply nex; exists (f (x)).
	exists (fun p => inr (some_answer Y)) => ka [y asd].
	exfalso; apply nex; by exists y.
split => [psi [f fhcr] [g ghcr] psinf psing | f].
	apply/ eq_sub => /=; rewrite /is_fun_name/= in psinf psing.
	have [F icf]:= exists_choice (eval (U psi)) (fun q => some_answer Y).
	apply/ frlzr_sing; apply/frlzr_rlzr; apply/icf_rlzr; try apply icf; [apply psinf | 	apply psing].
have [F [Frf Fcont]]:= (projT2 f).
have [psiF psinF]:= (U_universal (some_question X) (some_answer X) (fun q => (some_answer Y)) (countable_questions X) Fcont).
by exists psiF; apply/tight_trans; [apply tight_comp_r | apply Frf].
Qed.

Canonical rep_space_cont_fun X Y := @make_rep_space
	((space X) c-> (space Y))
	(seq (questions X * answers X) * questions Y)
	(questions X + answers Y)
	(@is_fun_name X Y)
	((nil, some_question Y))
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

Section EVALUATION.
Definition evaluation X Y (fx: (X c-> Y) * X) := (projT1 fx.1) fx.2.

Lemma eval_rlzr X Y:
	(eval (fun n psiphi q => U (lprj psiphi) n (rprj psiphi) q)) \is_realizer_of (F2MF (@evaluation X Y)).
Proof.
set R:=(fun n psiphi q => U (lprj psiphi) n (rprj psiphi) q).
rewrite rlzr_F2MF => phi [[f fhcr] x] [/=phinf phinx].
rewrite /is_fun_name/= in phinf.
split.
	have [ | Fphi FphiFphi]:= rlzr_dom phinf phinx; first by apply F2MF_tot.
	have eq: (eval (U (lprj phi))) (rprj phi) = (eval R) phi by trivial.
	by exists (Fphi); rewrite -eq.
move => Fphi RphiFphi.
by apply/ rlzr_val_sing; [ apply F2MF_sing | apply phinf | apply phinx | | ].
Qed.

Lemma eval_cmpt X Y:
	(@evaluation X Y) \is_computable_function.
Proof.
exists (fun n psiphi q => U (lprj psiphi) n (rprj psiphi) q).
exact: eval_rlzr.
Defined.

(*Lemma eval_hcr X Y:
	(@evaluation X Y) \has_continuous_realizer.
Proof.
exists (eval (fun n psiphi q => U (lprj psiphi) n (rprj psiphi) q)).
split; first exact: eval_rlzr.
move => psiphi q [Fpsiphi val].
have [n evl] := val q.
Admitted.*)

End EVALUATION.

Section COMPUTABLE_ELEMENTS.
Lemma cmpt_elt_mon_cmpt (X Y: rep_space) (f: X c-> Y):
	f \is_recursive_element -> (F2MF (projT1 f)) \is_monotone_computable.
Proof. move => [psiF comp]; exists (U psiF); split => //; exact: U_mon. Defined.

Lemma prod_space_cont (X Y Z: rep_space) (f: Z c-> X) (g: Z c-> Y):
	exists (F: rep_space_cont_fun Z (rep_space_prod X Y)),
		(forall z, (projT1 F z).1 = (projT1 f) z)
		/\
		(forall z, (projT1 F z).2 = (projT1 g) z).
Proof.
set F := fun z => ((projT1 f) **_f (projT1 g)) (z, z).
have Fhcr: (F2MF F) \has_continuous_realizer.
	have ->: (F2MF F) =~= (F2MF (projT1 f) ** F2MF (projT1 g)) o (F2MF (fun z => (z, z))).
		by rewrite -mfpp_fun_mfpp F2MF_comp.
	by apply comp_hcr; [apply diag_hcr | apply mfpp_hcr; [apply (projT2 f) | apply (projT2 g) ]].
by exists (exist_c Fhcr).
Qed.

Definition id_fun X := (exist_c (id_hcr X)).

Lemma id_rec_elt X:
	(id_fun X : X c-> X) \is_recursive_element.
Proof.
exists (fun p => match p.1: seq (questions X* answers X) with
		| nil => inl (p.2:questions X)
		| (q,a):: L => inr (a: answers X)
	end).
abstract by pose id_name p := match p.1: seq (questions X* answers X) with
		| nil => inl (p.2:questions X)
		| (q,a):: L => inr (a: answers X)
	end; rewrite /=/is_fun_name/=/rlzr comp_id_l -{1}(comp_id_r (rep X));
	apply /tight_comp_r/ (mon_cmpt_op); [exact: U_mon | move => phi q; exists 1].
Defined.

Definition composition X Y Z (f: X c-> Y) (g: Y c-> Z) :(X c-> Z) :=
	exist_c (comp_hcr_fun (projT2 f) (projT2 g)).

(*
Lemma fcmp_mon_cmpt X Y Z:
	(@composition X Y Z) \is_monotone_computable.
Proof.
Admitted.
*)

Lemma fst_fun_name X Y:
	(fun Lq => match Lq.1  with
		| nil => inl (inl Lq.2)
		| cons a K => inr a.2.1
		end) \is_name_of (exist_c (@fst_hcr X Y)).
Proof.
set psi:= (fun Lq => match Lq.1  with
	| nil => inl (inl Lq.2)
	| cons a K => inr a.2.1
end).
rewrite /=/is_fun_name.
suffices ->: eval (U psi) =~= F2MF (@lprj X Y) by apply frlzr_rlzr => phi x [/=phinx _].
move => phi Fphi.
split => ass; last by rewrite -ass; exists 1.
apply functional_extensionality => q.
have [n val] := ass q.
have U1: U psi 1 phi q = Some (lprj phi q) by trivial.
apply Some_inj.
rewrite -val.
apply esym.
apply/ U_mon; last apply U1.
rewrite /pickle/=.
by case: n val => // n val; lia.
Qed.

Lemma fst_cmpt (X Y: rep_space):
	(exist_c (@fst_hcr X Y): (rep_space_prod X Y) c-> X) \is_recursive_element.
Proof.
exists (fun Lq => match Lq.1  with
	| nil => inl (inl Lq.2)
	| cons a K => inr a.2.1
end).
exact: fst_fun_name.
Defined.

Lemma snd_fun_name X Y:
	(fun Lq => match Lq.1  with
		| nil => inl (inr Lq.2)
		| cons a K => inr a.2.2
		end) \is_name_of (exist_c (@snd_hcr X Y)).
Proof.
set psi:= (fun Lq => match Lq.1  with
	| nil => inl (inr Lq.2)
	| cons a K => inr a.2.2
end).
rewrite /=/is_fun_name.
suffices ->: eval (U psi) =~= F2MF (@rprj X Y) by apply frlzr_rlzr => phi x [_ phiny].
move => phi Fphi.
split => ass; last by rewrite -ass; exists 1.
apply functional_extensionality => q.
have [n val] := ass q.
have U1: U psi 1 phi q = Some (rprj phi q) by trivial.
apply Some_inj.
rewrite -val.
apply esym.
apply/ U_mon; last apply U1.
rewrite /pickle/=.
by case: n val => // n val; lia.
Qed.

Lemma snd_cmpt (X Y: rep_space):
	(exist_c (@snd_hcr X Y) :(rep_space_prod X Y) c-> Y) \is_recursive_element.
Proof.
exists (fun Lq => match Lq.1  with
	| nil => inl (inr Lq.2)
	| cons a K => inr a.2.2
end).
exact: snd_fun_name.
Defined.

(*
Lemma prod_space_cmpt (X Y Z: rep_space) (f: Z c-> X) (g: Z c-> Y):
	f \is_computable_element -> g \is_computable_element ->
	exists (F: Z c-> (rep_space_prod X Y)) (P:	F \is_computable_element),
		((F2MF (@fst X Y)) o (projT1 F) =~= (projT1 f))
		/\
		((F2MF (@snd X Y)) o (projT1 F) =~= (projT1 g)).
Proof.
move => [phi phinf] [psi psing].
have [F Fprop]:= prod_space_cont f g.
exists F; split; last exact: Fprop.
suffices eq: projT1 F =~= (((projT1 f) ** (projT1 g)) o (F2MF (fun z => (z, z)))).
exists (fun Lq => match Lq.2 with
	|inl q' => match phi (Lq.1, q') with
		| inl q'' => inl q''
		| inr a => inr (a, some_answer Y)
	end
	|inr q' => match psi (Lq.1, q') with
		| inl q'' => inl q''
		| inr a => inr (some_answer X, a)
	end
end).
set psiF:=(fun Lq => match Lq.2 with
	|inl q' => match phi (Lq.1, q') with
		| inl q'' => inl q''
		| inr a => inr (a, some_answer Y)
	end
	|inr q' => match psi (Lq.1, q') with
		| inl q'' => inl q''
		| inr a => inr (some_answer X, a)
	end
end).
*)
End COMPUTABLE_ELEMENTS.
