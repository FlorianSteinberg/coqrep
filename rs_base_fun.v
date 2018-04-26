From mathcomp Require Import all_ssreflect.
Require Import all_core rs_base rs_base_sub rs_base_prod.
Require Import FunctionalExtensionality ClassicalFacts ClassicalChoice Psatz.

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

Definition exist_fun (X Y: rep_space) (g: X -> Y) ghcr: X c-> Y:=
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
have []:= (count_sur (questions X)).2.
	by split; [apply: inhabits (some_question X) | apply (countable_questions X)].
move => cnt sur.
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
Definition evaluation X Y (fx: (X c-> Y) * X):= (projT1 fx.1) fx.2.

Lemma eval_sing X Y:
	(@evaluation X Y) \is_single_valued.
Proof.
move => [f x] y z fxy fxz.
have sing:= (projT2 f).1.1.
apply/ sing; [apply fxy| apply fxz].
Qed.

Lemma eval_tot X Y:
	(@evaluation X Y) \is_total.
Proof.
move => [f x].
have [y fxy]:= ((projT2 f).1.2 x).
by exists y.
Qed.

Lemma eval_rlzr X Y:
	(eval (fun n psiphi q => U (lprj psiphi) n (rprj psiphi) q)) \is_realizer_of (@evaluation X Y).
Proof.
set R:=(fun n psiphi q => U (lprj psiphi) n (rprj psiphi) q).
move => psiphi [y [[[f x] [[/=psinf phinx] fxy]] prop]].
rewrite /is_fun_name/= in psinf.
have eq: (eval (U (lprj psiphi))) (rprj psiphi) = (eval R) psiphi by trivial.
have Rsing: (oeval R) \is_single_valued.
	apply mon_sing_op => /= n m phi q' a' nlm Rnphiqa.
	apply/ U_mon; [ apply nlm | apply Rnphiqa ].
have [Fpsiphi val]:= (@rlzr_dom _ _ (sval f) _ psinf (rprj psiphi) x phinx ((projT2 f).1.2 x)).
have Fpsiphiny: Fpsiphi \is_name_of y.
	by apply/ rlzr_val_sing; [ apply (projT2 f).1.1 | apply psinf | apply phinx | apply fxy | ].
split.
	exists y; split; first by exists Fpsiphi.
	move => psi eval; rewrite (Rsing psiphi psi Fpsiphi) => //; exists y.
	by apply/ rlzr_val_sing; [ apply (projT2 f).1.1 | apply psinf | apply phinx | apply fxy | ].
move => y' [[Fphi [val' Fphiny]]cond].
split.
	exists (f,x); split => //.
	rewrite (Rsing psiphi Fphi Fpsiphi) in Fphiny => //.
	by rewrite (rep_sing Y Fpsiphi y' y).
move => [f' x'] [psinf' phinx'].
exists y; rewrite (rep_sing (X c-> Y) (lprj psiphi) f' f) => //.
by rewrite (rep_sing X (rprj psiphi) x' x).
Qed.

Lemma eval_cmpt X Y:
	(@evaluation X Y) \is_computable.
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
	f \is_computable_element -> (projT1 f) \is_monotone_computable.
Proof. move => [psiF comp]; exists (U psiF); split => //; exact: U_mon. Defined.

Lemma prod_space_cont (X Y Z: rep_space) (f: Z c-> X) (g: Z c-> Y):
	exists (F: rep_space_cont_fun Z (rep_space_prod X Y)),
		((F2MF (@fst X Y)) o (projT1 F) =~= (projT1 f))
		/\
		((F2MF (@snd X Y)) o (projT1 F) =~= (projT1 g)).
Proof.
set F := (((projT1 f) ** (projT1 g)) o (F2MF (fun z => (z, z)))).
have Fsing: F \is_single_valued.
	apply comp_sing; last exact: F2MF_sing.
	apply mfpp_sing; split; [apply (projT2 f).1.1 | apply (projT2 g).1.1].
have Ftot: F \is_total.
	apply comp_tot; first exact: F2MF_tot.
	apply mfpp_tot; split; [apply (projT2 f).1.2 | apply (projT2 g).1.2].
have Fhcr: F \has_continuous_realizer.
	by apply comp_hcr; [apply diag_hcr | apply mfpp_hcr; [apply (projT2 f).2 | apply (projT2 g).2 ]].
exists (exist_c Fsing Ftot Fhcr).
split.
	rewrite /=/F F2MF_comp.
	rewrite sing_comp => //=; rewrite /mf_prod_prod/=; [ | | ].
			rewrite /F2MF => z x.
			split => [val| fzx [x' y] [fzx' gzy]]; last by rewrite ((projT2 f).1.1 z x x').
			have [x' fzx']:= (projT2 f).1.2 z.
			have [y gzy]:= (projT2 g).1.2 z.
			by rewrite -(val (x',y) (conj fzx' gzy)) => //.
		move => z p p' [fzp fzp'] [gzp gzp'].
		by apply injective_projections; [rewrite ((projT2 f).1.1 z p.1 p'.1) | rewrite ((projT2 g).1.1 z p.2 p'.2)].
	move => z.
	have [x fzx]:= (projT2 f).1.2 z.
	have [y gzy]:= (projT2 g).1.2 z.
	by exists (x, y).
rewrite /=/F F2MF_comp sing_comp => //=; rewrite /mf_prod_prod/=; [ | | ].
rewrite /F2MF => z y.
split => [val| gzy [x y'] [fzx gzy']]; last by rewrite ((projT2 g).1.1 z y y').
have [y' gzy']:= (projT2 g).1.2 z.
have [x fzx]:= (projT2 f).1.2 z.
by rewrite -(val (x,y') (conj fzx gzy')) => //.
	move => z p p' [fzp fzp'] [gzp gzp'].
	by apply injective_projections; [rewrite ((projT2 f).1.1 z p.1 p'.1) | rewrite ((projT2 g).1.1 z p.2 p'.2)].
move => z.
have [x fzx]:= (projT2 f).1.2 z.
have [y gzy]:= (projT2 g).1.2 z.
by exists (x, y).
Qed.

Definition id_fun X := (exist_fun (id_hcr X)).

Lemma id_comp_elt X:
	(id_fun X : X c-> X) \is_computable_element.
Proof.
exists (fun p => match p.1: seq (questions X* answers X) with
		| nil => inl (p.2:questions X)
		| (q,a):: L => inr (a: answers X)
	end).
abstract by pose id_name p := match p.1: seq (questions X* answers X) with
		| nil => inl (p.2:questions X)
		| (q,a):: L => inr (a: answers X)
	end; rewrite /=/is_fun_name/=/rlzr id_comp -{1}(comp_id (rep X));
	apply /tight_comp_r/ (mon_cmpt_op); [exact: U_mon | move => phi q; exists 1].
Defined.

Definition fun_comp X Y Z (f: X c-> Y) (g: Y c-> Z) :(X c-> Z) :=
	exist_c (comp_sing (projT2 g).1.1 (projT2 f).1.1)
		(comp_tot (projT2 f).1.2 (projT2 g).1.2)
		(comp_hcr (projT2 f).2 (projT2 g).2).

Definition composition X Y Z := F2MF (fun fg => @fun_comp X Y Z fg.1 fg.2).

Lemma fcmp_sing X Y Z:
	(@composition X Y Z) \is_single_valued.
Proof. exact: F2MF_sing. Qed.

Lemma fcmp_tot X Y Z:
	(@composition X Y Z) \is_total.
Proof. exact: F2MF_tot. Qed.

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
		end) \is_name_of (exist_fun (@fst_hcr X Y)).
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
	(exist_fun (@fst_hcr X Y): (rep_space_prod X Y) c-> X) \is_computable_element.
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
		end) \is_name_of (exist_fun (@snd_hcr X Y)).
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
	(exist_fun (@snd_hcr X Y) :(rep_space_prod X Y) c-> Y) \is_computable_element.
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
