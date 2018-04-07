From mathcomp Require Import all_ssreflect.
Require Import all_core all_rs_base rs_one.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section OPTIONSPACES.
Definition rep_opt X phi x := match x with
	| some x => (phi (inl star)).1 = some star
		/\
		 @delta X (fun q => (phi (inr q)).2) x
	| None => (phi (inl star)).1 = None
end.

Lemma rep_opt_sing X:
	(@rep_opt X) \is_single_valued.
Proof.
move => phi x y phinx phiny.
case: x phinx.
	case: y phiny; last by move => /= Nope a [eq phina]; rewrite eq in Nope.
	move => a/= [eq phina] b [eq' phinb].
	by rewrite (rep_sing X (fun q => (phi (inr q)).2) a b).
case: y phiny => //.
move => /= a [eq phina] Nope.
by rewrite eq in Nope.
Qed.

Lemma rep_opt_rep X:
	(@rep_opt X) \is_representation.
Proof.
split; first exact: rep_opt_sing.
move => x.
case x => [a | ].
	have [phi phinx]:= (rep_sur X a).
	by exists (fun q => (Some star, if q is inr q' then phi q' else some_answer X)).
by exists (fun q => (None, some_answer X)).
Qed.

Canonical rep_space_opt (X: rep_space) := @make_rep_space
	(option X)
	(one + questions X)
	(option one * answers X)
	(@rep_opt X)
	((None, some_answer X))
	(sum_count one_count (countable_questions X))
	(prod_count (option_count one_count) (countable_answers X))
	(@rep_opt_rep X).

Notation unsm phi:= (fun q => (phi (inr q)).2).

Lemma unsm_prec (X: rep_space):
	(fun ox (x: X) => ox = some x) \is_prec.
Proof.
exists (fun phi q => unsm phi q).
move => phi [x [[ox [phinox eq]] _]].
rewrite eq in phinox. move: phinox => [/= stuff name].
split.
	exists x; split; first by exists (unsm phi).
	by move => psi <-; exists x.
move => t [[psi [<- phint]]].
rewrite (rep_sing _ (unsm phi) t x) => //.
split.
	exists ox; split => //; rewrite /rep_opt eq; first done.
move => s a; exists x.
rewrite (rep_sing _ phi s ox) => //.
by rewrite eq.
Qed.

Lemma option_rs_prec_inv (X: rep_space) (Y: rep_space) (f: option X -> Y):
	f \is_prec_function
	->
	(fun a => f (some a)) \is_prec_function * (f None) \is_computable_element.
Proof.
move => [M Mcmpt].
split.
exists (fun phi => (M (fun q => match q with
	| inl str => (some star, some_answer X)
	| inr q => (some star, phi q)
	end))).
by move => phi x phinx; apply Mcmpt.
by exists (M (fun _ => (None, some_answer X))); apply Mcmpt.
Qed.

Lemma option_rs_prec_ind (X: rep_space) (Y: rep_space) (f: option X -> Y):
	(fun a => f (some a)) \is_prec_function -> (f None) \is_computable_element
	-> f \is_prec_function.
Proof.
move => [M Mcmpt] [N Ncmpt].
exists (fun phi => match (phi (inl star)).1 with
	| None => N
	| Some str => M (fun q => (phi (inr q)).2)
end).
move => phi x phinx.
case: x phinx => [/=a [eq phina] |/= Nope].
by rewrite eq; apply Mcmpt.
by rewrite Nope; apply Ncmpt.
Qed.

Lemma Some_prec (X: rep_space):
	(@Some X) \is_prec_function.
Proof.
by exists (fun phi q => if q is inr q' then (Some star, phi q') else (Some star, some_answer X)).
Qed.
End OPTIONSPACES.
Notation unsm phi:= (fun q => (phi (inr q)).2).
