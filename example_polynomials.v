From mathcomp Require Import all_ssreflect all_algebra.
Require Import Qreals QArith Psatz Reals Field.
Require Import multi_valued_functions representation_facts.
Require Import FunctionalExtensionality.
Require Import example_approximating_reals_with_rationals representations.
Require Import basic_represented_spaces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section POLYNOMIALS.

Definition poly := list Q.

Fixpoint Qeval (p: poly) q :Q := if p is a :: L then q * (Qeval L q) + a else 0.

Lemma poly_equal p q :
	(forall r, Qeval p r == Qeval q r) <-> forall n, nth 0%Q p n == nth 0%Q q n.
Proof.
Admitted.

Lemma nth_iota p k:
	nth 0%Q [seq nth 0%Q p n0 | n0 <- iota 0 (size p)] k == nth 0%Q p k.
Proof.
case E: (k < size p)%nat.
rewrite (@nth_map nat 0%nat Q 0%Q (fun n => nth 0%Q p n) k (iota 0 (size p))); last by rewrite size_iota.
by rewrite seq.nth_iota => //.
have ineq: (size p <= k)%nat by rewrite leqNgt E.
by rewrite nth_default; [ rewrite nth_default | rewrite size_map size_iota].
Qed.

Fixpoint add p q :=
  if p is a :: p then
    if q is b :: q then a + b :: (add p q) else a :: p
  else q.

Lemma Qeval_add (p q: poly) (r: Q) :
	Qeval (add p q) r == (Qeval p r) + (Qeval q r).
Proof.
case: (size q <= size p)%nat.
	set q' := map (fun n => nth 0%Q q n) (iota 0%nat (size p)).
	have eq: forall n, nth 0%Q q n == nth 0%Q q' n.
		admit.
	move: ((poly_equal q q').2 eq).
	elim: (size p) q' eq.
Admitted.

Definition multx p := 0 :: p.

Fixpoint multa a p :=  [seq b * a | b <- p].

Fixpoint mult p q := 
  if p is a :: p' then add (multa a q) (multx (mult p' q)) else [::].


(* As example the chebycheff polynomials: *)
Fixpoint T n := 
  if n is n'.+1 then
   if n' is n''.+1 then add (multa (2#1) (multx (T n'))) [seq -i | i <- T n'']
   else [::0; 1]
  else [::1].

Fixpoint Reval (p: poly) x : R := 
  if p is a :: L then x * Reval L x + Q2R a else 0.

(* This does not evaluate *)
Compute Reval (T 5) (Q2R (2#3)).

(* But you can use the library to prove computability and then evaluate: *)
Lemma Reval_prec (p: poly):
	(Reval p) \is_prec_function.
Proof.
elim p.
	exists (fun phi eps => 0).
	move => phi x phinx eps ineq; rewrite {1}/Q2R/=.
	apply/ Rbasic_fun.Rabs_le; lra.
move => r q comp /=.
have rcomp: (fun x:R => Q2R r) \is_prec_function.
	exists (fun _ eps => r) => phi x phinx eps ineq.
	apply/ Rbasic_fun.Rabs_le; lra.
have xprcomp: (fun x:R => Rplus x (Q2R r)) \is_prec_function.
	apply/ prec_fun_comp; [ | apply Rplus_prec | ].
		apply/ prec_fun_comp; [apply diag_prec_fun | apply prod_prec_fun | ].
				by apply id_prec_fun.
			by apply rcomp.
		by trivial.
	by trivial.
have xmexcomp: (fun x:R => Rmult x (Reval q x)) \is_prec_function.
	apply /prec_fun_comp; [ | apply Rmult_prec | ].
		apply /prec_fun_comp; [apply diag_prec_fun | apply prod_prec_fun | ].
				by apply id_prec_fun.
			by apply comp.
		by trivial.
	by trivial.
by apply /prec_fun_comp; [apply xmexcomp | apply xprcomp | ].
Defined.

Compute projT1 (Reval_prec (T 5)) (projT1 (Q_cmpt_elts (2#3))) (1#100).
(* This is exact due to the names used for rationals: *)
Compute Qeval (T 5) (2#3) - projT1 (Reval_prec (T 5)) (projT1 (Q_cmpt_elts (2#3))) (1#100).
(* However, the interpretation of the return value should be that it is an approximation
to precision 1#100. Of course in this case there are easier ways to do this. For instance: *)
Goal forall x, x = Reval (T 5) (Q2R (2#3)) -> x = x.
move=> x H.
compute in H.
field_simplify in H.
by [].
Qed.
(* But the advantage of the above is that it still works if the input reals are non rationals.
Unfortunately I have do not have any algorithms to compute non-rational numbers so far. *)

(* You can also define a type for polynomials *)

Definition ply := list R.

Fixpoint eval (p: ply) q :R := 
  if p is a :: L then q * (eval L q) + a else 0.

Definition poly_R :=
	{f: R -> R | exists p:ply, forall x, eval p x = f x}.

Definition exist_ply:= @exist (R -> R) (fun f => (exists p:ply, forall x, eval p x = f x)).

Lemma ply_equal p q :
	eval p = eval q <-> forall n, nth 0%R p n = nth 0%R q n.
Proof.
Admitted.

Lemma nth_iota p k:
	nth 0%R [seq nth 0%R p n0 | n0 <- iota 0 (size p)] k = nth 0%R p k.
Proof.
case E: (k < size p)%nat.
rewrite (@nth_map nat 0%nat R 0%R (fun n => nth 0%R p n) k (iota 0 (size p))); last by rewrite size_iota.
by rewrite seq.nth_iota => //.
have ineq: (size p <= k)%nat by rewrite leqNgt E.
by rewrite nth_default; [ rewrite nth_default | rewrite size_map size_iota].
Qed.

Definition quot np (f: poly_R) :=
	exists p, size p = np.1 /\ eval p = projT1 f /\ forall n, nth 0%R p n = np.2 n.

Definition rep_poly_R := quot o (@delta (rep_space_prod rep_space_nat (rep_space_usig_prod rep_space_R))).

Lemma rep_poly_R_sing:
	rep_poly_R \is_single_valued.
Proof.
apply comp_sing; last exact: (rep_sing _).
move => np f g [p [lp [valp fp]]] [q [lq [valq gq]]].
apply eq_sub; rewrite -valp -valq.
rewrite (ply_equal p q) => n.
by rewrite (fp n) (gq n).
Qed.

Lemma rep_poly_R_rep:
	rep_poly_R \is_representation.
Proof.
split; first exact rep_poly_R_sing.
move => [f [p evlpf]].
rewrite /rep_poly_R.
have [phi phinxn]:= (rep_sur (rep_space_usig_prod rep_space_R) (fun n => nth 0%R p n)).
exists (@name_pair rep_space_nat (rep_space_usig_prod rep_space_R) (fun star => size p) (phi)).
split.
	exists (size p, (fun n => nth 0%R p n)).
	split; first by split; rewrite lprj_pair => //=.
	exists p;	split => //=; split; first by apply functional_extensionality => x; rewrite (evlpf x).
	move => n; by case: n.
move => [/=n yn] [/=phinn phinyn].
have ex: exists p, forall x, eval (p) x = f x by exists p.
exists (exist_ply ex).
exists (map (fun n => nth 0%R p n) (iota 0 n)).
split; first by rewrite size_map; apply size_iota.
split => /=.
	have ->: f = (eval p) by apply functional_extensionality => x.
	apply ply_equal => k.
	rewrite lprj_pair in phinn.
	rewrite -phinn.
	exact: nth_iota.
move => m.
rewrite lprj_pair/id_rep in phinn.
rewrite rprj_pair in phinyn.
rewrite (rep_sing _ _ _ _ phinyn phinxn).
rewrite -phinn.
exact: nth_iota.
Qed.

Canonical rep_space_poly_R := @make_rep_space
	poly_R
	_
	_
	_
	((0%nat, 0%Q))
	(countable_questions (rep_space_prod rep_space_nat (rep_space_usig_prod rep_space_R)))
	(countable_answers (rep_space_prod rep_space_nat (rep_space_usig_prod rep_space_R)))
	rep_poly_R_rep
	.

Definition evaluation (p: poly_R) (x: R):= (projT1 p) x.

Lemma poly_eval_prec_fix p:
	p \is_computable_element -> (fun x => evaluation p x) \is_prec_function.
Proof.
move => [/=phi phinp].
set pn := fix pn n := match n with
	| 0%nat => [::]
	| S n' => ((fun eps => (phi (inr (n', eps))).2) :: pn n')
end.
set q := pn (phi (inl star)).1.
elim: q.
exists (fun phi eps => 0%Q).
	move => psi x psinx.
	have : evaluation p x = 0%R.
	rewrite /evaluation.
	rewrite
elim: (phi (inl star)).1.
	exists (fun phi eps => 0).
	move => phi x phinx eps ineq; rewrite {1}/Q2R/=.
	apply/ Rbasic_fun.Rabs_le; lra.
move => r q comp /=.
have rcomp: (fun x:R => Q2R r) \is_prec_function.
	exists (fun _ eps => r) => phi x phinx eps ineq.
	apply/ Rbasic_fun.Rabs_le; lra.
have xprcomp: (fun x:R => Rplus x (Q2R r)) \is_prec_function.
	apply/ prec_fun_comp; [ | apply Rplus_prec | ].
		apply/ prec_fun_comp; [apply diag_prec_fun | apply prod_prec_fun | ].
				by apply id_prec_fun.
			by apply rcomp.
		by trivial.
	by trivial.
have xmexcomp: (fun x:R => Rmult x (Reval q x)) \is_prec_function.
	apply /prec_fun_comp; [ | apply Rmult_prec | ].
		apply /prec_fun_comp; [apply diag_prec_fun | apply prod_prec_fun | ].
				by apply id_prec_fun.
			by apply comp.
		by trivial.
	by trivial.
by apply /prec_fun_comp; [apply xmexcomp | apply xprcomp | ].
Defined.

End POLYNOMIALS.