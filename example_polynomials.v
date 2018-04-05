From mathcomp Require Import all_ssreflect all_algebra.
Require Import Qreals QArith Psatz Reals Field.
Require Import core_mf rs_base representation_facts basic_represented_spaces  rs_creals.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section POLYNOMIALS.

Definition poly := list Q.

Fixpoint Qeval (p: poly) q :Q := if p is a :: L then q * (Qeval L q) + a else 0.

Fixpoint add p q :=
  if p is a :: p then
    if q is b :: q then a + b :: (add p q) else a :: p
  else q.

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
have xprcomp: (fun x:R => Rplus x (Q2R r)) \is_prec_function.
apply/ prec_fun_comp; [apply diag_prec_fun | | ] => /=.
apply/ prec_fun_comp; [ apply prod_prec_fun; [apply id_prec_fun | apply cnst_fun_prec] | | ].
apply (Q_cmpt_elts r).
apply Rplus_prec.
done.
done.
apply /prec_fun_comp; [apply diag_prec_fun | | ].
apply /prec_fun_comp; [apply prod_prec_fun; [apply id_prec_fun | apply comp] | | ].
apply /prec_fun_comp; [apply Rmult_prec | | ].
apply xprcomp.
done.
done.
done.
Defined.

Compute Qred (projT1 (Reval_prec (T 5)) (projT1 (Q_cmpt_elts (2#3))) (1#100)).
(* This is exact due to the names used for rationals. *)
Compute Qred(Qeval (T 5) (2#3) - projT1 (Reval_prec (T 5)) (projT1 (Q_cmpt_elts (2#3))) (1#100)).
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

Definition ply := rep_space_list rep_space_R.

Fixpoint eval (p: ply) x: R := 
  if p is a :: q then x * (eval q x) + a else 0.

Definition poly_R :=
	{f: R -> R | exists p:ply, forall x, eval p x = f x}.

Definition exist_ply:= @exist (R -> R) (fun f => (exists p:ply, forall x, eval p x = f x)).

Lemma ply_exist p:
	exists q, forall x, eval q x = eval p x.
Proof. by exists p. Qed.

Definition quot p := @exist_ply (eval p) (ply_exist p).

Definition rep_poly_R := (F2MF quot) o (@delta _).

Lemma rep_poly_R_sing:
	rep_poly_R \is_single_valued.
Proof.
apply comp_sing; last exact: (rep_sing _).
exact: F2MF_sing.
Qed.

Lemma rep_poly_R_rep:
	rep_poly_R \is_representation.
Proof.
split; first exact rep_poly_R_sing.
move => [f [p evlpf]].
have [phi phinp]:= rep_sur ply p.
exists phi.
rewrite /rep_poly_R.
split; last by move => a b; exact: F2MF_tot.
exists p; split => //.
by rewrite /F2MF/quot; apply eq_sub; apply functional_extensionality.
Qed.

Canonical rep_space_poly_R := @make_rep_space
	poly_R
	_
	_
	_
	(some_answer (rep_space_list rep_space_R))
	(countable_questions (rep_space_list rep_space_R))
	(countable_answers (rep_space_list rep_space_R))
	rep_poly_R_rep
	.

Lemma quot_prec:
	(fun p => quot p:poly_R) \is_prec_function.
Proof.
exists (fun phi => phi).
move => phi p phinp.
rewrite /delta/=/rep_poly_R/=.
split; last by move => a b; apply: F2MF_tot.
by exists p.
Qed.

Definition quot_inv (f: poly_R) (p: ply):= forall x, eval p x = projT1 f x.

Lemma quot_inv_prec:
	quot_inv \is_prec.
Proof.
exists (fun phi => phi).
move => phi stuff.
split.
	move: stuff => [p [[pf [[[q  [phinq _]] _] eq]]] _].
	exists q.
	split; first by exists phi.
	by move => psi <-; exists q.
move: stuff => [q[[pf [phinpf _]] eq]] r [[psi [<- phinr]] prop].
split.
	exists (exist_ply (ply_exist r)); split => //.
	split; last by move => a b; exact: F2MF_tot.
	by exists r => //.
move => [pf' [p peqpf']] _.
by exists p.
Qed.

Lemma quot_inv_not_sing:
	~ quot_inv \is_single_valued.
Proof.
move => sing.
have val: quot_inv (exist_ply (ply_exist [::])) [::0%R] by move => x /=; lra.
have evl: (quot_inv (exist_ply (ply_exist [::])) [::]) by trivial.
by have/=:= sing (exist_ply (ply_exist [::])) [::0%R] [::] val evl.
Qed.

Lemma quot_inv_tot:
	quot_inv \is_total.
Proof.
by move => [pf [p val]]; exists p.
Qed.

Lemma eval_ply_prec:
	(fun px => eval px.1 px.2) \is_prec_function.
Proof.
pose g (x: R) := 0%R.
have gprec: g \is_prec_function.
	apply cnst_fun_prec.
	replace (0%R) with (Q2R 0%Q) by by rewrite /Q2R/=; lra.
	apply: Q_cmpt_elts.
pose h (zaT: rep_space_prod rep_space_R (rep_space_prod rep_space_R rep_space_R))
	:= (zaT.1 * zaT.2.2 + zaT.2.1)%R.
rewrite /= in h.
suffices evp: (fun xp => eval xp.2 xp.1) \is_prec_function.
	by apply/ prec_fun_comp; [apply switch_prec | apply evp | ].
suffices hprec: h \is_prec_function.
	apply/ (list_rs_prec_pind gprec hprec).
	by move => [z K]; rewrite /eval; elim: K => // a K /= ->.
rewrite /h.
apply/ prec_fun_comp; [apply prod_prec_fun; [ apply id_prec_fun | apply switch_prec]| | ] => /=.
apply/ prec_fun_comp; [apply prod_assoc_prec | | ] => /=.
apply/ prec_fun_comp; [apply prod_prec_fun; [apply Rmult_prec | apply id_prec_fun]| apply Rplus_prec | ] => /=.
done.
done.
done.
Defined.

Lemma eval_prec:
	(fun px: poly_R * R => projT1 px.1 px.2) \is_prec_function.
Proof.
apply/ prec_fun_prec_comp; [ | apply prod_prec | apply eval_ply_prec | ] => /=.
apply mfpp_tot.
split.
	apply quot_inv_tot.
	apply F2MF_tot.
apply quot_inv_prec.
apply id_prec.
by move => [f x] [p y] [/=qfp <-]/=; rewrite qfp.
Qed.

Fixpoint ply_add (p q:ply) :=
  if p is a :: p then
    if q is b :: q then (a + b)%R :: (ply_add p q) else a :: p
  else q.

Definition ply_multx p := 0%R :: p.

Fixpoint ply_multa a (p: ply) :=  [seq b * a | b <- p]%R.

Fixpoint ply_mult (p q: ply) := 
  if p is a :: p' then ply_add (ply_multa a q) (ply_multx (ply_mult p' q)) else [::]%R.

(* As example the chebycheff polynomials: *)
Fixpoint ply_T n := 
  if n is n'.+1 then
   if n' is n''.+1 then ply_add (ply_multa 2 (ply_multx (ply_T n'))) [seq -i | i <- ply_T n'']%R
   else [::0%R; 1%R]
  else [::1%R].

Definition seq_add (fg: (nat -> R) * (nat -> R)) :=
	(fun n => (fg.1 n) + (fg.2 n))%R.

Lemma seq_add_prec_fun:
	seq_add \is_prec_function.
Proof.
have [Mplus Mprop]:= Rplus_prec.
exists (fun (phi: names (rep_space_prod (rep_space_usig_prod rep_space_R)(rep_space_usig_prod rep_space_R))) q =>
	Mplus (name_pair (fun q' => lprj phi (q.1, q')) (fun q' => rprj phi (q.1, q'))) q.2).
move => phi [an bn] [/=phinan phinbn] n/=.
rewrite /seq_add/=.
apply ((Mprop (name_pair (fun q' => lprj phi (n, q')) (fun q' => rprj phi (n, q')))) (an n, bn n)).
by split; rewrite rprj_pair lprj_pair/=; [apply phinan | apply phinbn].
Qed.

Definition seq_mult (fg: (nat -> R) * (nat -> R)) :=
	(fun n => (fg.1 n) * (fg.2 n))%R.

Lemma seq_mult_prec_fun:
	seq_mult \is_prec_function.
Proof.
have [Mmult Mprop]:= Rmult_prec.
exists (fun (phi: names (rep_space_prod (rep_space_usig_prod rep_space_R)(rep_space_usig_prod rep_space_R))) q =>
	Mmult (name_pair (fun q' => lprj phi (q.1, q')) (fun q' => rprj phi (q.1, q'))) q.2).
move => phi [an bn] [/=phinan phinbn] n/=.
rewrite /seq_mult/=.
apply ((Mprop (name_pair (fun q' => lprj phi (n, q')) (fun q' => rprj phi (n, q')))) (an n, bn n)).
by split; rewrite rprj_pair lprj_pair/=; [apply phinan | apply phinbn].
Qed.

Definition poly_add (fg: poly_R * poly_R) (h: poly_R):=
	forall x, (projT1 fg.1 x + projT1 fg.2 x = projT1 h x)%R.

Lemma poly_add_prec:
	poly_add \is_prec.
Proof.
Admitted.

Definition poly_mult (fg: poly_R * poly_R) (h: poly_R):=
	forall x, (projT1 fg.1 x * projT1 fg.2 x = projT1 h x)%R.
End POLYNOMIALS.