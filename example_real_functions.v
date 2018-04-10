(* This is example uses the Cauchy representation on the reals. This means that everything is executable 
but slow. *)

From mathcomp Require Import all_ssreflect.
Require Import all_rs rs_reals_creals example_polynomials.
Require Import Qreals Reals Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import QArith.
Local Open Scope R_scope.

Section REALFUNCTIONS.

(* To prove that the power function is computable, we first prove that for each n the function x => x^n is
computable (prec is for "primitive recursive" and is stronger than computability). *)
Lemma pow_n_prec:
	forall n, (fun x => pow x n) \is_prec_function.
Proof.
elim; first by exists (fun phi eps => 1%Q) => phi x phinx eps epsg0; split_Rabs; lra.
move => n ih /=.
apply/ prec_fun_comp; [apply diag_prec_fun | | ].
	apply/ prec_fun_comp; [ apply prod_prec_fun; [ apply (id_prec_fun) | apply ih] | apply Rmult_prec | ].
	by move => x.
by trivial.
Defined.

(* The above is directly executable. To execute in a rational number q, you first have to get a name of the
rational number. You can either proof that (fun _ => q) does the trick or use the lemma Q_cmpt_elts.
To get the algorithmic content use projT1. So the following composes an algorithm extracted from the
above lemma where n is set to 5 with an algorithm extracted from the lemma Q_cmpt_elts where the rational
parameter is set to 1/2 to get an algorithm that produces arbitrary precision approximations to (1/2)^5 and
we execute this algorithm on input 1/100 to get a 1/100-approximation. *)
Compute (projT1 (pow_n_prec 5)) (projT1 (Q_cmpt_elts (1#2))) (1#100)%Q.

(* The proof that x^n is computable is uniform and can be turned into a statment that the function (n,x) => x^n
is computable. In terms of executability this does not add anything. *)
Lemma pow_prec:
	(fun p => pow p.1 p.2) \is_prec_function.
Proof.
exists (fun phi eps => (projT1 (pow_n_prec ((rprj phi) (star:questions rep_space_nat)))) (lprj phi) eps).
move => phi x [lphinx rphinn].
have prop:= (projT2 (pow_n_prec (rprj phi star)) (lprj phi) x.1 lphinx).
by have ->: x.2 = rprj phi star by rewrite /delta/= in rphinn; rewrite rphinn.
Qed.

(* The standard library likes to use real epsilons and strict inequality, we use rational epsilons and <=.
These differences are irrelevant since the rationals accumulate at zero. For instance, compare the limit
"Un_cv" defined in the standard library and the limit "lim" defined in this library. Here "=~=" is the
a notation for the equality of multivalued functions and translates to forall s t, f s t <-> g s t *)
Lemma Uncv_lim:
	Un_cv =~= lim.
Proof.
move => xn x.
split => limxnx eps epsg0.
	have [N Nprop]:= limxnx (Q2R eps) epsg0.
	exists N => n ineq.
	have ineq': (n >= N)%coq_nat by apply /leP.
	have:= Nprop n ineq'; rewrite /R_dist.
	split_Rabs; lra.
have [qeps [qepsg0 qepsleps]]:= Q_accumulates_to_zero epsg0.
have [N Nprop]:= limxnx (qeps) qepsg0.
exists N => n ineq.
have ineq': (N <= n)%nat by apply /leP.
have:= Nprop n ineq'; rewrite /R_dist.
split_Rabs; lra.
Qed.

(* Thus, the discontinuity proven for lim can be transfered to Un_cv *)
Lemma Uncv_not_cont:
	~ Un_cv \has_continuous_realizer.
Proof.
move => discont.
apply lim_not_cont.
rewrite -Uncv_lim.
done.
Qed.

(* And vice verca: *)
Lemma lim_mult xn x yn y:
	lim xn x -> lim yn y -> lim (ptw (fun p => p.1 * p.2) (xn, yn)) (x * y).
Proof.
move => limxnx limyny.
rewrite -(Uncv_lim _).
by apply CV_mult; rewrite (Uncv_lim _).
Qed.

(* It is easy to define subspaces *)
Definition I := (@rep_space_sub_space rep_space_R (fun x => -1 <= x <= 1)).
End REALFUNCTIONS.