From mathcomp Require Import all_ssreflect.
Require Import all_rs rs_reals_creals.
Require Import Qreals Reals Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import QArith.
Local Open Scope R_scope.

Section REALFUNCTIONS.
(* This is example uses the Cauchy representation on the reals. This means that everything is executable but slow. *)
Check rep rep_space_R.
(* The represented set is the type of real numbers from the standard library. *)
Compute space rep_space_R.
(* The names are functions from rationals to rationals *)
Compute names rep_space_R.
(* Where such a function phi is a name of a real number x if on positive rational
input eps it returns a rational eps approximation. *)
Print rep_R.
(* Here is the information that is saved: *)
Print rep_space_R.

(* The tools provided by the library are that the arithmetic operations are computable, or more
specifically prec functions (prec is for "primitive recursive" and is stronger than computability) *)
Check Rplus_prec.
Check Rplus_cmpt.
(* The proof of computability is just applying the general argument that a prec function is computable *)
Print Rplus_cmpt.

(* As an example, let's prove that the power function is computable. To do this, we first prove by 
induction that for each n the function x => x^n is computable. *)
Lemma pow_n_prec:
	forall n, (fun x => pow x n) \is_prec_function.
Proof.
elim.
	Locate "\is_prec_function".
	Print is_prec_fun.
	(* We have to specify a realizer of the constant one function. *)
	exists (fun phi eps => 1%Q).
	Locate "\is_realizer_function_for".
	rewrite /frlzr.
	(* The rewriting is not neccessary. *)
	move => phi x phinx.
	Locate "\is_name_of".
	(* delta is a generic representation. Simplifying reveals the concrete representation in this case *)
	rewrite /=.
	rewrite /rep_R.
	move => eps epsg0.
	(* The rest can automatically be done by the solver for linear inequalities over the reals. *)
	split_Rabs; lra.
move => n ih /=.
(* In this case we need to decompose the function into a composition of functions we already know
to be prec by using the lemma that proves that the composition of prec functions is prec. *)
apply/ prec_fun_comp => /=.
	(* First off we need two copies of x, one to multiply with and one to feed to the function x^n.
	This can be done using the diagonal function. *)
	apply diag_prec_fun.
	(* Since we still need to apply the function x^n and multiply, we need to split into a composition
	again. The second operation will be multiplication, so we apply that right away. *)
	apply/ prec_fun_comp; [ | apply Rmult_prec | ]  => /=.
	(* This last function is a function on a product space and we want to specify it componentwise.
	There is a lemma that facilitates this. *)
	apply prod_prec_fun => /=.
		(* The first argument should just be copied and not be modified. This is a prec operatioon. *)
		by apply (id_prec_fun).
	(* The operation in the second component is x -> x^n and prec by induction hypothesis. *)
	by apply ih.
(* Whats left over is to prove that the decomposition we specified actually produces the function.
This is typically trivial if everything was done correctly. *)
by trivial.
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
(* pow is defined inductively *)
rewrite /pow.
(* So one way of proving this is to use the induction principle for prec_functions on the natural numbers.
Note that there is a parameter r. Usually function spaces work well and this parameter can be curried.
Unfortunately when working with prec functions, this is not true. Thus the induction principle looks
a little more complicated than one might expect. *)
Check nat_rs_prec_pind.
apply (@nat_rs_prec_pind _ _ (fun _ => Q2R 1) (fun p => p.1 * p.2)).
	apply/ cnst_prec_fun.
	exact: Q_cmpt_elts.
exact: Rmult_prec.
move => [r n].
elim: n => //=.
	by rewrite /Q2R/=; lra.
by move => n /= ->.
Defined.

(* If one is familiar with the representations of the natural and real numbers, one can also specify an
algorithm directly and prove it correct. *)
Lemma pow_prec':
	(fun p => pow p.1 p.2) \is_prec_function.
Proof.
exists (fun phi eps => (projT1 (pow_n_prec (rprj phi (star: questions rep_space_nat)))) (lprj phi) eps).
abstract by move => phi [x n] [/=phinx phinn]; rewrite phinn; apply ((projT2 (pow_n_prec n)) (lprj phi) x phinx).
Defined.
(* Both of these are directly executable again. *)
Compute (projT1 pow_prec (name_pair (projT1 (Q_cmpt_elts (1#2))) (fun _ => 5%nat))) (1#100)%Q.
Compute (projT1 pow_prec' (name_pair (projT1 (Q_cmpt_elts (1#2))) (fun _ => 5%nat))) (1#100)%Q.
(* The later is the better practice as it keeps the non algorithmic part of the proof opaque.
Note that if some essential part of the proof is opaque, the computation will usually take
forever. But in case it comes to an end form the output it is usually apparent what needs to
be done to restore executability. Unfortunately, executability is somewhat fragile it can
also be broken by the use of lra in some cases. *)

(* The library also provides an algorithm for taking efficient limits *)
Check lim_eff_prec.
(* Here, lim_eff is the restriction of the limit operator  *)
Print lim.
(* To the efficiently convergent Cauchy sequences *)
Print eff_conv.
(* The restriction to efficiently convergent sequences is neccessary, as the limit
operator is discontinuous on its natural domain. *)
Check lim_not_cont.
(* And thus also not computable. *)

(* The standard library provides its own limit operator, which is called Un_cv *)
Print Un_cv.
(* Note, that there is a slight difference, as the limit operator used in the standard library makes
eps a real number and uses strict inequality. By contrast, lim uses a rational epsilons and <=.
The former has the advantage that it is not tied to any representation or arbitrary choice of a dense
subsequence. The later has the advantage that it makes computation easier. In particular the
discontinuous and therefore also uncomputable up function that is integral part of the type of reals
due to the archemidean Axiom *)
Print archimed.
(* is often used to translate an error bound eps into a discrete quantity like the index of a sequence.
It's restriction to the rationals is computable. *)
Print upQ.
Print Int_partQ.
Check archimedQ.
(* Some ineffient proofs can be made efficient by replacing real epsilons by rational epsilons and uses of
up function by uses of the upQ function. Of course, one has to prove that this does not change the
statement. As example consider the limit operator, not that "=~=" is a notation for the equality of
multivalued functions and translates to forall s t, f s t <-> g s t *)
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

(* On the other hand, the properties proved about Un_cv in the standard library can be transferred: *)
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