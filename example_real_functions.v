From mathcomp Require Import all_ssreflect.
Require Import all_rs rs_reals rs_reals_creals.
Require Import Qreals Reals Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import QArith.
Local Open Scope R_scope.

Section REALFUNCTIONS.
(* This is example uses the Cauchy representation on the reals. This means that everything is executable but slow. *)
Locate rep_space_R.
(* The represented set is the type of real numbers from the standard library. *)
Compute space rep_space_R.
(* The names are functions from rationals to rationals *)
Compute names rep_space_R.
(* Where such a function phi is a name of a real number x if on positive rational
input eps it returns a rational eps approximation. *)
Print rep_R.
(* Here is the information that is saved: *)
Print rep_space_R.

(* The tools provided by the library include that the arithmetic operations are computable,
or more specifically recursive functions (being recursive is slightly stronger than
computability) *)
Search _ R is_cmpt_fun.
Search _ R is_rec_fun.
(* And that all rational numbers are recursive as real numbers: *)
Check Q_rec_elts.
(* Furthermore, it provides a proof that it is possible to take efficient limits: *)
Check lim_eff_rec.
(* Where efficient limits are limits that guarantee that come with a rate of convergence: *)
Print lim_eff.
(* The library also provides some abstract tools for reasoning about recursive and
computable functions, for instance that these properties are preserved under
composition, and that a constant function with recursive values is recursive. *)
Check rec_fun_comp.
Check cnst_rec_fun.


(* As an example of how to apply these tools, let's prove that the power function
is computable. To do this, we first prove by induction that for each n 
the function x => x^n is computable. *)
Lemma pow_n_rec_fun:
	forall n, (fun x => pow x n) \is_recursive_function.
Proof.
elim.
	(*The function x => x^0 is constant and there is a lemma that a constant function
	is recursive if the element it maps to is. *)
	apply/cnst_rec_fun.
	(*The return value should be the real number 1 and is recursive because it is
	a rational number *)
	apply /(Q_rec_elts 1).
	(* It is left to prove that that claim is true. *)
	move => _ /=.
	by rewrite /Q2R/=; lra.
	(* Alternatively one could have proven this by hand:
	Locate "\is_recursive_function".
	Print is_rec_fun.
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
	split_Rabs; lra. *)
move => n ih /=.
(* In this case we need to decompose the function into a composition of functions we already know
to be recursive by using the lemma that proves that the composition of recursive functions is
recursive. *)
apply/ rec_fun_comp => /=.
	(* First off we need two copies of x, one to multiply with and one to feed to the function x^n.
	This can be done using the diagonal function. *)
	apply diag_rec_fun.
	(* Since we still need to apply the function x^n and multiply, we need to split into a composition
	again. The second operation will be multiplication, so we apply that right away. *)
	apply/ rec_fun_comp; [ | apply Rmult_rec_fun | ]  => /=.
	(* This last function is a function on a product space and we want to specify it componentwise.
	There is a lemma that facilitates this. *)
	apply prod_rec_fun => /=.
		(* The first argument should just be copied and not be modified. This is a prec operatioon. *)
		by apply (id_rec_fun).
	(* The operation in the second component is x -> x^n and prec by induction hypothesis. *)
	by apply ih.
(* Whats left over is to prove that the decomposition we specified actually produces the function.
This is typically trivial if everything was done correctly. *)
by trivial.
by trivial.
Defined.
(* It should be noted, that the above does not mention the Cauchy representation and the
proof can be reused for any representation of the real numbers for which proofs that the
arithmetic operations and the rationals are recurisive are available. *)

(* The above is also directly executable. To execute in a rational number q, you first have to
get a name of the rational number. You can either proof that (fun _ => q) does the
trick or use the lemma Q_cmpt_elts. To get the algorithmic content use projT1.
So the following composes an algorithm extracted from the above lemma where
n is set to 5 with an algorithm extracted from the lemma Q_cmpt_elts where the
rational parameter is set to 1/2 to get an algorithm that produces arbitrary precision
approximations to (1/2)^5 and we execute this algorithm on input 1/100 to get a
1/100-approximation. *)
Compute (projT1 (pow_n_rec_fun 5)) (projT1 (Q_rec_elts (1#2))) (1#100)%Q.

(* The proof that x^n is computable is uniform and can be turned into a statment that the function (n,x) => x^n
is computable. In terms of executability this does not add anything. *)
Lemma pow_rec_fun:
	(fun p => pow p.1 p.2) \is_recursive_function.
Proof.
(* pow is defined inductively *)
rewrite /pow.
(* So one way of proving this is to use the induction principle for prec_functions on the
natural numbers. Note that there is a parameter r. Usually function spaces work well and
this parameter can be curried. Unfortunately when working with prec functions, this is not
true. Thus the induction principle looks a little more complicated than one might expect. *)
Check nat_rs_rec_pind.
apply (@nat_rs_rec_pind _ _ (fun _ => Q2R 1) (fun p => p.1 * p.2)).
	by apply/ cnst_rec_fun; first apply: (Q_rec_elts 1).
exact: Rmult_rec_fun.
move => [r n].
elim: n => //=.
	by rewrite /Q2R/=; lra.
by move => n /= ->.
Defined.

(* If one is familiar with the representations of the natural and real numbers, one can also
specify an algorithm directly and prove it correct. *)
Lemma pow_rec_fun':
	(fun p => pow p.1 p.2) \is_recursive_function.
Proof.
exists (fun phi eps => (projT1 (pow_n_rec_fun (rprj phi (star: questions rep_space_nat)))) (lprj phi) eps).
abstract by move => phi [x n] [/=phinx phinn]; rewrite phinn; apply ((projT2 (pow_n_rec_fun n)) (lprj phi) x phinx).
Defined.
(* The later is the better practice as it keeps the non algorithmic part of the proof opaque.
Note that if some essential part of the proof is opaque, the computation will usually take
forever. But in case it comes to an end form the output it is usually apparent what needs to
be done to restore executability. Unfortunately, executability is somewhat fragile it can
also be broken by the use of lra in some cases. *)

(* Both of these are directly executable again. *)
Compute (projT1 pow_rec_fun (name_pair (projT1 (Q_rec_elts (1#2))) (fun _ => 5%nat))) (1#100)%Q.
Compute (projT1 pow_rec_fun' (name_pair (projT1 (Q_rec_elts (1#2))) (fun _ => 5%nat))) (1#100)%Q.

(* The limit operator on real numbers is defined as one would expect: *)
Print lim.
(* The standard library provides its own limit operator, which is called Un_cv *)
Print Un_cv.
(* The difference is the conventions in typing and inequalities, the induced functions
are identical and a prove of this is included in the library. *)
Check Uncv_lim.
(* This makes it possible to transfer the properties proved about Un_cv in the standard
library to the limit operator: *)
Lemma lim_mult xn x yn y:
	lim xn x -> lim yn y -> lim (ptw (fun p => p.1 * p.2) (xn, yn)) (x * y).
Proof.
by move => limxnx limyny; rewrite -(Uncv_lim _); apply CV_mult; rewrite (Uncv_lim _).
Qed.
(* With respect to the Cauchy representation, these limit operators are discontinuous *)
Check lim_not_cont.
Lemma Uncv_not_cont:
	~ Un_cv \has_continuous_realizer.
Proof. by move => discont; apply lim_not_cont; rewrite -Uncv_lim. Qed.
(* Thus, computability fails and the library provides an algorithm for taking efficient
limits instead. *)
Check lim_eff_rec.
(* Here, lim_eff is the restriction of the limit operator  *)
Check lim_eff_Cauchy.
(* To the efficiently convergent Cauchy sequences *)
Print Cauchy_crit_eff.

(* When using the Cauchy representation with limits, it is often convenient to restrict the
quantification over real epsilons to the rationals. The according operator is also defined
in the library *)
Print limQ.
(* Since the rationals are dense in R, this operator can be proven equivalent to the regular
limit operator *)
Check lim_limQ.
(* In the same vain, there are tools to make the up function efficient by restricting it to
rational inputs. This is convenient as it is often used to translate an error bound eps into
a discrete quantity like the index of a sequence. *)
Print upQ.
Print Int_partQ.
Check archimedQ.

(* It is easy to define subspaces *)
Definition I := (@rep_space_sub_space rep_space_R (fun x => -1 <= x <= 1)).
End REALFUNCTIONS.