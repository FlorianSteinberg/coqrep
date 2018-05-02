From mathcomp Require Import all_ssreflect all_algebra.
Require Import Qreals QArith Psatz Reals Field.
(* rs_list_rev provides a type for lists that saves the lists reversed, which is more appropriate
for saving polynomials. Rstruct makes the real numbers a ring in the sense of mathcomp. *)
Require Import rs_list_rev all_rs rs_reals_creals Rstruct.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section POLYNOMIALS.
Local Open Scope ring_scope.

(* Polynomials can be saved as their list of coefficients. The library provides a general list-type
construction. For polynomials it is more appropriate to save the lists backwards. *)
Definition seq_R := rep_space_list_rev rep_space_R.

(* Here is an example: *)
Definition lst := [::Q2R 0; Q2R(5#1); Q2R(1#2); Q2R 0; Q2R(4#3)].

Print horner_rec.
(* First we have to get a name for lst as polynomial. To do so we first prove that lst
is recursive as list. Being recursive is slightly stronger than being computable. *)
Lemma lst_rec_elt:
	lst \is_recursive_element.
Proof.
rewrite /lst.
apply /rec_fun_rec_elt; last first.
	apply /rec_elt_prod_rec.
		by apply cons_rec_fun_rev.
	by apply Q_rec_elts.
	done.
apply /rec_fun_rec_elt; last first.
	apply /rec_elt_prod_rec.
		by apply cons_rec_fun_rev.
	by apply Q_rec_elts.
	done.
apply /rec_fun_rec_elt; last first.
	apply /rec_elt_prod_rec.
		by apply cons_rec_fun_rev.
	by apply Q_rec_elts.
	done.
apply /rec_fun_rec_elt; last first.
	apply /rec_elt_prod_rec.
		by apply cons_rec_fun_rev.
	by apply Q_rec_elts.
	done.
apply /rec_fun_rec_elt; last first.
	apply /rec_elt_prod_rec.
		by apply cons_rec_fun_rev.
	by apply Q_rec_elts.
	done.
exact/ nil_rev_rec_elt.
Defined.
(* Here is how to access the elements of the list: *)
Compute rprj (unsm (projT1 lst_rec_elt)) (0%nat, 1#2).
Compute rprj (unsm (projT1 lst_rec_elt)) (3%nat, 1#2).
(* The name can also be queried where its values do not have any meaning: *)
Compute (projT1 lst_rec_elt) (inr (inr (15%nat, -1#2))).

(* However, usually a list representing a polynomial is required to have a non-zero leading coefficient.
For the reals this is equivalent to identifying a polynomial with the function it produces. This means
taking a quotient. Since quotient types are kind of problematic, the library does not provide a quotient type,
so the construction must be done by hand. The quotient map is defined in the library for polynomials and called
Poly *)
Check Poly.

(* The inverse of the quotient mapping still makes sense as a multivalued function. *)
Definition Poly_inv (p: {poly R}) (L: seq_R):= Poly L = p.

(* It is not single valued though, as lists that start in zeros are identified. *)
Lemma Poly_inv_not_sing:
	~ Poly_inv \is_single_valued.
Proof.
move => sing.
have val: Poly_inv (Poly [::]) [::0%R] by rewrite /Poly_inv/=cons_poly_def GRing.mul0r GRing.add0r.
have evl: (Poly_inv (Poly [::]) [::]) by trivial.
by have/=:= sing (Poly [::]) [::0%R] [::] val evl.
Qed.

(* It is total though, which translates to quot being surjective and is neccessary but not sufficient for
it to be possible to interpret quot as quotient map. *)
Lemma Poly_inv_tot:
	Poly_inv \is_total.
Proof. by move => p; exists (polyseq p); rewrite /Poly_inv polyseqK. Qed.

(* We want to interpret quot as a quotient map, i.e. use the composition of quot and the representation
of lists as a representation. *)
Definition rep_poly_R := (F2MF Poly) o (@delta seq_R).

(* That this indeed defines a representation of the space of polynomial, I.e. that this mapping is
single valued and surjective, needs to be proven. *)
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
move => p.
have [phi phinp]:= rep_sur _ (polyseq p).
exists phi.
rewrite /rep_poly_R.
split; last by move => a b; exact: F2MF_tot.
by exists p; split; last rewrite /F2MF polyseqK.
Qed.

(* We can now construct the represented space of polynomials. *)
Canonical rep_space_poly_R := @make_rep_space
	{poly R}
	_
	_
	_
	(some_question _)
	(some_answer (rep_space_list rep_space_R))
	(countable_questions (rep_space_list rep_space_R))
	(countable_answers (rep_space_list rep_space_R))
	rep_poly_R_rep
	.

(* The following two are basically saying that we indeed use the quotient space *)
Lemma Poly_rec_fun:
	(fun L: seq R => Poly L) \is_recursive_function.
Proof.
exists (fun phi => phi) => phi p phinp.
abstract by split; [exists p | by move => a b; apply: F2MF_tot].
Defined.

Lemma Poly_inv_rec:
	Poly_inv \is_recursive.
Proof.
exists (fun phi => phi).
abstract by move => phi /= p [[L [phinL PLp]] _] _; exists L.
Defined.

(* The example list from above is also computable as a polynoimal. *)
Lemma lst_cmpt_poly:
	(Poly lst) \is_recursive_element.
Proof.
apply/ rec_fun_rec_elt.
	exact lst_rec_elt.
exact Poly_rec_fun.
Defined.

(* Its coefficients can still be computed as before. Lets make this a little more readable using Notations:*)
Notation lst_name := (projT1 lst_cmpt_poly).
Notation ith phi n eps := (rprj (unsm phi) (n, eps)).
Compute ith lst_name 0%nat (1#2).
Compute ith lst_name 3%nat (1#2).
Compute ith lst_name 15%nat (1#2).

(* While a polynomial is a function, it is an abstract function on the type of reals which does not help
for computations. However, evaluation is computable. Polynomials are evaluated by using the horner scheme.
In the mathcomp library for polynomials, the horner scheme is defined by calling a the function horner_rec
that evaluates a list that need not have a vanishing leading coefficient. So we first prove that mapping to
be computable by using the induction principle for the list_rev type. *)

Lemma horner_rec_rec_fun:
	(fun L x => horner_rec (L: seq R) x) \is_recursive_function.
Proof.
pose g (x: R) := Q2R 0.
pose h (zaT: rep_space_prod rep_space_R (rep_space_prod rep_space_R rep_space_R))
	:= (zaT.1 * zaT.2.2 + zaT.2.1)%R; rewrite /= in h.
cut (fun xp => horner_rec (xp.2: seq_R) (xp.1: rep_space_R)) \is_recursive_function => [evp | ].
	by apply/ rec_fun_comp; [apply switch_rec_fun | apply evp | ].
apply/ (@list_rev_rs_rec_pind _ _ _ g h (fun px => horner_rec (px.2) px.1)).
	by apply cnst_rec_fun; apply: Q_rec_elts.
rewrite /h.
apply/ rec_fun_comp; [apply prod_rec_fun; [ apply id_rec_fun | apply switch_rec_fun]| | ] => /=.
apply/ rec_fun_comp; [apply prod_assoc_rec_fun | | ] => /=.
apply/ rec_fun_comp; [apply prod_rec_fun; [apply Rmult_rec_fun | apply id_rec_fun]| apply Rplus_rec_fun | ] => /=.
done. done. done.
move => [z K].
elim: K => //; first by rewrite /g/Q2R/= Rinv_1 Rmult_1_r.
by move => a K ih; rewrite /horner_rec/= -ih; rewrite/h [_ * z]Rmult_comm /=.
Defined.

(* To prove that evaluation is computable we translate to lists by using quot and quot_inv. *)
Lemma eval_rec_fun:
	(fun (p: {poly R}) x => p.[x]: rep_space_R) \is_recursive_function.
Proof.
apply/ rec_fun_rec_comp; [ | apply prod_rec | apply horner_rec_rec_fun | ] => /=.
			by apply mfpp_tot; split; [apply Poly_inv_tot | apply F2MF_tot].
		by apply Poly_inv_rec.
	by apply id_rec.
by move => [p x] [L u] [/= PLp <-]; rewrite -PLp horner_Poly.
Defined.

(* This allows us to evaluate in any real number we have a name for. For instance the rational 4#3. *)
Compute Qred ((projT1 eval_rec_fun) (name_pair lst_name (projT1 (Q_rec_elts (4#3)))) (1#100)).
(* Note that this algorithm reevaluates approximations to the number it evaluates on, which is very
inefficient especially if these approximations are more difficult to get than in this example. It is
possible but also more work, to specify the algorithm directly and prove it correct. *)

(* Addition of polynomials can be expressed via operations on list: *)
Definition ladd (L K: seq_R) : seq_R:=
	map (fun n => nth 0 L n + nth 0 K n) (iota 0 (maxn (size L) (size K))).

Lemma ladd_crct L K:
	Poly L + Poly K = Poly (ladd L K).
Proof.
rewrite /ladd.
rewrite -polyP => i.
rewrite coef_Poly.
have ->: [seq L`_n + K`_n | n <- iota 0 (maxn (size L) (size K))] = [seq (Poly L + Poly K)`_n | n <- iota 0 (maxn (size L) (size K))].
	by rewrite (@eq_map _ _ _ (fun n => (Poly L + Poly K)`_n)) => // n; rewrite coefD !coef_Poly.
case: (lt_dec i (maxn (size L) (size K)))%nat => ineq.
	rewrite (nth_map 0%nat); last by rewrite size_iota; apply /leP.
	by replace (nth 0%nat (iota 0%nat (maxn (size L) (size K))) i) with i by
		by rewrite (nth_iota); last apply /leP.
rewrite !nth_default; [ | rewrite size_map size_iota | apply/leq_trans; first exact: size_add ] => //.
	apply /leP/ Nat.nlt_ge /ineq.
rewrite geq_max.
apply/andP.
split.
	apply/ leq_trans;first by apply size_Poly.
	apply/ leq_trans; first by apply/ (leq_maxl _ (size K)).
	apply /leP /Nat.nlt_ge /ineq.
apply/ leq_trans; first by apply size_Poly.
apply/ leq_trans; first by apply/ (leq_maxr (size L)).
apply /leP /Nat.nlt_ge /ineq.
Qed.

(* Since the standard operations on lists are proven computable, this can be used to get an algorithm for
computing sums of polynomials *)

Lemma ladd_rec_fun:
	ladd \is_recursive_function.
Proof.
rewrite /ladd/=.
have nth0_rec: (fun (K:seq_R) => nth 0 K:(nat -> rep_space_R)) \is_recursive_function.
	apply /rec_fun_comp; [ | apply nth_rec_rev | ] => /=.
		apply /rec_fun_comp; [apply diag_rec_fun | | ] => /=.
			by apply /prod_rec_fun; [by apply/cnst_rec_fun/(Q_rec_elts 0) | apply id_rec_fun].
		done.
	by replace (Q2R 0) with 0%R by by rewrite /Q2R/=; lra.
have seq_rec:
	(fun (L K: seq_R) => (fun n => nth 0 L n + nth 0 K n):(nat -> rep_space_R)) \is_recursive_function.
	apply /rec_fun_comp; [ | apply/ (ptw_rec Rplus_rec_fun) | ] => /=.
		by apply/ prod_rec_fun; apply nth0_rec.
	done.
have max_rec: (fun (L K: seq_R) => maxn (size L) (size K)) \is_recursive_function.
	apply /rec_fun_comp; [apply prod_rec_fun; [apply size_rev_rec_fun | apply size_rev_rec_fun] | | ].
		by apply /(nat_nat_rec_fun maxn).
	done.
have iota_rec: (fun (L K: seq_R) => iota 0 (maxn (size L) (size K))) \is_recursive_function.
	apply /rec_fun_comp; [apply max_rec | | ] => //=.
	exact: iota0_rec_fun.
apply /rec_fun_comp; [ | apply map_rec_rev_par | ] => //=.
apply /rec_fun_comp; [apply diag_rec_fun | | ] => //=.
	by apply prod_rec_fun; [apply id_rec_fun | apply iota_rec].
	done.
have [M /= Mprop] := seq_rec.
cut (fun (LKn: (seq_R) * (seq_R) * nat) =>
	(nth 0 LKn.1.1 LKn.2 + nth 0 LKn.1.2 LKn.2):rep_space_R) \is_recursive_function => [seq' | ].
	by apply seq'.
exists (fun phipsi q => M (lprj phipsi) (rprj phipsi (star: questions rep_space_nat), q)).
move => phi [LK n] [/=phinLK ->].
by apply (Mprop (lprj phi) LK phinLK n).
done.
Defined.

Definition poly_add (pq: {poly R} * {poly R}) := pq.1 + pq.2.

Lemma poly_add_prec:
	poly_add \is_recursive_function.
Proof.
apply /rec_fun_rec_comp => /=.
		by apply mfpp_tot; split; apply Poly_inv_tot.
	by apply /prod_rec; [apply Poly_inv_rec | apply Poly_inv_rec].
by apply /rec_fun_comp; [apply ladd_rec_fun | apply Poly_rec_fun | ].
by move => [p q] [L K] [/=PpL PqK]; rewrite -ladd_crct -PpL PqK.
Defined.

(* This allows us to evaluate in any real number we have a name for. For instance the rational 4#3. *)
Compute Qred (ith ((projT1 poly_add_prec) (name_pair lst_name lst_name)) 1%nat (1#2)).
Compute Qred (ith ((projT1 poly_add_prec) (name_pair lst_name lst_name)) 4%nat (1#2)).
Compute Qred (ith ((projT1 poly_add_prec) (name_pair lst_name lst_name)) 15%nat (1#2)).

Definition poly_mult (pq: {poly R} * {poly R}) := pq.1 * pq.2.
End POLYNOMIALS.