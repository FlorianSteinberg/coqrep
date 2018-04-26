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
is computable as list. *)
Lemma lst_cmpt_seq:
	lst \is_computable_element.
Proof.
rewrite /lst.
apply /prec_fun_cmpt_elt; last first.
	apply /cmpt_elt_prod_prec.
		by apply cons_prec_fun_rev.
	by apply Q_cmpt_elts.
	done.
apply /prec_fun_cmpt_elt; last first.
	apply /cmpt_elt_prod_prec.
		by apply cons_prec_fun_rev.
	by apply Q_cmpt_elts.
	done.
apply /prec_fun_cmpt_elt; last first.
	apply /cmpt_elt_prod_prec.
		by apply cons_prec_fun_rev.
	by apply Q_cmpt_elts.
	done.
apply /prec_fun_cmpt_elt; last first.
	apply /cmpt_elt_prod_prec.
		by apply cons_prec_fun_rev.
	by apply Q_cmpt_elts.
	done.
apply /prec_fun_cmpt_elt; last first.
	apply /cmpt_elt_prod_prec.
		by apply cons_prec_fun_rev.
	by apply Q_cmpt_elts.
	done.
exact: nil_cmpt_elt.
Defined.
(* Here is how to access the elements of the list: *)
Compute rprj (unsm (projT1 lst_cmpt_seq)) (0%nat, 1#2).
Compute rprj (unsm (projT1 lst_cmpt_seq)) (3%nat, 1#2).
(* The name can also be queried where its values do not have any meaning: *)
Compute (projT1 lst_cmpt_seq) (inr (inr (15%nat, -1#2))).

(* However, usually a list representing a polynomial is required to have a non-zero leading coefficient.
For the reals this is equivalent to identifying a polynomial with the function it produces. This means
taking a quotient. Since quotient types are kind of problematic, the library does not provide a quotient type,
so the construction must be done by hand. The quotient map is defined in the library for polynomials and called
Poly *)
Check Poly.

(* The inverse of the quotient mapping still makes sense as a multivalued function. *)
Definition Poly_inv p (L: seq R):= Poly L = p.

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
Proof. by move => p; exists p; rewrite /Poly_inv polyseqK. Qed.

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
Lemma Poly_prec:
	(fun L: seq R => Poly L) \is_prec_function.
Proof.
exists (fun phi => phi) => phi p phinp.
abstract by split; [exists p | by move => a b; apply: F2MF_tot].
Defined.

Lemma Poly_inv_prec:
	Poly_inv \is_prec.
Proof.
exists (fun phi => phi).
abstract by move => phi /= p [[L [phinL PLp]] _] _; exists L.
Defined.

(* The example list from above is also computable as a polynoimal. *)
Lemma lst_cmpt_poly:
	(Poly lst) \is_computable_element.
Proof.
apply/ prec_fun_cmpt_elt.
	exact lst_cmpt_seq.
exact Poly_prec.
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

Lemma horner_rec_prec:
	(fun px => horner_rec (px.1: seq R) px.2) \is_prec_function.
Proof.
pose g (x: R) := Q2R 0.
pose h (zaT: rep_space_prod rep_space_R (rep_space_prod rep_space_R rep_space_R))
	:= (zaT.1 * zaT.2.2 + zaT.2.1)%R; rewrite /= in h.
suffices evp: (fun xp => horner_rec (xp.2: seq R) xp.1) \is_prec_function
	by apply/ prec_fun_comp; [apply switch_prec_fun | apply evp | ].
apply/ (@list_rev_rs_prec_pind _ _ _ g h (fun px => horner_rec (px.2) px.1)).
	by apply cnst_prec_fun; apply: Q_cmpt_elts.
rewrite /h.
apply/ prec_fun_comp; [apply prod_prec_fun; [ apply id_prec_fun | apply switch_prec_fun]| | ] => /=.
apply/ prec_fun_comp; [apply prod_assoc_prec | | ] => /=.
apply/ prec_fun_comp; [apply prod_prec_fun; [apply Rmult_prec | apply id_prec_fun]| apply Rplus_prec | ] => /=.
done.
done.
done.
move => [z K].
elim: K => //; first by rewrite /g/Q2R/= Rinv_1 Rmult_1_r.
by move => a K ih; rewrite /horner_rec/= -ih; rewrite/h [_ * z]Rmult_comm /=.
Defined.

(* To prove that evaluation is computable we translate to lists by using quot and quot_inv. *)
Lemma eval_prec:
	(fun px: {poly R} * R => px.1.[px.2]) \is_prec_function.
Proof.
apply/ prec_fun_prec_comp; [ | apply prod_prec | apply horner_rec_prec | ] => /=.
			by apply mfpp_tot; split; [apply Poly_inv_tot | apply F2MF_tot].
		by apply Poly_inv_prec.
	by apply id_prec.
by move => [p x] [L u] [/= PLp <-]; rewrite -PLp horner_Poly.
Defined.

(* This allows us to evaluate in any real number we have a name for. For instance the rational 4#3. *)
Compute Qred ((projT1 eval_prec) (name_pair lst_name (projT1 (Q_cmpt_elts (4#3)))) (1#100)).
(* Note that this algorithm reevaluates approximations to the number it evaluates on, which is very
inefficient especially if these approximations are more difficult to get than in this example. It is
possible but also more work, to specify the algorithm directly and prove it correct. *)

(* Addition of polynomials can be expressed via operations on list: *)
Definition ladd (L K: seq R):=
	map (fun n => nth 0 L n + nth 0 K n) (iota 0 (maxn (size L) (size K))).

Lemma ladd_crct L K:
	Poly L + Poly K = Poly (ladd L K).
Proof.
rewrite /ladd.
Search _ Poly map.
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

Lemma ladd_prec:
	(fun LK => ladd LK.1 LK.2) \is_prec_function.
Proof.
rewrite /ladd/=.
have nth0_prec: (fun (K:seq R) => nth 0 K) \is_prec_function.
	apply /prec_fun_comp; [ | apply nth_prec_rev | ] => /=.
		apply /prec_fun_comp; [apply diag_prec_fun | | ] => /=.
			apply /prod_prec_fun.
				apply cnst_prec_fun.
				by apply Q_cmpt_elts.
			by apply id_prec_fun.
		done.
	by replace 0 with (Q2R 0) by by rewrite /Q2R/= Rinv_1 Rmult_0_l.
have seq_prec:
	(fun (LK: (seq R) * (seq R)) => (fun n => nth 0 LK.1 n + nth 0 LK.2 n):(nat -> R)) \is_prec_function.
	apply /prec_fun_comp; [ | apply/ (ptw_prec Rplus_prec) | ] => /=.
		apply /prec_fun_comp; [ | apply /prod_prec_fun; apply nth0_prec | ] => /=.
			apply /prec_fun_comp; [apply diag_prec_fun | | ] => //=.
				apply /prod_prec_fun => /=.
					apply fst_prec.
				apply snd_prec.
			done.
		done.
	done.
have max_prec: (fun (LK: (seq R)* (seq R)) => maxn (size LK.1) (size LK.2)) \is_prec_function.
	apply /prec_fun_comp; [apply prod_prec_fun; [apply size_rev_prec_fun | apply size_rev_prec_fun] | | ].
		by apply /(nat_nat_prec_fun maxn).
	done.
have iota_prec: (fun (LK: (seq R) * (seq R)) => iota 0 (maxn (size LK.1) (size LK.2))) \is_prec_function.
	apply /prec_fun_comp; [apply max_prec | | ] => //=.
	exact: iota0_prec_fun.
apply /prec_fun_comp; [ | apply map_prec_rev_par | ] => //=.
apply /prec_fun_comp; [apply diag_prec_fun | | ] => //=.
	by apply prod_prec_fun; [apply id_prec_fun | apply iota_prec].
	done.
have [M /= Mprop] := seq_prec.
suffices seq': (fun (LKn: (seq R) * (seq R) * nat) =>
	(nth 0 LKn.1.1 LKn.2 + nth 0 LKn.1.2 LKn.2):R) \is_prec_function by apply seq'.
exists (fun phipsi q => M (lprj phipsi) (rprj phipsi (star: questions rep_space_nat), q)).
move => phi [LK n] [/=phinLK ->].
by apply (Mprop (lprj phi) LK phinLK n).
done.
Defined.

Definition poly_add (pq: {poly R} * {poly R}) := pq.1 + pq.2.

Lemma poly_add_prec:
	poly_add \is_prec_function.
Proof.
apply /prec_fun_prec_comp => /=.
		by apply mfpp_tot; split; apply Poly_inv_tot.
	by apply /prod_prec; [apply Poly_inv_prec | apply Poly_inv_prec].
by apply /prec_fun_comp; [apply ladd_prec | apply Poly_prec | ].
by move => [p q] [L K] [/=PpL PqK]; rewrite -ladd_crct -PpL PqK.
Defined.

(* This allows us to evaluate in any real number we have a name for. For instance the rational 4#3. *)
Compute Qred (ith ((projT1 poly_add_prec) (name_pair lst_name lst_name)) 1%nat (1#2)).
Compute Qred (ith ((projT1 poly_add_prec) (name_pair lst_name lst_name)) 4%nat (1#2)).
Compute Qred (ith ((projT1 poly_add_prec) (name_pair lst_name lst_name)) 15%nat (1#2)).

Definition poly_mult (pq: {poly R} * {poly R}) := pq.1 * pq.2.
End POLYNOMIALS.