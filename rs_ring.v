From mathcomp Require Import all_ssreflect all_algebra.
(* rs_list_rev provides a type for lists that saves the lists reversed, which is more appropriate
for saving polynomials. Rstruct makes the real numbers a ring in the sense of mathcomp. *)
Require Import rs_list_rev all_rs Rstruct.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RSRING.
Local Open Scope ring_scope.

Variable R: ringType.
Variable Q A: Type.
Variable delta: (Q -> A) ->> R.
Axiom Qcount: Q \is_countable.
Axiom Acount: A \is_countable.
Axiom delta_rep: delta \is_representation.
Axiom someq: Q.
Axiom somea: A.
Definition rep_space_R:= @make_rep_space R Q A delta someq somea Qcount Acount delta_rep.
(* Polynomials can be saved as their list of coefficients. The library provides a general list-type
construction. For polynomials it is more appropriate to save the lists backwards. *)
Definition seq_R := rep_space_list_rev rep_space_R.

(* However, usually a list representing a polynomial is required to have a non-zero leading coefficient.
For the reals this is equivalent to identifying a polynomial with the function it produces. This means
taking a quotient. Since quotient types are kind of problematic, the library does not provide a quotient type,
so the construction must be done by hand. The quotient map is defined in the library for polynomials and called
Poly The inverse of the quotient mapping still makes sense as a multivalued function. *)
Definition Poly_inv p (L: seq_R):= Poly L = p.

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
Definition rep_poly_R := (F2MF Poly) o (rep seq_R).

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
have [phi phinp]:= rep_sur _ (polyseq p: seq_R).
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
	(fun L: seq_R => Poly L) \is_recursive_function.
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

(* In the mathcomp library for polynomials, the horner scheme is defined by calling a the function horner_rec
that evaluates a list that need not have a vanishing leading coefficient. We can prove this mapping to be
computable under the assumption that the operations of the Ring are computable. *)
Axiom Rplus_rec_fun: (fun (x y: rep_space_R) => x + y: rep_space_R) \is_recursive_function.
Axiom Rmult_rec_fun: (fun (x y: rep_space_R) => x * y: rep_space_R) \is_recursive_function.
Axiom zero_rec_elt: (0: rep_space_R) \is_recursive_element.

Lemma horner_rec_rec:
	(fun (L: seq rep_space_R) (x: rep_space_R) => horner_rec L x : rep_space_R) \is_recursive_function.
Proof.
pose g (x: rep_space_R) := 0: rep_space_R.
pose h (zaT: rep_space_prod rep_space_R (rep_space_prod rep_space_R rep_space_R))
	:= zaT.2.2 * zaT.1 + zaT.2.1.
cut (fun xp: rep_space_R * seq_R => horner_rec xp.2 xp.1 : rep_space_R) \is_recursive_function => [evp | ].
	by apply/ rec_fun_comp; [apply switch_rec_fun | apply evp | ].
apply (@list_rev_rs_rec_pind _ _ _ g h).
	by apply cnst_rec_fun; apply: zero_rec_elt.
rewrite /h.
apply/ rec_fun_comp; [apply prod_rec_fun; [ apply id_rec_fun | apply switch_rec_fun]| | ] => /=.
apply/ rec_fun_comp; [apply prod_assoc_rec_fun | | ] => /=.
apply/ rec_fun_comp; [apply prod_rec_fun; [ | apply id_rec_fun]| apply Rplus_rec_fun | ] => /=.
apply /rec_fun_comp; [apply switch_rec_fun | apply Rmult_rec_fun | ].
done. done. done. done.
move => [z K].
elim: K => //.
by move => a K ih; rewrite /horner_rec/= -ih.
Defined.

(* To prove that evaluation is computable we translate to lists by using quot and quot_inv. *)
Lemma eval_prec:
	(fun (p: {poly R}) (x: rep_space_R) => p.[x]: rep_space_R) \is_recursive_function.
Proof.
apply/ rec_fun_rec_comp; [ | apply prod_rec | apply horner_rec_rec | ] => /=.
			by apply mfpp_tot; split; [apply Poly_inv_tot | apply F2MF_tot].
		by apply Poly_inv_rec.
	by apply id_rec.
by move => [p x] [L u] [/= PLp <-]; rewrite -PLp horner_Poly.
Defined.

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
case: (Compare_dec.lt_dec i (maxn (size L) (size K)))%coq_nat => ineq.
	rewrite (nth_map 0%nat); last by rewrite size_iota; apply /leP.
	by replace (nth 0%nat (iota 0%nat (maxn (size L) (size K))) i) with i by
		by rewrite (nth_iota); last apply /leP.
rewrite !nth_default; [ | rewrite size_map size_iota | apply/leq_trans; first exact: size_add ] => //.
	by rewrite leqNgt; move /leP: ineq.
rewrite geq_max.
apply/andP.
split.
	apply/ leq_trans;first by apply size_Poly.
	apply/ leq_trans; first by apply/ (leq_maxl _ (size K)).
	by rewrite leqNgt; move/leP: ineq.
apply/ leq_trans; first by apply size_Poly.
apply/ leq_trans; first by apply/ (leq_maxr (size L)).
by rewrite leqNgt; move /leP: ineq.
Qed.

(* Since the standard operations on lists are proven computable, this can be used to get an algorithm for
computing sums of polynomials *)

Lemma ladd_rec_fun: ladd \is_recursive_function.
Proof.
rewrite /ladd/=.
have nth0_rec: (fun (K:seq_R) => nth 0 K:(nat -> rep_space_R)) \is_recursive_function.
	apply /rec_fun_comp; [ | apply nth_rec_rev | ] => /=.
		apply /rec_fun_comp; [apply diag_rec_fun | | ] => /=.
			by apply /prod_rec_fun; [by apply/cnst_rec_fun/(zero_rec_elt) | apply id_rec_fun].
		done.
	done.
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

Definition poly_add (p q:{poly R}) := p + q.

Lemma poly_add_rec_fun:
	poly_add \is_recursive_function.
Proof.
apply /rec_fun_rec_comp => /=.
		by apply mfpp_tot; split; apply Poly_inv_tot.
	by apply /prod_rec; [apply Poly_inv_rec | apply Poly_inv_rec].
by apply /rec_fun_comp; [apply ladd_rec_fun | apply Poly_rec_fun | ].
by move => [p q] [L K] [/=PpL PqK]; rewrite -ladd_crct -PpL PqK.
Defined.

Definition poly_mult (pq: {poly R} * {poly R}) := pq.1 * pq.2.
End RSRING.