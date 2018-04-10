From mathcomp Require Import all_ssreflect all_algebra.
Require Import Qreals QArith Psatz Reals Field.
(* rs_list_rev provides a type for lists that saves the lists reversed, which is more appropriate
for saving polynomials. Rstruct makes the real numbers a ring in the sense of mathcomp. *)
Require Import rs_list_rev all_rs rs_reals_creals Rstruct.
Require Import FunctionalExtensionality ClassicalChoice.

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
so the construction must be done by hand. Here is the type of polynomial functions: *)
Definition poly_R :=
	{f: R -> R | exists p: {poly R}, forall x, p.[x] = f x}.

(* Constructing elements of a subtype is done using the exist constructor. The following is for ease of use of
this constructor. *)
Definition exist_poly:= @exist (R -> R) (fun f => (exists p:{poly R}, forall x, p.[x] = f x)).

(* Each sequence can be turned into a polynomial by removing leading zeros. *)
Lemma poly_exist (p: seq R):
	exists q: {poly R}, forall x, q.[x] = horner_rec p x.
Proof. exists (Poly p) => x; exact: horner_Poly. Qed.

(* So far seq_R is a represented space but poly_R is only a type. To turn poly_R into a represented space, we
interpret the mapping that takes a list to the funciton it evaluates to as a quotient mapping. *)
Definition quot (p: seq R) := @exist_poly (fun x => horner_rec p x) (poly_exist p).

(* The inverse of the quotient mapping still makes sense as a multivalued function. *)
Definition quot_inv (f: poly_R) (p: seq R):= forall x, horner_rec p x = projT1 f x.

(* It is not single valued though, as lists that start in zeros are identified. *)
Lemma quot_inv_not_sing:
	~ quot_inv \is_single_valued.
Proof.
move => sing.
have val: quot_inv (exist_poly (poly_exist [::])) [::0%R] by move => x /=; rewrite GRing.mul0r GRing.add0r.
have evl: (quot_inv (exist_poly (poly_exist [::])) [::]) by trivial.
by have/=:= sing (exist_poly (poly_exist [::])) [::0%R] [::] val evl.
Qed.

(* It is total though, which translates to quot being surjective and is neccessary but not sufficient for
it to be possible to interpret quot as quotient map. *)
Lemma quot_inv_tot:
	quot_inv \is_total.
Proof. by move => [pf [p val]]; exists p. Qed.

(* We want to interpret quot as a quotient map, i.e. use the composition of quot and the representation
of lists as a representation. *)
Definition rep_poly_R := (F2MF quot) o (@delta seq_R).

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
move => [f [p evlpf]].
have [phi phinp]:= rep_sur _ (polyseq p).
exists phi.
rewrite /rep_poly_R.
split; last by move => a b; exact: F2MF_tot.
exists p; split => //.
by rewrite /F2MF/quot; apply eq_sub; apply functional_extensionality.
Qed.

(* We can now construct the represented space of polynomials. *)
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

(* The following two are basically saying that we indeed use the quotient space *)
Lemma quot_prec:
	(fun p => quot p:poly_R) \is_prec_function.
Proof.
exists (fun phi => phi) => phi p phinp.
split; last by move => a b; apply: F2MF_tot.
by exists p.
Defined.

Lemma quot_inv_prec:
	quot_inv \is_prec.
Proof.
exists (fun phi => phi) => phi stuff.
split.
	move: stuff => [p [[pf [[[q  [phinq _]] _] eq]]] _].
	exists q; split; first by exists phi.
	by move => psi <-; exists q.
move: stuff => [q[[pf [phinpf _]] eq]] r [[psi [<- phinr]] prop].
split; last by move => [pf' [p peqpf']] _; exists (polyseq p).
exists (exist_poly (poly_exist r)); split => //.
split; last by move => a b; exact: F2MF_tot.
by exists r.
Defined.

(* The example list from above is also computable as a polynoimal. *)
Lemma lst_cmpt_poly:
	(exist_poly (poly_exist lst) : poly_R) \is_computable_element.
Proof.
replace (exist_poly (poly_exist lst)) with (quot lst) by trivial.
apply/ prec_fun_cmpt_elt.
	exact lst_cmpt_seq.
exact quot_prec.
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
	(fun px: poly_R * R => projT1 px.1 px.2) \is_prec_function.
Proof.
apply/ prec_fun_prec_comp; [ | apply prod_prec | apply horner_rec_prec | ] => /=.
			by apply mfpp_tot; split; [apply quot_inv_tot | apply F2MF_tot].
		by apply quot_inv_prec.
	by apply id_prec.
by move => [f x] [p y] [/=qfp <-]/=; rewrite qfp.
Defined.

(* This allows us to evaluate in any real number we have a name for. For instance the rational 4#3. *)
Compute Qred ((projT1 eval_prec) (name_pair lst_name (projT1 (Q_cmpt_elts (4#3)))) (1#100)).
(* Note that this algorithm reevaluates approximations to the number it evaluates on, which is very
inefficient especially if these approximations are more difficult to get than in this example. It is
possible but also more work, to specify the algorithm directly and prove it correct. *)

(* Addition of polynomials can be expressed via operations on list: *)
Definition ladd (L K: seq R):=
	map (fun n => nth 0 L n + nth 0 K n) (iota 0 (maxn (size L) (size K))).

Lemma ladd_crct p q x:
	horner_rec p x + horner_rec q x = horner_rec (ladd p q) x.
Proof.
rewrite -!horner_Poly -hornerD.
congr horner.
rewrite -polyP/= => i.
rewrite coef_Poly.
case: (lt_dec i (maxn (size p) (size q)))%nat => ineq.
	have ->/=:= (@nth_map nat 0%nat R 0 (fun n => p`_n + q`_n) i); last by rewrite size_iota; apply /leP.
	rewrite nth_iota/=; last by apply /leP.
	by rewrite coefD !coef_Poly.
rewrite coefD !coef_Poly.
rewrite nth_default; last first.
	apply/ leq_trans; first apply leq_maxl.
	by apply /leP/ Nat.nlt_ge /ineq.
rewrite nth_default; last first.
	apply/ leq_trans; first apply leq_maxr.
	by apply /leP/ Nat.nlt_ge /ineq.
rewrite nth_default; first by rewrite GRing.addr0.
by rewrite size_map size_iota; last by apply /leP/ Nat.nlt_ge.
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

Definition poly_add (fg: poly_R * poly_R) (h: poly_R):=
	forall x, projT1 fg.1 x + projT1 fg.2 x = projT1 h x.

Lemma poly_add_prec:
	poly_add \is_prec.
Proof.
apply /prec_comp; [apply /prod_prec; [apply quot_inv_prec | apply quot_inv_prec] | | ] => /=.
	apply /prec_comp; [apply prec_fun_prec; apply ladd_prec | apply prec_fun_prec; apply quot_prec | ].
	rewrite F2MF_comp/=/F2MF.
	by trivial.
move => [[pf [p pfp]] [qf [q qfq]]] M.
rewrite /poly_add/=.
split => prp.
	split; last by move => [L K] [/=a b]; exists (quot (ladd L K)).
	rewrite /rel_comp.
	exists (polyseq p, polyseq q) => /=.
	rewrite /mf_prod_prod/=/quot_inv/=.
	split => //.
	rewrite eq_sub/=; apply functional_extensionality => x.
	by rewrite -prp -pfp -qfq ladd_crct.
move:prp => [[[L K]] [[/=qinv qinv']] prp _] x.
rewrite /quot_inv/= in qinv.
rewrite /quot_inv/= in qinv'.
by rewrite -qinv -qinv' prp/= ladd_crct.
Defined.

(* This allows us to evaluate in any real number we have a name for. For instance the rational 4#3. *)
Compute Qred (ith ((projT1 poly_add_prec) (name_pair lst_name lst_name)) 1%nat (1#2)).
Compute Qred (ith ((projT1 poly_add_prec) (name_pair lst_name lst_name)) 4%nat (1#2)).
Compute Qred (ith ((projT1 poly_add_prec) (name_pair lst_name lst_name)) 15%nat (1#2)).

Definition poly_mult (fg: poly_R * poly_R) (h: poly_R):=
	forall x, (projT1 fg.1 x * projT1 fg.2 x = projT1 h x)%R.
End POLYNOMIALS.