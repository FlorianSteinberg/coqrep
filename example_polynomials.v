From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
From mathcomp Require Import finfun bigop prime binomial.
Require Import Qreals QArith Psatz.
Require Import multi_valued_functions representation_facts.
Require Import example_approximating_reals_with_rationals representations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section POLYNOMIALS.

Definition polynomial := list Q.

Fixpoint Qeval (p: polynomial) q :Q := match p with
	| nil => 0%Q
	| cons a L => q * (Qeval L q) + a
end.

Fixpoint add p q := match p with
	|nil => q
	|cons a p => match q with
		| nil => cons a p
		| cons b q => cons (a + b) (add p q)
	end
end.

Definition multx p := cons 0 p.

Fixpoint multa a p := match p with
	| nil => nil
	| cons b q => cons (b*a) (multa a q)
end.

Fixpoint mult p q := match p with
	| nil => nil
	| cons a p' => add (multa a q) (multx (mult p' q))
end.

Fixpoint T n := match n with
	| 0%nat => cons 1 nil
	| S n' => match n' with
		| 0%nat =>  cons 0%Q (cons 1 nil)
		| S n'' => add (multa (2#1) (multx (T n'))) (map Qopp (T n''))
	end
end.

Definition cheb_poly := list Q.

Fixpoint CP2P_rev cp := match cp with
	| nil => nil
	| cons a L => add (multa a (T (length L))) (CP2P_rev L)
end.
Definition CP2P cp := CP2P_rev (rev cp).

Fixpoint monom n := match n with
	| 0%nat => cons 1 nil
	| S n => cons 0 (monom n)
end.

Lemma CP2P_monom:
	forall n, CP2P (monom n) = T n.
Proof.
Admitted.

Compute CP2P (monom 5).
Compute T 5.

Fixpoint b (p: cheb_poly) (x: Q) := match p with
	| nil => cons 0 (cons 0 nil)
	|	cons a p' => cons (a + ((2#1) * x * (BinList.nth 0 1 (b p' x)) - (BinList.nth 0 2 (b p' x)))) (b p' x)
end.

Definition EvaluateClenshaw p x :=
	BinList.nth 0 1 (b p x) - x * BinList.nth 0 2 (b p x).

Compute Qeval (T 5) (2#3).
Compute EvaluateClenshaw (monom 5) (2#3).
Compute Qeval (T 5) (2#3) - EvaluateClenshaw (monom 5) (2#3).
(* lol. I probably shouldn't have used Q. *)

Fixpoint Reval (p: polynomial) x :R := match p with
	| nil => 0
	| cons a L => Rmult x (Reval L x) + Q2R a
end.
(* This does not evaluate *)
Compute Reval (T 5) (Q2R (2#3)).
(* But you can use my library to prove computability and then evaluate: *)
Lemma Reval_prec (p: polynomial):
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
		apply/ prec_fun_comp; [apply diag_cmpt | apply prod_prec_fun | ].
				by apply id_prec_fun.
			by apply rcomp.
		by trivial.
	by trivial.
have xmexcomp: (fun x:R => Rmult x (Reval q x)) \is_prec_function.
	apply /prec_fun_comp; [ | apply Rmult_prec | ].
		apply /prec_fun_comp; [apply diag_cmpt | apply prod_prec_fun | ].
				by apply id_prec_fun.
			by apply comp.
		by trivial.
	by trivial.
by apply /prec_fun_comp; [apply xmexcomp | apply xprcomp | ].
Defined.

Compute projT1 (Reval_prec (T 5)) (projT1 (Q_cmpt_elts (2#3))) (1#100).
(* This is exact due to the names used for rationals:*)
Compute Qeval (T 5) (2#3) - projT1 (Reval_prec (T 5)) (projT1 (Q_cmpt_elts (2#3))) (1#100).
(* However, the interpretation of the return value should be that it is an approximation
to precision 1#100. It should also be possible to get proofs that this is true by using the
other projections...But that didn't work for me. The above can be used to evaluate in an
arbitrary real number one has a name available for. Unfortunatelly I have not made any names
for real numbers available yet but for the rationals... Another downside is that it is awfully
slow for more complicated polynomials since it builds evaluation trees... of course one may
provide an algorithm directly and prove its correctnes. That would be a lot faster, but also
cumbersome since one has to do error estimation by hand... *)
End POLYNOMIALS.