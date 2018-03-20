From mathcomp Require Import all_ssreflect.
Require Import Qreals QArith Psatz Reals Field.
Require Import multi_valued_functions representation_facts.
Require Import example_approximating_reals_with_rationals representations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section POLYNOMIALS.

Definition polynomial := list Q.

Fixpoint Qeval (p: polynomial) q :Q := 
  if p is a :: L then q * (Qeval L q) + a else 0%Q. 

Fixpoint add p q :=
  if p is a :: p then
    if q is b :: q then a + b :: (add p q) else a :: p
  else q.

Definition multx p := 0 :: p.

Fixpoint multa a p :=  [seq b * a | b <- p].

Fixpoint mult p q := 
  if p is a :: p' then add (multa a q) (multx (mult p' q)) else [::].

Fixpoint T n := 
  if n is n'.+1 then
   if n' is n''.+1 then add (multa (2#1) (multx (T n'))) [seq -i | i <- T n'']
   else [::0; 1]
  else [::1].

Definition cheb_poly := list Q.

Fixpoint CP2P_rev cp := 
  if cp is a :: L then add (multa a (T (length L))) (CP2P_rev L) else [::].

Definition CP2P cp := CP2P_rev (rev cp).

Definition monom n := ncons n 0 [::1].

Lemma CP2P_monom n : CP2P (monom n) = T n.
Proof.
Admitted.

Compute CP2P (monom 5).
Compute T 5.

Fixpoint b (p: cheb_poly) (x: Q) :=
 if p is a :: p' then
   let t := b p' x in
   let a1 := a + (2#1) * x * t.1 - t.2 in
   (a1, t.1) else (0, 0).

Definition EvaluateClenshaw p x :=
	(b p x).1 - x * (b p x).2.

Compute Qeval (T 5) (2#3).
Compute EvaluateClenshaw (monom 5) (2#3).
Compute Qred (Qeval (T 5) (2#3) - EvaluateClenshaw (monom 5) (2#3)).
(* lol. I probably shouldn't have used Q. *)

Fixpoint Reval (p: polynomial) x : R := 
  if p is a :: L then x * Reval L x + Q2R a else 0.

(* This does not evaluate *)
Compute Reval (T 5) (Q2R (2#3)).
Goal forall x, x = Reval (T 5) (Q2R (2#3)) -> x = x.
move=> x H.
compute in H.
field_simplify in H.
by [].
Qed.

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