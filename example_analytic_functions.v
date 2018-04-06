(* This is example shows how to use a representation of the real numbers by means of rational
approximations to compute on the reals. Usually integers are prefered to avoid to many problems
that arise due to the possibility to use unnecessary high precission approximations. I tried
that approach but it lead to extensive additional work so I gave up at some point. I feel that
the approach in the present file is more appropriate. *)

From mathcomp Require Import all_ssreflect.
Require Import all_rs rs_reals_creals.
Require Import Qreals Reals Psatz FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import QArith.
Local Open Scope R_scope.

(* The following is different from what is used in the standard library in that epsilon is rational
instead of real. It should be straight forward to proof the limits to be equivalent by using the 
density of the rationals *)

Lemma pow_n_prec:
	forall n, (fun x => pow x n) \is_prec_function.
Proof.
elim.
	rewrite /pow/=.
	exists (fun phi eps => 1%Q).
	move => phi x phinx eps epsg0; split_Rabs; lra.
move => n ih /=.
apply/ prec_fun_comp; [apply diag_prec_fun | | ].
	apply/ prec_fun_comp; [ apply prod_prec_fun; [ apply (id_prec_fun) | apply ih] | apply Rmult_prec | ].
	by move => x.
by trivial.
Defined.

Compute (projT1 (pow_n_prec 5)) (projT1 (Q_cmpt_elts (1#2))) 1%Q.

Lemma pow_prec:
	(fun p => pow p.1 p.2) \is_prec_function.
Proof.
exists (fun phi eps => (projT1 (pow_n_prec ((rprj phi) (star:questions rep_space_nat)))) (lprj phi) eps).
move => phi x [lphinx rphinn].
have prop:= (projT2 (pow_n_prec (rprj phi star)) (lprj phi) x.1 lphinx).
by have ->: x.2 = rprj phi star by rewrite /delta/= in rphinn; rewrite rphinn.
Qed.

Definition I := (@rep_space_sub_space rep_space_R (fun x => -1 <= x <= 1)).

Require Import example_polynomials.

Definition ps_eval an (x: I) y:=
	lim (fun m => eval (in_seg an m) (projT1 x)) y.

Definition geo_series n := 1/(two_power_nat n).

Lemma geo_series_comp_elt:
	geo_series \is_computable_element.
Proof.
exists (fun p => 1/inject_Z (two_power_nat p.1))%Q.
move => n eps epsg0 /=.
suffices <-: geo_series n  = Q2R (1 / inject_Z (two_power_nat n)) by split_Rabs; lra.
rewrite /geo_series.
suffices ->: (Q2R (1 / inject_Z (two_power_nat n))) = (1/ Q2R (inject_Z (two_power_nat n))).
	suffices ->: IZR (two_power_nat n) = Q2R (inject_Z(two_power_nat n)) by trivial.
	by rewrite /Q2R/inject_Z /=; rewrite Rinv_1 Rmult_1_r.
by rewrite /Q2R/= Rinv_1 Rmult_1_r/=.
Defined.

Lemma geo_series_sum x:
	ps_eval geo_series x (1/(1-(projT1 x)/2)).
Proof.
Admitted.

Lemma analytic (an: nat -> R):
	eff_zero an -> (fun (x: I) (y: R) => ps_eval an x y) \is_prec.
Proof.
move => ez.
rewrite /eff_zero in ez.
Admitted.



















