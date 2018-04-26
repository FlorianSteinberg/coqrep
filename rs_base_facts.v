From mathcomp Require Import all_ssreflect.
Require Import all_core rs_base rs_base_prod.
Require Import FunctionalExtensionality ClassicalFacts ClassicalChoice Psatz.
Require Import Morphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BASIC_LEMMAS.

Lemma rec_cmpt (X Y:rep_space) (f: X ->> Y):
	f \is_recursive -> f \is_computable.
Proof.
move => [N Nir]; exists (fun n phi q' => Some (N phi q')).
abstract by move: Nir; rewrite rrlzr_rlzr => Nir; apply/ tight_trans; first apply/ tight_comp_r/(rec_F2MF_op 0).
Qed.

Lemma rec_fun_rec_elt (X Y: rep_space) (f: X -> Y) (x: X):
	x \is_recursive_element -> f \is_recursive_function -> (f x) \is_recursive_element.
Proof.
move => [phi phinx] [M Mrf].
by exists (M phi); apply Mrf.
Defined.

Lemma mon_cmpt_cmpt (X Y: rep_space) (f: X ->> Y):
	f \is_monotone_computable -> f \is_computable.
Proof. by move => [M [mon comp]]; exists M. Defined.

Lemma rec_fun_comp (X Y Z: rep_space) (f: X -> Y) (g: Y -> Z):
	f \is_recursive_function -> g \is_recursive_function
	-> forall h, (forall x, h x = g (f x)) -> h \is_recursive_function.
Proof.
move => [M comp] [N comp'] h eq.
exists (fun phi => N (M phi)).
abstract by move => phi x phinx; rewrite/prog/= eq; apply comp'; apply comp.
Defined.

Lemma rec_comp (X Y Z: rep_space) (f: X ->> Y) (g: Y ->> Z) h:
	f \is_recursive -> g \is_recursive -> h =~= g o f -> h \is_recursive.
Proof.
move => [M comp] [N comp'] eq.
exists (fun phi => N (M phi)).
abstract by rewrite rrlzr_rlzr eq; have ->: F2MF (fun phi => N (M phi)) =~= (F2MF N) o (F2MF M);
	[rewrite F2MF_comp | apply rlzr_comp; rewrite -rrlzr_rlzr].
Defined.

Lemma rec_fun_rec_comp_tech (X Y Z: rep_space) (f: X ->> Y) (g: Y -> Z) M N:
	f \is_total -> M \is_rec_realizer_of f -> N \is_realizer_function_for g
	-> forall h, (forall x y, f x y -> h x = g y) -> (fun phi => N (M phi)) \is_realizer_function_for h.
Proof.
move => ftot comp comp' h eq phi x phinx.
move: comp; rewrite rrlzr_rlzr => comp.
have [y fxy]:= ftot x.
have prop: phi \from_dom (f o (delta (r:=X))).
	exists y; split; first by exists x.
	by move => x' phinx'; rewrite (rep_sing X phi x' x).
have [y' [[psi [<- name]] _]]:= (comp phi prop).1.
rewrite (eq x y') => //; first by apply comp'.
have cond: ((delta (r:=Y)) o (F2MF M) phi y').
	split; first by exists (M phi).
	by move => Mpsi <-; exists y'.
have [[x' [phinx' fx'y']] _] := (comp phi prop).2 y' cond.
by rewrite (rep_sing X phi x x').
Qed.

Lemma rec_fun_rec_comp (X Y Z: rep_space) (f: X ->> Y) (g: Y -> Z):
	f \is_total -> f \is_recursive -> g \is_recursive_function
	-> forall h, (forall x y, f x y -> h x = g y) -> h \is_recursive_function.
Proof.
move => ftot [M comp] [N comp'] h eq.
exists (fun phi => N (M phi)).
by apply (rec_fun_rec_comp_tech ftot comp comp').
Defined.

Lemma rec_fun_cmpt_comp_tech (X Y Z: rep_space) (f: X -> Y) (g: Y -> Z) M N:
	M \is_realizer_function_for f -> (eval N) \is_realizer_of (F2MF g)
	-> forall h, (forall x, h x = g (f x)) -> (eval (fun (n: nat) phi => N n (M phi))) \is_realizer_of (F2MF h).
Proof.
move => comp comp' h eq.
have eq': (F2MF h) =~= ((F2MF g) o (F2MF f)) by rewrite F2MF_comp/ F2MF => r; rewrite -(eq r).
rewrite eq'.
apply/ tight_trans; last first.
	by rewrite comp_assoc; apply tight_comp_r; apply ((frlzr_rlzr _ _).1 comp).
apply/ tight_trans; last by rewrite -comp_assoc; apply tight_comp_l; apply comp'.
by rewrite comp_assoc; apply/ tight_comp_r; rewrite F2MF_comp.
Qed.

Lemma rec_fun_cmpt_comp (X Y Z: rep_space) (f: X -> Y) (g: Y -> Z):
	f \is_recursive_function -> g \is_computable_function
	-> forall h, (forall x, h x = g (f x)) -> h \is_computable_function.
Proof.
move => [M comp] [N comp']; exists (fun n phi => N n (M phi)).
exact: (rec_fun_cmpt_comp_tech comp comp').
Defined.

Lemma rec_fun_cmpt (X Y: rep_space) (f: X -> Y):
	f \is_recursive_function -> f \is_computable_function.
Proof.
move => [N Nir]; exists (fun n phi q' => Some (N phi q')).
abstract by apply/ tight_trans; [apply tight_comp_r; apply: rec_F2MF_op 0 | apply frlzr_rlzr; apply/ Nir].
Defined.

Lemma cnst_rec_fun (X Y: rep_space) (fx: Y):
	fx \is_recursive_element -> (fun x: X => fx) \is_recursive_function.
Proof. by move => [psi psiny]; exists (fun _ => psi). Defined.

Lemma cnst_rec (X Y: rep_space) (fx: Y):
	fx \is_recursive_element -> (F2MF (fun (x: X) => fx)) \is_recursive.
Proof. by move => fxcmpt; by apply rec_fun_rec; apply cnst_rec_fun. Defined.

Lemma id_rec_fun X:
	(@id (space X)) \is_recursive_function.
Proof. by exists id. Defined.

Lemma id_rec X:
	@is_rec X X (F2MF id).
Proof. exists id; abstract by rewrite rrlzr_rlzr -frlzr_rlzr. Defined.

Lemma id_cmpt X:
	@is_cmpt X X (F2MF id).
Proof. exact: (rec_cmpt (id_rec X)). Defined.

Lemma id_hcr X:
	@hcr X X (F2MF id).
Proof.
exists (F2MF id).
split; first by apply frlzr_rlzr.
move => phi q' _.
exists [ ::q'].
move => Fphi /= <- psi coin Fpsi <-.
apply coin.1.
Qed.

Lemma diag_cmpt_fun (X: rep_space):
	(@diag X) \is_computable_function.
Proof. by apply rec_fun_cmpt; apply diag_rec_fun. Defined.

Lemma diag_hcr (X: rep_space):
	(F2MF (@diag X)) \has_continuous_realizer.
Proof.
exists (F2MF (fun phi => name_pair phi phi)).
split; first by apply frlzr_rlzr.
move => phi q.
case: q => q; by exists [:: q] => Fphi/= <- psi [eq _] Fpsi <-; rewrite /name_pair eq.
Qed.

Lemma diag_cmpt (X: rep_space):
	(F2MF (@diag X)) \is_computable.
Proof. apply rec_cmpt; apply diag_rec. Defined.

Lemma rec_elt_prod_rec (X Y Z: rep_space) (g: X * Y -> Z) (x: X) f:
	g \is_recursive_function -> x \is_recursive_element -> f = (fun y => g (x,y)) -> f \is_recursive_function.
Proof.
move => frec xcmpt ->.
apply /rec_fun_comp.
	apply diag_rec_fun.
	apply /rec_fun_comp.
		apply /prod_rec_fun.
			by apply id_rec_fun.
		by apply/ cnst_rec_fun; apply xcmpt.
	apply/ rec_fun_comp.
		by apply switch_rec_fun.
	by apply frec.
done.
done.
done.
Defined.

(*Lemma cmpt_fun_comp (X Y Z: rep_space) (f: X -> Y) (g: Y -> Z):
	f \is_monotone_computable -> g \is_computable_function
	-> forall h, (forall x, h x = g (f x)) -> h \is_computable_function.
Proof.
move => [M comp] [N comp'] h eq.
exists (fun phi => N (M phi)).
by move => phi x phinx; rewrite eq; apply comp'; apply comp.
Defined.*)
End BASIC_LEMMAS.