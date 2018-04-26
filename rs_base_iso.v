From mathcomp Require Import all_ssreflect.
Require Import all_core rs_base rs_base_fun.
Require Import FunctionalExtensionality ClassicalFacts ClassicalChoice Psatz ProofIrrelevance.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ISOMORPHISMS.
Definition isomorphism (X Y: rep_space) (f: X c-> Y) :=
	exists (g: Y c-> X) (P: f \is_recursive_element) (Q:g \is_recursive_element),
		((projT1 f) o (projT1 g) =~= F2MF id /\ (projT1 g) o (projT1 f) =~= F2MF id).

Definition wisomorphism (X Y: rep_space) (f: X ->> Y) :=
	exists (g: Y ->> X) (P: f \is_computable) (Q: g \is_computable),
	(f o g =~= F2MF id /\ g o f =~= F2MF id).

Definition isomorphic (X Y: rep_space):=
	exists f, @isomorphism X Y f.
Arguments isomorphic {X Y}.

Definition wisomorphic (X Y: rep_space):=
	exists f, @wisomorphism X Y f.
Arguments isomorphic {X Y}.

Notation "X ~=~ Y" := (@isomorphic X Y) (at level 2).

Lemma iso_ref X:
	X ~=~ X.
Proof.
exists (id_fun X); exists (id_fun X).
exists (id_rec_elt X); exists (id_rec_elt X).
by split; rewrite comp_id.
Qed.

Lemma iso_sym X Y:
	X ~=~ Y -> Y ~=~ X.
Proof.
move => [f [g [fcomp [gcomp [bij1 bij2]]]]].
exists g; exists f.
by exists gcomp; exists fcomp.
Qed.

(*
Lemma iso_trans X Y Z (someqx: questions X) (someqz: questions Z):
	X ~=~ Y -> Y ~=~ Z -> X ~=~ Z.
Proof.
move => [f [g [fcomp [gcomp [bij1 bij2]]]]] [f' [g' [f'comp [g'comp [bij1' bij2']]]]].
exists (fun_comp f f').
exists (fun_comp g' g).
split.
	apply/ cmpt_fun_cmpt_elt; [apply: fun_sprd someqx | apply fcmp_mon_cmpt | apply fcmp_sing | | ].
		by apply prod_cmpt_elt; [apply fcomp | apply f'comp].
	by trivial.
split.
	by apply: (@cmpt_fun_cmpt_elt
		(rep_space_prod (Z c-> Y) (Y c-> X)) (Z c-> X)
		(@composition Z Y X)
		(g', g)
		(fun_comp g' g)
		(fun_sprd someqz)
		(fcmp_mon_cmpt Z Y X)
		(@fcmp_sing Z Y X)
		(prod_cmpt_elt g'comp gcomp)
		_
		).
rewrite /fun_comp/=.
split.
	rewrite -comp_assoc (comp_assoc (sval f') (sval f) (sval g)).
	by rewrite bij1 comp_id bij1'.
rewrite -comp_assoc (comp_assoc (sval g) (sval g') (sval f')).
by rewrite bij2' comp_id bij2.
Qed.
*)
End ISOMORPHISMS.
Notation "X ~=~ Y" := (@isomorphic X Y) (at level 2).
