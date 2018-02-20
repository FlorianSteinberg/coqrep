From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section REP.

Definition is_rep S T (delta: S ->> T):=
	delta is_surjective_partial_function.
Notation "delta 'is_representation'" := (is_rep delta) (at level 2).

Structure rlzr_space := make_rlzr_space {
  space :> Type;
  names : Type;
  some_name: names;
  delta : names ->> space;
  representation_is_valid : delta is_representation
  }.
Notation rep_val:= representation_is_valid.
Notation rep_valid:= representation_is_valid.
Notation "'rep'" := @delta (at level 2).
Notation "phi 'is_name_of' x" := (delta phi x) (at level 2).
Notation "x 'is_computable'" := {phi | delta phi x} (at level 2).

Lemma prod_rep (X Y : rlzr_space):
  (@delta X \, @delta Y) is_representation.
Proof.
split.
	move => [] phi psi [] x y [] x' y' [] /= phinx psiny []/= phinx' psiny'.
	apply injective_projections => /=.
		by apply/ ((rep_val X).1 phi).
	by apply/ ((rep_val Y).1 psi).
move => [] x y.
move: ((rep_val X).2 x) ((rep_val Y).2 y)=> [] phi phinx [] psi psiny.
by exists (phi,psi).
Qed.

(* Canonical construction for the product of represented spaces *)
Canonical rep_space_prod X Y := @make_rlzr_space
  ((space X) * (space Y))
  (names X * names Y)
  (pair (some_name X) (some_name Y))
  (rep X \, rep Y)
  (@prod_rep X Y).

Definition is_mf_rlzr (X Y: rlzr_space) (F: (names X) ->> (names Y)) (f: X ->> Y) :=
	(rep Y) o F tightens (f o (rep X)).

(* rlzr is short for realizer. Realizers can be used to compute multifunctions. Encoding
multifunctions by their relizers leads to problems when the functions are not total.*)
Definition is_rlzr (X Y: rlzr_space) (F: (names X) -> (names Y)) (f: X -> Y) :=
	forall phi x, (rep X) phi x -> (rep Y) (F phi) (f x).
Notation "f 'is_realized_by' F" := (is_rlzr F f) (at level 2).
Notation "F 'is_realizer_of' f" := (is_rlzr F f) (at level 2).

(* The total functions can be represented by their realizers and this can be used for a
function space construction . *)
Lemma is_rlzr_is_rep X Y:
  (@is_rlzr X Y) is_representation.
Proof.
split.
	move => F f g Frf Frg.
	apply functional_extensionality => x.
	move: ((rep_val X).2 x) => [] phi phinx.
	apply/ (rep_val Y).1.
		by apply: (Frf phi).
	by apply: (Frg phi).
move => f.
set R :=(fun phi psi => phi from_dom (rep X) -> forall x, (rep X) phi x -> (rep Y) psi (f x)).
have cond: forall phi, exists psi, R phi psi.
	move => phi.
	case: (classic (phi from_dom (rep X))).
		move => [] x phinx.
		move: ((rep_val Y).2 (f x)) => [] psi psiny.
		exists psi.
		move => _ x' phinx'.
		by rewrite -((rep_val X).1 phi x x').
	move => ass.
	exists (some_name Y).
	move => phifd.
	by exfalso;apply ass.
move: (choice R cond) => [] F Fcond.
exists F.
move => phi x phinx.
apply Fcond => //.
by exists x.
Qed.

(* canonical function space construction. The use should be avoided as it is often inappropriate.
A more appropriate function space construction is availabe for the alternate structure in the
file "par_spaces.v" *)
Canonical rep_space_all_functions X Y := @make_rlzr_space
  (space X -> space Y)
  (names X -> names Y)
  (fun x => @some_name Y)
  (@is_rlzr X Y)
  (@is_rlzr_is_rep X Y).
End REP.
Notation rep_val:= representation_is_valid.
Notation rep_valid:= representation_is_valid.
Notation "'rep'" := @delta (at level 2).
Notation "phi 'is_name_of' x" := (delta phi x) (at level 2).
