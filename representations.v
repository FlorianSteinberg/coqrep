From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions spaces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This should be... realizability theory? *)

Section REALIZABILITY.

Definition is_rep S T (delta: S ->> T):=
	forall s s' t t', delta s t -> delta s t' -> delta s' t' -> delta s' t.
Notation "delta 'is_representation'" := (is_rep delta) (at level 2).

Definition is_rep_of S X (delta: S ->> (type X)) :=
	is_rep delta /\ forall x y, (@equal X) x y <-> (exists psi, delta psi x /\ delta psi y).
Notation "delta 'is_representation_of' X" := (@is_rep_of _ X delta) (at level 2).
(* S ->> T is a notation for S -> T -> Prop. This defines a representation to be a
surjective and singlevalued multi-valued function. Due to delta being single-valued
this can also be phrased as a representation being a partial surjection. *)

(* To construct a represented space it is necessary to provide a proof that the
representation is actually a representation. The names can be an arbitrary type
but will usually be something that can be computed on, i.e. Baire space or something.
At some point I will probably change the names to be a size_type. The type of names
must be inherited for the rather irrelevant full function-space construction to
work. This may change depending on whether other function space constructions also
need this or not. *)

Structure rlzr_space := make_rlzr_space {
  space :> Space;
  names : Type;
  inhe: names;
  delta : names ->> (type space);
  representation_is_valid : delta is_representation_of space
  }.
Notation rep_val:= representation_is_valid.
Notation rep_valid:= representation_is_valid.
Notation "'rep'" := @delta (at level 2).
Notation "phi 'is_name_of' x" := (delta phi x) (at level 2).
Notation "x 'is_element'" := (equal x x) (at level 2).
Notation "x 'is_from' X" := (@equal (@space X) x) (at level 2).
Notation "x 'equals' y" := (equal x y) (at level 2).
Notation "x 'is_computable'" := {phi | delta phi x} (at level 2).

Lemma prod_rep (X Y : rlzr_space):
  (@delta X \, @delta Y) is_representation_of (prod_space (space X) (space Y)).
Proof.
split.
	move => phi psi x y []dphix1 dphix2 [] dphiy1 dphiy2 []dpsiy1 dpsiy2.
	split.
		by apply/ ((rep_val X).1 phi.1 psi.1 x.1 y.1).
	by apply/ ((rep_val Y).1 phi.2 psi.2 x.2 y.2).
move => [] x y [] x' y'.
split.
	move => [] /= xex' yey'.
	move: (((@rep_val X).2 x x').1 xex') => [] phi [] dphix dphix'.
	move: (((@rep_val Y).2 y y').1 yey') => [] psi [] dpsiy dpsiy'.
	exists (phi, psi).
	split.
		by split.
	by split.
move => [] [] phi psi [] []/= dphix dpsiy []/= dphix' dpsiy'.
split.
	apply/ ((@rep_val X).2 x x').
	by exists phi.
apply/ ((@rep_val Y).2 y y').
by exists psi.
Qed.

(* This is the product of represented spaces. At some point I should prove that this
is the product in some category, but I am unsure what the morphisms are supposed to be. *)

Canonical rep_space_prod X Y := @make_rlzr_space
  (prod_space (space X) (space Y))
  (names X * names Y)
  (pair (inhe X) (inhe Y))
  (rep X \, rep Y)
  (@prod_rep X Y).

Definition is_mf_rlzr (X Y: rlzr_space) (F: (names X) ->> (names Y)) (f: (type (space X)) ->> (type (space Y))) :=
	(rep Y) o F tightens ((@equal (space Y)) o f o (rep X)).

Definition is_rlzr (X Y: rlzr_space) (F: (names X) ->> (names Y)) (f: (type (space X)) -> (type (space Y))) :=
	@is_mf_rlzr X Y F (F2MF f)
	/\
	forall x y, x equals y -> (f x) equals (f y).
Notation "f 'is_realized_by' F" := (is_rlzr F f) (at level 2).
Notation "F 'is_realizer_of' f" := (is_rlzr F f) (at level 2).

Lemma is_rlzr_is_rep X Y:
  (@is_rlzr X Y) is_representation.
Proof.
move => F G f g [] Frf ftotal [] Frg gtotal [] Grg _.
split => //.
move => phi exfx.
move: exfx (Frf phi exfx) => _ [] [] fx [] [] Fphi [] FphiFphi Fphinfx a b.
have dFphifx: ((@delta Y) o F) phi fx.
	split => //.
	by exists Fphi.
move: dFphifx (b fx dFphifx) => _ [] [] x [] phinx [] [] f'x [] fxf'x f'xefx _ _.
rewrite -fxf'x in f'xefx.
move: f'x fxf'x => _ _.
have: Fphi is_name_of (f x).
	move: (((@rep_valid Y).2 (f x) fx).1 f'xefx) => [] Fpsi []Fpsinf'x Fpsinfx.
	apply/ (rep_valid Y).1.
			by apply Fpsinf'x.
		by apply Fpsinfx.
	done.
move: b fx f'xefx Fphinfx => _ _ _ _ Fphinfx.
have dFphifx: ((@delta Y) o F) phi (f x).
	split => //.
	by exists Fphi.
move: a => _.
have exgx: (exists t : type (space Y),((@equal Y) o (F2MF g)) o (@delta X) phi t).
	exists (g x).
	split.
		exists x.
		split => //.
		split.
			exists (g x).
			split => //.
			apply: (gtotal x x) => //.
			apply ((rep_valid X).2 x x).2.
			by exists phi.
		exists (g x).
		rewrite -H.
		apply: (gtotal x x) => //.
		apply ((rep_valid X).2 x x).2.
		by exists phi.
	move => s phins.
	exists (g s).
	split.
		exists (g s).
		split => //.
		apply/ (gtotal s s) => //.
		apply ((rep_valid X).2 s s).2.
		by exists phi.
	move => s0 gss0.
	rewrite -gss0.
	exists (g s).
	apply/ (gtotal s s) => //.
	apply ((rep_valid X).2 s s).2.
	by exists phi.
move: (Frg phi exgx) => [] [] gx' [] [] Fpsi [] FphiFpsi Fpsingx' a b.
have dFphigx': ((@delta Y) o F) phi gx'.
	split.
		by exists Fpsi.
	by apply a.
move: a dFphigx' (b gx' dFphigx') => _ _ [] [] x' [] phinx' [] [] g'x [] gxg'x g'xegx _ _.
rewrite -gxg'x in g'xegx.
move: g'x gxg'x => _ _.
have: Fpsi is_name_of (g x').
	move: (((rep_valid Y).2 (g x') gx').1 g'xegx) => [] Fpsi' [] Fpsi'ng'x Fpsi'ngx.
	apply/ (rep_valid Y).1.
			by apply Fpsi'ng'x.
		by apply Fpsi'ngx.
	done.
have fxegx': (f x) equals (g x').
	move: dFphifx (b (f x) dFphifx) => _ [] [] x'' [] phinx'' [] [] 	gx'' [] gx''fx gx''efx _ _.
	rewrite -gx''fx in gx''efx.
	move: gx'' gx''fx => _ _.
	apply/ equal_trans.
		by apply: (equal_sym gx''efx).
	apply (gtotal x'' x').
	apply ((rep_valid X).2 x'' x').2.
	by exists phi.
move: b gx' g'xegx Fpsingx' => _ _ _ _ Fpsingx'.
move: (Grg phi exgx) => [] [] gx [] [] Gpsi [] GphiGpsi Gpsingx a b.
move: exgx => _.

split.
	exists (gx).
	split => //.
	exists Gpsi.
	by split.
move: gx Gpsi GphiGpsi Gpsingx => _ _ _ _.
move => y [] [] Gphi [] GphiGphi Gphiny _.
have dGphiy:(@delta Y) o G phi y.
	split => //.
	by exists Gphi.
move: a => _.
move: (b y dGphiy) => [] [] x'' [] phinx'' [] []gx'' [] gx''gx'' 
gx''ey _ _.
rewrite -gx''gx'' in gx''ey.
move: gx'' gx''gx'' => _ _.
have: Gphi is_name_of (g x'').
	move: (((rep_valid Y).2 (g x'') y).1 gx''ey) => [] Gpsi [] Gpsingx'' Gpsiny.
	apply/ (rep_valid Y).1.
			by apply Gpsingx''.
		by apply Gpsiny.
	done.
move: b dGphiy => _ _ Gphingx''.
have fxey: (f x) equals y.
	apply/ (equal_trans);last first.
		by apply gx''ey.
	apply/ (equal_trans);last first.
		apply (gtotal x' x'').
		apply ((rep_valid X).2 x' x'').2.
		by exists phi.
	apply fxegx'.
split.
	exists x.
	split => //.
	split.
		exists (f x).
		by split.
	move => s fxs.
	rewrite -fxs.
	exists (f x).
	apply ((rep_valid Y).2 (f x) (f x)).2.
	by exists (Fphi).
move => x''' phinx'''.
exists (f x''').
split.
	exists (f x''').
	split => //.
	apply (ftotal x''') => //.
	apply ((rep_valid X).2 x''' x''').2.
	by exists phi.
move => s fx'''s.
rewrite -fx'''s.
exists (f x''').
apply (ftotal x''') => //.
apply ((rep_valid X).2 x''' x''').2.
by exists phi.
Qed.
End REALIZABILITY.
Notation rep_val:= representation_is_valid.
Notation rep_valid:= representation_is_valid.
Notation "'rep'" := @delta (at level 2).
Notation "phi 'is_name_of' x" := (delta phi x) (at level 2).
Notation "x 'is_element'" := (equal x x) (at level 2).
Notation "x 'is_from' X" := (@equal (@space X) x) (at level 2).
Notation "x 'equals' y" := (equal x y) (at level 2).
