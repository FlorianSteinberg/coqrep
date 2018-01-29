From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SPACES.

Structure Space:= make_space {
	type : Type;
	equal: type ->> type;
	equal_sym: forall s t, equal s t -> equal t s;
	equal_trans: forall s t r, equal s t -> equal t r -> equal s r;
}.
Notation "x 'equals' y" := (equal x y) (at level 2).
Notation "x 'is_from' X" := (@equal X x x) (at level 2).
Notation "x 'is_element'" := (equal x x) (at level 2).

Lemma prod_equal_sym X Y x y:
	(@equal X) x.1 y.1 /\ (@equal Y) x.2 y.2 -> (@equal X) y.1 x.1 /\ (@equal Y) y.2 x.2.
Proof.
move => [] xey1 xey2.
split.
	by apply (equal_sym xey1).
by apply (equal_sym xey2).
Qed.

Lemma prod_equal_trans X Y x y z:
	(@equal X) x.1 y.1 /\ (@equal Y) x.2 y.2 -> (@equal X) y.1 z.1 /\ (@equal Y) y.2 z.2 ->
	(@equal X) x.1 z.1 /\ (@equal Y) x.2 z.2.
Proof.
move => [] xey1 xey2 [] yez1 yez2.
split.
	by apply (equal_trans xey1 yez1).
by apply (equal_trans xey2 yez2).
Qed.

Canonical prod_space X Y := @make_space
	((type X) * (type Y))
	(fun p p' => (@equal X) p.1 p'.1 /\ (@equal Y) p.2 p'.2)
	(@prod_equal_sym X Y)
	(@prod_equal_trans X Y).

Section SPACES_CONSTRUCORS.

Lemma strd_equal_sym T:
	forall (s t: T), s = t -> t = s.
Proof.
by trivial.
Qed.

Lemma strd_equal_trans T:
	forall (s t r: T), s = t -> t = r -> s = r.
Proof.
move => s t r st tr; by rewrite st -tr.
Qed.

Canonical space_from_type T:=
	@make_space
		T
		(fun (s t : T) => s = t) 
		(@strd_equal_sym T)
		(@strd_equal_trans T).

Lemma prop_equal_sym T P:
	forall (s t: T), P s /\ s = t -> P t /\ t = s.
Proof.
move => s t [] Ps st; split => //.
by rewrite -st.
Qed.

Lemma prop_equal_trans T P:
	forall (s t r: T), P s /\ s = t -> P t /\ t = r -> P s /\ s = r.
Proof.
move => s t r [] Ps st []Pt tr;split => //.
by rewrite st -tr.
Qed.

Definition space_from_pred T P:=
	@make_space
		T
		(fun (s t: T) => P s /\ s = t)
		(@prop_equal_sym T P)
		(@prop_equal_trans T P).
End SPACES_CONSTRUCORS.

Definition well_def X Y (f: (type X) ->> (type Y)):=
	forall x fx, x is_from X -> f x fx -> fx is_from Y.

Notation "f 'is_well_defined'" := (well_def f) (at level 2).

Structure multifunction X Y:= make_multi_function {
	graph:> (type X) ->> (type Y);
	well_defined: graph is_well_defined
}.
Notation "X ->> Y" := (multifunction X Y).

Context (X Y X' Y': Space).

Lemma mf_prod_well_def (f: X ->> Y) (g: X' ->> Y'):
(mf_prod f g) is_well_defined.
Proof.
move => [] x y [] fx gy [] /= xie yie [] /= fxfx gygy.
split.
	by apply (@well_defined X Y f x fx).
by apply (@well_defined X' Y' g y gy).
Qed.

Canonical prod_mf (f: X ->> Y) (g: X' ->> Y') := @make_multi_function
	(prod_space X X') (prod_space Y Y') ((graph f) \, (graph g)) (@mf_prod_well_def f g).
Notation "f \, g" := (prod_mf f g) (at level 50).

Definition is_sing X Y (f: X ->> Y):=
	forall x y fx fy, x equals y -> f x fx -> f y fy -> fx equals fy.
Notation "f 'is_single_valued'" := (is_sing f) (at level 2).

Lemma prod_sing (f: X ->> Y) (g : X' ->> Y'):
  f is_single_valued /\ g is_single_valued -> (f \, g) is_single_valued.
Proof.
move => [fsing gsing] x x' y y' xey fgxy fgx'y'; split.
	by apply/ (fsing x.1 x'.1 y.1 y'.1 xey.1 fgxy.1 fgx'y'.1).
by apply/ (gsing x.2 x'.2 y.2 y'.2 xey.2 fgxy.2 fgx'y'.2).
Qed.

Lemma mf_comp_well_def (f: Y ->> Y') (g: X ->> Y):
	f is_well_defined -> g is_well_defined -> f o g is_well_defined.
Proof.
move => fwd gwd x fgx xie [] [] y [] gxy fyfgx prop.
move: (gwd x y xie gxy) => yie.
by apply: (fwd y fgx).
Qed.

Canonical comp_mf (f: Y ->> Y') (g: X ->> Y) := @make_multi_function
	X Y' ((graph f) o (graph g)) (@mf_comp_well_def f g (@well_defined Y Y' f) (@well_defined X Y g)).
Notation "f 'o' g" := (comp_mf f g) (at level 2).

Lemma single_valued_composition (f: Y ->> Y') (g : X ->> Y) :
	f is_single_valued -> g is_single_valued -> f o g is_single_valued.
Proof.
move => fsing gsing x x' fgx fgx' xex' [] [] y [] gxy fyfgx _ [][] y' [] gx'y' fy'fgx' _.
have yey': y equals y' by apply (gsing x x' y y').
by apply: (fsing y y' fgx fgx').
Qed.

End SPACES.
