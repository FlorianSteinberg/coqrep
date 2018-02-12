From mathcomp Require Import all_ssreflect.
Require Import Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SPACES.

Structure Space:= make_space {
	type :> Type;
	equal: type -> type -> Prop;
	equal_sym: forall x y, equal x y -> equal y x;
	equal_trans: forall x y z, equal x y -> equal y z -> equal x z;
}.
Notation "x 'equals' y" := (equal x y) (at level 70).
Notation "x 'is_from' X" := (@equal X x x) (at level 2).
Notation "x 'is_element'" := (x equals x) (at level 2).

Lemma equal_proj_fst (X: Space) (x y: X):
	x equals y -> x is_element.
Proof.
move => xey.
apply/equal_trans.
	by apply xey.
by apply/equal_sym.
Qed.

Lemma equal_proj_snd (X: Space) (x y: X):
	x equals y -> y is_element.
Proof.
move => xey.
apply: equal_proj_fst.
apply equal_sym.
apply xey.
Qed.

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

Section SPACES_CONSTRUCTIONS.

Context (X Y: Space).

Lemma prod_equal_sym (x y: X * Y):
	(x.1 equals y.1 /\ x.2 equals y.2) -> y.1 equals x.1 /\ y.2 equals x.2.
Proof.
case => xey1 xey2.
split; by apply/ equal_sym.
Qed.

Lemma prod_equal_trans (x y z: X * Y):
	(@equal X) x.1 y.1 /\ (@equal Y) x.2 y.2 -> (@equal X) y.1 z.1 /\ (@equal Y) y.2 z.2 ->
	(@equal X) x.1 z.1 /\ (@equal Y) x.2 z.2.
Proof.
move => [] xey1 xey2 [] yez1 yez2.
split.
	by apply/ (equal_trans xey1).
by apply/ (equal_trans xey2).
Qed.

Canonical prod_space := @make_space
	(X * Y)
	(fun p p' => p.1 equals p'.1 /\ p.2 equals p'.2)
	prod_equal_sym
	prod_equal_trans.

Definition is_morph (f: X -> Y):=
	forall x y, x equals y -> (f x) equals (f y).
Notation "f 'is_morphism'":= (is_morph f) (at level 2).

Definition f_rel (f g: X -> Y) :=
	forall x y, x equals y -> (f x) equals (g y).

Lemma morph_rel (f: X -> Y):
	f is_morphism <-> f_rel f f.
Proof.
done.
Qed.

Lemma morph_rel_simp (f g: X -> Y):
	is_morph f -> (f_rel f g <-> forall x, x equals x -> (f x) equals (g x)).
Proof.
move => morph.
split.
	move => rel x xie.
	by apply (rel x x).
move => cond x y xey.
apply/ equal_trans.
apply: (morph x y xey).
apply (cond y).
apply/ equal_trans.
	apply/ equal_sym.
	by apply xey.
by apply xey.
Qed.

Lemma f_rel_sym:
	forall (f g: X -> Y), f_rel f g -> f_rel g f.
Proof.
move => f g frel x y xey.
apply equal_sym.
apply/ frel => //.
by apply equal_sym.
Qed.

Lemma f_rel_trans:
	forall (f g h: X -> Y), f_rel f g -> f_rel g h -> f_rel f h.
Proof.
move => f g h frg grh x y xey.
apply/ equal_trans.
apply: (frg x y xey).
apply/ (grh y y).
apply/ equal_trans.
	apply/ equal_sym.
	by apply xey.
by apply xey.
Qed.

Canonical fun_space :=
@make_space (X -> Y) f_rel f_rel_sym f_rel_trans.
End SPACES_CONSTRUCTIONS.
End SPACES.
Notation "x 'equals' y" := (equal x y) (at level 70).
Notation "x 'is_from' X" := (@equal X x x) (at level 2).
Notation "x 'is_element'" := (x equals x) (at level 2).
Notation "f 'is_morphism'":= (is_morph f) (at level 2).