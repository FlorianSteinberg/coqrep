From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Structure space:= make_space {
	type : Type;
	equal: type ->> type;
	equal_sym: forall s t, equal s t -> equal t s;
	equal_trans: forall s t r, equal s t -> equal t r -> equal s r;
}.

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

Definition space_from_type T:=
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
`