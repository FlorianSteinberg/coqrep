(* This file provides an alternative formulation of represented spaces that saves
the input and output types of the names *)
From mathcomp Require Import all_ssreflect.
Require Import continuity universal_machine multi_valued_functions machines.
Require Import FunctionalExtensionality Psatz ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section REPRESENTED_SPACES.
Definition is_rep S T (delta: S ->> T) :=
  delta is_single_valued /\ delta is_surjective.
Notation "delta 'is_representation'" := (is_rep delta) (at level 2).
(* S ->> T is a notation for S -> T -> Prop. This defines a representation to be a
surjective and singlevalued multi-valued function. Due to delta being single-valued
this can also be phrased as a representation being a partial surjection. *)

Definition is_rep_of S T (delta: S ->> T) (P : T -> Prop) :=
  delta is_single_valued_wrt (fun t t' => t = t') /\ delta is_surjective_wrt P.
Notation "delta 'is_representation_of' elements" := (is_rep_of delta elements) (at level 2).
(* To make subspaces work, we allow predicates as the underlying set of a represented space. *)

Definition is_rep_of_wrt S T (delta: S ->> T) (P: T -> Prop) (R: T-> T -> Prop) :=
  delta is_single_valued_wrt R /\ delta is_surjective_wrt P.
Notation "delta 'represents' elements 'wrt' identify" := (is_rep_of_wrt delta elements identify) (at level 2).

Definition is_rep_wrt S T (delta: S ->> T) (R: T-> T -> Prop) :=
	delta is_single_valued_wrt R /\ delta is_surjective_wrt (fun t => R t t).

Notation "delta 'is_representation_wrt' equal" :=
  (is_rep_wrt delta equal) (at level 2).
(* This is to make it possible to identify elements arbirarily, i.e. make quotients work. *)

Lemma R_sym S T delta P R:
	@is_rep_of_wrt S T delta P R ->
		forall s t, P s -> (R s t <-> R t s).
Proof.
move => [] sing sur t t' Pt.
split => eq.
	move: (sur t Pt) => [] s [] dst sprop.
	move: (sing.2.1 s t t' dst eq) => dst'.
	by apply/ (sing.1 s).
move: (sur t Pt) => [] s [] dst sprop.
move: (sing.2.2 s t t' dst eq) => dst'.
by apply/ (sing.1 s).
Qed.

Lemma R_trans S T delta P R:
	@is_rep_of_wrt S T delta P R ->
		forall s r t, P r -> R s r -> R r t -> R s t.
Proof.
move => rep s r t Pr Rsr Rrt'.
move: (rep.2 r Pr) => [] s' [] ds'r sprop.
move: (rep.1.2.1 s' r t ds'r Rrt') => ds't.
move: ((@R_sym S T delta P R rep r s Pr).2 Rsr) => Rrs.
move: (rep.1.2.1 s' r s ds'r Rrs) => dst.
apply/ (rep.1.1).
apply dst.
apply ds't.
Qed.

Lemma R_ref S T delta P R:
	@is_rep_of_wrt S T delta P R ->
		(forall t, P t -> R t t).
Proof.
move => rep t Pt.
move: ((rep.2 t Pt)) => [] s' [] ds't sprop.
by apply (rep.1.1 s' t t).
Qed.

Lemma sur_rep_b S T (delta: S ->> T) :
  delta is_representation <-> delta is_representation_of (fun x => True).
Proof.
split.
- move => [issing issur].
	split.
		split.
 			move => s t t' dst dst'.
 			by apply: (issing.1 s t t').
 		split => s t t' dst eq.
 			by rewrite -eq.
 		by rewrite eq.
  move => t _ .
  move: (issur t) => [] s dst.
  by exists s.
move => [issing issur].
split.
	split.
		move => s t t' dst dst'.
  	by apply: (issing.1 s t t').
	split => s t t' dst eq.
		by rewrite -eq.
	by rewrite eq.
move => t.
have: True.
	done.
move => true.
move: (issur t true) => []s []dst_.
by exists s.
Qed.

Lemma sur_rep S T (delta: S ->> T) :
  delta is_representation -> delta is_representation_of (fun x => True).
Proof.
  move: (sur_rep_b delta) => [cond cond'].
  exact: cond.
Qed.

Lemma sur_rep_sing_b S T (delta: S ->> T) (P: T -> Prop) :
  delta is_representation_of P <-> delta represents P wrt (fun x y => x = y).
Proof.
done.
Qed.

Lemma rep_wrt S T (delta: S ->> T) (P: T-> Prop) (R: T -> T -> Prop):
	delta represents P wrt R <-> delta is_representation_wrt (fun t t' => P t /\ R t t').
Proof.
split.
	move => [] sing sur.
	split.
		split.
			move => s t t' dst dst'.
			move: (sing.1 s t t').
			split => s t t' dst eq.
				apply: (sing.2.1 s t t') =>//.
				apply eq.2 => //.
			apply: (sing.2.2 s t t') =>
			apply eq.2.2.

Lemma sur_rep_sing S T (delta: S ->> T) (P: T -> Prop) :
  delta is_representation_of P -> delta represents P wrt (fun x y => x = y).
Proof.
move: (sur_rep_sing_b delta P) => [cond cond'].
exact: cond.
Qed.

(* To construct a represented space it is necessary to provide a proof that the
representation is actually a representation. The names can be an arbitrary type
but will usually be something that can be computed on, i.e. Baire space or something.
At some point I will probably change the names to be a size_type. The type of names
must be inherited for the rather irrelevant full function-space construction to
work. This may change depending on whether other function space constructions also
need this or not. *)
Structure type := make_rep_space {
  space : Type;
  equal: space -> space -> Prop;
  questions : Type;
  answers : Type;
	No_answer:answers;
  delta : (questions -> answers) ->> space;
  countable_questions: questions is_countable;
  countable_answers: answers is_countable;
  representation_is_valid : delta is_representation_wrt equal
  }.
Notation names X := ((questions X) -> (answers X)).
Notation rep_space := type.
Notation "'rep'" := @delta (at level 2).
Notation "phi 'is_name_of' x" := (delta phi x) (at level 2).
Notation "x 'is_element'" := (equal x x) (at level 2).
Notation "x 'is_from' X" := (@equal X x x) (at level 2).
Notation "x 'equals' y" := (equal x y) (at level 2).

Lemma equal_ref X:
	(forall x:space X, x is_from X <-> x equals x).
Proof.
done.
Qed.

Lemma equal_sym X:
	forall (x:space X) y, x is_from X -> (x equals y <-> y equals x).
Proof.
exact: (R_sym (representation_is_valid X)).
Qed.

Lemma equal_trans X:
		forall x y z:space X, y is_from X -> x equals y -> y equals z -> x equals z.
Proof.
exact (R_trans (representation_is_valid X)).
Qed.

Definition prod_rep X Y :=
	(fun (phipsi : (questions X + questions Y -> answers X + answers Y)) x =>
      delta (fun q => match phipsi (inl q) with
        | inl a => a
        | inr b => No_answer X
      end) x.1 /\ delta (fun q => match phipsi (inr q) with
        | inl a => No_answer Y
        | inr b => b
      end) x.2).

Lemma prod_rep_is_rep (X Y : type):
  (@prod_rep X Y) is_representation_wrt (fun x y => equal x.1 y.1 /\ equal x.2 y.2).
Proof.
move: (@representation_is_valid X) (@representation_is_valid Y)
  => [xsing xsur] [ysing ysur].
split.
	split.
		move => phipsi [x y] [x' y'] /= [inx iny] [inx' iny'].
    split.
      apply: xsing.1 => //.
      	by apply: inx.
      by apply: inx'.
    apply: ysing.1 => //.
      by apply iny.
    by apply iny'.
	split => phipsi.
		move => [] x y [] x' y' /=[] inx iny [] ex ey.
		split.
			apply/ xsing.2.1.
				by apply inx.
			done.
		apply/ ysing.2.1.
			by apply iny.
		done.
	move => [] x y [] x' y' /=[] inx iny [] ex ey.
	split.
		apply/ xsing.2.2.
			by apply inx.
		done.
	apply/ ysing.2.2.
		by apply iny.
	done.
move => [] x y /=[Px Py].
move: (xsur x Px) => [] phi []dphix phiprop.
move: (ysur y Py) => [] psi []dpsiy psiprop.
exists (fun q => match q with
	| inl qx => inl (phi qx)
	| inr qy => inr (psi qy)
end).
rewrite /prod_rep.
split => //= [] s t' [] dx dy [] dt1 dt2.
split.
	apply: phiprop.
		by apply dx.
	by apply dt1.
apply: psiprop.
	by apply dy.
by apply dt2.
Qed.

(* This is the product of represented spaces. At some point I should prove that this
is the product in some category, but I am unsure what the morphisms are supposed to be. *)

Lemma sum_is_countable Q Q':
  Q is_countable -> Q' is_countable -> (Q + Q') is_countable.
Proof.
move => [cnt1] sur1 [cnt2] sur2.
set cnt' := fix cnt' n acc := match n with
	| 0 => inl (cnt1 acc) 
	| 1 => inr (cnt2 acc)
	| S (S n') => (cnt' n' (S acc))
end.

have prop: forall n k, cnt' (2 * n) k = inl(cnt1 (n + k)).
	elim => //.
	move => n ih k.
	replace (2*n.+1) with ((2*n).+2) by by rewrite /muln/muln_rec; lia.
	rewrite /= (ih (k.+1)).
	by replace (n + k.+1) with (n.+1 + k) by by rewrite /addn/addn_rec; lia.
have prop2: forall n k, cnt' (2 * n + 1) k = inr(cnt2 (n + k)).
	elim => //.
	move => n ih k.
	replace (2*n.+1) with ((2*n).+2) by by rewrite /muln/muln_rec; lia.
	rewrite /= (ih (k.+1)).
	by replace (n + k.+1) with (n.+1 + k) by by rewrite /addn/addn_rec; lia.

exists (fun n => cnt' n 0).
rewrite /is_sur.
apply sum_rect.
	move => s.
	move: (sur1 s) => [n] idx.
	exists (2*n).
	move: n s idx.
	rewrite /F2MF.
	elim.
		move => s idx.
		by rewrite -idx.
	move => n ih s idx.
	replace (2 * n.+1) with ((2 * n).+2) by by rewrite /muln/muln_rec; lia.
		rewrite -idx /=.
		rewrite prop.
		by replace (S n) with (n + 1) by by rewrite /addn/addn_rec; lia.
	move => s.
	move: (sur2 s) => [n] idx.
	exists (2*n + 1).
	move: n s idx.
	rewrite /F2MF.
	elim.
		move => s idx.
		by rewrite -idx.
	move => n ih s idx.
	replace (2 * n.+1) with ((2 * n).+2) by by rewrite /muln/muln_rec; lia.
		rewrite -idx /=.
		rewrite prop2.
		by replace (S n) with (n + 1) by by rewrite /addn/addn_rec; lia.
Qed.

Canonical rep_space_prod X Y := @make_rep_space
  (space X * space Y)
  (fun x y => equal x.1 y.1 /\ equal x.2 y.2)
  (@questions X + @questions Y)
  (@answers X + @answers Y)
  (inl (No_answer X))
  (@prod_rep X Y)
  (sum_is_countable (countable_questions X) (countable_questions Y))
  (sum_is_countable (countable_answers X) (countable_answers Y))
  (@prod_rep_is_rep X Y).

Canonical sub_rep_space (X,P) := @make_rep_space
  (space X)
  (fun x y => P x /\ P yequal x.1 y.1 /\ equal x.2 y.2)
  (@questions X + @questions Y)
  (@answers X + @answers Y)
  (inl (No_answer X))
  (@prod_rep X Y)
  (sum_is_countable (countable_questions X) (countable_questions Y))
  (sum_is_countable (countable_answers X) (countable_answers Y))
  (@prod_rep_is_rep X Y).


Lemma prod_is_countable Q Q':
  Q is_countable -> Q' is_countable -> (Q * Q') is_countable.
Proof.
admit.
Admitted.

Lemma list_is_countable Q:
	Q is_countable -> (list Q) is_countable.
Proof.
admit.
Admitted.

Definition is_mf_realizer (X Y : rep_space) F (f : (space X) ->> (space Y)) :=
  forall phi x y, x is_from X -> delta phi x -> f x y -> y is_from Y /\ delta (F phi) y.
(* One candidate for the morphisms: The multivalued realizable functions. *)

Definition is_realizer (X Y : rep_space) F (f: space X -> space Y) :=
	is_mf_realizer F (F2MF f).
(* A second candidate: the total singlevalued realizable functions *)
Notation "F 'is_realizer_of' f" := (is_realizer F f) (at level 2).

Lemma is_realizer_is_rep (X Y : rep_space):
  (@is_realizer X Y)
    is_representation_wrt
  (fun f g => forall x y, x is_from X -> y is_from X -> x equals y -> (f x) equals (g y)).
Proof.
  move: (@representation_is_valid X) (@representation_is_valid Y)
    => [xsing xsur] [ysing ysur].
  split.
  	split.
  		move => F f g irf irg x y xie yie xey.
    	move: (xsur x xie) => [] phi [] phinx prop.
    	apply: (ysing.1 (F phi) (f x) (g y)).
				by apply/ (irf phi x (f x) xie phinx _).2.
			move: (xsing.2.1 phi x y phinx xey) => phiny.
			by apply: (irg phi y (g y) yie phiny _).2.
		split => F f g irf prop phi x gx xie phinx gxgx.
			rewrite - gxgx.
			have Fphinfx: (F phi) is_name_of (f x) by apply (irf phi x (f x)).
			move: (prop x x xie xie xie) => fxegx.
 			have Fphingx: (F phi) is_name_of (g x) by apply: (ysing.2.1 (F phi) (f x) (g x)).
 			split => //.
 			have fxefx: (f x) equals (f x) by apply/ (irf phi x (f x) _ _ _).1.
			apply/ equal_trans.
					by apply fxefx.
				by apply (@equal_sym Y (f x) (g x) fxefx).
			by apply fxegx.
		rewrite - gxgx.
		have Fphinfx: (F phi) is_name_of (f x) by apply (irf phi x (f x)).
		move: (prop x x xie xie xie) => fxegx.
		have Fphingx: (F phi) is_name_of (g x) by apply: (ysing.2.2 (F phi) (f x) (g x)).
		split => //.
		have fxefx: (f x) equals (f x) by apply/ (irf phi x (f x) _ _ _).1.
		apply/ equal_trans.
				by apply fxefx => //.
			by apply fxegx.
		by apply (@equal_sym Y (f x) (g x) fxefx).			
	move => f cond.
  set R := fun a b => forall x, x is_element -> delta a x -> (f x) is_element /\ delta b (f x).
  have: forall a, exists b, R a b.
  move => a.
  case: (classic (exists x, delta a x /\ x is_element)).
  	move => [x [anx xie]].
		move: (cond x x xie xie xie) => fxie.
    move: (ysur (f x) fxie) => [b []bnx] prop.
    exists b.
    move => y yie any.
    move: (xsing.1 a x y anx any) => xey.
    move: (cond x y xie yie xey) => fxefy.
    split.
    	apply/ equal_trans.
   				by apply fxie.
   			by apply (equal_sym (f y) fxie).
   		done.
   	by apply: (ysing.2.1 b (f x) (f y)).
  move => eq.
  exists (fun q => @No_answer Y).
  move => y yifx any.
  exfalso.
  apply eq.
  by exists y.
move => fe.
move: (@choice (names X) (names Y) R fe) => [F Fir].
rewrite /R in fe Fir.
move: R fe => _ _.
exists F.
split.
	move => a x y xie anx eq.
	move: (Fir a x xie anx) => Fanfx.
	by rewrite -eq.
move => G g Grf Grg x.
move => y xie yie xey.
move: (xsur x xie) => [] phi [] phinx _.
move: (xsur y yie) => [] psi [] psiny _.
have fxefx: (f x) equals (f x) by apply (Fir phi x xie phinx).1.
have fyefy: (f y) equals (f y) by apply (Fir psi y yie psiny).1.
have gxefx: (g x) equals (f x).
	apply/ ysing.1.
		by apply: (Grg phi x (g x) _ _ _).2.
	by apply: (Grf phi x (f x) _ _ _).2.
have gyefy:	(g y) equals (f y).
	apply/ ysing.1.
		by apply: (Grg psi y (g y) _ _ _).2.
	by apply: (Grf psi y (f y) _ _ _).2.
apply: (equal_trans fxefx gxefx) => //.
have fxefy: (f x) equals (f y) by apply cond.
apply: (equal_trans fyefy fxefy).
by apply: (equal_sym (g y) fyefy).2.
Qed.

Definition is_mf_rlzr (X Y: rep_space) (F: (names X) ->> (names Y)) (f: (space X) ->> (space Y)) :=
	(rep Y) o F tightens (f o (rep X)).

Definition is_rlzr (X Y: rep_space) (F: (names X) ->> (names Y)) (f: (space X) -> (space Y)) :=
	@is_mf_rlzr X Y F (F2MF f).

Definition has_cont_rlzr (X Y : rep_space) (f : (space X) -> (space Y)) :=
	exists F, is_rlzr F f /\ @is_cont (questions X) (answers X) (questions Y) (answers Y) F.

Definition is_ass (X Y: rep_space) psiF (f: (space X) -> (space Y)) :=
	exists F, (@is_rlzr X Y F f) /\ (fun n phi q' => U n psiF phi q') computes F.

Lemma is_associate_is_rep (X Y : rep_space):
  (@is_ass X Y)
    represents
  (@has_cont_rlzr X Y)
  	wrt
  (fun f g => forall x y, x is_from X -> y is_from X -> x equals y -> (f x) equals (g y)).
Proof.
move: (representation_is_valid X) (representation_is_valid Y) => [] xsing xsur [] ysing ysur.
split.
Admitted.

Canonical rep_space_cont_fun X Y := @make_rep_space
  (space X -> space Y)
  (fun f g => f has_cont_rlzr /\ g has_cont_rlzr /\ equal x.1 y.1 /\ equal x.2 y.2)
  (@questions X + @questions Y)
  (@answers X + @answers Y)
  (inl (No_answer X))
  (@prod_rep X Y)
  (sum_is_countable (countable_questions X) (countable_questions Y))
  (sum_is_countable (countable_answers X) (countable_answers Y))
  (@prod_rep_is_rep X Y).


(*Definition make_rep_space_from_sur
  (space : Type)
  (questions : Type)
  (answers : Type)
  (delta : (questions->answers) ->> space) (representation_is_valid : is_rep delta) :=
  @make_rep_space space
    (fun x=> True)
    (fun x y => x= y)
    questions
    answers
    (sur_rep_sing (sur_rep representation_is_valid))
  .*)

Lemma fun_rep_on_range S X (f : S -> X) :
  (F2MF f) is_representation_of (range (F2MF f)).
Proof.
split.
	split => s t t' fst H;by rewrite -H.
move => t [] s fst.
exists s.
split => //.
move => s' x' fs't fs't'.
by exists s'.
Qed.

(*
Definition make_rep_space_from_fun
  (space : Type)
  (names : Type)
  (inhe : names)
  (delta : names -> space) :=
    @rep_space.make_rep_space
      space
      (range (F2MF delta))
      (fun x y => x = y)
      names
      inhe
      (F2MF delta)
      (sur_rep_sing (fun_rep_on_range delta))
    .
*)

Lemma single_valued_rep_on_range S T (f : S ->> T) :
  f is_single_valued -> f is_representation_of (range f).
Proof.
move => sing.
split => //.
move => t [] s fst.
exists s.
split => //.
move => s' t' _ fs't'.
by exists s'.
Qed.

(*
Definition make_rep_space_from_mfun
  (space: Type)
  (names : Type)
  (inhe:names)
  (delta: names ->> space)
  (sing: delta is_single_valued) :=
    @rep_space.make_rep_space
      space
      (range delta)
      (fun x y => x = y)
      names
      inhe
      delta
      (sur_rep_sing (single_valued_rep_on_range sing)).

Definition make_rep_space_from_fun
  (space : Type)
  (questions : Type)
  (answers : Type)
  (delta: (questions->option answers) -> space) :=
    @make_rep_space
      space
      (range (F2MF delta))
      (fun x y => x = y)
      questions
      answers
      (F2MF delta)
      (sur_rep_sing (fun_rep_on_range delta))
    .
*)

Definition is_prim_rec (X Y : rep_space) (f : space X -> space Y) :=
  exists F, is_realizer F f.
Notation "f 'is_primitive_recursive'" := (is_prim_rec f) (at level 2).

Notation "X ~> Y" := (nat -> (names X) -> (questions Y) -> answers Y) (format "X ~> Y", at level 2).
(* I think about this type as a type of machines: For M : B ~> B' I "read M s n = nothing" as
"the Machine can't say anything about the return value yet" and "M s n = some t" as "after n
steps the machine considers t to be the best answer". Since no assumption about concurrency
have been made, in general a machine will produce an infinite list of return values. *)

Definition eval (X Y : rep_space) (M : X ~> Y) : ((names X) ->> (names Y)) :=
  fun (phi : names X) (psi : names Y) => forall (a : questions Y), exists n, M n phi a = psi a.
(* if M is a machine then eval M is the function the machine computes. Since no assumptions
about convergence or concurrency have been made, the computed multivalued function need
neither be singlevalued nor total. *)
