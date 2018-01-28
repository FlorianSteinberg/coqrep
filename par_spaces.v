(* This file provides an alternative formulation of represented spaces that saves
the input and output types of the names *)
From mathcomp Require Import all_ssreflect.
Require Import continuity universal_machine multi_valued_functions machines.
Require Import FunctionalExtensionality Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section REPRESENTED_SPACES.
Structure space:= make_space {
	type : Type;
	equal: type -> type -> Prop;
}.

Definition is_rep_of_all S T (delta: S ->> T) :=
  delta is_single_valued /\ delta is_surjective.
Notation "delta 'is_representation_of_all'" := (is_rep_of_all delta) (at level 2).
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

Definition is_repr S T (delta: S ->> T) := forall s s' t t',
	delta s t -> delta s t' -> delta s' t' -> delta s' t.
Notation "delta 'is_representation'" := (is_repr delta) (at level 2).

Definition is_rep_wrt S T (delta: S ->> T) (R: T-> T -> Prop) :=
	is_repr delta /\
	forall t t', R t t' <-> exists s, delta s t /\ delta s t'.

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
  delta is_representation_of_all <-> delta is_representation_of (fun x => True).
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
  delta is_representation_of_all -> delta is_representation_of (fun x => True).
Proof.
  move: (sur_rep_b delta) => [cond cond'].
  exact: cond.
Qed.

Lemma sur_rep_sing_b S T (delta: S ->> T) (P: T -> Prop) :
  delta is_representation_of P <-> delta represents P wrt (fun x y => x = y).
Proof.
done.
Qed.

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
  questions : Type;
  answers : Type;
	No_answer:answers;
  delta : (questions -> answers) ->> space;
  countable_questions: questions is_countable;
  countable_answers: answers is_countable;
  representation_is_valid : delta is_representation
  }.
About set.
Notation names X := ((questions X) -> (answers X)).
Notation rep_space := type.
Notation "'rep'" := @delta (at level 2).
Notation "phi 'is_name_of' x" := (delta phi x) (at level 2).
Definition equal X x y := (exists phi, (rep X) phi x /\ (rep X) phi y).
Notation "x 'equals' y" := (equal x y) (at level 2).
Notation "x 'is_element'" := (equal x x) (at level 2).
Notation "x 'is_from' X" := (@equal X x x) (at level 2).
Notation "x 'equals' y" := (equal x y) (at level 2).
Notation "'rep_valid' X" := (@representation_is_valid X) (at level 2).

Lemma equal_ref X:
	(forall x:space X, x is_from X <-> x equals x).
Proof.
done.
Qed.

Lemma equal_sym X:
	forall (x:space X) y, (x equals y <-> y equals x).
Proof.
move => x y.
split.
	move => [] phi [] phinx phiny.
	by exists phi.
move => [] phi [] phinx phiny.
by exists phi.
Qed.

Lemma equal_trans X:
		forall x y z:space X, x equals y -> y equals z -> x equals z.
Proof.
move => x y z [] phi [] phinx phiny [] psi [] psiny psinz.
exists psi.
split => //.
by apply: ((rep_valid X) phi psi x y).
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

Lemma prod_rep_is_rep (X Y: rep_space):
	(@prod_rep X Y) is_representation.
Proof.
move => phipsi phi'psi' x x'.
move => [] phinx1 psinx2 [] phinx'1 psinx'2 [] phi'nx'1 psi'nx'2.
split.
	apply/ ((rep_valid X) _ _ x.1 x'.1).
				by apply phinx1.
			done.
		done.
apply/ ((rep_valid Y) _ _ x.2 x'.2).
		by apply psinx2.
	done.
done.
Qed.

(* This is the product of represented spaces. At some point I should prove that this
is the product in some category, but I am unsure what the morphisms are supposed to be. *)

Lemma sum_count Q Q':
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
  (@questions X + @questions Y)
  (@answers X + @answers Y)
  (inl (No_answer X))
  (@prod_rep X Y)
  (sum_count (countable_questions X) (countable_questions Y))
  (sum_count (countable_answers X) (countable_answers Y))
  (@prod_rep_is_rep X Y).

Lemma prod_rep_equal (X Y: rep_space) (x: space X) (y: space Y) x' y':
  (x,y) equals (x',y') <-> x equals x' /\ y equals y'.
Proof.
split.
	move => [] phipsi [] [] /= phinx psiny [] /= phinx' psiny'.
	split.
		by exists (fun q : questions X =>
          match phipsi (inl q) with
          | inl a => a
          | inr _ => No_answer X
          end).
  by exists (fun q : questions Y =>
          match phipsi (inr q) with
          | inl _ => No_answer Y
          | inr b => b
          end).
move => [] [] phi [] phinx phinx' [] psi [] psiny1 psiny2.
by exists (fun q => match q with
	| inl q' => inl (phi q')
	| inr q' => inr (psi q')
end).
Qed.

Lemma prod_count Q Q':
  Q is_countable -> Q' is_countable -> (Q * Q') is_countable.
Proof.
admit.
Admitted.

Lemma list_count Q:
	Q is_countable -> (list Q) is_countable.
Proof.
admit.
Admitted.

Definition is_mf_rlzr (X Y: rep_space) (F: (names X) ->> (names Y)) (f: (space X) ->> (space Y)) :=
	(rep Y) o F tightens ((@equal Y) o f o (rep X)).

Definition is_rlzr (X Y: rep_space) (F: (names X) ->> (names Y)) (f: (space X) -> (space Y)) :=
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
have dFphifx: (delta (t:=Y) o F) phi fx.
	split => //.
	by exists Fphi.
move: dFphifx (b fx dFphifx) => _ [] [] x [] phinx [] [] f'x [] fxf'x f'xefx _ _.
rewrite -fxf'x in f'xefx.
move: f'x fxf'x => _ _.
have: Fphi is_name_of (f x).
	move: f'xefx => [] Fpsi []Fpsinf'x Fpsinfx.
	apply/ (rep_valid Y).
			by apply Fpsinf'x.
		by apply Fpsinfx.
	done.
move: b fx f'xefx Fphinfx => _ _ _ _ Fphinfx.
have dFphifx: (delta (t:=Y) o F) phi (f x).
	split => //.
	by exists Fphi.
move: a => _.
have exgx: (exists t : space Y,((equal (X:=Y)) o (F2MF g)) o (delta (t:=X)) phi t).
	exists (g x).
	split.
		exists x.
		split => //.
		split.
			exists (g x).
			split => //.
			apply: (gtotal x x) => //.
			by exists phi.
		exists (g x).
		rewrite -H.
		apply: (gtotal x x) => //.
		by exists phi.
	move => s phins.
	exists (g s).
	split.
		exists (g s).
		split => //.
		apply/ (gtotal s s) => //.
		by exists phi.
	move => s0 gss0.
	rewrite -gss0.
	exists (g s).
	apply/ (gtotal s s) => //.
	by exists phi.
move: (Frg phi exgx) => [] [] gx' [] [] Fpsi [] FphiFpsi Fpsingx' a b.
have dFphigx': (delta (t:=Y) o F) phi gx'.
	split.
		by exists Fpsi.
	by apply a.
move: a dFphigx' (b gx' dFphigx') => _ _ [] [] x' [] phinx' [] [] g'x [] gxg'x g'xegx _ _.
rewrite -gxg'x in g'xegx.
move: g'x gxg'x => _ _.
have: Fpsi is_name_of (g x').
	move: g'xegx => [] Fpsi' [] Fpsi'ng'x Fpsi'ngx.
	apply/ (rep_valid Y).
			by apply Fpsi'ng'x.
		by apply Fpsi'ngx.
	done.
have fxegx': (f x) equals (g x').
	move: dFphifx (b (f x) dFphifx) => _ [] [] x'' [] phinx'' [] [] 	gx'' [] gx''fx gx''efx _ _.
	rewrite -gx''fx in gx''efx.
	move: gx'' gx''fx => _ _.
	apply/ equal_trans.
		by apply: ((equal_sym (f x) (g x'')).2 gx''efx).
	apply (gtotal x'' x').
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
have dGphiy:(delta (t:=Y)) o G phi y.
	split => //.
	by exists Gphi.
move: a => _.
move: (b y dGphiy) => [] [] x'' [] phinx'' [] []gx'' [] gx''gx'' 
gx''ey _ _.
rewrite -gx''gx'' in gx''ey.
move: gx'' gx''gx'' => _ _.
have: Gphi is_name_of (g x'').
	move: gx''ey => [] Gpsi [] Gpsingx'' Gpsiny.
	apply/ (rep_valid Y).
			by apply Gpsingx''.
		by apply Gpsiny.
	done.
move: b dGphiy => _ _ Gphingx''.
have fxey: (f x) equals y.
	apply/ (equal_trans);last first.
		by apply gx''ey.
	apply/ (equal_trans);last first.
		apply (gtotal x' x'').
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
	by exists (Fphi).
move => x''' phinx'''.
exists (f x''').
split.
	exists (f x''').
	split => //.
	apply (ftotal x''') => //.
	by exists phi.
move => s fx'''s.
rewrite -fx'''s.
exists (f x''').
apply (ftotal x''') => //.
by exists phi.
Qed.

Definition has_cont_rlzr (X Y : rep_space) (f : (space X) -> (space Y)) :=
	exists F, is_rlzr F f /\ @is_cont (questions X) (answers X) (questions Y) (answers Y) F.

Notation opU psi:=(eval (fun n phi q' => U n psi phi q')).

Definition is_ass (X Y: rep_space) psi (f: (space X) -> (space Y)) := (opU psi) is_realizer_of f.

Lemma is_ass_is_rep (X Y : rep_space):
  (@is_ass X Y) is_representation.
Proof.
move => psif psig f g psifaf psifag psigag.
exact: (@is_rlzr_is_rep X Y 
	(eval (fun n phi q' => U n psif phi q'))
	(eval (fun n phi q' => U n psig phi q'))
	f g psifaf psifag psigag
	).
Qed.

Canonical rep_space_cont_fun X Y := @make_rep_space
  (space X -> space Y)
  (seq (questions X * answers X) * questions Y)
  (questions X + answers Y)
  (inr (No_answer Y))
  (@is_ass X Y)
  (prod_count
  	(list_count (prod_count
  		(countable_questions X)
  		(countable_answers X)))
  	(countable_questions Y))
  (sum_count (countable_questions X) (countable_answers Y))
  (@is_ass_is_rep X Y).

Lemma cont_fun_equal X Y (f g: space X -> space Y):
	f equals g <-> has_cont_rlzr f /\ has_cont_rlzr g
		/\ forall x y, x equals y -> (f x) equals (g y).
Proof.
split.
	move=> [] psi []psinf psing.
	split.
		exists (opU psi).
		split => //.
		admit.
	split.
		exists (opU psi).
		split => //.
		admit.
	move => x y xey.
	apply/ equal_trans.
		by apply: (psinf.2 x y).
	admit.
move => [] [] F [] Frf Fcont [][] G [] Grg Gcont prop.

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
