(* This file provides an alternative formulation of represented spaces that saves
the input and output types of the names *)
From mathcomp Require Import all_ssreflect.
Require Import continuity universal_machine multi_valued_functions machines spaces.
Require Import FunctionalExtensionality Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section REPRESENTED_SPACES.

Definition is_rep S T (delta: S ->> T) := forall s s' t t',
	delta s t -> delta s t' -> delta s' t' -> delta s' t.
Notation "delta 'is_representation'" := (is_rep delta) (at level 2).

Definition delts S T (delta: S ->> T) x :=
	exists psi, delta psi x.

Definition deq S T (delta: S ->> T) x y:=
	exists psi, delta psi x /\ delta psi y.

Lemma deq_ref S T (delta: S ->> T) x:
	delts delta x <-> deq delta x x.
Proof.
split.
	rewrite /delts /deq => [][] psi dpsix.
	by exists psi.
rewrite /delts/deq => [] [] psi [] dpsix _.
by exists psi.
Qed.

Lemma deq_sym S T (delta: S ->> T):
	forall x y, (deq delta x y -> deq delta y x).
Proof.
move=>  x y [] phi [] phinx phiny.
by exists phi.
Qed.

Lemma deq_trans S T (delta: S ->> T) (is_rep: delta is_representation):
	forall x y z, deq delta x y -> deq delta y z -> deq delta x z.
Proof.
move => x y z [] phi [] phinx phiny [] psi [] psiny psinz.
exists psi.
split => //.
by apply: (is_rep phi psi x y).
Qed.

Definition Space_from_rep S T (delta: S ->> T) (is_rep: delta is_representation) :=
	@make_space T (deq delta) (@deq_sym S T delta) (@deq_trans S T delta is_rep).

Definition is_rep_of S (X: Space) (delta: S ->> (type X)) :=
	delta is_representation /\ forall x y, deq delta x y <-> (@equal X) x y.
Notation "delta 'is_representation_of' X" := (@is_rep_of _ X delta) (at level 2).

Lemma rep_of_space_from_rep S T (delta: S ->> T) (is_rep: delta is_representation) :
	delta is_representation_of (Space_from_rep is_rep).
Proof.
done.
Qed.

(* To construct a represented space it is necessary to provide a proof that the
representation is actually a representation. The names can be an arbitrary type
but will usually be something that can be computed on, i.e. Baire space or something.
At some point I will probably change the names to be a size_type. The type of names
must be inherited for the rather irrelevant full function-space construction to
work. This may change depending on whether other function space constructions also
need this or not. *)
Structure rep_space := make_rep_space {
  space :> Space;
  questions : Type;
  answers : Type;
  delta : (questions -> answers) ->> (@type space);
	No_answer: answers;
  countable_questions: questions is_countable;
  countable_answers: answers is_countable;
  representation_is_valid : delta is_representation_of space
}.
Notation names X := ((questions X) -> (answers X)).
Notation "'rep'" := @delta (at level 2).
Notation "phi 'is_name_of' x" := (delta phi x) (at level 2).
Notation "x 'equals' y" := (equal x y) (at level 2).
Notation "x 'is_element'" := (equal x x) (at level 2).
Notation "x 'is_from' X" := (@equal X x x) (at level 2).
Notation "x 'equals' y" := (equal x y) (at level 2).
Notation "'rep_valid' X" := (@representation_is_valid X) (at level 2).

Definition rep_space_from_rep X Q A
	(No_answer:A)
	(countable_questions:Q is_countable)
	(countable_answers:A is_countable)
	(delta: (Q -> A) ->> X)
	(is_rep: delta is_representation) :=
@make_rep_space
	(Space_from_rep is_rep)
	Q
	A
	delta
	No_answer
	countable_questions
	countable_answers
	(rep_of_space_from_rep is_rep).

Lemma sing_rep S T (delta: S ->> T):
	delta is_single_valued -> delta is_representation.
Proof.
move => sing s s' t t' dst dst' ds't'.
by rewrite (sing s t t').
Qed.

Lemma sing_sur_rep S T (delta: S ->> T):
	delta is_single_valued -> delta is_surjective -> delta is_representation_of (space_from_type T).
Proof.
move => sing sur.
split.
	apply/ (sing_rep sing).
move => x y.
split.
	move => [] psi [] dpsix dpsiy.
	by rewrite (sing psi x y).
move => /= eq.
rewrite eq /deq.
move: (sur y) => [] psi.
by exists psi.
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
	(@prod_rep X Y) is_representation_of (prod_space (space X) (space Y)).
Proof.
split.
	move => phipsi phi'psi' x x'.
	move => [] phinx1 psinx2 [] phinx'1 psinx'2 [] phi'nx'1 psi'nx'2.
	split.
		apply/ ((rep_valid X).1 _ _ x.1 x'.1).
					by apply phinx1.
				done.
			done.
	apply/ ((rep_valid Y).1 _ _ x.2 x'.2).
			by apply psinx2.
		done.
	done.
move => [] x x' [] y y'.
split.
	move => [] phipsi [] [] /= phinx psinx' [] /= phiny psiny'.
	split.
		apply/ (rep_valid X).2.
		by exists (fun q : questions X =>
         match phipsi (inl q) with
         | inl a => a
         | inr _ => No_answer X
         end).
	apply/ (rep_valid Y).2.
	by exists (fun q : questions Y =>
          match phipsi (inr q) with
          | inl _ => No_answer Y
          | inr b => b
          end).
move => [] /= xey x'ey'.
move: (((rep_valid X).2 x y).2 xey) => [] phi [] phinx phiny.
move: (((rep_valid Y).2 x' y').2 x'ey') => [] psi [] psinx' psiny'.
by exists (fun q => match q with
			| inl q' => inl (phi q')
			| inr q' => inr (psi q')
		end).
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
  (prod_space (space X) (space Y))
  (@questions X + @questions Y)
  (@answers X + @answers Y)
  (@prod_rep X Y)
  (inl (No_answer X))
  (sum_count (countable_questions X) (countable_questions Y))
  (sum_count (countable_answers X) (countable_answers Y))
  (@prod_rep_is_rep X Y).

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

Definition is_mf_rlzr (X Y: rep_space) (F: (names X) ->> (names Y)) (f: (type (space X)) ->> (type (space Y))) :=
	(rep Y) o F tightens ((@equal Y) o f o (rep X)).

Definition is_rlzr (X Y: rep_space) (F: (names X) ->> (names Y)) (f: (type (space X)) -> (type (space Y))) :=
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
	move: (((rep_valid Y).2 (f x) fx).2 f'xefx) => [] Fpsi []Fpsinf'x Fpsinfx.
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
			apply ((rep_valid X).2 x x).1.
			by exists phi.
		exists (g x).
		rewrite -H.
		apply: (gtotal x x) => //.
		apply ((rep_valid X).2 x x).1.
		by exists phi.
	move => s phins.
	exists (g s).
	split.
		exists (g s).
		split => //.
		apply/ (gtotal s s) => //.
		apply ((rep_valid X).2 s s).1.
		by exists phi.
	move => s0 gss0.
	rewrite -gss0.
	exists (g s).
	apply/ (gtotal s s) => //.
	apply ((rep_valid X).2 s s).1.
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
	move: (((rep_valid Y).2 (g x') gx').2 g'xegx) => [] Fpsi' [] Fpsi'ng'x Fpsi'ngx.
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
	apply ((rep_valid X).2 x'' x').1.
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
	move: (((rep_valid Y).2 (g x'') y).2 gx''ey) => [] Gpsi [] Gpsingx'' Gpsiny.
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
		apply ((rep_valid X).2 x' x'').1.
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
	apply ((rep_valid Y).2 (f x) (f x)).1.
	by exists (Fphi).
move => x''' phinx'''.
exists (f x''').
split.
	exists (f x''').
	split => //.
	apply (ftotal x''') => //.
	apply ((rep_valid X).2 x''' x''').1.
	by exists phi.
move => s fx'''s.
rewrite -fx'''s.
exists (f x''').
apply (ftotal x''') => //.
apply ((rep_valid X).2 x''' x''').1.
by exists phi.
Qed.

Definition has_cont_rlzr (X Y : rep_space) (f : (type (space X)) -> (type (space Y))) :=
	exists F, is_rlzr F f /\ @is_cont (questions X) (answers X) (questions Y) (answers Y) F.

Notation opU psi := (evaltt (fun n phi q' => U n psi phi q')).

Definition is_ass (X Y: rep_space) psi (f: (type (space X)) -> (type (space Y))) := (opU psi) is_realizer_of f.

Lemma is_ass_is_rep (X Y : rep_space):
  (@is_ass X Y) is_representation.
Proof.
move => psif psig f g psifaf psifag psigag.
exact: (@is_rlzr_is_rep X Y 
	(evaltt (fun n phi q' => U n psif phi q'))
	(evaltt (fun n phi q' => U n psig phi q'))
	f g psifaf psifag psigag
	).
Qed.

Canonical rep_space_cont_fun X Y := @make_rep_space
  (Space_from_rep (@is_ass_is_rep X Y))
  (seq (questions X * answers X) * questions Y)
  (questions X + answers Y)
  (@is_ass X Y)
  (inr (No_answer Y))
  (prod_count
  	(list_count (prod_count
  		(countable_questions X)
  		(countable_answers X)))
  	(countable_questions Y))
  (sum_count (countable_questions X) (countable_answers Y))
  (rep_of_space_from_rep (@is_ass_is_rep X Y)).

Definition has_comp_name (X: rep_space) (x: X):=
	{M | exists phi, M computes (F2MF phi) /\ phi is_name_of x}.
Definition has_prim_rec_name (X: rep_space) (x: X) :=
	{phi| phi is_name_of x}.

Lemma prim_rec_elt_comp_elt (X: rep_space) (x: X): has_prim_rec_name x -> has_comp_name x.
Proof.
move => [] phi phinx.
exists (fun n q => some (phi q)).
exists phi.
split => //.
move => q _.
split.
	exists (phi q).
	by exists 0.
move => a  [] n ev.
by apply Some_inj.
Qed.

Definition is_comp_fun (X Y: rep_space) (f: X -> Y) :=
	{M | exists F, M type_two_computes F /\ F is_realizer_of f}.

Definition is_prim_rec_fun (X Y: rep_space) (f: X -> Y) :=
	{F | F is_realizer_of f}.

Lemma prim_rect_fun_comp_fun (X Y: rep_space) (f:X -> Y) : is_prim_rec_fun f -> is_comp_fun f.
Proof.
move => [] F Frf.
exists (fun n phi q => some (F phi q)).
exists phi.
split => //.
move => q _.
split.
	exists (phi q).
	by exists 0.
move => a  [] n ev.
by apply Some_inj.
Qed.

End REPRESENTED_SPACES.
Notation "delta 'is_representation'" := (is_rep delta) (at level 2).
Notation "delta 'is_representation_of' X" := (@is_rep_of _ X delta) (at level 2).
Notation names X := ((questions X) -> (answers X)).
Notation "'rep'" := @delta (at level 2).
Notation "phi 'is_name_of' x" := (delta phi x) (at level 2).
Notation "x 'equals' y" := (equal x y) (at level 2).
Notation "x 'is_element'" := (equal x x) (at level 2).
Notation "x 'is_from' X" := (@equal X x x) (at level 2).
Notation "x 'equals' y" := (equal x y) (at level 2).
Notation "'rep_valid' X" := (@representation_is_valid X) (at level 2).
Notation "f 'is_realized_by' F" := (is_rlzr F f) (at level 2).
Notation "F 'is_realizer_of' f" := (is_rlzr F f) (at level 2).
Notation opU psi:=(eval (fun n phi q' => U n psi phi q')).
Notation "x 'is_computable_element'" := (has_comp_name x) (at level 2).
Notation "x 'is_primitive_recursive_element'" := (has_prim_rec_name x) (at level 2).
Notation "f 'is_computable_function'" := (is_comp_fun f) (at level 2).
(*

Lemma eval_comp X Y:
	is_cmptbl (fun (p: space (rep_space_prod (rep_space_cont_fun X Y) X)) => p.1 p.2).
Proof.
exists (e val (fun n psi q' => U n (psi.1) psi.2 q')).

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
*)