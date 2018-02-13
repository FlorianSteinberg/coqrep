(* This file is supposed to be come a module for multivalued functions *)

From mathcomp Require Import all_ssreflect.
Require Import spaces ClassicalChoice Setoid SetoidClass.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MULTIVALUED_FUNCTIONS.

Section MF_BASE.
Context (X Y: Space).

Definition mf_rel (f g: X -> Y -> Prop) :=
	forall x x' y y', x equals x' -> y equals y' -> f x y <-> g x' y'.

Lemma mf_rel_sym (f g: X -> Y -> Prop): mf_rel f g -> mf_rel g f.
Proof.
move => frg x x' y y' xex' yey'.
rewrite (frg x' x y' y) => //.
	by apply equal_sym.
by apply equal_sym.
Qed.

Lemma mf_rel_trans (f g h: X -> Y -> Prop): mf_rel f g -> mf_rel g h -> mf_rel f h.
Proof.
move => feg geh x x' y y' xex' yey'.
rewrite feg; last first.
		by apply yey'.
	by apply xex'.
rewrite geh;last first.
		by apply: equal_proj_snd yey'.
	by apply: equal_proj_snd xex'.
done.
Qed.

Lemma mf_rel_per:
	PER mf_rel.
Proof.
split.
	exact: mf_rel_sym.
exact: mf_rel_trans.
Qed.

Canonical mf_space :=
	@make_space (X -> Y -> Prop) (Build_PartialSetoid mf_rel_per).

Definition F2MF (f: X -> Y) := (fun x y => (f x) equals y).

Lemma F2MF_fun:
	F2MF is_from (fun_space (fun_space X Y) (mf_space)).
Proof.
move => f g feg x x' y y' xex' yey'.
split => ass.
	apply/equal_trans; last first.
		by apply yey'.
	apply/equal_trans; last first.
		by apply ass.
	apply/ equal_sym.
	by apply feg.
apply/equal_trans; last first.
	apply equal_sym.
	apply yey'.
apply/equal_trans;last first.
	by apply ass.
by apply feg.
Qed.

End MF_BASE.
Notation "X ->> Y" := (mf_space X Y) (at level 70).

Section DOM_RANGE_TOT_SING.
Context (X Y: Space).

Definition dom (f: X ->> Y) s := s is_element /\ (exists t, t is_element /\ f s t).
Notation "s 'from_dom' f" := (dom f s) (at level 70).

Lemma dom_mf:
	dom is_from (mf_space (mf_space X Y) X).
Proof.
move => f g x y feg xey.
split.
	move => [] xie [] fx [] fxie fxfx.
	split.
		by apply: equal_proj_snd xey.
	exists fx.
	split => //.
	apply/ feg.
			by apply xey.
		by apply fxie.
	done.
move => [] xie [] fx [] fxie fxfx.
split.
	by apply: equal_proj_fst xey.
exists fx.
split => //.
apply/ feg.
		by apply xey.
	by apply fxie.
done.
Qed.

Definition range (f: X ->> Y) t := t is_element /\ (exists s, s is_element /\ f s t).
Notation "t 'from_range' f" := (range f t) (at level 70).
(* the range of a multivalued function is the union of all its value sets. *)

Lemma range_fun:
	range is_from (mf_space (mf_space X Y) Y).
Proof.
move => f g x y feg xey.
split.
	move => [] xie [] fx [] fxie fxfx.
	split.
		by apply: equal_proj_snd xey.
	exists fx.
	split => //.
	apply/ feg.
			by apply fxie.
		by apply xey.
	done.
move => [] xie [] fx [] fxie fxfx.
split.
	by apply: equal_proj_fst xey.
exists fx.
split => //.
apply/ feg.
		by apply fxie.
	by apply xey.
done.
Qed.

Definition is_tot (f: X ->> Y) :=
	forall x, x is_element -> exists y, y is_element /\ f x y.
Notation "f 'is_total'" := (is_tot f) (at level 2).

Definition is_cotot (f: X ->> Y) :=
	forall y, y is_element -> exists x, x is_element /\ f x y.
Notation "f 'is_cototal'" := (is_cotot f) (at level 50).

Lemma tot_dom (f: X ->> Y):
	f is_total <-> (forall x, x from_dom f <-> x is_element).
Proof.
split.
	move => tot x.
	split.
		by move => [] xie _.
	move => xie.
	split => //.
	by apply tot.
move => prop x xie.
move: ((prop x).2 xie) => [] _ [] y cond.
by exists y.
Qed.

Definition is_sing (f: X ->> Y):=
	forall x y fx fy, x equals y -> f x fx -> f y fy -> fx equals fy.
Notation "f 'is_single_valued'" := (is_sing f) (at level 2).

Lemma morph_sing_tot (f: X -> Y) :
	is_morph f <-> is_tot (F2MF f) /\ is_sing (F2MF f).
Proof.
split.
	move => morph.
	split.
		move => x xie.
		exists (f x).
		split; by apply/morph.
	move => x y fx fy xey fxfx fyfy.
	apply/equal_trans.
		apply/equal_sym.
		by apply fxfx.
	apply /equal_trans; last first.
		by apply fyfy.
	by apply morph.
move => [] tot sing x y xey.
apply/sing.
		by apply xey.
	move: (tot x (equal_proj_fst xey)) => [] fx [] fxie fxefx.
	apply/equal_trans.
		by apply fxefx.
	by apply equal_sym.
move: (tot y (equal_proj_snd xey)) => [] fy [] fyie fyefy.
apply/equal_trans.
	by apply fyefy.
by apply equal_sym.
Qed.

End DOM_RANGE_TOT_SING.
Notation "s 'from_dom' f" := (dom f s) (at level 70).
Notation "t 'from_range' f" := (range f t) (at level 70).
Notation "f 'is_total'" := (is_tot f) (at level 2).
Notation "f 'is_single_valued'" := (is_sing f) (at level 2).

Section MF_CONSTRUCTIONS.

Context (X Y X' Y': Space).

Definition mf_sum (f : X ->> Y) (g : X' ->> Y') :=
  fun c x => match c with
    | inl a => match x with
      | inl y => f a y
      | inr z => False
    end
    | inr b => match x with
      | inl y => False
      | inr z => g b z
    end
  end.
(* the sum of multivalued functions is not used anywhere so far. Probably because
it the use of sums is rather unusual for represented spaces. While infinite co-
products show up for some weird spaces like polynomials or analytic functions, I
have not seen finite coproducts very often. *)

Definition mf_prod (f : X ->> Y) (g : X' ->> Y')
	:= fun c x => f c.1 x.1 /\ g c.2 x.2.
(* in contrast to coproducts, products are very common and I have already included
several lemmas about them because I needed them. *)

Notation "f \, g" := (mf_prod f g) (at level 50).
(*This is the notation for the tupling of multifunctions*)

Lemma mf_prod_fun_mf:
	(fun fg => (fg.1 \, fg.2)) is_from
	(fun_space (prod_space (X ->> Y) (X' ->> Y')) ((prod_space X X') ->> (prod_space Y Y'))).
Proof.
move => [] f g [] f' g' []/= frf' grg' x x' y y' [] xex'1 xex'2 [] yey'1 yey'2.
split.
	move => [] fxy gxy.
	split.
		apply/ frf'.
				apply xex'1.
			by apply yey'1.
		done.
	apply/ grg'.
			apply xex'2.
		by apply yey'2.
	done.
move => [] f'xy g'xy.
split.
	apply/ frf'.
		apply xex'1.
		by apply yey'1.
	done.
apply/ grg'.
		apply xex'2.
	by apply yey'2.
done.
Qed.

Lemma prod_range (f: X ->> Y) (g : X' ->> Y') :
  forall (s: Y) (t: Y'), s from_range f /\ t from_range g -> (s,t) from_range (f \, g).
Proof.
move => y y'.
move => [][]yie [] x [] xie fxy [] y'ie [] x' [] x'ie gx'y'.
split; first by split.
by exists (x,x'); split; split.
Qed.

Lemma prod_total (f: X ->> Y) (g: X' ->> Y'):
  f is_total /\ g is_total ->(f \, g) is_total.
Proof.
move => [] ftot gtot [] x x' []/= xie x'ie.
move: (ftot x xie) (gtot x' x'ie) => [] y [] yie fxy [] y' [] y'ie gx'y'.
by exists (y,y'); split; split.
Qed.

Lemma prod_sing (f: X ->> Y) (g: X' ->> Y'):
  f is_single_valued /\ g is_single_valued -> (f \, g) is_single_valued.
Proof.
move => []fsing gsing x y fx fy xey [] fxfx gxgx [] fyfy gygy.
split.
	apply/ (fsing x.1 y.1) => //.
	by apply xey.1.
apply (gsing x.2 y.2) => //.
by apply (xey.2).
Qed.

Lemma mf_prod_fun_fun:
	(fun fg => (F2MF fg.1 \, F2MF fg.2)) is_from
	(fun_space (prod_space (fun_space X Y) (fun_space X' Y')) ((prod_space X X') ->> (prod_space Y Y'))).
Proof.
move => [] f g [] f' g' []/= frf' grg'  x x' y y' [] xie1 xie2 [] yie1 yie2.
split.
	move => [] fxy gxy.
	split.
		apply/equal_trans.
			apply/equal_sym.
			by apply: (frf' x.1 x'.1 xie1).
		apply/equal_trans.
			by apply fxy.
		done.
	apply/equal_trans.
		apply equal_sym.
		by apply (grg' x.2 x'.2 xie2).
	apply/equal_trans.
		apply gxy.
	done.
move => [] f'xy g'xy.
split.
	apply/equal_trans.
		by apply: (frf' x.1 x'.1 xie1).
	apply/equal_trans.
		apply f'xy.
	by apply equal_sym.
apply/equal_trans.
	by apply (grg' x.2 x'.2 xie2).
apply/equal_trans.
	by apply g'xy.
by apply equal_sym.
Qed.

Definition tight (f: X ->> Y) (g: X ->> Y) :=
	forall s, s from_dom f -> s from_dom g /\ forall t, t is_element -> g s t -> f s t.
Notation "f 'is_tightened_by' g" := (tight f g) (at level 2).
Notation "g 'tightens' f" := (tight f g) (at level 2).

Lemma tight_mf:
	tight is_from ((X ->> Y) ->> (X ->> Y)).
Proof.
move => f f' g g' fef' geg'.
split => ass.
	move => x xfdf'.
	have xfdf: x from_dom f.
		apply/ (dom_mf).
				apply fef'.
			apply xfdf'.1.
		apply xfdf'.
	move: (ass x xfdf) => [] xfdg prop.
	split.
		apply/ dom_mf.
					apply equal_sym.
					by apply geg'.
				apply xfdf.1.
			done.
		move => gx gxie g'xgx.
		apply/ fef'.
				apply xfdf.1.
			apply gxie.
		apply prop => //.
	rewrite geg'.
			apply g'xgx.
		apply xfdf.1.
	done.
move => x xfdf'.
have xfdf: x from_dom f'.
	apply/ (dom_mf).
			apply equal_sym.
			apply fef'.
		apply xfdf'.1.
	apply xfdf'.
move: (ass x xfdf) => [] xfdg prop.
split.
	apply/ dom_mf.
				by apply geg'.
			apply xfdf.1.
		done.
	move => gx gxie g'xgx.
	apply/ fef'.
			apply xfdf.1.
		apply gxie.
	apply prop => //.
rewrite -geg'.
		apply g'xgx.
	apply xfdf.1.
done.
Qed.

Lemma tight_ref (f: X ->> Y):
	f tightens f.
Proof.
done.
Qed.

Lemma tight_trans (f g h: X ->> Y):
	f tightens g -> g tightens h -> f tightens h.
Proof.
move => ftg gth s eh.
split.
	apply: (ftg s (gth s eh).1).1.
move => t tie fst.
apply: ((gth s eh).2 t) => //.
by apply: ((ftg s (gth s eh).1).2 t).
Qed.

Lemma tight_ref_plus (f g: X ->> Y):
	f equals f -> g equals g -> g tightens f /\ f tightens g -> f equals g.
Proof.
move => fef geg [] gtf ftg x x' y y' xex' yey'.
split => ass.
	have x'fdf: x' from_dom f.
		split.
			by apply: equal_proj_snd xex'.
		exists y'.
		split.
			by apply: equal_proj_snd yey'.
		apply/ fef.
				apply equal_sym.
				apply xex'.
			apply equal_sym.
			apply yey'.
		done.
	move: (gtf x' x'fdf) => [] x'fdg _.
	apply: (ftg x' x'fdg).2.
		by apply: equal_proj_snd yey'.
	apply/ fef.
			apply equal_sym.
			apply xex'.
		apply equal_sym.
		apply yey'.
	done.
have x'fdf: x from_dom g.
	split.
		by apply: equal_proj_fst xex'.
	exists y.
	split.
		by apply: equal_proj_fst yey'.
	apply/ geg.
			apply xex'.
		apply yey'.
	done.
move: (ftg x x'fdf) => [] x'fdg _.
apply: (gtf x x'fdg).2.
		by apply: equal_proj_fst yey'.
	apply/ geg.
		apply xex'.
	apply yey'.
done.
Qed.

(* To extend to tightenings for multivalued functions makes sense: for instance a Choice
function of a multi valued funtion is a thightening of that funciton. *)
Definition icf (f: X ->> Y) g := forall x, x from_dom f -> (g x) is_element /\ f x (g x).
Notation "g 'is_choice_for' f" := (icf f g) (at level 2).

Lemma icf_mf:
	icf is_from ((X ->> Y) ->> (fun_space X Y)).
Proof.
move => f f' g g' fef' geg'.
split => ass x [] xie [] y [] yie f'xy.
	split.
		apply/ equal_trans.
			apply/ equal_sym.
			by apply (geg' x x).
		by apply/ geg'.
	apply/fef'.
			apply xie.
		apply geg'.
		by apply xie.
	apply ass.
	split => //.
	move: ((fef' x x y y xie yie).2 f'xy) => fxy.
	by exists y.
split.
	apply/ equal_trans.
		by apply (geg' x x).
	apply equal_sym.
	by apply/ geg'.
apply/fef'.
		apply xie.
	apply geg'.
	by apply xie.
apply ass.
split => //.
move: ((fef' x x y y xie yie).1 f'xy) => fxy.
by exists y.
Qed.

Lemma exists_choice:
	(exists y, y is_from Y) -> icf is_total.
Proof.
move => [] y yie f fie.
set R := fun x y => x.1 equals x.2 -> y.1 = y.2
	/\
	(x.1 from_dom f -> x.2 from_dom f -> f x.1 y.1 /\ f x.2 y.2).
have cond: forall x, exists fx, R x fx.
	move => [] x x'.
	case: (classic (x from_dom f)).
		move => [] xie [] fx [] fxie fxfx.
		exists (fx,fx) => xex'.
		rewrite /= in xex'.
		split => //.
		move => [] x'ie [] fx' [] fx'ie fx'fx'.
		split => //=.
		by rewrite -(fie x x' fx fx).
	move => false.
	exists (y,y) => xex'.
	by split.
move: (choice R cond) => [] F prop.
rewrite /R in prop;move: R cond => _ _.
exists (fun x => (F (x,x)).1).
split.
	move => x x' xex'.
	apply/ equal_trans.
	move: (prop (x,x') xex').1.
	move: (equal_proj_snd xex').
Admitted.

Definition mf_comp R S T (f : S ->> T) (g : R ->> S) :=
  fun r t => (exists s, s is_element /\ g r s /\ f s t)
  	/\ (forall s,  s is_element -> g r s -> s from_dom f).
Notation "f 'o' g" := (mf_comp f g) (at level 2).

Lemma mf_comp_fun R S T:
	(@mf_comp R S T) is_from (fun_space (S ->> T) (fun_space (R ->> S) (R ->> T))).
Proof.
move => f f' fef' g g' geg' r r' t t' rer' tet'.
split.
	move => [] [] s [] sie [] grs fst prop.
	split.
		exists s.
		split => //.
		split.
			apply/geg'.
					apply rer'.
				apply sie.
			done.
		apply/ fef'.
				apply sie.
			apply tet'.
		done.
	move => s' s'ie g'r's'.
	split => //.
	have grs': g r s'.
		apply/ geg'.
				apply rer'.
			apply s'ie.
		done.
	move: (prop s' s'ie grs') => [] _ [] t'' [] t''ie fs't''.
	exists t''.
	split => //.
	apply/fef'.
			apply s'ie.
		apply t''ie.
	done.
move => [] [] s [] sie [] grs fst prop.
split.
	exists s.
	split => //.
	split.
		apply/geg'.
				apply rer'.
			apply sie.
		done.
	apply/ fef'.
			apply sie.
		apply tet'.
	done.
move => s' s'ie g'r's'.
split => //.
have grs': g' r' s'.
	apply/ geg'.
			apply rer'.
		apply s'ie.
	done.
move: (prop s' s'ie grs') => [] _ [] t'' [] t''ie fs't''.
exists t''.
split => //.
apply/fef'.
		apply s'ie.
	apply t''ie.
done.
Qed.

Lemma mf_comp_assoc (f: X' ->> Y') g (h: X ->> Y):
	f is_element -> h is_element ->
		(@equal (X ->> Y')) ((f o g) o h) (f o (g o h)).
Proof.
move => fie hie x x' y  y' xex' yey'.
split.
move => [] [] s [] sie [] hxs [] [] t [] tie [] gst fty prop cond.
	split.
		exists t.
		split => //.
		split.
			split.
				exists s.
				split => //.
				split => //.
				apply/ hie.
						apply equal_sym.
						apply xex'.
					apply sie.
				done.
			move => z zie hx'z.
			have hxz: h x z.
				apply/ hie.
						apply xex'.
					apply zie.
				done.
			move: (cond z zie hxz) => [] _ [] _ [] _ [] [] l 
			[] lie [] gzl _ _.
			split => //.
			by exists l.
		apply/ fie.
				apply tie.
			apply equal_sym.
			apply yey'.
		done.
	move => u uie ghx'u.
	move: (ghx'u) => [] [] t0 [] t0ie [] hx't0 gt0u prop'.
	have hxt0: h x t0.
		apply/hie.
				apply xex'.
			apply t0ie.
		done.
	move: (cond t0 t0ie hxt0) => [] _ [] y0 [] y0ie [] _ cond'.
	by apply cond'.
move => [] [] t [] tie [] [] [] s [] sie [] hx's gst prop fty' cond.
split.
	exists s.
	split => //.
	split.
		apply/hie.
				apply xex'.
			apply sie.
		done.
	split.
		exists t.
		split => //.
		split => //.
		apply/fie.
				apply tie.
			apply yey'.
		done.
	move =>t' gst' t'ie.
	have ghx't': g o h x' t'.
		split.
			exists s.
			by split.
		by apply prop.
	by apply: cond.
move => s' s'ie hxs'.
split => //.
exists y'.
split.
	by apply (equal_proj_snd yey').
split.
	have hx's': h x' s'.
		apply/ hie.
				apply equal_sym.
				apply xex'.
			apply s'ie.
		done.
	move: (prop s' s'ie hx's') => [] _ [] t' [] t'ie gs't'.
	exists t'.
	split => //.
	split => //.
	apply/ fie.
			apply t'ie.
		apply equal_sym.
		apply yey'.
	
	
		

	
		
Qed.


Lemma mf_comp_is_fun:
	(fun fg => fg.1 o (fg.2)) is_from
	(fun_space (prod_space (Y ->> Y') (X ->> Y)) (X ->> Y')).
Proof.
move => []f g [] f' g' [] /= frf' grg' x y' elt.
split.
	move => [] [] y [] gxy fyy' _.
	split.
		exists y.
			rewrite -frf'.
			rewrite -grg' => //.
			by right.
		by left.
	
			move: (prop t gxt) => [] q ftq.
			

Lemma mf_comp_well_def (f: Y ->> Y') (g: X ->> Y):
	f is_well_defined -> g is_well_defined -> f o g is_well_defined.
Proof.
move => fwd gwd x fgx comp.
move: comp ((mf_comp_assoc (@equal Y') f g x fgx).2 comp) => _ [] [] y [] gxy comp1 comp2.
split.
	exists y.
	split => //.
	by apply/ well_defined.
move => y' gxy'.
move: (comp2 y' gxy') => [] x'.
exists (x').
by apply/well_defined.
Qed.

Lemma single_valued_composition (f: Y ->> Y') (g : X ->> Y) :
	f is_single_valued -> g is_single_valued -> f o g is_single_valued.
Proof.
move => fsing gsing x x' fgx fgx' xex' [] [] y [] gxy fyfgx _ [][] y' [] gx'y' fy'fgx' _.
have yey': y equals y' by apply (gsing x x' y y').
by apply: (fsing y y' fgx fgx').
Qed.


Lemma comp_id_l (f: S ->> T) x fx:
	(F2MF id) o f x fx <-> f x fx.
Proof.
split.
	move => [][] t[] fxt eq.
	by rewrite -eq.
move => fxfx.
split.
	by exists fx.
move => s fxs.
by exists s.
Qed.

Lemma comp_id_r (f: S ->> T) x fx:
	f o (F2MF id) x fx <-> f x fx.
Proof.
split.
	move => [][] t[] eq ftfx prop.
	by rewrite eq.
move => fxfx.
split.
	by exists x.
move => s fxs.
exists fx.
by rewrite fxs in fxfx.
Qed.

Lemma prod_comp R R'
(f: S ->> T) (g: S' ->> T') (f': R ->> S) (g': R' ->> S'):
	forall x fx, (f \, g) o (f' \, g') x fx <-> (f o f' \, g o g') x fx.
Proof.
move => x ffggx.
split.
	move => [] [] fgx [] [] fxfgx gxfgx [] ffgxffggx gfgxffggx prop.
	split.
		split.
			by exists fgx.1.
		move => s f'xs.
		have temp: ((s, fgx.2) from_dom (f \, g)) by apply: ((prop (s, fgx.2))).
		move: temp => [] [] x1 x2 [] /= fsx1.
		by exists x1.
	split.
		by exists fgx.2.
	move => s f'xs.
	have temp: ((fgx.1,s) from_dom (f \, g)) by apply: ((prop (fgx.1, s))).
	move: temp => [] [] x1 x2 [] /= fsx1.
	by exists x2.
move => [] [] [] s1 [] fxs1 fs1ffggx prop [] [] s2 [] fxs2 fs2ffggx prop'.
split.
	by exists (s1,s2).
move => [] s'1 s'2 [] fs' gs'.
move: (prop s'1 fs') (prop' s'2 gs') => [] t fst [] t' fst'.
by exists (t,t').
Qed.

Lemma sing_comp (f: T ->> T') (g : S ->> T) :
	f is_single_valued -> g is_single_valued -> f o g is_single_valued.
Proof.
move => fsing gsing.
move => r t t' [][] s [] grs fst prop [][] s' [] grs' fs't' prop'.
move: (gsing r s s' grs grs') (fsing s t t') => eq eq'.
by rewrite eq' => //; rewrite eq.
Qed.

Notation "f 'restricted_to' P" := (fun s t => P s /\ f s t) (at level 2).

Definition is_sur S T (f: S ->> T) :=
  forall t, range f t.
Notation "f 'is_surjective'" := (is_sur f) (at level 2).
(* this notion of surjectivity is only usefull in combination with single-valuedness *)

Definition is_really_sur_wrt S T (f: S ->> T) (P: T -> Prop):=
	exists F, F is_choice_for f /\ forall t, (P t -> exists s, s from_dom f /\ F s = t).
(* Due to choice functions being involved, this notion is not nice to work with.
Since we are mostly interested in the case where the function is single valued,
we use the following notion instead, that can be proven equivalent in this case: *)

Definition is_sur_wrt S T (f: S ->> T) (P: T -> Prop) :=
  forall t,  P t -> (exists s, f s t /\ forall s t', f s t -> f s t' -> P t').
Notation "f 'is_surjective_wrt' A" := (is_sur_wrt f A) (at level 2).
(* This says: a multivalued function is said to be surjective on a set X if whenever
one of its value sets f(s) has a nonempty intersection with X, then it is already
included in X. This notion has to be more elaborate to work well with composition
as defined below. It does kind of make sense if the value set is interpreted as the
set of "acceptable return values": It should either be the case that all acceptable
values are from X or that none is. *)

Lemma sur_and_really_sur (f: S ->> T) P:
	(exists (t: T), True) -> f is_single_valued ->
		(is_really_sur_wrt f P <-> f is_surjective_wrt P).
Proof.
move => e sing.
split.
	move => []F [] icf prop t Pt.
	move: prop (prop t Pt) => _ [] s [] sfd Fst.
	exists (s); split.
		by rewrite -Fst; move: (icf s sfd).
	move => s0 t' fs0t fs0t'.
	by rewrite (sing s0 t t' fs0t fs0t') in Pt.
move: (exists_choice f e) => [] F prop sur.
exists F; split => //.
move => t Pt.
move: (sur t Pt) => [] s [] fst cond.
exists s; split.
	by exists t.
have ex: (exists t, f s t) by exists t.
move: (prop s ex) => fsFs.
by rewrite (sing s t (F s)).
Qed.

Lemma surjective_composition_wrt (f: T ->> T') (g : S ->> T):
	f is_surjective -> g is_surjective_wrt (dom f) -> f o g is_surjective.
Proof.
move => fsur gsur t.
move: (fsur t) => [s] fst.
have sdomf: s from_dom f by exists t.
move: (gsur s sdomf) => [] r [] grs cond.
exists r; split.
	by exists s.
by move => s'; apply: (cond r s').
Qed.

(* Due to the definition of the composition there is no Lemma for surjectivity that
does not have additional assumptions. It is probably possible to prove:
Lemma surjective_composition R S T (f: S ->> T) (g: R ->> S):
	f is_surjective -> f is_total -> g is_surjective -> f o g is_surjective.
I did not try, though. *)
End MULTIVALUED_FUNCTIONS.
Notation F2MF f := (fun s t => f s = t).
Notation "S ->> T" := (S -> T -> Prop) (format "S ->> T", at level 2).
Notation "f \, g" := (mf_prod f g) (at level 50).
Notation "f 'is_single_valued'" := (is_sing f) (at level 2).
Notation "f 'restricted_to' P" := (fun s t => P s /\ f s t) (at level 2).
Notation "t 'from_range' f" := (range f t) (at level 2).
Notation "f 'is_surjective'" := (is_sur f) (at level 2).
Notation "s 'from_dom' f" := (dom f s) (at level 2).
Notation "f 'is_tightened_by' g" := (tight f g) (at level 2).
Notation "g 'tightens' f" := (tight f g) (at level 2).
Notation "g 'extends' f" := (forall s t, f s t -> g s t) (at level 2).
Notation "g 'is_choice_for' f" := ((F2MF g) tightens f) (at level 2).
Notation "f 'is_total'" := (is_tot f) (at level 2).
Notation "f 'o' g" := (mf_comp f g) (at level 2).
Notation "f 'restricted_to' P" := (fun s t => P s /\ f s t) (at level 2).
Notation "f 'is_surjective_wrt' A" := (is_sur_wrt f A) (at level 2).

