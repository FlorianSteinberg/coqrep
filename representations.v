(* This file provides an alternative formulation of represented spaces that saves
the input and output types of the names *)
From mathcomp Require Import all_ssreflect.
Require Import continuity universal_machine multi_valued_functions machines oracle_machines.
Require Import FunctionalExtensionality ClassicalFacts ClassicalChoice Psatz ProofIrrelevance.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section REPRESENTED_SPACES.

Definition is_rep S T (delta: S ->> T):=
	delta \is_surjective_partial_function.
Notation "delta '\is_representation'" := (is_rep delta) (at level 2).

(* To construct a represented space it is necessary to provide a proof that the
representation is actually a representation. The names have to be of the formulation
Q -> A where Q and A are countable and A is inhabited. This must also be proven. *)
Structure rep_space := make_rep_space {
  space :> Type;
  questions: Type;
  answers: Type;
  delta: (questions -> answers) ->> space;
	some_answer: answers;
  countable_questions: questions \is_countable;
  countable_answers: answers \is_countable;
  representation_is_valid : delta \is_representation
}.
Notation names X := ((questions X) -> (answers X)).
Notation rep := @delta.
Notation "phi '\is_name_of' x" := (delta phi x) (at level 2).
Notation rep_valid X := (@representation_is_valid X).
Notation rep_sur X := (rep_valid X).2.
Notation rep_sing X := (rep_valid X).1.

(* This is the product of represented spaces. *)

Definition lprj X Y (phipsi: questions X + questions Y -> answers X * answers Y) q := (phipsi (inl q)).1.
Definition rprj X Y (phipsi: questions X + questions Y -> answers X * answers Y) q := (phipsi (inr q)).2.

Definition name_pair (X Y: rep_space) (phi: names X) (psi: names Y) :=
	fun c => match c with
		| inl s => (phi s, some_answer Y)
		| inr t => (some_answer X, psi t)
	end.

Lemma lprj_pair (X Y: rep_space) (phi: names X) (psi: names Y):
	lprj (name_pair phi psi) =  phi.
Proof. by trivial. Qed.

Lemma rprj_pair (X Y: rep_space) (phi: names X) (psi: names Y):
	rprj (name_pair phi psi) =  psi.
Proof. by trivial. Qed.

Definition prod_rep X Y :=
	(fun (phipsi : (questions X + questions Y -> answers X * answers Y)) xy =>
      (rep X ** rep Y) (lprj phipsi, rprj phipsi) xy).

Lemma prod_rep_is_rep (X Y: rep_space):
	(@prod_rep X Y) \is_representation.
Proof.
split => [phipsi x x' [] phinx1 psinx2 [] phinx'1 psinx'2 | x].
	apply: injective_projections.
		by apply/ (rep_sing X); first apply phinx1.
	by apply/ (rep_sing Y); first apply psinx2.
have [phi phinx1]:= (rep_sur X x.1).
have [psi psinx2]:= (rep_sur Y x.2).
by exists (name_pair phi psi).
Qed.

Lemma sum_count Q Q':
  Q \is_countable -> Q' \is_countable -> (Q + Q') \is_countable.
Proof.
move => [cnt1] sur1 [cnt2] sur2.
set cnt' := fix cnt' n acc := match n with
	| 0 => inl (cnt1 acc) 
	| 1 => inr (cnt2 acc)
	| S (S n') => (cnt' n' (S acc))
end.

have prop: forall n k, cnt' (2 * n) k = inl(cnt1 (n + k)).
	elim => // n ih k.
	replace (2*n.+1) with ((2*n).+2) by by rewrite /muln/muln_rec; lia.
	rewrite /= (ih (k.+1)).
	by replace (n + k.+1) with (n.+1 + k) by by rewrite /addn/addn_rec; lia.
have prop2: forall n k, cnt' (2 * n + 1) k = inr(cnt2 (n + k)).
	elim => // n ih k.
	replace (2*n.+1) with ((2*n).+2) by by rewrite /muln/muln_rec; lia.
	rewrite /= (ih (k.+1)).
	by replace (n + k.+1) with (n.+1 + k) by by rewrite /addn/addn_rec; lia.

exists (fun n => cnt' n 0).
rewrite /initial_segments.is_sur.
apply sum_rect => s.
	move: (sur1 s) => [n] idx.
	exists (2*n).
	move: n s idx.
	elim => [s idx | n ih s idx]; first by rewrite -idx.
	replace (2 * n.+1) with ((2 * n).+2) by by rewrite /muln/muln_rec; lia.
	rewrite -idx /= prop.
	by replace (S n) with (n + 1) by by rewrite /addn/addn_rec; lia.
move: (sur2 s) => [n] idx.
exists (2*n + 1).
move: n s idx.
elim => [s idx | n ih s idx]; first by rewrite -idx.
replace (2 * n.+1) with ((2 * n).+2) by by rewrite /muln/muln_rec; lia.
rewrite -idx /= prop2.
by replace (S n) with (n + 1) by by rewrite /addn/addn_rec; lia.
Qed.

Lemma prod_count Q Q':
  Q \is_countable -> Q' \is_countable -> (Q * Q') \is_countable.
Proof.
Admitted.

Canonical rep_space_prod X Y := @make_rep_space
  ((space X) * (space Y))
  (@questions X + @questions Y)
  (@answers X * @answers Y)
  (@prod_rep X Y)
  ((some_answer X, some_answer Y))
  (sum_count (countable_questions X) (countable_questions Y))
  (prod_count (countable_answers X) (countable_answers Y))
  (@prod_rep_is_rep X Y).

Lemma list_count Q:
	Q \is_countable -> (list Q) \is_countable.
Proof.
Admitted.

Definition is_rlzr (X Y: rep_space) (F: (names X) ->> (names Y)) (f: X ->> Y) :=
	(rep Y) o F \tightens (f o (rep X)).
Notation "f '\is_realized_by' F" := (is_rlzr F f) (at level 2).
Notation "F '\is_realizer_of' f" := (is_rlzr F f) (at level 2).
Global Instance rlzr_prpr (X Y: rep_space):
	Proper (@equiv (names X) (names Y) ==> @equiv (space X) (space Y) ==> iff) (@is_rlzr X Y).
Proof. by move => F G FeG f g feg; rewrite /is_rlzr FeG feg. Qed.

Definition is_fun_rlzr (X Y: rep_space) (F: (names X) -> (names Y)) (f: X -> Y) :=
	forall phi x, (rep X) phi x -> ((rep Y) (F phi) (f x)).

Lemma frlzr_rlzr (X Y: rep_space) F (f: X -> Y):
	is_fun_rlzr F f <-> is_rlzr (F2MF F) (F2MF f).
Proof.
split => [rlzr phi [fx [[x [phinx eq]] prop]] | mfrlzr phi x phinx].
	split => [ | y [[Fphi [FphiFphi Fphiny]] prop']].
		exists (f x);	split => [ | Fphi FphiFphi].
			by exists (F phi); split => //; apply rlzr.
		by exists (f x); rewrite -FphiFphi; exact: rlzr.
	apply tot_comp; first exact: F2MF_tot; exists x.
	split => //; rewrite -FphiFphi in Fphiny.
	by apply: (representation_is_valid Y).1; [apply rlzr | apply/ Fphiny ].
have exte: ((delta (r:=Y)) o (F2MF F)) \extends ((F2MF f) o (delta (r:=X))).
	apply/ exte_tight => //; apply: comp_sing; try exact: F2MF_sing.
		exact: (representation_is_valid X).1.
	exact: (representation_is_valid Y).1.
have Fphinfx: ((F2MF f) o (delta (r:=X))) phi (f x) by apply tot_comp; [exact: F2MF_tot | exists x].
have [Fphi [eq Fphifx]]:= (exte phi (f x) Fphinfx).1.
by rewrite eq.
Qed.

Lemma mfrlzr_rlzr (X Y: rep_space) F (f: X ->> Y) (somey: Y): f \is_single_valued -> f \is_total
	-> (exists g, g \is_choice_for f /\ is_fun_rlzr F g) <-> is_rlzr (F2MF F) f.
Proof.
move => sing tot.
split => [ [g [icf rlzr]] | mfrlzr].
	move: ((@sing_tot_F2MF_icf X Y f g sing tot).1 icf) => eq.
	suffices: is_rlzr (F2MF F) (F2MF g) by rewrite /is_rlzr -eq.
	exact/ frlzr_rlzr.
have ass: f \is_single_valued /\ f \is_total by split.
have [g eq]:= ((F2MF_sing_tot f (somey)).1 ass).
exists g; split; first by apply sing_tot_F2MF_icf.
apply/ frlzr_rlzr.
by rewrite /is_rlzr eq.
Qed.

Lemma icf_rlzr (X Y: rep_space) F (f: X ->> Y):
	F \is_realizer_of f -> forall G, G \is_choice_for F -> (F2MF G) \is_realizer_of f.
Proof.
move => rlzr G icf.
apply/ tight_trans; last by apply rlzr.
apply/ tight_comp_r.
exact/ icf_F2MF_tight.
Qed.

Lemma tight_rlzr (X Y: rep_space) G F (f: X ->> Y):
	G \tightens F -> F \is_realizer_of f -> G \is_realizer_of f.
Proof.
move => GtF Frf.
rewrite /is_rlzr.
apply/ tight_trans.
apply/ tight_comp_r; first by apply GtF.
apply Frf.
Qed.

Lemma rlzr_comp (X Y Z: rep_space) G F (f: X ->> Y) (g: Y ->> Z):
	G \is_realizer_of g -> F \is_realizer_of f -> (G o F) \is_realizer_of (g o f).
Proof.
move => Grg Frf.
rewrite /is_rlzr.
rewrite -comp_assoc.
apply/ tight_trans.
	by apply /tight_comp_l; apply Grg.
apply/ tight_trans.
	rewrite comp_assoc.
	by apply /tight_comp_r; apply Frf.
by rewrite comp_assoc.
Qed.

Lemma rlzr_dom (X Y: rep_space) (f: X ->> Y) F:
	F \is_realizer_of f -> forall phi x, phi \is_name_of x -> x \from_dom f -> exists Fphi, F phi Fphi.
Proof.
move => rlzr phi x phinx [y fxy].
have phifd: phi \from_dom (f o (delta (r:=X))).
	exists y.
	split; first by exists x.
	move => x' phinx'.
	by rewrite (rep_sing X phi x' x); first by exists y.
have [y' [[Fphi [FphiFphi Fphiny']]] _]:= (rlzr phi phifd).1.
by exists Fphi.
Qed.

Definition prod_rlzr (X Y X' Y': rep_space) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):=
	(fun (phipsi: names (rep_space_prod X X')) FphiGpsi =>
	(F ** G) (lprj phipsi, rprj phipsi)	(lprj FphiGpsi, rprj FphiGpsi)).

Lemma rlzr_prod (X Y X' Y': rep_space) (f: X ->> Y) (g: X' ->> Y') F G:
	F \is_realizer_of f -> G \is_realizer_of g -> (prod_rlzr F G) \is_realizer_of (f ** g).
Proof.
move => Frf Grg phipsi [[y y']] [[[x x' [[/=phinx psinx'] [/= fxy gx'y']]]prop]].
have lprjfd: ((lprj phipsi) \from_dom (f o (delta (r:=X)))).
	exists y; split => [ | z phinz]; first by exists x.
	by rewrite (rep_sing X (lprj phipsi) z x); first exists y.
have [[z [[Fphi [FphiFphi Fphinz]]] propl]condl]:= Frf (lprj phipsi) lprjfd.
have rprjfd: ((rprj phipsi) \from_dom (g o (delta (r:=X')))).
	exists y'; split => [ | z' phinz']; first by exists x'.
	by rewrite (rep_sing X' (rprj phipsi) z' x'); first exists y'.
have [[z' [[Gpsi [GpsiGpsi Gpsinz']]] propr]condr]:= Grg (rprj phipsi) rprjfd.
split.
	exists (z, z').
	split; first by exists (name_pair Fphi Gpsi).
	move => FphiGpsi [/= FphiFphi' GpsiGpsi'].
	have [l nl]:= (propl (lprj FphiGpsi) FphiFphi').
	have [k nk]:= (propr (rprj FphiGpsi) GpsiGpsi').
	by exists (l,k); split.
move => [l k] [[FphiGpsi [[/=FphiFphi' GphiGphi'][/= Fphinl Gpsink]]] proplk].
have phipsil: ((delta (r:=Y)) o F (lprj phipsi) l).
	by split => //; exists (lprj FphiGpsi).
have [[x'' [phinx'' fx''l]] prpl]:= (condl l phipsil).
have phipsir: ((delta (r:=Y')) o G (rprj phipsi) k).
	by split => //; exists (rprj FphiGpsi).
have [[y'' [phiny'' gy''l]] prpr]:= (condr k phipsir).
split.
	exists (x, x'); split => //; split => /=.
		by rewrite (rep_sing X (lprj phipsi) x x'').
	by rewrite (rep_sing X' (rprj phipsi) x' y'').
move => [a b] [/=phina psinb].
have [this stuff]:= prpl a phina.
have [this' stuff']:= prpr b psinb.
by exists (this, this').
Qed.

Lemma is_frlzr_is_rep X Y:
  (@is_fun_rlzr X Y) \is_representation.
Proof.
split => [F f g Frf Frg | f].
	apply functional_extensionality => x.
	have [phi phinx]:= (rep_sur X x).
	apply/ (rep_sing Y); first exact: (Frf phi x phinx).
	exact: (Frg phi x phinx).
set R :=(fun phi psi => phi \from_dom (rep X) -> forall x, (rep X) phi x -> (rep Y) psi (f x)).
have Rtot: R \is_total.
	move => phi.
	case: (classic (phi \from_dom (rep X))) => [[x phinx] | nfd].
		have [psi psiny]:= (rep_sur Y (f x)).
		by exists psi => _ x' phinx'; rewrite -(rep_sing X phi x x').
	by exists (fun q => some_answer Y) => fd; exfalso; apply nfd.
have [F Fcond]:= (choice R Rtot).
by exists F => phi x phinx; apply Fcond => //; exists x.
Qed.

Fact eq_sub T P (a b : {x : T | P x}) : a = b <-> projT1 a = projT1 b.
Proof.
split=> [->//|]; move: a b => [a Pa] [b Pb] /= eqab.
case: _ / eqab in Pb *; congr (exist _ _ _).
exact: Classical_Prop.proof_irrelevance.
Qed.

Definition has_cont_rlzr (X Y : rep_space) (f : X ->> Y) :=
	exists F, is_rlzr F f
	/\
	@is_cont (questions X) (answers X) (questions Y) (answers Y) F.
Notation "f '\has_continuous_realizer'":= (has_cont_rlzr f) (at level 2).

Lemma comp_hcr (X Y Z: rep_space) (f: X ->> Y) (g: Y ->> Z):
	f \has_continuous_realizer -> g \has_continuous_realizer -> (g o f) \has_continuous_realizer.
Proof.
move => [F [Frf Fcont]] [G [Grg Gcont]].
exists (G o F).
split; first by apply rlzr_comp.
by apply/ cont_comp.
Qed.

Definition is_ass (X Y: rep_space) psi (f: X ->> Y) :=
	(oeval (U psi)) \is_realizer_of f.

Notation "X c-> Y" :=
	{f: X ->> Y | (f \is_single_valued /\ f \is_total) /\ has_cont_rlzr f} (at level 2).
Definition exist_fun (X Y: rep_space):=
exist (fun f => (f \is_single_valued /\ f \is_total) /\ @has_cont_rlzr X Y f).

Definition is_fun_name (X Y: rep_space) psi (f: X c-> Y) :=
	(eval (U psi)) \is_realizer_of (projT1 f).

Axiom prop_ext: prop_extensionality.

Lemma is_fun_name_is_rep (X Y : rep_space):
	(@is_fun_name X Y) \is_representation.
Proof.
case (classic (exists y: Y, true)) => [[somey _] | nex];last first.
split => [psi f g psinf psing | ].
	apply eq_sub.
	apply functional_extensionality => x.
	exfalso; apply nex.
	have [[_ tot] _] := projT2 f.
	have [y _] := tot x.
	by exists (y).
move => f.
exists (fun p => inr (some_answer Y)) => ka [y asd].
exfalso; apply nex; by exists y.
split => [psi f g psinf psing | f].
	move: (projT2 f) (projT2 g) => [[fsing ftot] hasrlzrf] [[gsing gtot] hastrlzrg].
	have [hf eqf]:= ((@F2MF_sing_tot X Y (projT1 f) somey).1 (conj fsing ftot)).
	have [hg eqg]:= ((@F2MF_sing_tot X Y (projT1 g) somey).1 (conj gsing gtot)).
	apply/ eq_sub.
	apply functional_extensionality => x;	apply functional_extensionality => y; apply prop_ext; move: x y.
	suffices: F2MF hf =~= F2MF hg by rewrite eqf eqg.
	suffices: hf = hg by move => <-.
	have [F icf]:= exists_choice (eval (U psi)) (fun q => some_answer Y).
	apply/ (is_frlzr_is_rep X Y).1.
		apply frlzr_rlzr.
		apply/ tight_rlzr.
			apply/ icf_F2MF_tight.
			by apply icf.
		by rewrite /is_rlzr eqf.
	apply frlzr_rlzr.
	apply/ tight_rlzr.
		apply/ icf_F2MF_tight.
		by apply icf.
	by rewrite /is_rlzr eqg.
have [cnt sur]:= (countable_questions X).
have [[ftot fsing] [F [Frf Fcont]]]:= (projT2 f).
have [psiF psinF]:= (U_is_universal (some_answer X) (fun q => (some_answer Y)) sur Fcont).
exists psiF.
rewrite /is_fun_name.
apply/ tight_trans; last by apply Frf.
by apply tight_comp_r.
Qed.

Canonical rep_space_cont_fun X Y := @make_rep_space
	((space X) c-> (space Y))
	(seq (questions X * answers X) * questions Y)
	(questions X + answers Y)
	(@is_fun_name X Y)
	(inr (some_answer Y))
  (prod_count
  	(list_count (prod_count
  		(countable_questions X)
  		(countable_answers X)))
  	(countable_questions Y))
  (sum_count (countable_questions X) (countable_answers Y))
  (@is_fun_name_is_rep X Y).
End REPRESENTED_SPACES.

Notation "delta '\is_representation'" := (is_rep delta) (at level 2).
Notation names X := ((questions X) -> (answers X)).
Notation "'\rep'" := @delta (at level 2).
Notation "phi '\is_name_of' x" := (delta phi x) (at level 2).
Notation rep_valid X := (@representation_is_valid X).
Notation rep_sur X := (rep_valid X).2.
Notation rep_sing X := (rep_valid X).1.
Notation "f '\is_realized_by' F" := (is_rlzr F f) (at level 2).
Notation "F '\is_realizer_of' f" := (is_rlzr F f) (at level 2).
Notation "f '\has_continuous_realizer'" := (has_cont_rlzr f) (at level 2).
Notation "X c-> Y" := (rep_space_cont_fun X Y) (at level 2).

Section COMPUTABILITY_DEFINITIONS.
Definition is_comp_elt (X: rep_space) (x: X) :=
	{phi| phi \is_name_of x}.

Definition is_comp (X Y: rep_space) (f: X ->> Y) :=
	{M | (eval M) \is_realizer_of f}.

Definition is_mon_comp (X Y: rep_space) (f: X ->> Y) :=
	{M | M \is_monotone_oracle_machine /\ (eval M) \is_realizer_of f}.

Definition is_prim_rec (X Y: rep_space) (f: X ->> Y) :=
	{F | is_rlzr (F2MF F) f}.

Definition is_comp_fun (X Y: rep_space) (f: X -> Y) :=
	{M | (eval M) \is_realizer_of (F2MF f)}.

Definition is_prim_rec_fun (X Y: rep_space) (f: X -> Y) :=
	{M | is_fun_rlzr M f}.

Definition isomorphism (X Y: rep_space) (f: X c-> Y) :=
	exists (g: Y c-> X) (P: is_comp_elt f) (Q: is_comp_elt g),
		((projT1 f) o (projT1 g) =~= F2MF id /\ (projT1 g) o (projT1 f) =~= F2MF id).

Definition wisomorphism (X Y: rep_space) (f: X ->> Y) :=
	exists (g: Y ->> X) (P: is_comp f) (Q: is_comp g),
	(f o g =~= F2MF id /\ g o f =~= F2MF id).

Definition isomorphic (X Y: rep_space):=
	exists f, @isomorphism X Y f.
Arguments isomorphic {X Y}.

Definition wisomorphic (X Y: rep_space):=
	exists f, @wisomorphism X Y f.
Arguments isomorphic {X Y}.
End COMPUTABILITY_DEFINITIONS.
Notation opU psi:=(eval (fun n phi q' => U n psi phi q')).
Notation "x '\is_computable_element'" := (is_comp_elt x) (at level 2).
Notation "f '\is_computable'" := (is_comp f) (at level 2).
Notation "f '\is_monotone_computable'" := (is_mon_comp f) (at level 2).
Notation "f '\is_prec_function'" := (is_prim_rec_fun f) (at level 2).
Notation "f '\is_computable_function'" := (is_comp_fun f) (at level 2).
Notation "X ~=~ Y" := (@isomorphic X Y) (at level 2).