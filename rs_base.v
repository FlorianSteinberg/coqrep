From mathcomp Require Import all_ssreflect.
Require Import all_core.
Require Import FunctionalExtensionality ClassicalFacts ClassicalChoice Psatz.
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
  some_question: questions;
	some_answer: answers;
  countable_questions: questions \is_countable;
  countable_answers: answers \is_countable;
  representation_is_valid : delta \is_representation
}.
End REPRESENTED_SPACES.
Notation "delta '\is_representation'" := (is_rep delta) (at level 2).
Notation names X := ((questions X) -> (answers X)).
Notation rep := @delta.
Notation "phi '\is_name_of' x" := (delta phi x) (at level 2).
Notation rep_valid X := (@representation_is_valid X).
Notation rep_sur X := (rep_valid X).2.
Notation rep_sing X := (rep_valid X).1.

Section REALIZERS.
Definition rlzr (X Y: rep_space) (F: (names X) ->> (names Y)) (f: X ->> Y) :=
	(rep Y) o F \tightens (f o (rep X)).
Notation "f '\is_realized_by' F" := (rlzr F f) (at level 2).
Notation "F '\is_realizer_of' f" := (rlzr F f) (at level 2).
Global Instance rlzr_prpr (X Y: rep_space):
	Proper (@equiv (names X) (names Y) ==> @equiv (space X) (space Y) ==> iff) (@rlzr X Y).
Proof. by move => F G FeG f g feg; rewrite /rlzr FeG feg. Qed.

Definition frlzr (X Y: rep_space) (F: (names X) -> (names Y)) (f: X -> Y) :=
	forall phi x, (rep X) phi x -> ((rep Y) (F phi) (f x)).
Notation "F '\is_realizer_function_for' f":= (frlzr F f) (at level 2).

Lemma frlzr_rlzr (X Y: rep_space) F (f: X -> Y):
	F \is_realizer_function_for f <-> (F2MF F) \is_realizer_of (F2MF f).
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

Global Instance frlzr_prpr (X Y: rep_space):
	Proper (@eqfun (names Y) (names X) ==> @eqfun (space Y) (space X) ==> iff) (@frlzr X Y).
Proof.
move => F G FeG f g feg.
have eq: (F2MF F) =~= (F2MF G) by move => s; rewrite /F2MF (FeG s).
have eq': (F2MF f) =~= (F2MF g) by move => s; rewrite /F2MF (feg s).
by rewrite !frlzr_rlzr eq eq'.
Qed.


Lemma mfrlzr_rlzr (X Y: rep_space) F (f: X ->> Y) (somey: Y): f \is_single_valued -> f \is_total
	-> (exists g, g \is_choice_for f /\ F \is_realizer_function_for g) <-> (F2MF F) \is_realizer_of f.
Proof.
move => sing tot.
split => [ [g [icf rlzr]] | mfrlzr].
	move: ((@sing_tot_F2MF_icf X Y f g sing tot).1 icf) => eq.
	suffices: (F2MF F) \is_realizer_of (F2MF g) by rewrite /rlzr -eq.
	exact/ frlzr_rlzr.
have ass: f \is_single_valued /\ f \is_total by split.
have [g eq]:= ((F2MF_sing_tot f (somey)).1 ass).
exists g; split; first by apply sing_tot_F2MF_icf.
apply/ frlzr_rlzr.
by rewrite /rlzr eq.
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
rewrite /rlzr.
apply/ tight_trans.
apply/ tight_comp_r; first by apply GtF.
apply Frf.
Qed.

Lemma rlzr_comp (X Y Z: rep_space) G F (f: X ->> Y) (g: Y ->> Z):
	G \is_realizer_of g -> F \is_realizer_of f -> (G o F) \is_realizer_of (g o f).
Proof.
move => Grg Frf.
rewrite /rlzr.
rewrite -comp_assoc.
apply/ tight_trans.
	by apply /tight_comp_l; apply Grg.
apply/ tight_trans.
	rewrite comp_assoc.
	by apply /tight_comp_r; apply Frf.
by rewrite comp_assoc.
Qed.

Lemma rlzr_dom (X Y: rep_space) (f: X ->> Y) F:
	F \is_realizer_of f -> forall phi x, phi \is_name_of x -> x \from_dom f -> phi \from_dom F.
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

Lemma rlzr_val_sing (X Y: rep_space) (f: X ->> Y) F: f \is_single_valued -> F \is_realizer_of f ->
	forall phi x Fphi y, phi \is_name_of x -> f x y -> F phi Fphi -> Fphi \is_name_of y.
Proof.
move => sing Frf phi x Fphi y phinx fxy FphiFphi.
have phifd: phi \from_dom (f o (delta (r:=X))).
	by exists y; split => [ | x' phinx']; [exists x | rewrite (rep_sing X phi x' x); first exists y].
have [[y' [[Fphi' [FphiFphi' Fphi'ny']] prop]] cond]:= (Frf phi phifd).
have [z Fphinz]:= (prop Fphi FphiFphi).
have phinz: (delta (r:=Y)) o F phi z by split => [ | n H]; [exists Fphi | apply prop].
have [[x' [phinx' fx'z]]prp] := cond z phinz.
rewrite (sing x y z) => //.
by rewrite (rep_sing X phi x x').
Qed.

Lemma sing_rlzr (X Y: rep_space) (f: X ->> Y) F: F \is_single_valued -> f \is_single_valued ->
	F \is_realizer_of f
	<->
	(forall phi x, phi \is_name_of x -> x \from_dom f -> phi \from_dom F)
		/\
	(forall phi x Fphi y, phi \is_name_of x -> f x y -> F phi Fphi -> Fphi \is_name_of y).
Proof.
move => Fsing fsing.
split.
	by move => Frf; split; [exact: rlzr_dom | exact: rlzr_val_sing].
move => [prp cnd] phi [y [[x [phinx fxy]] _]].
have xfd: x \from_dom f by exists y.
have [Fphi FphiFphi]:= prp phi x phinx xfd.
have Fphiny:= cnd phi x Fphi y phinx fxy FphiFphi.
split.
	exists y; split; first by exists Fphi.
	move => Fphi' FphiFphi'; exists y.
	by rewrite (Fsing phi Fphi' Fphi).
move => y' [[Fphi' [FphiFphi' Fphi'ny']] _].
split.
	exists x; split => //.
	rewrite (Fsing phi Fphi' Fphi) in Fphi'ny' => //.
	by rewrite (rep_sing Y Fphi y' y).
move => x' phinx'.
by exists y; rewrite (rep_sing X phi x' x).
Qed.

Definition rrlzr (X Y: rep_space) (F: (names X) -> (names Y)) (f: X ->> Y) :=
	(forall phi x, phi \is_name_of x -> x \from_dom f ->
		exists y, (F phi) \is_name_of y /\ f x y).
Notation "F '\is_rec_realizer_of' f":= (rrlzr F f) (at level 2).

Lemma rrlzr_rlzr (X Y: rep_space) (f: X ->> Y) F:
	F \is_rec_realizer_of f
	<->
	(F2MF F) \is_realizer_of f.
Proof.
split; last first.
	move => Frf phi x phinx [y fxy].
	have phifd: phi \from_dom (f o (delta (r:=X))).
		exists y; split; first by exists x.
		by move => x' phinx'; rewrite (rep_sing X phi x' x) => //; exists y.
	have [[y' [[Fphi [<- Fphiny']] prp]] cnd]:= (Frf phi phifd).
	have phiny': (delta (r:=Y)) o (F2MF F) phi y'.
		split; first by exists (F phi).
		by move => Fphi' <-; exists y'.
	have [[x' [phinx' fx'y']]prp']:= cnd y' phiny'.
	exists y'; split => //.
	by rewrite (rep_sing X phi x x').
move => prop phi [y [[x [phinx fxy]] prp]].
have xfd: x \from_dom f by exists y.
have [y' [Fphiny' fxy']]:= prop phi x phinx xfd.
split.
	exists y'; split; first by exists (F phi).
	move => Fphi <-; by exists y'.
move => y'' [[Fphi [<- Fphiny'']]cnd].
split; first by exists x; rewrite (rep_sing Y (F phi) y'' y').
by move => x' phinx'; rewrite (rep_sing X phi x' x).
Qed.

Global Instance rrlzr_prpr (X Y: rep_space):
	Proper (@eqfun (names Y) (names X) ==> @equiv (space X) (space Y) ==> iff) (@rrlzr X Y).
Proof.
move => F G FeG f g feg.
have eq: (F2MF F) =~= (F2MF G) by move => s; rewrite /F2MF (FeG s).
by rewrite !rrlzr_rlzr eq feg.
Qed.

Lemma rlzr_F2MF (X Y: rep_space) (f: X -> Y) F:
	F \is_realizer_of (F2MF f)
	<->
	forall phi x, phi \is_name_of x -> phi \from_dom F /\ forall Fphi, F phi Fphi -> Fphi \is_name_of (f x).
Proof.
split.
	move => Frf phi x phinx; split; first by apply/ rlzr_dom; [apply Frf | apply phinx | apply F2MF_tot ].
	by move => Fphi FphiFphi; apply/ rlzr_val_sing; [apply F2MF_sing | apply Frf | apply phinx | | ].
move => prp phi [_ [[x [phinx _]] _]].
split.
	exists (f x).
	split; last by move => Fphi FphiFphi; exists (f x); apply (prp phi x phinx).2.
	have [Fphi FphiFphi]:= (prp phi x phinx).1.
	exists Fphi; split => //.
	by apply (prp phi x phinx).2.
move => y [[Fphi [FphiFphi Fphiny]] cnd].
split; last by move => a b; exact: F2MF_tot.
exists x; split => //.
have Fphinfx := (prp phi x phinx).2 Fphi FphiFphi.
by rewrite (rep_sing Y Fphi y (f x)).
Qed.

Lemma frlzr_is_rep X Y:
  (@frlzr X Y) \is_representation.
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

Definition hcr (X Y : rep_space) (f : X ->> Y) :=
	exists F, F \is_realizer_of f
	/\
	@is_cont (questions X) (answers X) (questions Y) (answers Y) F.
Notation "f '\has_continuous_realizer'":= (hcr f) (at level 2).

Global Instance hcr_prpr (X Y: rep_space):
	Proper (@equiv (space X) (space Y) ==> iff) (@hcr X Y).
Proof. by move => f g feg; split; move => [F [Frf Fcont]]; exists F; [rewrite -feg | rewrite feg]. Qed.

Lemma comp_hcr (X Y Z: rep_space) (f: X ->> Y) (g: Y ->> Z):
	f \has_continuous_realizer -> g \has_continuous_realizer -> (g o f) \has_continuous_realizer.
Proof.
move => [F [Frf Fcont]] [G [Grg Gcont]].
exists (G o F).
split; first by apply rlzr_comp.
by apply/ cont_comp.
Qed.
End REALIZERS.
Notation "f '\has_continuous_realizer'":= (hcr f) (at level 2).
Notation "f '\is_realized_by' F" := (rlzr F f) (at level 2).
Notation "F '\is_realizer_of' f" := (rlzr F f) (at level 2).
Notation "F '\is_realizer_function_for' f" := (frlzr F f) (at level 2).
Notation "F '\is_rec_realizer_of' f":= (rrlzr F f) (at level 2).

Section DEFINITIONS.

Definition is_rec_elt (X: rep_space) (x: X) :=
	{phi| phi \is_name_of x}.

Definition is_cmpt_elt (X: rep_space) (x: X) :=
	{phi: nat -> _ | exists psi, (meval phi) =~= F2MF psi /\ psi \is_name_of x}.

Definition is_cmpt (X Y: rep_space) (f: X ->> Y) :=
	{M | (eval M) \is_realizer_of f}.

Definition is_mon_cmpt (X Y: rep_space) (f: X ->> Y) :=
	{M | M \is_monotone_oracle_machine /\ (eval M) \is_realizer_of f}.

Definition is_rec (X Y: rep_space) (f: X ->> Y) :=
	{F | F \is_rec_realizer_of f}.

(*
Definition iffT (S T: Type) :=
exists (f: S -> T) (g:T -> S), (forall s, f (g s) = s) /\ forall t, g (f t) = t.

Global Instance eq_iffT:
	Equivalence iffT.
Proof.
split.
		by move => T; do 2 exists (fun t => t).
	by move => S T [TS [ST [fsg gsf]]]; exists ST; exists TS.
move => S T R [f [g [fsg gsf]]] [f' [g' [f'sg' g'sf']]].
	exists (fun s => f' (f s)).
exists (fun r => g (g' r)).
by split => [s | t]; [rewrite (fsg (g' s)) | rewrite (g'sf' (f t))].
Qed.

Global Instance prec_prpr (X Y: rep_space):
	Proper (@equiv X Y ==> iffT) (@prec X Y).
Proof.
move => f g feg.
have imp1: prec f -> prec g.
	by move => [M Mprop]; exists M; rewrite -prlzr_rlzr -feg prlzr_rlzr; apply Mprop.
exists imp1.
have imp2: prec g -> prec f.
	by move => [M Mprop];	exists M; rewrite -prlzr_rlzr feg prlzr_rlzr; apply Mprop.
exists imp2.
split => s.

Qed.*)

Definition is_cmpt_fun (X Y: rep_space) (f: X -> Y) :=
	{M | (eval M) \is_realizer_of (F2MF f)}.

Definition is_rec_fun (X Y: rep_space) (f: X -> Y) :=
	{M | M \is_realizer_function_for f}.
End DEFINITIONS.

Notation opU psi:=(eval (fun n phi q' => U n psi phi q')).
Notation "x '\is_recursive_element'" := (is_rec_elt x) (at level 2).
Notation "x '\is_computable_element'" := (is_cmpt_elt x) (at level 2).
Notation "f '\is_computable'" := (is_cmpt f) (at level 2).
Notation "f '\is_monotone_computable'" := (is_mon_cmpt f) (at level 2).
Notation "f '\is_recursive'" := (is_rec f) (at level 2).
Notation "f '\is_recursive_function'" := (is_rec_fun f) (at level 2).
Notation "f '\is_computable_function'" := (is_cmpt_fun f) (at level 2).

Section BASIC_LEMMAS.
Lemma rec_fun_rec (X Y: rep_space) (f: X -> Y):
	f \is_recursive_function -> (F2MF f) \is_recursive.
Proof.
by move => [M Mprop]; exists M; apply/ rrlzr_rlzr/ frlzr_rlzr.
Qed.

Lemma rec_cmpt (X Y:rep_space) (f: X ->> Y):
	f \is_recursive -> f \is_computable.
Proof.
move => [N Nir]; exists (fun n phi q' => Some (N phi q')).
abstract by move: Nir; rewrite rrlzr_rlzr => Nir; apply/ tight_trans; first apply/ tight_comp_r/(prec_F2MF_op 0).
Qed.

Lemma rec_fun_rec_elt (X Y: rep_space) (f: X -> Y) (x: X):
	x \is_recursive_element -> f \is_recursive_function -> (f x) \is_recursive_element.
Proof.
move => [phi phinx] [M Mrf].
by exists (M phi); apply Mrf.
Defined.

Lemma mon_cmpt_cmpt (X Y: rep_space) (f: X ->> Y):
	f \is_monotone_computable -> f \is_computable.
Proof. by move => [M [mon comp]]; exists M. Defined.

Lemma rec_fun_comp (X Y Z: rep_space) (f: X -> Y) (g: Y -> Z):
	f \is_recursive_function -> g \is_recursive_function
	-> forall h, (forall x, h x = g (f x)) -> h \is_recursive_function.
Proof.
move => [M comp] [N comp'] h eq.
exists (fun phi => N (M phi)).
abstract by move => phi x phinx; rewrite eq; apply comp'; apply comp.
Defined.

Lemma rec_comp (X Y Z: rep_space) (f: X ->> Y) (g: Y ->> Z) h:
	f \is_recursive -> g \is_recursive -> h =~= g o f -> h \is_recursive.
Proof.
move => [M comp] [N comp'] eq.
exists (fun phi => N (M phi)).
abstract by rewrite rrlzr_rlzr eq; have ->: F2MF (fun phi => N (M phi)) =~= (F2MF N) o (F2MF M);
	[rewrite F2MF_comp | apply rlzr_comp; rewrite -rrlzr_rlzr].
Defined.

Lemma rec_fun_rec_comp_tech (X Y Z: rep_space) (f: X ->> Y) (g: Y -> Z) M N:
	f \is_total -> M \is_rec_realizer_of f -> N \is_realizer_function_for g
	-> forall h, (forall x y, f x y -> h x = g y) -> (fun phi => N (M phi)) \is_realizer_function_for h.
Proof.
move => ftot comp comp' h eq phi x phinx.
move: comp; rewrite rrlzr_rlzr => comp.
have [y fxy]:= ftot x.
have prop: phi \from_dom (f o (delta (r:=X))).
	exists y; split; first by exists x.
	by move => x' phinx'; rewrite (rep_sing X phi x' x).
have [y' [[psi [<- name]] _]]:= (comp phi prop).1.
rewrite (eq x y') => //; first by apply comp'.
have cond: ((delta (r:=Y)) o (F2MF M) phi y').
	split; first by exists (M phi).
	by move => Mpsi <-; exists y'.
have [[x' [phinx' fx'y']] _] := (comp phi prop).2 y' cond.
by rewrite (rep_sing X phi x x').
Qed.

Lemma rec_fun_rec_comp (X Y Z: rep_space) (f: X ->> Y) (g: Y -> Z):
	f \is_total -> f \is_recursive -> g \is_recursive_function
	-> forall h, (forall x y, f x y -> h x = g y) -> h \is_recursive_function.
Proof.
move => ftot [M comp] [N comp'] h eq.
exists (fun phi => N (M phi)).
exact: (rec_fun_rec_comp_tech ftot comp comp').
Defined.

Lemma rec_fun_cmpt_comp_tech (X Y Z: rep_space) (f: X -> Y) (g: Y -> Z) M N:
	M \is_realizer_function_for f -> (eval N) \is_realizer_of (F2MF g)
	-> forall h, (forall x, h x = g (f x)) -> (eval (fun (n: nat) phi => N n (M phi))) \is_realizer_of (F2MF h).
Proof.
move => comp comp' h eq.
have eq': (F2MF h) =~= ((F2MF g) o (F2MF f)) by rewrite F2MF_comp/ F2MF => r; rewrite -(eq r).
rewrite eq'.
apply/ tight_trans; last first.
	by rewrite comp_assoc; apply tight_comp_r; apply ((frlzr_rlzr _ _).1 comp).
apply/ tight_trans; last by rewrite -comp_assoc; apply tight_comp_l; apply comp'.
by rewrite comp_assoc; apply/ tight_comp_r; rewrite F2MF_comp.
Qed.

Lemma rec_fun_cmpt_comp (X Y Z: rep_space) (f: X -> Y) (g: Y -> Z):
	f \is_recursive_function -> g \is_computable_function
	-> forall h, (forall x, h x = g (f x)) -> h \is_computable_function.
Proof.
move => [M comp] [N comp']; exists (fun n phi => N n (M phi)).
exact: (rec_fun_cmpt_comp_tech comp comp').
Defined.

Lemma rec_fun_cmpt (X Y: rep_space) (f: X -> Y):
	f \is_recursive_function -> f \is_computable_function.
Proof.
move => [N Nir]; exists (fun n phi q' => Some (N phi q')).
abstract by apply/ tight_trans; [apply tight_comp_r; apply: prec_F2MF_op 0 | apply frlzr_rlzr; apply/ Nir].
Defined.

Lemma cnst_rec_fun (X Y: rep_space) (fx: Y):
	fx \is_recursive_element -> (fun x: X => fx) \is_recursive_function.
Proof. by move => [psi psiny]; exists (fun _ => psi). Defined.

Lemma cnst_rec (X Y: rep_space) (fx: Y):
	fx \is_recursive_element -> (F2MF (fun (x: X) => fx)) \is_recursive.
Proof. by move => fxcmpt; by apply rec_fun_rec; apply cnst_rec_fun. Defined.

Lemma id_rec_fun X:
	(@id (space X)) \is_recursive_function.
Proof. by exists id. Defined.

Lemma id_rec X:
	@is_rec X X (F2MF id).
Proof. exists id; abstract by rewrite rrlzr_rlzr -frlzr_rlzr. Defined.

Lemma id_cmpt X:
	@is_cmpt X X (F2MF id).
Proof. exact: (rec_cmpt (id_rec X)). Defined.

Lemma id_hcr X:
	@hcr X X (F2MF id).
Proof.
exists (F2MF id).
split; first by apply frlzr_rlzr.
move => phi q' _.
exists [ ::q'].
move => Fphi /= <- psi coin Fpsi <-.
apply coin.1.
Qed.

(*Lemma cmpt_fun_comp (X Y Z: rep_space) (f: X -> Y) (g: Y -> Z):
	f \is_monotone_computable -> g \is_computable_function
	-> forall h, (forall x, h x = g (f x)) -> h \is_computable_function.
Proof.
move => [M comp] [N comp'] h eq.
exists (fun phi => N (M phi)).
by move => phi x phinx; rewrite eq; apply comp'; apply comp.
Defined.*)
End BASIC_LEMMAS.