From mathcomp Require Import all_ssreflect.
Require Import all_core rs_base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PRODUCTSPACES.
(* This is the product of represented spaces. *)

Definition lprj X Y (phipsi: questions X + questions Y -> (answers X) * (answers Y)) q := (phipsi (inl q)).1.
Definition rprj X Y (phipsi: questions X + questions Y -> (answers X) * (answers Y)) q := (phipsi (inr q)).2.

Definition name_pair X Y (phi: names X) (psi: names Y) :=
	fun c => match c with
		| inl s => (phi s, some_answer Y)
		| inr t => (some_answer X, psi t)
	end.

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

Canonical rep_space_prod X Y := @make_rep_space
  ((space X) * (space Y))
  (@questions X + @questions Y)
  (@answers X * @answers Y)
  (@prod_rep X Y)
  ((some_answer X, some_answer Y))
  (sum_count (countable_questions X) (countable_questions Y))
  (prod_count (countable_answers X) (countable_answers Y))
  (@prod_rep_is_rep X Y).

Lemma fst_prec (X Y: rep_space):
	(@fst X Y) \is_prec_function.
Proof.
by exists (@lprj X Y); move => phi x [phinx _].
Defined.

Lemma snd_prec (X Y: rep_space):
	(@snd X Y) \is_prec_function.
Proof.
by exists (@rprj X Y); move => phi x [_ phinx].
Defined.

Lemma switch_prec_fun (X Y: rep_space):
	(fun x: X * Y => (x.2, x.1)) \is_prec_function.
Proof. 
by exists (fun phi => name_pair (rprj phi) (lprj phi)); move => phi [x y] [phinx phiny].
Defined.

Lemma prod_assoc_prec (X Y Z: rep_space):
	(fun x: X * (Y * Z) => (x.1, x.2.1,x.2.2)) \is_prec_function.
Proof.
exists (fun phi => name_pair (name_pair (lprj phi) (lprj (rprj phi))) (rprj (rprj phi))).
by move => phi [x [y z]] [phinx [phiny phinz]].
Defined.

Lemma prod_assoc_inv_prec (X Y Z: rep_space):
	(fun x: X * Y * Z => (x.1.1, (x.1.2, x.2))) \is_prec_function.
Proof.
exists (fun phi => name_pair (lprj (lprj phi)) (name_pair (rprj (lprj phi)) (rprj phi))).
by move => phi [[x y] z] [[phinx phiny] phinz].
Defined.

Lemma prod_cmpt_elt (X Y: rep_space) (x: X) (y: Y):
	x \is_computable_element -> y \is_computable_element -> (x, y) \is_computable_element.
Proof.
move => [phi phinx] [psi psiny].
by exists (fun q => match q with
	| inl qx => (phi qx, some_answer Y)
	| inr qy => (some_answer X, psi qy)
end).
Defined.

Lemma lprj_cont X Y:
	(F2MF (@lprj X Y)) \is_continuous.
Proof.
move => phi q; exists ([::inl q]).
by move => Fphi/= <- psi [eq _] Fpsi <-; rewrite /lprj eq.
Qed.

Lemma fst_hcr (X Y: rep_space):
	(F2MF (@fst X Y)) \has_continuous_realizer.
Proof.
exists (F2MF (@lprj X Y)).
by split; [apply frlzr_rlzr => phi x [phinx _] | exact: lprj_cont].
Qed.

Lemma rprj_cont X Y:
	(F2MF (@rprj X Y)) \is_continuous.
Proof.
move => phi q; exists ([::inr q]).
by move => Fphi/= <- psi [eq _] Fpsi <-; rewrite /rprj eq.
Qed.

Lemma snd_hcr (X Y: rep_space):
	(F2MF (@snd X Y)) \has_continuous_realizer.
Proof.
exists (F2MF (@rprj X Y)).
by split; [apply frlzr_rlzr => phi x [_ phinx] | exact: rprj_cont].
Qed.

Lemma lprj_pair (X Y: rep_space) (phi: names X) (psi: names Y):
	lprj (name_pair phi psi) =  phi.
Proof. by trivial. Qed.

Lemma rprj_pair (X Y: rep_space) (phi: names X) (psi: names Y):
	rprj (name_pair phi psi) =  psi.
Proof. by trivial. Qed.

Definition mfpp_rlzr (X Y X' Y': rep_space) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):=
	(fun (phipsi: names (rep_space_prod X X')) FphiGpsi =>
		FphiGpsi = name_pair (lprj FphiGpsi) (rprj FphiGpsi)
		/\
		(F ** G) (lprj phipsi, rprj phipsi)	(lprj FphiGpsi, rprj FphiGpsi)).

Definition mfpp_frlzr (X Y X' Y': rep_space) (F: (names X) -> (names Y)) (G: (names X') -> (names Y')):=
	(fun (phipsi: names (rep_space_prod X X')) => name_pair (F (lprj phipsi)) (G (rprj phipsi))).

Lemma prod_prec_fun (X Y X' Y': rep_space) (f: X -> Y) (g: X' -> Y'):
	f \is_prec_function -> g \is_prec_function -> (fun p => (f p.1, g p.2)) \is_prec_function.
Proof.
move => [M Mrf] [N Nrg].
exists (mfpp_frlzr M N).
abstract by move => phipsi [x x'] [phinx psinx']; split; [apply Mrf | apply Nrg].
Defined.

Lemma mfpp_frlzr_rlzr (X Y X' Y': rep_space) (F: (names X) -> (names Y)) (G: (names X') -> (names Y')):
	F2MF (mfpp_frlzr F G) =~= mfpp_rlzr (F2MF F) (F2MF G).
Proof.
move => phi FGphi; rewrite {1}/F2MF.
split => [eq | [np [/=vall valr]]]; last by rewrite np /mfpp_frlzr vall valr.
by rewrite -eq /mfpp_rlzr/=/mfpp_frlzr lprj_pair rprj_pair.
Qed.

Lemma prod_rlzr (X Y X' Y': rep_space) (f: X ->> Y) (g: X' ->> Y') F G:
	F \is_realizer_of f -> G \is_realizer_of g -> (mfpp_rlzr F G) \is_realizer_of (f ** g).
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
	move => FphiGpsi [/= np [/=FphiFphi' GpsiGpsi']].
	have [l nl]:= (propl (lprj FphiGpsi) FphiFphi').
	have [k nk]:= (propr (rprj FphiGpsi) GpsiGpsi').
	by exists (l,k); split.
move => [l k] [[FphiGpsi [[ np [/=FphiFphi' GphiGphi']][/= Fphinl Gpsink]]] proplk].
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

Lemma prod_prec (X Y X' Y': rep_space) (f: X ->> Y) (g: X' ->> Y'):
	f \is_prec -> g \is_prec -> (f ** g) \is_prec.
Proof.
move => [M Mrf] [N Nrg].
exists (mfpp_frlzr M N).
abstract by rewrite mfpp_frlzr_rlzr; apply prod_rlzr.
Defined.

Lemma mfpp_cont (X Y X' Y': rep_space) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):
	F \is_continuous -> G \is_continuous -> (mfpp_rlzr F G) \is_continuous.
Proof.
have mapl: forall K (q:questions X), List.In q K -> List.In ((@inl _ (questions X')) q) (map inl K).
	elim => // q K ih q' /=listin; by case: listin => ass; [left; rewrite -ass | right; apply ih].
have mapr: forall K (q:questions X'), List.In q K -> List.In ((@inr (questions X) _) q) (map inr K).
	elim => // q K ih q' /=listin; by case: listin => ass; [left; rewrite -ass | right; apply ih].
move => Fcont Gcont phi q [FGphi [ np [/=FlphilFGphi GrphirFGphi]]].
case: q => q.
	have lphifd: (lprj phi) \from_dom F by exists (lprj FGphi).
	have [L Lprop] := (Fcont (lprj phi) q lphifd).
	exists (map inl L).
	move => FGphi' [np' [/=vall valr]] psi coin Fpsi [ np'' [/=val'l val'r]].
	rewrite np' np''; apply injective_projections => //=.
	rewrite (cont_to_sing Fcont vall FlphilFGphi).
	apply/ Lprop; [ | | apply val'l ] => //=.
	rewrite /lprj.
	rewrite coin_lstn => q' listin/=.
	rewrite ((@coin_lstn _ _ _ _ (map inl L)).1 coin (inl q')) => //.
	by apply (mapl L q').
have rphifd: (rprj phi) \from_dom G by exists (rprj FGphi).
have [L Lprop] := (Gcont (rprj phi) q rphifd).
exists (map inr L).
move => FGphi' [np' [/=vall valr]] psi coin Fpsi [ np'' [/=val'l val'r]].
rewrite np' np''; apply injective_projections => //=.
rewrite (cont_to_sing Gcont valr GrphirFGphi).
apply/ Lprop; [ | | apply val'r ] => //=.
rewrite /rprj coin_lstn => q' listin/=.
rewrite ((@coin_lstn _ _ _ _ (map inr L)).1 coin (inr q')) => //.
by apply (mapr L q').
Qed.

Lemma mfpp_hcr (X Y X' Y': rep_space) (f: X ->> Y) (g: X' ->> Y'):
	f \has_continuous_realizer -> g \has_continuous_realizer -> (f ** g) \has_continuous_realizer.
Proof.
move => [F [Frf Fcont]] [G [Grg Gcont]].
exists (mfpp_rlzr F G).
split; [exact: prod_rlzr | exact: mfpp_cont].
Qed.

Lemma prod_space_fun (X Y Z: rep_space) (f: Z -> X) (g: Z -> Y):
	exists (F: Z -> X * Y),
		(forall z, (F z).1 = f z)
		/\
		(forall z, (F z).2 = g z).
Proof.
by exists (fun z => (f z, g z)).
Defined.

Lemma prod_space_prec_fun (X Y Z: rep_space) (f: Z -> X) (g: Z -> Y):
	f \is_prec_function -> g \is_prec_function ->
	exists (F: Z -> (rep_space_prod X Y)) (P:	F \is_prec_function),
		((F2MF (@fst X Y)) o (F2MF F) =~= (F2MF f))
		/\
		((F2MF (@snd X Y)) o (F2MF F) =~= (F2MF g)).
Proof.
move => [F Frf] [G Grg].
exists (fun z => (f z, g z)).
split; last by split; by rewrite F2MF_comp /F2MF/=.
exists (fun phi => (mfpp_frlzr F G) (name_pair phi phi)).
move => phi z phinz.
rewrite /mfpp_frlzr.
split => /=; [rewrite lprj_pair | rewrite rprj_pair].
	by apply Frf; rewrite lprj_pair.
by apply Grg; rewrite rprj_pair.
Qed.

Definition diag (X: rep_space):= (fun x => (x,x): rep_space_prod X X).

Lemma diag_prec_fun (X: rep_space):
	(@diag X) \is_prec_function.
Proof. by exists (fun phi => name_pair phi phi). Defined.

Lemma diag_prec (X: rep_space):
	(F2MF (@diag X)) \is_prec.
Proof. by exists (fun phi => name_pair phi phi); rewrite -frlzr_rlzr. Defined.

Lemma diag_cmpt_fun (X: rep_space):
	(@diag X) \is_computable_function.
Proof. by apply prec_fun_cmpt; apply diag_prec_fun. Defined.

Lemma diag_hcr (X: rep_space):
	(F2MF (@diag X)) \has_continuous_realizer.
Proof.
exists (F2MF (fun phi => name_pair phi phi)).
split; first by apply frlzr_rlzr.
move => phi q.
case: q => q; by exists [:: q] => Fphi/= <- psi [eq _] Fpsi <-; rewrite /name_pair eq.
Qed.

Lemma diag_cmpt (X: rep_space):
	(F2MF (@diag X)) \is_computable.
Proof. apply prec_cmpt; apply diag_prec. Defined.

Lemma cmpt_elt_prod_prec (X Y Z: rep_space) (g: X * Y -> Z) (x: X) f:
	g \is_prec_function -> x \is_computable_element -> f = (fun y => g (x,y)) -> f \is_prec_function.
Proof.
move => fprec xcmpt ->.
apply /prec_fun_comp.
	apply diag_prec_fun.
	apply /prec_fun_comp.
		apply /prod_prec_fun.
			by apply id_prec_fun.
		by apply/ cnst_prec_fun; apply xcmpt.
	apply/ prec_fun_comp.
		by apply switch_prec_fun.
	by apply fprec.
done.
done.
done.
Defined.

(*
Class Uncurry T (f : T) src tgt := { prog : src -> tgt }.
Arguments prog {T} f {src tgt _}.

Instance Uncurry_base (X Y : rep_space) f : @Uncurry (X -> Y) f _ _ :=
  {| prog := f |}.
Instance Uncurry_step (X Y : rep_space) Z (f : X -> Y -> Z)
                       T (g : forall a, @Uncurry (Y -> Z) (f a) Y T) :
                                          @Uncurry (X -> Y -> Z) f (X * Y) T :=
  {| prog := (fun x : rep_space_prod X Y => @prog _ _ _ _ (g (fst x)) (snd x)) |}.
Notation "f '\is_prec_function'" := (is_prec_fun (prog f)) (at level 2).
*)
End PRODUCTSPACES.
