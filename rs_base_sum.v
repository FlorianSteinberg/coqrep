From mathcomp Require Import all_ssreflect.
Require Import all_core rs_base rs_base_prod rs_base_facts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SUMSPACES.
(* This is the sum of represented spaces. *)

Definition linc X Y (phi: names X) (p: questions X * questions Y) :=
@inl (answers X) (answers Y) (phi (p.1)).
Definition rinc X Y (psi: names Y) (p: questions X * questions Y) :=
@inr (answers X) (answers Y) (psi (p.2)).

Definition lslct X Y (phipsi: questions X * questions Y -> answers X + answers Y) :=
	fun q => match phipsi (q, some_question Y) with
		| inl a => a
		| inr b => some_answer X
	end.

Definition rslct X Y (phipsi: questions X * questions Y -> answers X + answers Y) :=
	fun q => match phipsi (some_question X, q) with
		| inl b => some_answer Y
		| inr b => b
	end.

Lemma linc_lslct (X Y: rep_space) (phi: names X):
	@lslct X Y (linc phi) =  phi.
Proof. by trivial. Qed.

Lemma rinc_rslct (X Y: rep_space) (psi: names Y):
	@rslct X Y (rinc psi) =  psi.
Proof. by trivial. Qed.

Definition sum_rep X Y :=
	fun phipsi xpy => match xpy with
		| inl x => (exists a, phipsi (some_question X, some_question Y) = inl a)
			/\ rep X (lslct phipsi) x
		| inr y => (exists a, phipsi (some_question X, some_question Y) = inr a)
			/\ rep Y (rslct phipsi) y
	end.

Lemma sum_rep_is_rep (X Y: rep_space):
	(@sum_rep X Y) \is_representation.
Proof.
split.
	move => phi; rewrite /sum_rep.
	case => [x | y].
		case => [x' | y'] => [[_ phinx] [_ phinx'] | [[a eq] _] [[b eq'] _]].
			by rewrite (rep_sing X (lslct phi) x x').
		by rewrite eq in eq'.
	case => [x' | y'] => [[[a eq] _] [[b eq'] _] | [_ phinx] [_ phinx']].
		by rewrite eq in eq'.
	by rewrite (rep_sing Y (rslct phi) y y').
case => [xy | xy]; have [phi phin]:= rep_sur _ xy.
	by exists (linc phi); split; first by exists (phi (some_question X)).
by exists (rinc phi); split; first by exists (phi (some_question Y)).
Qed.

Canonical rep_space_prod X Y := @make_rep_space
  ((space X) + (space Y))
  (@questions X * @questions Y)
  (@answers X + @answers Y)
  (@sum_rep X Y)
 	(some_question X, some_question Y)
  (inl (some_answer X))
  (prod_count (countable_questions X) (countable_questions Y))
  (sum_count (countable_answers X) (countable_answers Y))
  (@sum_rep_is_rep X Y).
End SUMSPACES.

Section SUMLEMMAS.
Lemma inl_rec_fun (X Y: rep_space):
	(@inl X Y) \is_recursive_function.
Proof.
by exists (@linc X Y); split; first by exists (phi (some_question X)).
Defined.

Lemma inl_rec (X Y: rep_space):
	(F2MF (@inl X Y)) \is_recursive.
Proof. exact/rec_fun_rec/inl_rec_fun. Defined.

Lemma inr_rec_fun (X Y: rep_space):
	(@inr X Y) \is_recursive_function.
Proof.
by exists (@rinc X Y); split; first by exists (phi (some_question Y)).
Defined.

Lemma inr_rec (X Y: rep_space):
	(F2MF (@inr X Y)) \is_recursive.
Proof. exact/rec_fun_rec/inr_rec_fun. Defined.

(*
Lemma sum_assoc_rec_fun (X Y Z: rep_space):
	(fun xyz: X + (Y + Z) => match xyz with
		| inl x => inl (inl x)
		| inr yz => match yz with
			| inl y => inl (inr y)
			| inr z => inr z
		end
	end) \is_recursive_function.
Proof.
Admitted.

Lemma sum_assoc_rec (X Y Z: rep_space):
	(F2MF (fun x: X * (Y * Z) => (x.1, x.2.1,x.2.2))) \is_recursive.
Proof.
exact/rec_fun_rec/prod_assoc_rec_fun.
Defined.

Lemma prod_assoc_inv_rec_fun (X Y Z: rep_space):
	(fun x: X * Y * Z => (x.1.1, (x.1.2, x.2))) \is_recursive_function.
Proof.
exists (fun phi => name_pair (lprj (lprj phi)) (name_pair (rprj (lprj phi)) (rprj phi))).
by move => phi [[x y] z] [[phinx phiny] phinz].
Defined.

Lemma prod_assoc_inv_rec (X Y Z: rep_space):
	(F2MF (fun x: X * Y * Z => (x.1.1, (x.1.2, x.2)))) \is_recursive.
Proof.
exact/rec_fun_rec/prod_assoc_inv_rec_fun.
Defined.*)

Lemma linc_cont X Y:
	(F2MF (@linc X Y)) \is_continuous.
Proof.
move => phi q; exists ([:: q.1]).
by move => Fphi/= <- psi [eq _] Fpsi <-; rewrite /linc eq.
Qed.

Lemma inl_hcr (X Y: rep_space):
	(F2MF (@inl X Y)) \has_continuous_realizer.
Proof.
exists (F2MF (@linc X Y)); split; last exact: linc_cont.
by apply frlzr_rlzr; split; first by exists (phi (some_question X)).
Qed.

Lemma rinc_cont X Y:
	(F2MF (@rinc X Y)) \is_continuous.
Proof.
move => phi q; exists ([::q.2]).
by move => Fphi/= <- psi [eq _] Fpsi <-; rewrite /rinc eq.
Qed.

Lemma inr_hcr (X Y: rep_space):
	(F2MF (@inr X Y)) \has_continuous_realizer.
Proof.
exists (F2MF (@rinc X Y)); split; last exact: rinc_cont.
by apply frlzr_rlzr; split; first by exists (phi (some_question Y)).
Qed.

(*
Definition mfpp_rlzr (X Y X' Y': rep_space) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):=
	(fun (phipsi: names (rep_space_prod X X')) FphiGpsi =>
		FphiGpsi = name_pair (lprj FphiGpsi) (rprj FphiGpsi)
		/\
		(F ** G) (lprj phipsi, rprj phipsi)	(lprj FphiGpsi, rprj FphiGpsi)).

Definition mfpp_frlzr (X Y X' Y': rep_space) (F: (names X) -> (names Y)) (G: (names X') -> (names Y')):=
	(fun (phipsi: names (rep_space_prod X X')) => name_pair (F (lprj phipsi)) (G (rprj phipsi))).

Lemma prod_rec_fun (X Y X' Y': rep_space) (f: X -> Y) (g: X' -> Y'):
	f \is_recursive_function -> g \is_recursive_function -> (fun p => (f p.1, g p.2)) \is_recursive_function.
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
	exists (z, z'); split; first by exists (name_pair Fphi Gpsi).
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

Lemma prod_rec (X Y X' Y': rep_space) (f: X ->> Y) (g: X' ->> Y'):
	f \is_recursive -> g \is_recursive -> (f ** g) \is_recursive.
Proof.
move => [M Mrf] [N Nrg].
exists (mfpp_frlzr M N).
abstract by rewrite rrlzr_rlzr mfpp_frlzr_rlzr; apply prod_rlzr; rewrite -rrlzr_rlzr.
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

Lemma prod_space_rec_fun (X Y Z: rep_space) (f: Z -> X) (g: Z -> Y):
	f \is_recursive_function -> g \is_recursive_function ->
	exists (F: Z -> (rep_space_prod X Y)) (P:	F \is_recursive_function),
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

Lemma diag_rec_fun (X: rep_space):
	(@diag X) \is_recursive_function.
Proof. by exists (fun phi => name_pair phi phi). Defined.

Lemma diag_rec (X: rep_space):
	(F2MF (@diag X)) \is_recursive.
Proof. by exists (fun phi => name_pair phi phi); rewrite rrlzr_rlzr -frlzr_rlzr. Defined.*)
End SUMLEMMAS.
