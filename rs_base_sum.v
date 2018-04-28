From mathcomp Require Import all_ssreflect.
Require Import all_core rs_base rs_base_prod rs_base_facts.
Require Import FunctionalExtensionality.

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

Canonical rep_space_sum X Y := @make_rep_space
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

Definition mfss_rlzr (X Y X' Y': rep_space) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):=
	fun (phi: names (rep_space_sum X X')) FGphi =>
		match phi (some_question X, some_question X') with
			| inl y => F (lslct phi) (lslct FGphi) /\ linc (lslct FGphi) = FGphi
			| inr y' => G (rslct phi) (rslct FGphi) /\ rinc (rslct FGphi) = FGphi
		end.

Definition mfss_frlzr X Y X' Y' (F: (names X) -> (names Y)) (G: (names X') -> (names Y')):=
	fun (phi: names (rep_space_sum X X')) =>
	match phi (some_question X, some_question X') with
		| inl y => linc (F (lslct phi))
		| inr y' => rinc (G (rslct phi))
	end.

Lemma mfss_rec_fun (X Y X' Y': rep_space) (f: X -> Y) (g: X' -> Y'):
	f \is_recursive_function -> g \is_recursive_function -> (fun xx' => match xx' with
		| inl x => inl (f x)
		| inr x' => inr (g x')
	end) \is_recursive_function.
Proof.
move => [M /= Mrf] [N /= Nrg].
exists (mfss_frlzr M N).
move => phi.
case => [x [[a eq] phinx] |x' [[a eq] phinx']]; rewrite /mfss_frlzr/=.
	split; rewrite eq; first by exists (M (lslct phi) (some_question _)).
	exact (Mrf (lslct phi) x phinx).
split; rewrite eq; first by exists (N (rslct phi) (some_question _)).
exact (Nrg (rslct phi) x' phinx').
Defined.

Lemma mfss_frlzr_rlzr (X Y X' Y': rep_space) (F: (names X) -> (names Y)) (G: (names X') -> (names Y')):
	F2MF (mfss_frlzr F G) =~= mfss_rlzr (F2MF F) (F2MF G).
Proof.
split; rewrite /F2MF/mfss_rlzr/mfss_frlzr.
	by case (s (some_question X, some_question X')) => _ <-.
by case (s (some_question X, some_question X')) => _ [->].
Qed.

Definition mfss_fun X X' Y Y' (f: X -> Y) (g: X' -> Y') xx':= match xx' with
	| inl x => inl (f x)
	| inr x' => inr (g x')
end.

Lemma mfss_mfss_fun X X' Y Y' (f: X -> Y) (g: X' -> Y'):
	F2MF (mfss_fun f g) =~= mfss (F2MF f) (F2MF g).
Proof.
split; rewrite /F2MF; first by case: s => a <-.
by case: s => a; case: t => // a1 <-.
Qed.

Lemma mfss_rlzrs (X Y X' Y': rep_space) (f: X ->> Y) (g: X' ->> Y') F G:
	F \is_realizer_of f -> G \is_realizer_of g -> (mfss_rlzr F G) \is_realizer_of (mfss f g).
Proof.
move => Frf Grg phi [].
case => y [[]].
	case => [x [[[a eq] phinx] /= fxy] prp | x']; last by rewrite {1}/mfss/= => [][].
	have fd: (lslct phi) \from_dom (f o (delta (r:=X))).
		exists y; split; first by exists x.
		by intros; rewrite (rep_sing _ (lslct phi) s x) => //; exists y.
	have [[y' [[psi [Fphipsi psiny']]] prop cnd]]:= Frf (lslct phi) fd.
	split.
		exists (inl y');split.
			exists (linc psi); split; rewrite /mfss_rlzr; first by rewrite eq.
			by split; [exists (psi (some_question Y)) | rewrite linc_lslct].
		move => psi'; rewrite /mfss_rlzr eq => [[b c]].
		have [y'' name]:= prop (lslct psi') b; exists (inl y'').
		by split; first by exists (lslct psi' (some_question Y)); rewrite -c.
	case => y'' [[psi'' [val /= [[a' eq'] name]] cond]]; last first.
		move: val; rewrite /mfss_rlzr eq => [[val inc]].
		by rewrite -inc /linc/= in eq'.
	move: val; rewrite /mfss_rlzr eq => [[val inc]].
	split; last first.
		case => x'' [[a'' eq''] name']; last by rewrite eq'' in eq.
		rewrite (rep_sing _ (lslct phi) x'' x) => //.
		by exists (inl y).
	exists (inl x); split; first by split; first by exists a.
	have phiy'': (delta (r:=Y)) o F (lslct phi) y''.
		by split; first by exists (lslct psi'').
	have [[this [tmpnm con]]]:= cnd y'' phiy''.
	by rewrite (rep_sing X (lslct phi) x this).
case => [x' | x [[[a eq] phinx] /= fxy] prp]; first by rewrite {1}/mfss/= => [][].
have fd: (rslct phi) \from_dom (g o (delta (r:=X'))).
	exists y; split; first by exists x.
	by intros; rewrite (rep_sing _ (rslct phi) s x) => //; exists y.
have [[y' [[psi [Fphipsi psiny']]] prop cnd]]:= Grg (rslct phi) fd.
split.
	exists (inr y'); split.
		exists (rinc psi); split; rewrite /mfss_rlzr; first by rewrite eq.
		by split; [exists (psi (some_question Y')) | rewrite rinc_rslct].
	move => psi'; rewrite /mfss_rlzr eq => [[b c]].
	have [y'' name]:= prop (rslct psi') b; exists (inr y'').
	by split; first by exists (rslct psi' (some_question Y')); rewrite -c.
case => y'' [[psi'' [val /= [[a' eq'] name]] cond]].
	move: val; rewrite /mfss_rlzr eq => [[val inc]].
	by rewrite -inc /rinc/= in eq'.
move: val; rewrite /mfss_rlzr eq => [[val inc]].
split; last first.
	case => x'' [[a'' eq''] name']; first by rewrite eq'' in eq.
	rewrite (rep_sing _ (rslct phi) x'' x) => //.
	by exists (inr y).
exists (inr x).
split; first by split; first by exists a.
have phiy'': (delta (r:=Y')) o G (rslct phi) y''.
	by split; first by exists (rslct psi'').
have [[this [tmpnm con]]]:= cnd y'' phiy''.
by rewrite (rep_sing X' (rslct phi) x this).
Qed.

Lemma mfss_rec (X Y X' Y': rep_space) (f: X ->> Y) (g: X' ->> Y'):
	f \is_recursive -> g \is_recursive -> (mfss f g) \is_recursive.
Proof.
move => [M Mrf] [N Nrg].
exists (mfss_frlzr M N).
abstract by rewrite rrlzr_rlzr mfss_frlzr_rlzr; apply mfss_rlzrs; rewrite -rrlzr_rlzr.
Defined.

(*
Lemma mfss_cont (X Y X' Y': rep_space) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):
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
Qed.*)

Lemma sum_space_fun (X Y Z: rep_space) (f: X -> Z) (g: Y -> Z):
	exists! (F: X + Y -> Z),
		(forall x, F (inl x) = f x)
		/\
		(forall y, F (inr y) = g y).
Proof.
exists (fun xy => match xy with
	| inl x => f x
	| inr y => g y
end).
abstract by split => // F [eq eq']; apply functional_extensionality => [[x | y]].
Defined.

Lemma sum_space_rec_fun (X Y Z: rep_space) (f: X -> Z) (g: Y -> Z):
	f \is_recursive_function -> g \is_recursive_function ->
	exists (F: X + Y -> Z) (P:	F \is_recursive_function),
		((F2MF F) o (F2MF (@inl X Y)) =~= (F2MF f))
		/\
		((F2MF F) o (F2MF (@inr X Y)) =~= (F2MF g)).
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
