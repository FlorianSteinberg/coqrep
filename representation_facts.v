(* This file provides an alternative formulation of represented spaces that saves
the input and output types of the names *)
From mathcomp Require Import all_ssreflect.
Require Import continuity universal_machine multi_valued_functions machines oracle_machines representations.
Require Import FunctionalExtensionality ClassicalFacts ClassicalChoice Psatz ProofIrrelevance.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section COMPUTABILITY_LEMMAS.

Lemma prod_cmpt_elt (X Y: rep_space) (x: X) (y: Y):
	x \is_computable_element -> y \is_computable_element -> (x, y) \is_computable_element.
Proof.
move => [phi phinx] [psi psiny].
by exists (fun q => match q with
	| inl qx => (phi qx, some_answer Y)
	| inr qy => (some_answer X, psi qy)
end).
Qed.

Lemma prec_fun_cmpt_elt (X Y: rep_space) (f: X -> Y) (x: X):
	x \is_computable_element -> f \is_prec_function -> (f x) \is_computable_element.
Proof.
move => [phi phinx] [M Mrf].
by exists (M phi); apply Mrf.
Defined.

Lemma cnst_fun_prec (X Y: rep_space) (y: Y):
	y \is_computable_element -> (fun x:X => y) \is_prec_function.
Proof. by move => [psi psiny]; exists (fun _ => psi). Qed.

Lemma prod_prec_fun (X Y X' Y': rep_space) (f: X -> Y) (g: X' -> Y'):
	f \is_prec_function -> g \is_prec_function -> (fun p => (f p.1, g p.2)) \is_prec_function.
Proof.
move => [M Mrf] [N Nrg].
exists (fun np q => match q with
	| inl q => (M (fun q' => (np (inl q')).1) q, some_answer Y')
	| inr q => (some_answer Y, N (fun q' => (np (inr q')).2) q)
end).
by move => phipsi [x x'] [phinx psinx']; split; [apply Mrf | apply Nrg].
Defined.

Lemma cmpt_elt_mon_cmpt (X Y: rep_space) (f: X c-> Y):
	f \is_computable_element -> (projT1 f) \is_monotone_computable.
Proof. move => [psiF comp]; exists (U psiF); split => //; exact: U_mon. Qed.

Lemma mon_cmpt_cmpt (X Y: rep_space) (f: X ->> Y):
	f \is_monotone_computable -> f \is_computable.
Proof. by move => [M [mon comp]]; exists M. Qed.

Lemma prec_fun_comp (X Y Z: rep_space) (f: X -> Y) (g: Y -> Z):
	f \is_prec_function -> g \is_prec_function
	-> forall h, (forall x, h x = g (f x)) -> h \is_prec_function.
Proof.
move => [M comp] [N comp'] h eq.
exists (fun phi => N (M phi)).
by move => phi x phinx; rewrite eq; apply comp'; apply comp.
Defined.

Lemma cmpt_fun_comp (X Y Z: rep_space) (f: X -> Y) (g: Y -> Z):
	f \is_prec_function -> g \is_prec_function
	-> forall h, (forall x, h x = g (f x)) -> h \is_prec_function.
Proof.
move => [M comp] [N comp'] h eq.
exists (fun phi => N (M phi)).
by move => phi x phinx; rewrite eq; apply comp'; apply comp.
Defined.

Lemma prec_fun_cmpt (X Y: rep_space) (f: X -> Y):
	f \is_prec_function -> f \is_computable_function.
Proof.
move => [N Nir]; exists (fun n phi q' => Some (N phi q')).
apply/ tight_trans; last by apply frlzr_rlzr; apply Nir.
apply tight_comp_r; apply: prec_F2MF_op 0.
Qed.

Lemma prec_cmpt (X Y:rep_space) (f: X ->> Y):
	f \is_prec -> f \is_computable.
Proof.
move => [N Nir]; exists (fun n phi q' => Some (N phi q')).
by apply/ tight_trans; first by apply/ tight_comp_r;	apply (prec_F2MF_op 0).
Qed.

Definition diag (X: rep_space):= (fun x => (x,x): rep_space_prod X X).

Lemma diag_hcr (X: rep_space):
	(F2MF (@diag X)) \has_continuous_realizer.
Proof.
exists (F2MF (fun phi => name_pair phi phi)).
split; first by apply frlzr_rlzr.
move => phi q.
case: q => q; by exists [:: q] => Fphi/= <- psi [eq _] Fpsi <-; rewrite /name_pair eq.
Qed.

Lemma diag_prec_fun (X: rep_space):
	(@diag X) \is_prec_function.
Proof.
by exists (fun phi => name_pair phi phi).
Defined.

Lemma diag_prec (X: rep_space):
	(F2MF (@diag X)) \is_prec.
Proof.
by exists (fun phi => name_pair phi phi); rewrite -frlzr_rlzr.
Qed.

Lemma diag_cmpt_fun (X: rep_space):
	(@diag X) \is_computable_function.
Proof.
apply prec_fun_cmpt; apply diag_prec_fun.
Qed.

Lemma diag_cmpt (X: rep_space):
	(F2MF (@diag X)) \is_computable.
Proof.
apply prec_cmpt; apply diag_prec.
Qed.
End COMPUTABILITY_LEMMAS.

Section PRODUCTS.
Lemma fst_prec (X Y: rep_space):
	(@fst X Y) \is_prec_function.
Proof.
by exists (@lprj X Y); move => phi x [phinx _].
Qed.

Lemma snd_prec (X Y: rep_space):
	(@snd X Y) \is_prec_function.
Proof.
by exists (@rprj X Y); move => phi x [_ phinx].
Qed.

Lemma fst_cont (X Y: rep_space):
	(F2MF (@fst X Y)) \has_continuous_realizer.
Proof.
exists (F2MF (@lprj X Y)).
split; first by apply frlzr_rlzr => phi x [phinx _].
move => phi q phifd.
exists ([::inl q]) => Fphi <- psi [/=coin _] Fpsi <-.
by rewrite /lprj coin.
Qed.

Lemma snd_cont (X Y: rep_space):
	(F2MF (@snd X Y)) \has_continuous_realizer.
Proof.
exists (F2MF (@rprj X Y)).
split; first by apply frlzr_rlzr => phi x [_ phinx].
move => phi q phifd.
exists ([::inr q]) => Fphi <- psi [/=coin _] Fpsi <-.
by rewrite /rprj coin.
Qed.

Lemma fst_cmpt (X Y: rep_space):
	(exist_fun (@fst_cont X Y)) \is_computable_element.
Proof.
exists (fun Lq => match Lq.1  with
	| nil => inl (inl Lq.2)
	| cons a K => inr a.2.1
end).
set psi:= (fun Lq => match Lq.1  with
	| nil => inl (inl Lq.2)
	| cons a K => inr a.2.1
end).
have eq: eval (U psi) =~= F2MF (@lprj X Y).
	move => phi Fphi.
	split => ass; last by rewrite -ass; exists 1.
	apply functional_extensionality => q.
	have [n val] := ass q.
	have U1: U psi 1 phi q = Some (lprj phi q) by trivial.
	apply Some_inj.
	rewrite -val.
	apply esym.
	apply/ U_mon; last apply U1.
	rewrite /pickle/=.
	by case: n val => // n val; lia.
rewrite /delta/=/is_fun_name/= eq.
by apply frlzr_rlzr => phi x [phinx _].
Qed.

Lemma snd_cmpt (X Y: rep_space):
	(exist_fun (@snd_cont X Y)) \is_computable_element.
Proof.
exists (fun Lq => match Lq.1  with
	| nil => inl (inr Lq.2)
	| cons a K => inr a.2.2
end).
set psi:= (fun Lq => match Lq.1  with
	| nil => inl (inr Lq.2)
	| cons a K => inr a.2.2
end).
have eq: eval (U psi) =~= F2MF (@rprj X Y).
	move => phi Fphi.
	split => ass; last by rewrite -ass; exists 1.
	apply functional_extensionality => q.
	have [n val] := ass q.
	have U1: U psi 1 phi q = Some (rprj phi q) by trivial.
	apply Some_inj.
	rewrite -val.
	apply esym.
	apply/ U_mon; last apply U1.
	rewrite /pickle/=.
	by case: n val => // n val; lia.
rewrite /delta/=/is_fun_name/= eq.
by apply frlzr_rlzr => phi x [_ phinx].
Qed.

Lemma prod_space_fun (X Y Z: rep_space) (f: Z -> X) (g: Z -> Y):
	exists (F: Z -> X * Y),
		(forall z, (F z).1 = f z)
		/\
		(forall z, (F z).2 = g z).
Proof.
by exists (fun z => (f z, g z)).
Qed.

Lemma prod_space_cont (X Y Z: rep_space) (f: Z c-> X) (g: Z c-> Y):
	exists (F: rep_space_cont_fun Z (rep_space_prod X Y)),
		((F2MF (@fst X Y)) o (projT1 F) =~= (projT1 f))
		/\
		((F2MF (@snd X Y)) o (projT1 F) =~= (projT1 g)).
Proof.
set F := (((projT1 f) ** (projT1 g)) o (F2MF (fun z => (z, z)))).
have Fsing: F \is_single_valued.
	apply comp_sing; last exact: F2MF_sing.
	apply mfpp_sing; split; [apply (projT2 f).1.1 | apply (projT2 g).1.1].
have Ftot: F \is_total.
	apply comp_tot; first exact: F2MF_tot.
	apply mfpp_tot; split; [apply (projT2 f).1.2 | apply (projT2 g).1.2].
have Fhcr: F \has_continuous_realizer.
	by apply comp_hcr; [apply diag_hcr | apply mfpp_hcr; [apply (projT2 f).2 | apply (projT2 g).2 ]].
exists (exist_c Fsing Ftot Fhcr).
split.
	rewrite /=/F F2MF_comp.
	rewrite sing_comp => //=; rewrite /mf_prod_prod/=; [ | | ].
			rewrite /F2MF => z x.
			split => [val| fzx [x' y] [fzx' gzy]]; last by rewrite ((projT2 f).1.1 z x x').
			have [x' fzx']:= (projT2 f).1.2 z.
			have [y gzy]:= (projT2 g).1.2 z.
			by rewrite -(val (x',y) (conj fzx' gzy)) => //.
		move => z p p' [fzp fzp'] [gzp gzp'].
		by apply injective_projections; [rewrite ((projT2 f).1.1 z p.1 p'.1) | rewrite ((projT2 g).1.1 z p.2 p'.2)].
	move => z.
	have [x fzx]:= (projT2 f).1.2 z.
	have [y gzy]:= (projT2 g).1.2 z.
	by exists (x, y).
rewrite /=/F F2MF_comp sing_comp => //=; rewrite /mf_prod_prod/=; [ | | ].
rewrite /F2MF => z y.
split => [val| gzy [x y'] [fzx gzy']]; last by rewrite ((projT2 g).1.1 z y y').
have [y' gzy']:= (projT2 g).1.2 z.
have [x fzx]:= (projT2 f).1.2 z.
by rewrite -(val (x,y') (conj fzx gzy')) => //.
	move => z p p' [fzp fzp'] [gzp gzp'].
	by apply injective_projections; [rewrite ((projT2 f).1.1 z p.1 p'.1) | rewrite ((projT2 g).1.1 z p.2 p'.2)].
move => z.
have [x fzx]:= (projT2 f).1.2 z.
have [y gzy]:= (projT2 g).1.2 z.
by exists (x, y).
Qed.

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

Lemma prod_space_cmpt (X Y Z: rep_space) (f: Z c-> X) (g: Z c-> Y):
	f \is_computable_element -> g \is_computable_element ->
	exists (F: Z c-> (rep_space_prod X Y)) (P:	F \is_computable_element),
		((F2MF (@fst X Y)) o (projT1 F) =~= (projT1 f))
		/\
		((F2MF (@snd X Y)) o (projT1 F) =~= (projT1 g)).
Proof.
move => [phi phinf] [psi psing].
have [F Fprop]:= prod_space_cont f g.
exists F; split; last exact: Fprop.
Admitted.
End PRODUCTS.

Section FUNCTION_SPACES.
Definition is_sprd (X: rep_space) := forall (x: X) (M: nat -> questions X -> option (answers X)),
	(exists phi, (meval M) \tightens (F2MF phi) /\ phi \is_name_of x) -> x \is_computable_element.
Notation "X '\is_spread'" := (is_sprd X) (at level 2).

Lemma prod_sprd (X Y: rep_space):
	X \is_spread -> Y \is_spread -> (rep_space_prod X Y) \is_spread.
Proof.
move => sprdx sprdy [x y] MN prop.
pose M n q := match MN n (inl q) with
	| some a => Some a.1
	| None => None
end.
pose N n q := match MN n (inr q) with
	| Some a => Some a.2
	| None => None
end.
have ex: exists phi, (meval M) \tightens (F2MF phi) /\ phi \is_name_of x.
	have [phipsi [comp [/=phinx psiny]]]:= prop.
	exists (lprj phipsi).
	split; last by apply phinx.
	move => q _.
	have qfd': (inl q) \from_dom (F2MF phipsi) by exists (phipsi (inl q)).
	split.
		have [a [n MNqa]]:= (comp (inl q) qfd').1.
		by exists a.1; exists n; rewrite /M MNqa.
	move => a [n Mqa]; rewrite /F2MF/lprj.
	rewrite /M in Mqa.
	have [a' [MNqa' eq]]: exists a', MN n (inl q) = some a' /\ a'.1 = a.
		by case: (MN n (inl q)) Mqa => // a' eq; exists a'; split => //; apply Some_inj.
	have val: (meval MN (inl q) a') by exists n.
	have:= ((comp (inl q) qfd').2 a' val).
	by rewrite /F2MF -eq => ->.
have:= sprdx x M ex.
have ex': exists psi, (meval N) \tightens (F2MF psi) /\ psi \is_name_of y.
	have [phipsi [comp [/=phinx psiny]]]:= prop.
	exists (rprj phipsi).
	split; last by apply psiny.
	move => q _.
	have qfd': (inr q) \from_dom (F2MF phipsi) by exists (phipsi (inr q)).
	split.
		have [a [n MNqa]]:= (comp (inr q) qfd').1.
		by exists a.2; exists n; rewrite /N MNqa.
	move => a [n Mqa]; rewrite /F2MF/rprj.
	rewrite /N in Mqa.
	have [a' [MNqa' eq]]: exists a', MN n (inr q) = some a' /\ a'.2 = a.
		by case: (MN n (inr q)) Mqa => // a' eq; exists a'; split => //; apply Some_inj.
	have val: (meval MN (inr q) a') by exists n.
	have:= ((comp (inr q) qfd').2 a' val).
	by rewrite /F2MF -eq => ->.
have:= sprdy y N ex'.
move => [psi psiny] [phi phinx].
by exists (name_pair phi psi).
Qed.

(*Lemma fun_sprd (X Y: rep_space) (someq: questions X): (X c-> Y) \is_spread.
Proof.
move => f psif prop.
pose psif' n q := fix psif' q := match q.1 with
	| nil => psif n q
	| cons p K => match psif n (K, q.2) with
		| Some a => cons p K
		| None => K
	end
end.
exists (fun p => match psif' (length p.1) p with
	| Some a => a
	| None => inl someq
end).
Admitted.*)

Lemma cmpt_fun_cmpt_elt (X Y: rep_space) (f: X ->> Y) (x: X) (y: Y):
	Y \is_spread -> f \is_monotone_computable -> f \is_single_valued
	-> x \is_computable_element -> f x y -> y \is_computable_element.
Proof.
move => sprd [M [mon comp]] sing [phi phinx] fxy.
have phifd: phi \from_dom (eval M).
	suffices phifd': (phi \from_dom (f o (delta (r:=X)))).
		by have [y' [[Mphi [MphiMphi asd]] prop]]:= (comp phi phifd').1; exists Mphi.
	exists y; split; first by exists x.
	move => x' phinx'; exists y.
	suffices: x = x' by move => <-.
	by apply/ (rep_sing X); first by apply phinx.
have Mop: (eval M) \is_computable_operator by exists M.
have Msing: (eval M) \is_single_valued by apply/ mon_sing_op.
have [N Nprop]:= (cmpt_op_cmpt phifd Mop Msing).
have qfd: forall q, q \from_dom (fun (q' : questions Y) (a' : answers Y) =>
  exists Ff : names Y, (eval M) phi Ff /\ Ff q' = a').
	by move => q; have [Mphi MphiMphi]:= phifd; exists (Mphi q); exists Mphi.
have Ntot: (meval N) \is_total by move => q; have [qfdN prop] := Nprop q (qfd q).
apply/ (sprd y N).
have [psi psiprop]:= choice (meval N) Ntot.
have eq: forall Mphi, (eval M) phi Mphi -> Mphi = psi.
	move => Mphi MphiMphi.
	apply/ Msing; first by apply MphiMphi.
	move => q'.
	have [n eq]:= MphiMphi q'.
	exists n;	rewrite eq; congr Some.
	have Npsi: (meval N) q' (psi q') by apply psiprop.
	have [Mpsi [MphiMpsi eq']]:= (Nprop q' (qfd q')).2 (psi q') Npsi.
	suffices: Mphi = Mpsi by move => ->.
	by apply/ Msing.
exists psi.
split.
	move => q _.
	split; first by exists (psi q); apply psiprop.
	move => a evl.
	have [Mphi [MphiMphi val]]:= (Nprop q (qfd q)).2 a evl.
	by rewrite -(eq Mphi).
have [Mphi MphiMphi] := phifd.
rewrite -(eq Mphi) => //.
have phiny: (f o (delta (r:=X))) phi y.
	split; first by exists x.
	move => x' phinx'.
	exists y.
	suffices: x' = x by move => ->.
	by apply/ (rep_sing X); first by apply phinx'.
have phifd': phi \from_dom (f o (delta (r:=X))) by exists y.
have [[fx [[Mpsi [MphiMpsi Mpsinfx]]] prop'] prop]:= comp phi phifd'.
have [fx' Mphinfx']:= prop' Mphi MphiMphi.
rewrite -(Msing phi Mphi Mpsi) in Mpsinfx => //.
have fdsing: (f o (\rep X)) \is_single_valued.
	apply/ comp_sing => //.
	by apply (rep_sing X).
suffices: fx = y by move => <-.
apply/ fdsing; last by apply phiny.
apply/prop.
split; first by exists Mphi.
move => Mphi' MphiMphi'.
exists fx.
by rewrite (Msing phi Mphi' Mphi).
Qed.

Lemma id_prec X:
	@is_prec X X (F2MF id).
Proof. by exists id; apply frlzr_rlzr. Defined.

Lemma id_prec_fun X:
	(@id (space X)) \is_prec_function.
Proof. by exists id. Defined.

Lemma id_cmpt X:
	@is_comp X X (F2MF id).
Proof. exact: (prec_cmpt (id_prec X)). Qed.

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

Definition id_fun X :=
	(exist_fun (id_hcr X)).

Lemma id_comp_elt X:
	(id_fun X) \is_computable_element.
Proof.
pose id_name p := match p.1: seq (questions X* answers X) with
		| nil => inl (p.2:questions X)
		| (q,a):: L => inr (a: answers X)
	end.
exists (id_name).
rewrite /delta /= /is_fun_name/=.
rewrite /is_rlzr id_comp.
rewrite -{1}(comp_id (\rep X)).
apply tight_comp_r.
apply/ (mon_cmpt_op); first exact: U_mon.
by move => phi q; exists 1.
Qed.

Definition fun_comp X Y Z (f: X c-> Y) (g: Y c-> Z) :(X c-> Z) :=
	exist_c (comp_sing (projT2 g).1.1 (projT2 f).1.1)
		(comp_tot (projT2 f).1.2 (projT2 g).1.2)
		(comp_hcr (projT2 f).2 (projT2 g).2).

Definition composition X Y Z := F2MF (fun fg => @fun_comp X Y Z fg.1 fg.2).

Lemma fcmp_sing X Y Z:
	(@composition X Y Z) \is_single_valued.
Proof. exact: F2MF_sing. Qed.

Lemma fcmp_tot X Y Z:
	(@composition X Y Z) \is_total.
Proof. exact: F2MF_tot. Qed.

(*
Lemma fcmp_mon_cmpt X Y Z:
	(@composition X Y Z) \is_monotone_computable.
Proof.
pose p1 psifg Lxqy:= (psifg (inl Lxqy)).1.
pose p2 psifg Lyqz:= (psifg (inr Lyqz)).2.
Admitted.
*)

Lemma iso_ref X:
	X ~=~ X.
Proof.
exists (id_fun X); exists (id_fun X).
exists (id_comp_elt X); exists (id_comp_elt X).
by split; rewrite comp_id.
Qed.

Lemma iso_sym X Y:
	X ~=~ Y -> Y ~=~ X.
Proof.
move => [f [g [fcomp [gcomp [bij1 bij2]]]]].
exists g; exists f.
by exists gcomp; exists fcomp.
Qed.

(*
Lemma iso_trans X Y Z (someqx: questions X) (someqz: questions Z):
	X ~=~ Y -> Y ~=~ Z -> X ~=~ Z.
Proof.
move => [f [g [fcomp [gcomp [bij1 bij2]]]]] [f' [g' [f'comp [g'comp [bij1' bij2']]]]].
exists (fun_comp f f').
exists (fun_comp g' g).
split.
	apply/ cmpt_fun_cmpt_elt; [apply: fun_sprd someqx | apply fcmp_mon_cmpt | apply fcmp_sing | | ].
		by apply prod_cmpt_elt; [apply fcomp | apply f'comp].
	by trivial.
split.
	by apply: (@cmpt_fun_cmpt_elt
		(rep_space_prod (Z c-> Y) (Y c-> X)) (Z c-> X)
		(@composition Z Y X)
		(g', g)
		(fun_comp g' g)
		(fun_sprd someqz)
		(fcmp_mon_cmpt Z Y X)
		(@fcmp_sing Z Y X)
		(prod_cmpt_elt g'comp gcomp)
		_
		).
rewrite /fun_comp/=.
split.
	rewrite -comp_assoc (comp_assoc (sval f') (sval f) (sval g)).
	by rewrite bij1 comp_id bij1'.
rewrite -comp_assoc (comp_assoc (sval g) (sval g') (sval f')).
by rewrite bij2' comp_id bij2.
Qed.
*)

Definition evaluation X Y (fx: (X c-> Y) * X):= (projT1 fx.1) fx.2.

Lemma eval_sing X Y:
	(@evaluation X Y) \is_single_valued.
Proof.
move => [f x] y z fxy fxz.
have sing:= (projT2 f).1.1.
apply/ sing; [apply fxy| apply fxz].
Qed.

Lemma eval_tot X Y:
	(@evaluation X Y) \is_total.
Proof.
move => [f x].
have [y fxy]:= ((projT2 f).1.2 x).
by exists y.
Qed.

Lemma eval_rlzr X Y:
	(eval (fun n psiphi q => U (lprj psiphi) n (rprj psiphi) q)) \is_realizer_of (@evaluation X Y).
Proof.
set R:=(fun n psiphi q => U (lprj psiphi) n (rprj psiphi) q).
move => psiphi [y [[[f x] [[/=psinf phinx] fxy]] prop]].
rewrite /is_fun_name/= in psinf.
have eq: (eval (U (lprj psiphi))) (rprj psiphi) = (eval R) psiphi by trivial.
have Rsing: (oeval R) \is_single_valued.
	apply mon_sing_op => /= n m phi q' a' nlm Rnphiqa.
	apply/ U_mon; [ apply nlm | apply Rnphiqa ].
have [Fpsiphi val]:= (@rlzr_dom _ _ (sval f) _ psinf (rprj psiphi) x phinx ((projT2 f).1.2 x)).
have Fpsiphiny: Fpsiphi \is_name_of y.
	by apply/ rlzr_val_sing; [ apply (projT2 f).1.1 | apply psinf | apply phinx | apply fxy | ].
split.
	exists y; split; first by exists Fpsiphi.
	move => psi eval; rewrite (Rsing psiphi psi Fpsiphi) => //; exists y.
	by apply/ rlzr_val_sing; [ apply (projT2 f).1.1 | apply psinf | apply phinx | apply fxy | ].
move => y' [[Fphi [val' Fphiny]]cond].
split.
	exists (f,x); split => //.
	rewrite (Rsing psiphi Fphi Fpsiphi) in Fphiny => //.
	by rewrite (rep_sing Y Fpsiphi y' y).
move => [f' x'] [psinf' phinx'].
exists y; rewrite (rep_sing (X c-> Y) (lprj psiphi) f' f) => //.
by rewrite (rep_sing X (rprj psiphi) x' x).
Qed.

Lemma eval_cmpt X Y:
	(@evaluation X Y) \is_computable.
Proof.
exists (fun n psiphi q => U (lprj psiphi) n (rprj psiphi) q).
exact: eval_rlzr.
Qed.

(*Lemma eval_hcr X Y:
	(@evaluation X Y) \has_continuous_realizer.
Proof.
exists (eval (fun n psiphi q => U (lprj psiphi) n (rprj psiphi) q)).
split; first exact: eval_rlzr.
move => psiphi q [Fpsiphi val].
have [n evl] := val q.
Admitted.*)

End FUNCTION_SPACES.


































