From mathcomp Require Import all_ssreflect.
Require Import all_rs_base.
Require Import ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SPREADS.
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

(*
Lemma fun_sprd (X Y: rep_space) (someq: questions X): (X c-> Y) \is_spread.
Proof.
move => f psif prop.
pose psifacc := fix psif' n Lq := match Lq.1 with
	| nil => (nil, psif n Lq)
	| cons p K => match psif n (K, Lq.2) with
		| Some a => ((cons p K), psif n (K, Lq.2))
		| None => (K, psif n (K, Lq.2))
	end
end.
pose psif' := (fun Lq => match (psifacc (length Lq.1) Lq).2 with
	| Some a => a
	| None => inl someq
end).
suffices psif'prop: forall psi, (meval psif) \tightens (F2MF psi) -> eval (U psi) =~= eval (U psif').
	exists psif';	rewrite /delta/=/is_fun_name/=.
	by have [psi [tight psinf]]:= prop; rewrite -(psif'prop psi tight).
move => psi cmpt phi Fphi.
split => ass q'; have [n evl]:= ass q'; last first.
	exists n.
	have UFphiq: U_rec n psif' phi q' = inl (Fphi q').
		by rewrite /U in evl; case: (U_rec n psif' phi q') evl => // a [<-].
	move: evl => _.
	have cond: exists m, exists K,
		U_rec 0 psif' phi q' = inl (Fphi q')
		\/
		U_rec m psif' phi q' = inr K /\ U_step psif' phi q' K = inl (Fphi q').
	elim: n UFphiq.
		 move => U0; exists 0; exists nil; left.
		move => U0 exists
	move => n ih cond.
	case E: (U_rec n psif' phi q') => [a | L].
		suffices eq: a = (Fphi q').
		rewrite eq in E; exact: ih E.
		apply Some_inj.
		have <-: U psif' n.+1 phi q' = Some (Fphi q') by rewrite /U cond.
		have ineq: (n <= n.+1)%coq_nat by lia.
		apply esym; apply/ U_mon; first apply ineq.
		by rewrite /U E.
	exists n; exists L.
	split => //.
	by rewrite /= E in cond.

	rewrite /U_rec in Ua'.
	rewrite /U_step in Ua'.
	have: exists L, 
	rewrite /U_rec.
	rewrite /psif'.
	rewrite /U.
	have [cnt sur] := countable_questions X.
	have fd: ((flst phi (initial_segments.in_seg cnt n), q') \from_dom (F2MF psi)).
		exact: F2MF_tot psi ((flst phi (initial_segments.in_seg cnt n), q')).
	have [[a [k val]]]:= cmpt ((universal_machine.flst phi (initial_segments.in_seg cnt n), q')) fd.
	exists (max k n).
	admit.
admit.
Admitted.
*)

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
have fdsing: (f o (rep X)) \is_single_valued.
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
End SPREADS.
