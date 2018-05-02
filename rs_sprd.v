From mathcomp Require Import all_ssreflect.
Require Import all_rs_base.
Require Import ClassicalChoice Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SPREADS.
Definition sprd (X: rep_space) := forall (M: nat -> _ -> _),
	{psi | forall phi (x: X), M \computes (F2MF phi) -> phi \is_name_of x -> psi \is_name_of x}.
Notation "X '\is_spread'" := (sprd X) (at level 2).

Lemma prod_sprd (X Y: rep_space):
	X \is_spread -> Y \is_spread -> (rep_space_prod X Y) \is_spread.
Proof.
move => sprdx sprdy MN.
pose M n q := match MN n (inl q) with
	| some a => Some a.1
	| None => None
end.
pose N n q := match MN n (inr q) with
	| Some a => Some a.2
	| None => None
end.
have [lpsi lpsiprop]:= sprdx M.
have [rpsi rpsiprop]:= sprdy N.
exists (name_pair lpsi rpsi) => [phi [x y] tight [/=phinx phiny]] .
split; [apply (lpsiprop (lprj phi)) | apply (rpsiprop (rprj phi))] => // q _ .
	have [ | [[la ra] [/=n evl]] prp]:= tight (inl q) _; first by apply F2MF_tot.
	split; first by exists la; exists n; rewrite /M evl.
	move => a [/=m val]; rewrite /M in val.
	case E: (MN m (inl q)) => [a' | ]; last by rewrite E in val.
	rewrite E in val; have ev: meval MN (inl q) a' by exists m.
	by rewrite /F2MF/lprj; have ->:= (prp a' ev); apply Some_inj.
have lqfd: (inr q) \from_dom (F2MF phi) by apply F2MF_tot.
have [[[la ra] [/=n evl]] prp]:= tight (inr q) lqfd.
split; first by exists ra; exists n; rewrite /N evl.
move => a [/=m val]; rewrite /N in val.
case E: (MN m (inr q)) => [a' | ]; last by rewrite E in val.
rewrite E in val; have ev: meval MN (inr q) a' by exists m.
by rewrite /F2MF/rprj; have ->:= (prp a' ev); apply Some_inj.
Qed.

Lemma sprd_cmpt_rec (X Y: rep_space) (f: X ->> Y):
	Y \is_spread -> f \is_monotone_computable -> f \is_recursive.
Proof.
move => sprd [M [Mmon Mprop]].
exists (fun phi => projT1 (sprd (fun n:nat => M n phi))).
move => phi x phinx [y fxy].
have phifd: phi \from_dom (f o (rep X)).
	exists y;	split; first by exists x.
	by move => x' phinx'; rewrite (rep_sing X phi x' x); first by exists y.
have [[y' [[Mphi [MphiMphi Mphiny']]]]phifd' prp]:= Mprop phi phifd.
have [ | [x' [phinx' fx'y']]cnd]:= prp y' _.
	by split; [exists Mphi | apply phifd'].
exists y'; split; last by rewrite (rep_sing X phi x x').
apply/ (projT2 (sprd (fun n => M n phi)) Mphi y') => // q _.
have [n evl]:= MphiMphi q.
split; first by exists (Mphi q); exists n.
by move => a [/= m eq]; apply /(eq_mon evl eq).
Qed.

Lemma cmpt_fun_cmpt_elt (X Y: rep_space) (f: X ->> Y) (x: X) (y: Y):
	Y \is_spread -> f \is_monotone_computable -> f \is_single_valued
	-> x \is_recursive_element -> f x y -> y \is_recursive_element.
Proof.
move => sprd mon sing [phi phinx]; have [M Mprop]:= sprd_cmpt_rec sprd mon; exists (M phi).
by have [ | y' [Mphiny' fxy']]:= Mprop phi x phinx _; [exists y | rewrite (sing x y y')].
Qed.

Lemma fun_sprd (X Y: rep_space): (X c-> Y) \is_spread.
Proof.
move => N.
have [K Kprop]:= cmpt_mon_cmpt_strong (answers (X c-> Y)) (questions (X c-> Y)) nat_countType.
set M := K N.
move: Kprop (Kprop N) => _ [Mmon Mprop].
rewrite -/M in Mmon Mprop.
pose M' := fix M' n L q {struct L} := match L with
	| nil => M n (nil, q)
	| cons p K => match M' n K q with
		| Some a => M n (L, q)
		| None => M' n K q
	end
end.
pose psi' Lq := match M' (length Lq.1) Lq.1 Lq.2 with
	| Some a => a
	| None => inl (some_question _)
end.
exists psi' => psi f Ncomp psinf.
move: Ncomp Mprop (Mprop (F2MF psi) Ncomp) => _ _ /mon_cmpt_fun Mcmpt.
specialize (Mcmpt Mmon).
rewrite /delta/=/is_fun_name/=.
have <-: eval (U psi) =~= eval (U psi') => //.
move => phi' Fphi'.
split => ass q; have [/=n val]:= ass q.
elim: n val => [<- | ].
	have [/=m evl]:= Mcmpt (nil, q).
	exists m.
	elim: m evl; first by rewrite /U/U_rec/U_step/psi'/= => ->.
	move => m ih /=eq.
	rewrite /U.
	replace (U_rec m.+1 psi' phi' q) with (match (U_rec m psi' phi' q) with
		| inl a' => inl a'
		| inr L => U_step psi' phi' q L
	end) by trivial.
	rewrite /U in ih.
	case: (U_rec m psi' phi' q) ih.
		move => a -> //.
		admit.
	move => L <-.
	case E: (U_step psi' phi' q L).
	rewrite /U_step/psi' in E.
	rewrite ih.
		
	case E: (U_step psi phi' q [::]); case E': (U_rec m.+1 psi' phi' q) => //.
		rewrite /U_rec in E'.
		
	case E: (U_rec m.+1 psi' phi' q).
	rewrite ih.
	rewrite /psi'.
	exists n.
	elim: n val => [ | ].
	rewrite /U/U_rec/U_step/psi'/=.
	rewrite /psi'.
	have 
	admit.
have [n val] := ass q.
exists n.
rewrite /psi in val.
Admitted.

End SPREADS.
