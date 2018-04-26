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
split; rewrite lprj_pair rprj_pair/=;
	[apply (lpsiprop (lprj phi)) | apply (rpsiprop (rprj phi))] => // q _ .
	have lqfd: (inl q) \from_dom (F2MF phi) by apply F2MF_tot.
	have [[[la ra] [/=n evl]] prp]:= tight (inl q) lqfd.
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
have phiv: (rep Y) o (eval M) phi y'.
	split; first by exists Mphi.
	move => psi evl; by apply phifd'.
have [[x' [phinx' fx'y']]cnd]:= prp y' phiv.
rewrite (rep_sing X phi x' x) in fx'y' => //.
exists y'; split => //.
apply/ (projT2 (sprd (fun n => M n phi)) Mphi y') => //.
move => q _.
have [n evl]:= MphiMphi q.
split; first by exists (Mphi q); exists n.
move => a [/= m eq].
apply Some_inj; rewrite /F2MF.
case E: (m <= n).
	rewrite -evl.
	apply/ Mmon; last exact eq.
	by apply/ leP; rewrite /pickle/=E.
rewrite -eq; apply esym.
apply/ Mmon; last exact evl.
rewrite /pickle/=.
move /leP: E; lia.
Qed.

Lemma cmpt_fun_cmpt_elt (X Y: rep_space) (f: X ->> Y) (x: X) (y: Y):
	Y \is_spread -> f \is_monotone_computable -> f \is_single_valued
	-> x \is_recursive_element -> f x y -> y \is_recursive_element.
Proof.
move => sprd mon sing [phi phinx] fxy.
have xfd: x \from_dom f by exists y.
have [M Mprop]:= sprd_cmpt_rec sprd mon.
exists (M phi).
have [y' [Mphiny' fxy']]:= Mprop phi x phinx xfd.
by rewrite (sing x y y').
Qed.

(*
Lemma fun_sprd (X Y: rep_space) (someq: questions X): (X c-> Y) \is_spread.
Proof.
move => M.
pose Macc := fix Macc n Lq := match Lq.1 with
	| nil => (nil, M n Lq)
	| cons p K => match M n (K, Lq.2) with
		| Some a => ((cons p K), M n (K, Lq.2))
		| None => (K, M n (K, Lq.2))
	end
end.
pose psi := (fun Lq => match (Macc (length Lq.1) Lq).2 with
	| Some a => a
	| None => inl someq
end).
exists psi => phi f Mcomp phinf.
rewrite /delta/=/is_fun_name/=.
suffices <-: eval (U phi) =~= eval (U psi) by trivial.
move => phi' Fphi'.
split => ass q.
	have [n val]:= ass q.
	admit.
have [n val] := ass q.
exists n.
rewrite /psi in val.
Admitted.
*)

End SPREADS.
