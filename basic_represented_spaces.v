(* This file provides an alternative formulation of represented spaces that saves
the input and output types of the names *)
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions continuity machines oracle_machines.
Require Import representations representation_facts baire_space universal_machine.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BASIC_REP_SPACES.
Inductive one := star.

Definition id_rep S := (fun phi (s: S) => phi star = s).

Lemma id_rep_is_rep:
	forall S: Type, (@id_rep S) \is_representation.
Proof.
by split => [ phi s s' eq eq' | s ]; [rewrite -eq -eq' | exists (fun str => s)].
Qed.

Lemma one_count:
	one \is_countable.
Proof. by exists (fun n => star); move => star; exists 0%nat; elim star. Qed.

Canonical rep_space_one := @make_rep_space
	one
	one
	one
	(@id_rep one)
	star
	one_count
	one_count
	(@id_rep_is_rep one).

Lemma nat_count:
	nat \is_countable.
Proof. exists (fun n:nat => n); move => n; by exists n. Qed.

Canonical rep_space_nat := @make_rep_space
	nat
	one
	nat
	(@id_rep nat)
	1%nat
	one_count
	nat_count
	(id_rep_is_rep nat).

Inductive Sirp := top | bot.

Definition rep_S phi s :=
	(exists n:nat, phi n = Some star) <-> s = top.

Lemma rep_S_is_rep:
 rep_S \is_representation.
Proof.
split => [ phi s s' [imp imp'] [pmi pmi'] | s].
	case (classic (exists n, phi n = Some star)) => ex; first by rewrite (imp ex) (pmi ex).
	case E: s; first by exfalso; apply ex; apply (imp' E).
	apply NNPP => neq.
	have eq: s' = top by case Q: s' => //; exfalso; apply neq.
	by apply ex; apply pmi'.
case s; last by exists (fun _ => None); split => // [[n ev]].
by exists (fun _ => some star); split => // _; by exists 0.
Qed.

Lemma option_one_count:
	(option one) \is_countable.
Proof.
by exists (fix c n := match n with
	| 0 => Some star
	| S n' => None
end) => s; case: s; [exists 0; elim: a| exists 1].
Qed.

Canonical rep_space_S := @make_rep_space
	(Sirp)
	(nat)
	(option one)
	(rep_S)
	(None)
  (nat_count)
  (option_one_count)
  (rep_S_is_rep).
End BASIC_REP_SPACES.

Section BASIC_CONSTRUCTIONS.
Definition rep_usig_prod (X: rep_space) phi (xn: nat -> X):=
	forall n, (fun p => (phi (n,p))) \is_name_of (xn n).

Lemma rep_usig_prod_is_rep (X: rep_space):
	(@rep_usig_prod X) \is_representation.
Proof.
split => [ phi xn yn phinxn phinyn | xn ].
	apply functional_extensionality => n.
	by apply/ (rep_sing X); [apply phinxn | apply phinyn ].
pose R n phi:= phi \is_name_of (xn n).
have Rtot: R \is_total.
	by move => n; have [phi phinx]:= (rep_sur X (xn n)); exists phi.
by have [phi phinxn]:= choice R Rtot; exists (fun p => phi p.1 p.2).
Qed.

Canonical rep_space_usig_prod (X: rep_space) := @make_rep_space
	(nat -> space X)
	(nat * questions X)
	(answers X)
	(@rep_usig_prod X)
	(some_answer X)
  (prod_count nat_count (countable_questions X))
  (countable_answers X)
  (@rep_usig_prod_is_rep X).

Definition rep_opt X phi x := match x with
	| some x => (phi (inl star)).1 = some star
		/\
		 @delta X (fun q => (phi (inr q)).2) x
	| None => (phi (inl star)).1 = None
end.

Lemma rep_opt_sing X:
	(@rep_opt X) \is_single_valued.
Proof.
move => phi x y phinx phiny.
case: x phinx.
	case: y phiny; last by move => /= Nope a [eq phina]; rewrite eq in Nope.
	move => a/= [eq phina] b [eq' phinb].
	by rewrite (rep_sing X (fun q => (phi (inr q)).2) a b).
case: y phiny => //.
move => /= a [eq phina] Nope.
by rewrite eq in Nope.
Qed.

Lemma rep_opt_rep X:
	(@rep_opt X) \is_representation.
Proof.
split; first exact: rep_opt_sing.
move => x.
case x => [a | ].
	have [phi phinx]:= (rep_sur X a).
	by exists (fun q => match q with
		|inl str => (some star, some_answer X)
		|inr q => (some star, phi q)
	end).
by exists (fun q => (None, some_answer X)).
Qed.

Lemma option_count T:
	T \is_countable -> (option T) \is_countable.
Proof.
move => [cnt sur].
exists (fun n => match n with
	| 0 => None
	| S n' => Some (cnt n')
end).
move => x.
case x; last by exists 0.
move => a.
have [n cntna]:= sur a.
by exists (S n); rewrite cntna.
Qed.

Canonical rep_space_opt (X: rep_space) := @make_rep_space
	(option X)
	(one + questions X)
	(option one * answers X)
	(@rep_opt X)
	((None, some_answer X))
	(sum_count one_count (countable_questions X))
	(prod_count (option_count one_count) (countable_answers X))
	(@rep_opt_rep X).

Lemma rs_prec_option_rec_inv (X: rep_space) (Y: rep_space) (f: option X -> Y):
	f \is_prec_function
	->
	(fun a => f (some a)) \is_prec_function * (f None) \is_computable_element.
Proof.
move => [M Mcmpt].
split.
exists (fun phi => (M (fun q => match q with
	| inl str => (some star, some_answer X)
	| inr q => (some star, phi q)
	end))).
by move => phi x phinx; apply Mcmpt.
exists (M (fun _ => (None, some_answer X))).
by apply Mcmpt.
Qed.

Lemma rs_prec_option_rec (X: rep_space) (Y: rep_space) (f: option X -> Y):
	(fun a => f (some a)) \is_prec_function * (f None) \is_computable_element
	-> f \is_prec_function.
Proof.
move => [[M Mcmpt] [N Ncmpt]].
exists (fun phi => match (phi (inl star)).1 with
	| None => N
	| Some str => M (fun q => (phi (inr q)).2)
end).
move => phi x phinx.
case: x phinx => [/=a [eq phina] |/= Nope].
by rewrite eq; apply Mcmpt.
by rewrite Nope; apply Ncmpt.
Qed.

Definition N_XN_lst
	(X: rep_space)
	(n: rep_space_nat)
	(an: rep_space_usig_prod X):= map an (iota 0 n).

Definition NXN_lst X 
	(nan: rep_space_opt (rep_space_prod rep_space_nat (rep_space_usig_prod X)))
	:= match nan with
		| None => [::]
		| some nan => N_XN_lst nan.1 nan.2
	end.

Definition rep_list (X: rep_space) := (F2MF (@NXN_lst X)) o (@delta _).

Lemma rep_list_sing X:
	(@rep_list X) \is_single_valued.
Proof.
apply comp_sing; last exact (rep_sing _).
exact: F2MF_sing.
Qed.

Lemma map_nth_iota T (x:T) p:
	[seq nth x p n0 | n0 <- iota 0 (size p)] = p.
Proof.
apply (@eq_from_nth T x); rewrite size_map size_iota => //.
move => k E.
rewrite (@nth_map nat 0%nat T x (fun n => nth x p n) k (iota 0 (size p))); last by rewrite size_iota.
by rewrite seq.nth_iota => //.
Qed.

Lemma rep_list_rep X:
	(@rep_list X) \is_representation.
Proof.
split; first exact: rep_list_sing.
move => L.
elim L.
	exists (fun _ => (None, some_answer (rep_space_prod rep_space_nat (rep_space_usig_prod X)))).
	by rewrite /rep_list/=; split; [exists None | move => s names; apply: F2MF_tot].
move => x K [/=phi [[/=y [phiny yK]] _]].
rewrite /F2MF in yK.
set n := size K.
have [psi psina]:= rep_sur X x.
set nK := map (fun n => (fun q => (phi (inr (inr (n, q)))).2.2)) (iota 0 n).
exists (fun q => match q with
	| inl str => (some star, (0, some_answer X))
	| inr q' => match q' with
		| inl str => (some star, (S n, some_answer X))
		| inr p => (some star, (some_answer rep_space_nat, match p.1 with
			| 0 => psi p.2
			| S n => nth psi nK n p.2
		end))
	end
end).
rewrite /rep_list/=.
split; last by move => a b; exact: F2MF_tot.
exists (Some (S n, (fun n => nth x (x:: K) n))).
rewrite /rep_opt/=/prod_rep/=/id_rep/=/rep_usig_prod/=;
rewrite /lprj/=/rprj/=/mf_prod_prod/=/NXN_lst/F2MF/=.
split.
	split => //.
	split => //.
	move => k.
	case E: (k <= n); rewrite /n in E.
		case E': k => [ | m]//=.
		rewrite /rep_opt in phiny.
		case: y phiny yK.
			move => nan [/=sm name] nanK.
			rewrite /nK.
			rewrite /N_XN_lst in nanK.
			rewrite /prod_rep/=/id_rep/=/lprj/rprj/=/mf_prod_prod/=/rep_usig_prod/= in name.
			move: name => [nnan prop].
			have ineq: m < n by rewrite /n; apply /leP; rewrite -E'; apply /leP; rewrite E.
			rewrite (nth_map 0); last by rewrite size_iota.
			specialize (prop m); rewrite nth_iota => //.
			suffices ->: (nth x K m) = nan.2 m by trivial.
			rewrite -nanK/=.
			have -> : nan.1 = n by rewrite /n -nanK size_map size_iota.
			rewrite (nth_map 0); last by rewrite size_iota.
			by rewrite nth_iota.
		rewrite /NXN_lst/N_XN_lst => _ eq; rewrite -eq/= in E.
		have k0: k= 0 by apply /eqP; rewrite -leqn0 E.
		by rewrite k0 in E'.
	case: k E => // m E.
	by rewrite !nth_default => //=; [rewrite ltnS | rewrite /nK size_map size_iota/n]; rewrite leqNgt E.
rewrite /N_XN_lst/n.
replace (size K).+1 with (size ( x:: K)) by trivial.
by rewrite map_nth_iota.
Qed.

Canonical rep_space_list (X: rep_space) := @make_rep_space
	(list X)
	_
	_
	(@rep_list X)
	(Some star, (some_answer rep_space_nat, some_answer X))
	(countable_questions (rep_space_opt (rep_space_prod rep_space_nat (rep_space_usig_prod X))))
	(countable_answers (rep_space_opt (rep_space_prod rep_space_nat (rep_space_usig_prod X))))
	(@rep_list_rep X).

Lemma cons_prec_fun (X: rep_space):
	(fun p => cons (p.1: X) p.2) \is_prec_function.
Proof.
pose sK (phi: names (rep_space_prod X (rep_space_list X))) := match (rprj phi (inl star)).1 with
	| Some str => (rprj phi (inr (inl star))).2.1
	| None => 0
end.
pose nK (phi: names (rep_space_prod X (rep_space_list X))) :=
	map (fun n => (fun q => (rprj phi (inr (inr (n, q)))).2.2)) (iota 0 (sK phi)).
exists (fun (phi: names (rep_space_prod X (rep_space_list X))) q => match q with
	| inl str => (some star, (0, some_answer X))
	| inr q' => match q' with
		| inl str => (some star, (S (sK phi), some_answer X))
		| inr p => (some star, (some_answer rep_space_nat, match p.1 with
			| 0 => lprj phi p.2
			| S n => nth (lprj phi) (nK phi) n p.2
		end))
	end
end).
move => phi [x K] [/=phinx [[y [/=phiny yK]] _]].
rewrite /rep_list/=.
split; last by move => a b; exact: F2MF_tot.
exists (Some (S (size K), (fun n => nth x (x:: K) n))).
rewrite /rep_opt/=/prod_rep/=/id_rep/=/rep_usig_prod/=;
rewrite /lprj/=/rprj/=/mf_prod_prod/=/NXN_lst/F2MF/=.
have eq: sK phi = size K.
	rewrite /rep_opt in phiny.
	case: y phiny yK; last by rewrite /sK/F2MF/NXN_lst/N_XN_lst => -> <-.
	move => nan [/=sm name] nanK.
	rewrite /nK.
	rewrite /N_XN_lst in nanK.
	rewrite /prod_rep/=/id_rep/=/lprj/rprj/=/mf_prod_prod/=/rep_usig_prod/= in name.
	move: name => [nnan prop].
	rewrite /sK sm nnan -nanK /NXN_lst/N_XN_lst.
	by rewrite size_map size_iota.
split.
	split => //.
	split; first by rewrite eq.
	move => k.
	case E: (k <= (size K)).
		case E': k => [ | m]//=.
		rewrite /delta/rep_opt/= in phinx.
		case: y phiny yK.
			move => nan [/=sm name] nanK.
			rewrite /nK.
			rewrite /N_XN_lst in nanK.
			rewrite /prod_rep/=/id_rep/=/lprj/rprj/=/mf_prod_prod/=/rep_usig_prod/= in name.
			move: name => [nnan prop].
			have ineq: m < size K by rewrite /sK; apply /leP; rewrite -E'; apply /leP; rewrite E.
			rewrite /F2MF/NXN_lst/N_XN_lst/= in nanK.
			rewrite (nth_map 0); last by rewrite size_iota eq.
			specialize (prop m); rewrite nth_iota; last by rewrite eq.
			suffices ->: (nth x K m) = nan.2 m by trivial.
			rewrite -nanK/= /N_XN_lst.
			have -> : nan.1 = sK phi by rewrite /sK sm.
			rewrite (nth_map 0); last by rewrite size_iota eq.
			by rewrite nth_iota; last by rewrite eq.
		rewrite /NXN_lst/N_XN_lst/F2MF/= => name eq'.
		rewrite -eq'/= in E.
		have k0: k= 0 by apply /eqP; rewrite -leqn0 E.
		by rewrite k0 in E'.
	case: k E => // m E.
	rewrite !nth_default => //=.
		by rewrite ltnS leqNgt E.
	by rewrite /nK size_map eq size_iota leqNgt E.
rewrite /N_XN_lst/sK.
replace (size K).+1 with (size ( x:: K)) by trivial.
by rewrite map_nth_iota.
Qed.

End BASIC_CONSTRUCTIONS.

Section BASIC_PROPERTIES.
(* This Definition is equivalent to the notion Arno introduces in "https://arxiv.org/pdf/1204.3763.pdf".
One of the drawbacks fo the version here is that it does not have a computable version.*)
Definition is_dscrt X :=
	forall Y (f: (space X) -> (space Y)), (F2MF f) \has_continuous_realizer.
Notation "X '\is_discrete'" := (is_dscrt X) (at level 2).

Lemma dscrt_rel X:
	X \is_discrete -> (forall Y (f: (space X) ->> (space Y)), f \has_continuous_realizer).
Proof.
move => dscrt Y f_R.
case: (classic (exists y:Y, true)) => [[y _] | ]; last first.
	move => next;	exists (F2MF (fun _ => (fun _:questions Y => some_answer Y))).
	split; first by move => phi [y _]; exfalso; apply next; exists y.
	by move => phi val phifd; exists nil => Fphi /= <- psi _ Fpsi <-.
have [f icf]:= exists_choice f_R y.
have [F [Frf Fcont]]:= (dscrt Y f).
exists F; split => //.
apply/ tight_trans; first by apply Frf.
by apply tight_comp_l; apply icf_F2MF_tight.
Qed.

Lemma one_dscrt: rep_space_one \is_discrete.
Proof.
move => X f.
have [phi phinfs]:= rep_sur X (f star).
exists (F2MF (fun _ => phi)).
split; last by exists nil => Fphi <- psi _ Fpsi <-.
apply frlzr_rlzr => psi str psinstr.
by elim str.
Qed.

Lemma nat_dscrt: rep_space_nat \is_discrete.
Proof.
move => X f.
pose R phi psi:= forall n, phi \is_name_of n -> psi \is_name_of (f n).
have [F icf]:= exists_choice R (fun _ => some_answer X).
exists (F2MF F).
split.
	apply frlzr_rlzr => phi n phinn.
	have [ psi psinfn] := rep_sur X (f n).
	suffices Rphipsi: R phi psi by apply/ (icf phi psi Rphipsi).
	move => n' phinn'.
	by have <-: n = n' by rewrite -(rep_sing rep_space_nat phi n n').
move => n q _.
exists (cons star nil).
move => Fphi /= <- psi coin Fpsi <-.
suffices <-: n = psi by trivial.
apply functional_extensionality => str.
by elim str; rewrite coin.1.
Qed.

(*
Lemma iso_one (X :rep_space) (somex: X):
	(rep_space_one c-> X) ~=~ X.
Proof.
pose f (xf: rep_space_one c-> X) := (projT1 xf) star.
pose L := fix L n := match n with
	| 0 => nil
	| S n => cons (star, star) (L n)
end.
pose F n (phi: names (rep_space_one c-> X)) q := match (phi ((L n), q)) with
	| inl q => None
	| inr a => Some a
end.
have: (eval F) \is_realizer_of f.
move => phi [x [[xf [phinxf fxfx]]] prop].
have [xF icf] := exists_choice (projT1 xf) somex.
split.
	exists x.
	split.
		pose psi (str: one) := star.
		have []:= (phinxf psi).
		(exists (xF star)).
		split; first by exists star; split => //; apply/ icf; apply fxfx.
		move => s psins; exists x; elim s; apply fxfx.
	move => [x' [[phi' [evl phi'nx']]prop']] stuff.
	exists (phi').
	split.
		move => q.
		have [c val]:= evl q.
		exists c.
		apply/ icf'.
pose pT1g (x: X) := F2MF (fun _: rep_space_one => x).
have crlzr: forall x:X, has_cont_rlzr (pT1g x) by move => x; apply one_dscrt.
have sing: forall (x: X), (pT1g x) \is_single_valued by move => x; apply F2MF_sing.
have tot: forall (x: X), (pT1g x) \is_total by move => x; apply F2MF_tot.
pose g (x:X) := exist_fun (conj (conj (sing x) (tot x)) (crlzr x)).
exists f'.
exists (F2MF g).
split.
	admit.
split.
	apply prim_rec_comp.
	pose psi:= fun (phi: names X) => (fun p: seq (one * one) * (questions X) => inr (phi p.2): sum one _).
	exists (psi).
	apply frlzr_rlzr.
	move => phi x phinx/=.
	rewrite /is_fun_name/is_rlzr/=.
	move => p pfd.
	split.
		exists x.
		split.
			exists phi.
			split => //.
			by exists 0.
		move => phi' ev.
		exists x.
		suffices: phi = phi' by move <-.
		apply functional_extensionality => q.
		apply Some_inj.
		have [/=n <-]:= (ev q).
		replace (Some (phi q)) with (U (psi phi) n p q) => //.
		have U0: U (psi phi) 0 p q = Some (phi q) by trivial.
		apply/ U_mon; last by apply U0.
		by replace (pickle 0) with 0 by trivial; lia.
	move => x' [[phi' [ev phi'nx']] prop].
	split.
		exists star.
		split; first by rewrite /id_rep; case (p star).
		suffices eq: phi = phi'	by apply ((\rep_valid X).1 phi x x') => //; rewrite eq.
		apply functional_extensionality => q.
		apply Some_inj.
		have [/=n <-]:= (ev q).
		replace (Some (phi q)) with (U (psi phi) n p q) => //.
		have U0: U (psi phi) 0 p q = Some (phi q) by trivial.
		apply/ U_mon; last by apply U0.
		by replace (pickle 0) with 0 by trivial; lia.
	by move => str eq; exists x.
split.
	rewrite F2MF_comp => x y.
	by rewrite /f /g /pT1g/F2MF/=.
rewrite comp_tot.
split.
	move => [x [b c]].
	rewrite /f in b.
	rewrite -c /g/pT1g/F2MF/=.
	apply eq_sub.
	apply functional_extensionality => str/=.
	elim str.
	apply functional_extensionality => x'/=.
	rewrite /= in b.
Admitted.

Lemma wiso_usig X:
	wisomorphic (rep_space_usig_prod X) (rep_space_cont_fun rep_space_nat X).
Proof.
have crlzr: forall xn: nat -> X, hcr (F2MF xn).
	move => xn.
	pose R phi psi := psi \is_name_of (xn (phi star)).
	have Rtot: R \is_total by move => phi; apply (rep_sur X).
	have [F icf]:= choice R Rtot.
	(*
	exists F; split.
		by apply rlzr_mfrlzr => phi x phinx; rewrite -phinx; apply/icf.
	move => phi q phifd; exists ([::star]) => Fphi /= FphiFphi psi coin.
	have eq: phi = psi.
		by apply functional_extensionality => /= str; elim: str; apply coin.
	by rewrite -eq => Fpsi FpsiFpsi; rewrite -FpsiFpsi -FphiFphi.*)
Admitted. *)
End BASIC_PROPERTIES.

