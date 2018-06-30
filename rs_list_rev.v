From mathcomp Require Import all_ssreflect.
Require Import all_rs_base rs_one rs_nat rs_opt rs_usig.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section REVERSEDLISTS.

Definition NXN_lst_rev (X: rep_space) (onan: rep_space_opt _)
	:= if onan is Some nan then map nan.2 (iota 0 nan.1) else [::]:seq X.

Definition rep_list_rev (X: rep_space) := (F2MF (@NXN_lst_rev X)) o (@delta _).

Lemma rep_list_rev_sing X:
	(@rep_list_rev X) \is_single_valued.
Proof. by apply comp_sing; [exact: F2MF_sing | exact (rep_sing _)]. Qed.

Lemma map_nth_iota T (x:T) p:
	[seq nth x p n0 | n0 <- iota 0 (size p)] = p.
Proof.
apply (@eq_from_nth T x); rewrite size_map size_iota => // k E.
rewrite (@nth_map nat 0%nat T x (fun n => nth x p n) k (iota 0 (size p))); last by rewrite size_iota.
by rewrite seq.nth_iota => //.
Qed.

Lemma rep_list_rev_rep X:
	(@rep_list_rev X) \is_representation.
Proof.
split; first exact: rep_list_rev_sing.
elim.
	exists (fun _ => (None, (0,some_answer X))).
	split; first by exists None.
	move => a b; exact: F2MF_tot.
move => x K [phi [[/=y [phiny yK]] _]].
rewrite /F2MF in yK.
set n := size K.
have [psi psina]:= rep_sur X x.
set nK := map (fun n => (fun q => rprj (unsm phi) (n,q))) (iota 0 n).
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
split; last by move => a b; exact: F2MF_tot.
exists (Some (S n, (fun n => nth x (x:: K) n))).
rewrite /rep_opt/=/prod_rep/=/id_rep/=/rep_usig_prod/=;
rewrite /lprj/=/rprj/=/mfpp/=/NXN_lst_rev/F2MF.
split; last by rewrite map_nth_iota.
split => //.
split => //.
move => k.
case E: (k <= n); rewrite /n in E.
	case E': k => [ | m]//=.
	rewrite /rep_opt in phiny.
	case: y phiny yK.
		move => nan [/=sm name] nanK.
		rewrite /nK.
		rewrite /prod_rep/=/id_rep/=/lprj/rprj/=/mfpp/=/rep_usig_prod/= in name.
		move: name => [nnan prop].
		have ineq: m < n by rewrite /n; apply /leP; rewrite -E'; apply /leP; rewrite E.
		rewrite (nth_map 0); last by rewrite size_iota.
		specialize (prop m); rewrite nth_iota => //.
		suffices ->: (nth x K m) = nan.2 m by trivial.
		rewrite -nanK/=.
		have -> : nan.1 = n by rewrite /n -nanK size_map size_iota.
		rewrite (nth_map 0); last by rewrite size_iota.
		by rewrite nth_iota.
	rewrite /NXN_lst_rev => _ eq; rewrite -eq/= in E.
	have k0: k= 0 by apply /eqP; rewrite -leqn0 E.
	by rewrite k0 in E'.
case: k E => // m E.
by rewrite !nth_default => //=; [rewrite ltnS | rewrite /nK size_map size_iota/n]; rewrite leqNgt E.
Qed.

Canonical rep_space_list_rev (X: rep_space) := @make_rep_space
	(list X)
	_
	_
	(@rep_list_rev X)
	(some_question _)
	(Some star, (some_answer rep_space_nat, some_answer X))
	(countable_questions (rep_space_opt (rep_space_prod rep_space_nat (rep_space_usig_prod X))))
	(countable_answers (rep_space_opt (rep_space_prod rep_space_nat (rep_space_usig_prod X))))
	(@rep_list_rev_rep X).

Definition lnmr_size X (phi: names (rep_space_list_rev X)) :=
	match (phi (inl star)).1 with
		| Some str => (unsm phi (inl star)).1
		| None => 0
	end.

Lemma lnmr_size_crct X K phi:
	phi \is_name_of K -> (@lnmr_size X phi) = size K.
Proof.
move => [[[]]]; rewrite /F2MF/NXN_lst_rev/=/lnmr_size/=; last by move => [-> <-].
by move => [n an] [[-> [/=name _]] eq] _; rewrite -eq size_map size_iota -name /lprj.
Qed.

Lemma size_rev_rec_fun X:
	(fun K: rep_space_list_rev X => size K) \is_recursive_function.
Proof.
exists (fun phi str => lnmr_size phi).
abstract by move => phi K phinK; rewrite (lnmr_size_crct phinK).
Defined.

Definition lnmr_list X (phi: names (rep_space_list_rev X)):=
	map (fun n => (fun q => (phi (inr (inr (n, q)))).2.2)) (iota 0 (lnmr_size phi)).

Lemma lnmr_list_size X phi:
	@lnmr_size X phi = size (lnmr_list phi).
Proof. by rewrite /lnmr_list size_map size_iota. Qed.

Definition nth_frlzr (X: rep_space) psiphi p := match lnmr_size (rprj psiphi) with
		| 0 => lprj psiphi p.2: answers X
		| S n => nth (lprj psiphi) (lnmr_list (rprj psiphi)) p.1 p.2
	end.

Lemma nth_rlzr_crct (X: rep_space):
	(fun phipsi (p: questions (rep_space_usig_prod X)) => @nth_frlzr X phipsi p)
		\is_realizer_function_for
	(fun aK : space (rep_space_prod X (rep_space_list_rev X)) => nth aK.1 aK.2: rep_space_usig_prod X).
Proof.
move => phi [a K] [/=psina phinK] n; rewrite /nth_frlzr.
rewrite (lnmr_size_crct phinK)/=.
case: K phinK => /=; first by rewrite nth_default.
move => b K phinK.
case E: (n <= size K); last first.
	have ineq: size K < n by rewrite leqNgt; apply /leP => ineq;
		have:= le_S_n n (size K) ineq; apply /leP; rewrite E.
	rewrite !nth_default => //=; last rewrite /lnmr_list size_map size_iota (lnmr_size_crct phinK) => //=.
rewrite /lnmr_list.
have ineq: n < S (size K) by rewrite ltnS.
rewrite (nth_map 0); last rewrite size_iota (lnmr_size_crct phinK) => //=.
rewrite nth_iota; last rewrite (lnmr_size_crct phinK) => //=.
move: phinK => [[onan [phinonan onanK]] _].
rewrite /F2MF /NXN_lst_rev in onanK.
case: onan onanK phinonan => // [[k an]] onanK [_ [/=phinn phinK]].
have nk: n < k.
	suffices ->: k = (size (b::K)) by trivial.
	by rewrite -onanK size_map size_iota.
rewrite -onanK (nth_map 0); last rewrite size_iota => //=.
rewrite {1}/rprj in phinK.
by rewrite nth_iota.
Qed.

Lemma nth_rec_rev (X: rep_space):
	(fun a K => nth (a: X) K) \is_recursive_function.
Proof.
exists (@nth_frlzr X).
exact: nth_rlzr_crct.
Defined.

Definition cons_frlzr (X: rep_space) :=
(fun (phi: names (rep_space_prod X (rep_space_list_rev X))) (q: questions (rep_space_list_rev X)) => match q with
	| inl str => (some star, (0, some_answer X))
	| inr q' => match q' with
		| inl str => (some star, (S (lnmr_size (rprj phi)), some_answer X))
		| inr p => (some star, (some_answer rep_space_nat, match p.1 with
			| 0 => lprj phi p.2
			| S n => nth_frlzr phi (n, p.2)
		end))
	end
end).

Lemma cons_frlzr_crct (X: rep_space):
	(@cons_frlzr X) \is_realizer_function_for (fun p => cons (p.1: X) (p.2: rep_space_list_rev X)).
Proof.
move => phi [x K] [/=phinx phinK].
have eq:= (lnmr_size_crct phinK).
have phinxK: phi \is_name_of (x, K) by split.
move: phinK => [[y [/=phiny yK]] _].
split; last by move => a b; exact: F2MF_tot.
exists (Some (size (x:: K), (fun n => nth x (x:: K) n))).
rewrite /rep_opt/=/prod_rep/=/id_rep/=/rep_usig_prod/=;
rewrite /lprj/=/rprj/=/mfpp/=/NXN_lst_rev/F2MF.
split; last by rewrite map_nth_iota.
split => //.
split; first by rewrite eq.
move => k.
case E: (k <= (size K)).
	case E': k => [ | m]//=.
	apply usig_base.
	by apply/ rlzr_val_sing; [ apply F2MF_sing | apply frlzr_rlzr; apply nth_rlzr_crct | apply phinxK | | ].
case: k E => // m E /=.
apply usig_base.
by apply/ rlzr_val_sing; [ apply F2MF_sing | apply frlzr_rlzr; apply nth_rlzr_crct | apply phinxK | | ].
Qed.

Lemma cons_rec_fun_rev (X: rep_space):
	(fun p => cons (p.1: X) (p.2: rep_space_list_rev X):rep_space_list_rev X) \is_recursive_function.
Proof.
exists (fun (phi: names (rep_space_prod X (rep_space_list_rev X))) q => match q with
	| inl str => (some star, (0, some_answer X))
	| inr q' => match q' with
		| inl str => (some star, (S (lnmr_size (rprj phi)), some_answer X))
		| inr p => (some star, (some_answer rep_space_nat, match p.1 with
			| 0 => lprj phi p.2
			| S n => nth_frlzr phi (n, p.2)
		end))
	end
end).
exact: cons_frlzr_crct.
Defined.

Let psi X (n:nat) (phi:names (rep_space_list_rev X)) (q: questions (rep_space_list_rev X)):= match n with
	| 0 => (None, (0, some_answer X))
	| S n => (Some star, (n, if q is (inr (inr p)) then (phi (inr (inr (S p.1,p.2)))).2.2 else some_answer X))
end.

Lemma list_rev_rs_prec_pind_tech (X Y Z: rep_space) (g: Z -> Y)
	(h: (rep_space_prod Z (rep_space_prod X Y)) -> Y) f gM hM:
	gM \is_realizer_function_for g -> hM \is_realizer_function_for h
	-> (forall zK, f zK = (fix f z (K: rep_space_list_rev X) := match K with
		| nil => g z
		| cons a K => h (z, (a, f z K)) 
	end) zK.1 zK.2) -> (fun psi' => (fix fM' n (phi: names (rep_space_prod Z (rep_space_list_rev X))) := match n with
	| 0 => gM (lprj phi)
	| S n' => hM (name_pair (lprj phi) (name_pair (fun q =>
		((rprj phi) (inr (inr (0, q)))).2.2:answers X) (fM' n' (name_pair (lprj phi) (psi n (rprj phi))))))
end) (lnmr_size (rprj psi')) psi') \is_realizer_function_for f.
Proof.
move => gMcmpt hMcmpt feq phi [z K] [/=phinz phinK].
set fM' := (fun psi' => (fix fM' n (phi: names (rep_space_prod Z (rep_space_list_rev X))) := match n with
	| 0 => gM (lprj phi)
	| S n' => hM (name_pair (lprj phi) (name_pair (fun q =>
		((rprj phi) (inr (inr (0, q)))).2.2:answers X) (fM' n' (name_pair (lprj phi) (psi n (rprj phi))))))
end) (lnmr_size (rprj psi')) psi').
elim: K phi phinz phinK => [ | a K].
	by rewrite feq => phi phinz phinK; rewrite (lnmr_size_crct phinK)/=; apply gMcmpt.
move => ih phi phinz phinK.
replace (f (z,(a :: K))) with (h (z, (a, f (z,K)))) by by rewrite (feq (z,a::K)) feq.
rewrite (lnmr_size_crct phinK).
move: phinK => [[y [phiny yaK]] _].
case: y phiny yaK => // [[n an]] [_ [/=phinn phinan]] yaK.
rewrite /id_rep/lprj in phinn.
rewrite /F2MF/NXN_lst_rev/= in yaK.
have eq: a = an 0 by case: n phinn yaK => //= n phinn [-> yak].
have psinK : (psi n (rprj phi)) \is_name_of K.
	rewrite /psi/=/delta/=/F2MF/=/NXN_lst_rev/=.
	split; last by move => b c; apply: F2MF_tot.
	rewrite/ rel_comp.
	case E: n => [ | m]; first by rewrite E/= in yaK.
	exists (Some (m, (fun n => an (S n)))) => /=.
	split; last first.
		rewrite E in yaK.
		move : yaK => [_ <-]/=.
		apply /(@eq_from_nth _ a).
			by rewrite !size_map !size_iota.
		move => i ass /=.
		have im: i < m by rewrite size_map size_iota in ass.
		rewrite !(nth_map 0) => //; try rewrite size_iota//.
		rewrite !nth_iota => //=.
	split => //; split => //=.
	rewrite /id_rep/lprj.
	rewrite /rep_usig_prod/= => k.
	by rewrite /rprj/=; apply phinan.
specialize (ih (name_pair (lprj phi) (psi n (rprj phi))) phinz psinK).
pose phia0 q := (rprj phi (inr (inr (0, q)))).2.2.
have phia0na: phia0 \is_name_of a by rewrite eq;apply phinan.
have np:
	(name_pair (lprj phi)
		(name_pair phia0 [eta fM' (name_pair (lprj phi) (psi n (rprj phi)))]))
			\is_name_of (z,(a,f (z, K))) by trivial.
apply/ rlzr_val_sing; [ apply F2MF_sing | apply frlzr_rlzr; apply hMcmpt | | | ].
		exact: np.
	by rewrite feq.
rewrite /=/fM'/=(lnmr_size_crct psinK)/F2MF.
rewrite /name_pair/phia0.
by have /= ->: n = size (a :: K) by rewrite -yaK size_map size_iota.
Qed.

Lemma list_rev_rs_rec_pind (X Y Z: rep_space) (g: Z -> Y) (h: (rep_space_prod Z (rep_space_prod X Y)) -> Y) f:
	g \is_recursive_function -> h \is_recursive_function
	-> (forall zK, f zK = (fix f z (K: rep_space_list_rev X) := match K with
		| nil => g z
		| cons a K => h (z, (a, f z K)) 
	end) zK.1 zK.2) -> f \is_recursive_function.
Proof.
move => [gM gMcmpt] [hM hMcmpt] feq.
exists (fun psi' => (fix fM' n (phi: names (rep_space_prod Z (rep_space_list_rev X))) := match n with
	| 0 => gM (lprj phi)
	| S n' => hM (name_pair (lprj phi) (name_pair (fun q =>
		((rprj phi) (inr (inr (0, q)))).2.2:answers X) (fM' n' (name_pair (lprj phi) (psi n (rprj phi))))))
end) (lnmr_size (rprj psi')) psi').
exact: (list_rev_rs_prec_pind_tech gMcmpt hMcmpt).
Defined.

Lemma list_rev_rs_rec_ind (X Y: rep_space) (g: Y) (h: (rep_space_prod X Y) -> Y) f:
	g \is_recursive_element -> h \is_recursive_function
	-> (forall K, f K = (fix f (K: rep_space_list_rev X) := match K with
		| nil => g
		| cons a K => h (a, f K)
	end) K) -> f \is_recursive_function.
Proof.
move => grec hrec feq.
set g' := (fun str: rep_space_one => g).
have g'rec: g' \is_recursive_function by apply /cnst_rec_fun; first apply: grec.
set h' := (fun p:rep_space_prod rep_space_one (rep_space_prod X Y) => h p.2).
have h'rec: h' \is_recursive_function.
	move: hrec => [hM hMprop].
	exists (fun phi q => hM (rprj phi) q).
	by move => phi [z p] [phinz phinp]; apply hMprop.
have: (fun oK: rep_space_prod rep_space_one (_) => f oK.2)\is_recursive_function.
	apply/ (list_rev_rs_rec_pind g'rec h'rec) => /=.
	by move => [str K]; rewrite feq; elim:str => /=; elim: K => // a K ->.
move => [fM fMprop].
exists (fun phi q => fM (name_pair (fun _ => star) phi) q).
move => phi x phinx.
by apply (fMprop (name_pair (fun _ => star) phi) (star, x)).
Defined.

Lemma nil_rev_rec_elt (X: rep_space):
	(@nil X) \is_recursive_element.
Proof.
exists (fun _ => (None, some_answer _)).
abstract by split; [exists None | move => a b; exact: F2MF_tot].
Defined.

Lemma cmpt_elt_seq_rev (X: rep_space) K:
	(forall x: X, List.In x K -> x \is_recursive_element) -> K \is_recursive_element.
Proof.
elim: K => [ prp | a K ih prp]; first exact: nil_rev_rec_elt.
apply/ rec_fun_rec_elt.
	apply ih => x listin.
	by apply prp; right.
apply/ rec_fun_comp; [apply diag_rec_fun| | ].
apply/ rec_fun_comp.
	apply prod_rec_fun.
		by apply/cnst_rec_fun; first by apply /prp; left.
	by apply id_rec_fun.
apply cons_rec_fun_rev.
done.
done.
Defined.

Lemma map_prec_rev (X Y: rep_space) (f: X -> Y):
	f \is_recursive_function -> (fun (K: rep_space_list_rev X) => map f K) \is_recursive_function.
Proof.
move => frec.
have hrec: (fun p => (f p.1 :: p.2)) \is_recursive_function.
	apply/ rec_fun_comp; first by apply diag_rec_fun.
	apply/ rec_fun_comp; first by apply prod_rec_fun; [apply/ fst_rec_fun | apply/ snd_rec_fun].
	apply/ rec_fun_comp; first by apply prod_rec_fun; [apply frec | apply id_rec_fun].
	by apply cons_rec_fun_rev.
	done. done. done.
by apply (list_rev_rs_rec_ind (nil_rev_rec_elt Y) hrec).
Defined.

Lemma map_rec_rev_par (X Y Z: rep_space) (f: Z*X -> Y): f \is_recursive_function ->
	(fun (zK:rep_space_prod Z (rep_space_list_rev X)) => map (fun K => f (zK.1,K)) zK.2) \is_recursive_function.
Proof.
move => frec.
have hrec: (fun zaT => (f (zaT.1, zaT.2.1) :: zaT.2.2)) \is_recursive_function.
	apply /rec_fun_comp; first by apply prod_assoc_rec_fun.
	apply/ rec_fun_comp; first by apply prod_rec_fun; [apply frec | apply id_rec_fun].
	by apply cons_rec_fun_rev.
	done. done.
apply/ list_rev_rs_rec_pind; first by apply /cnst_rec_fun; first apply /nil_rev_rec_elt.
	exact: hrec.
move => [z K] /=; by elim: K => // a K <-.
Defined.

Lemma iota0_rec_fun:
	(iota 0) \is_recursive_function.
Proof.
exists (fun phi q => match (phi star) with
	| 0 => (None, (0, 0))
	| S n => match q with 
		| inl str => (Some star, (0, 0))
		| inr (inl star) => (None, (S n, 0))
		| inr (inr p) => (None, (0, p.1))
	end
end).
abstract by move => phi n ->/=; case E: n => [ | m]; [split; [exists None | move => a b; apply F2MF_tot]|
split; [by exists (Some (n, fun i => i)); split; last by rewrite /F2MF/NXN_lst_rev -E /= map_id | move => a b; apply F2MF_tot]].
Defined.
End REVERSEDLISTS.