From mathcomp Require Import all_ssreflect.
Require Import all_rs_base rs_one rs_nat rs_opt rs_usig.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LISTSPACES.
Definition NXN_lst (X: rep_space) (onan: rep_space_opt _)
	:= if onan is Some nan then in_seg nan.2 (S nan.1) else [::]:seq X.

Definition rep_list (X: rep_space) := (F2MF (@NXN_lst X)) o (@delta _).

Lemma rep_list_sing X:
	(@rep_list X) \is_single_valued.
Proof.
by apply comp_sing; [exact: F2MF_sing | exact (rep_sing _)].
Qed.

Lemma inseg_trunc T an (m: nat) (a: T):
	forall k, m <= k -> in_seg (fun n: nat => if n < k then an n else a) m = in_seg an m.
Proof.
elim: m => // m ih k ineq/=.
by rewrite ineq ih; last by apply ltnW.
Qed.

Lemma rep_list_rep X:
	(@rep_list X) \is_representation.
Proof.
split; first exact: rep_list_sing.
elim.
	exists (fun _ => (None, some_answer _)).
	split; first by exists None.
	move => a b; exact: F2MF_tot.
move => a L [phi [[/=onan [phinonan onanL]] _]].
have [psi psina]:= rep_sur X a.
exists (fun q => (Some star, match q with
	| inl str => (0, some_answer X)
	| inr q' =>
		match q' with
		| inl str => (size L, some_answer X)
		| inr q'' => (0, if q''.1 < (size L) then rprj (unsm phi) q'' else psi q''.2)
	end
end)).
split; last by move => c d; exact: F2MF_tot.
case: onan phinonan onanL => [nan phinnan nanL | eq]; last first.
	by move <-; exists (Some (0, fun _ => a)); do 3 split => //.
exists (Some ((size L), fun n => if n < size L then nan.2 n else a)).
split.
	split; split => //=; rewrite /rprj => n /=.
	case (n < size L) => //; apply phinnan.2.
rewrite -nanL /F2MF /NXN_lst size_inseg/=.
have ->: S nan.1 < S nan.1 = false by apply ltnn.
have ->: nan.1 < S nan.1 by apply ltnSn.
have ->: in_seg (fun n : nat => if n < nan.1.+1 then nan.2 n else a) nan.1 = in_seg nan.2 nan.1 => //.
by elim: nan.1 => // n ih; rewrite inseg_trunc.
Qed.

Canonical rep_space_list (X: rep_space) := @make_rep_space
	(list X)
	_
	_
	(@rep_list X)
	(some_question _)
	(Some star, (some_answer rep_space_nat, some_answer X))
	(countable_questions (rep_space_opt (rep_space_prod rep_space_nat (rep_space_usig_prod X))))
	(countable_answers (rep_space_opt (rep_space_prod rep_space_nat (rep_space_usig_prod X))))
	(@rep_list_rep X).

Lemma nil_rec_elt X:
	(@nil X: rep_space_list X) \is_recursive_element.
Proof.
exists (fun _ => (None, some_answer _)).
by split; [exists None | move => b c; exact: F2MF_tot].
Qed.

Definition lnm_size X (phi: names (rep_space_list X)) :=
	match (phi (inl star)).1 with
		| Some str => S (unsm phi (inl star)).1
		| None => 0
	end.

Lemma lnm_size_spec X K phi:
	phi \is_name_of K -> (@lnm_size X phi) = size K.
Proof.
do 3 case; rewrite /NXN_lst/=/lnm_size/=; last by move => [-> <-].
by move => [n an] [[-> [/=<- _]] <-] _; rewrite/=size_inseg.
Qed.

Lemma size_rec_fun X:
	(fun K: rep_space_list X => size K) \is_recursive_function.
Proof.
exists (fun phi str => lnm_size phi) => phi K phinK.
by rewrite (lnm_size_spec phinK).
Qed.

Definition lnm_list X (phi: names (rep_space_list X)):=
	in_seg (fun n => (fun q => rprj (unsm phi) (n, q))) (lnm_size phi).

Lemma lnm_list_size X phi:
	@lnm_size X phi = size (lnm_list phi).
Proof. by rewrite /lnm_list size_inseg. Qed.

Definition cons_frlzr X := fun (phi: names (rep_space_prod X (rep_space_list X))) q =>
match (q: questions (rep_space_list X)) with
	| inl str => (some star, some_answer _): answers (rep_space_opt _)
	| inr q' => match (q': questions (rep_space_opt _)) with
		| inl str => (Some star, ((lnm_size (rprj phi)), some_answer X))
		| inr p => (Some star, (0,if p.1 < lnm_size (rprj phi)
		then rprj (unsm (rprj phi)) p else (lprj phi p.2)))
	end
end.

Lemma cons_frlzr_cons X:
	(@cons_frlzr X) \is_realizer_function_for (fun xL => cons xL.1 xL.2).
Proof.
move => phi [x K] [/=phinx phinK].
have eq:= (lnm_size_spec phinK).
have phinxK: phi \is_name_of (x, K) by split.
move: phinK => [[/=y [/=phiny yK]] _].
split; last by move => a b; exact: F2MF_tot.
case: y phiny yK => [nan phiny nanK | phiny yK]; last first.
	exists (Some (0, fun n => x)).
	rewrite -yK/= in eq => //; split; last by rewrite -yK.
	by split; last by split; rewrite /= eq.
exists (Some (size  K, (fun n => if n < size K then nan.2 n else x))).
split; first by do 2 split => //; rewrite/=eq/rprj=> n/=; case: (n < size K) => //; apply phiny.2.2.
rewrite -nanK /F2MF/NXN_lst size_inseg /=.
have ->: (nan.1.+1 < nan.1.+1) = false by rewrite ltnn.
have ->: (nan.1 < nan.1.+1) = true by rewrite ltnSn.
by rewrite inseg_trunc.
Qed.

Lemma cons_rec_fun (X: rep_space):
	(@cons X) \is_recursive_function.
Proof. exists (@cons_frlzr X); exact: cons_frlzr_cons. Defined.

Lemma list_rs_rec_pind (X Y Z: rep_space) (g: Z -> Y) (h: (rep_space_prod Z (rep_space_prod X Y)) -> Y) f:
	g \is_recursive_function -> h \is_recursive_function
	-> (forall zK, f zK = (fix f z K := match K with
		| nil => g z
		| cons a K => h (z, (a, f z K)) 
	end) zK.1 zK.2) -> f \is_recursive_function.
Proof.
move => [gM gMcmpt] [hM hMcmpt] feq.
pose psi (n:nat) (phi:names (rep_space_list X)) (q: questions (rep_space_list X)):= match n with
	| 0 => (None, (0, some_answer X))
	| S n => (Some star, (n, if q is (inr (inr p)) then (phi (inr (inr p))).2.2 else some_answer X))
end.
pose fM' := fix fM' n (phi: names (rep_space_prod Z (rep_space_list X))) := match n with
	| 0 => gM (lprj phi)
	| S n' => hM (name_pair (lprj phi)
		(name_pair (fun q => rprj (unsm (rprj phi)) (n', q))
		(fM' n' (name_pair (lprj phi) (psi n' (rprj phi))))))
end.
exists (fun phi q => fM' (lnm_size (rprj phi)) phi q).
move => phi [z K] [/=phinz phinK].
elim: K phi phinz phinK => [ | a K ih] phi phinz phinK.
	by rewrite feq /fM' (lnm_size_spec phinK)/=; apply gMcmpt.
replace (f (z,(a :: K))) with (h (z, (a, f (z,K)))) by by rewrite (feq (z,a::K)) feq.
rewrite (lnm_size_spec phinK).
have [[y [phiny yaK]] _]:= phinK.
case: y phiny yaK => // [[n an]] [nn [/=phinn phinan]] yaK.
rewrite /id_rep/lprj in phinn.
rewrite /F2MF/NXN_lst/= in yaK.
apply hMcmpt.
have [<- anK]:= yaK.
do 2 split => //; rewrite !lprj_pair !rprj_pair/=.
	suffices <-: n = size K by apply phinan.
	by rewrite -anK size_inseg.
case E: (size K) => [ | k].
	have ->: K = nil by case T: K E => //.
	by rewrite /fM' feq/=; apply gMcmpt.
have psinK: (psi (S k) (rprj phi)) \is_name_of K.
	split; last by move => b c; exact: F2MF_tot.
	exists (Some (k, an)); split => //.
	rewrite /F2MF/NXN_lst/=.
	have [_ <-]:= yaK.
	have ->: n = size K by rewrite -anK size_inseg.
	by rewrite E.
rewrite -E.
have {1}<-: lnm_size (rprj (name_pair (lprj phi) (psi (size K) (rprj phi)))) = size K.
	by rewrite rprj_pair/psi/lnm_size E/=.
apply ih => //.
by rewrite rprj_pair E.
Qed.

Lemma list_rs_rec_ind (X Y: rep_space) (g: Y) (h: rep_space_prod X Y -> Y) f:
	g \is_recursive_element -> h \is_recursive_function
	-> (forall K, f K = (fix f K := match K with
		| nil => g
		| cons a K => h (a, (f K))
	end) K) -> f \is_recursive_function.
Proof.
move => gcmpt hprec feq.
set g' := (fun _: rep_space_one => g).
have g'rec: g' \is_recursive_function by apply /cnst_rec_fun; first apply gcmpt.
set h' := (fun p:rep_space_prod rep_space_one (rep_space_prod X Y) => h p.2).
have h'rec: h' \is_recursive_function.
	move: hprec => [hM hMprop].
	exists (fun phi q => hM (rprj phi) q).
	by move => phi [z p] [phinz phinp]; apply hMprop.
have: (fun (_: rep_space_one) (K: rep_space_list X) => f K)\is_recursive_function.
	apply/ (list_rs_rec_pind g'rec h'rec) => /=.
	by move => [str K]; rewrite feq; elim:str => /=; elim: K => // a K ->.
move => [fM fMprop].
exists (fun phi q => fM (name_pair (fun _ => star) phi) q) => phi x phinx.
by apply (fMprop (name_pair (fun _ => star) phi) (star, x)).
Qed.

Lemma map_prec (X Y: rep_space) (f: X -> Y):
	f \is_recursive_function -> (fun K => map f K) \is_recursive_function.
Proof.
move => frec.
cut (fun p => (f p.1 :: p.2)) \is_recursive_function => [hrec| ].
	by apply/ (list_rs_rec_ind (nil_rec_elt _) hrec).
by apply/ rec_fun_comp; [apply (prod_rec_fun frec (id_rec_fun _)) | apply cons_rec_fun | ].
Qed.
End LISTSPACES.