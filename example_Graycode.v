From mathcomp Require Import all_ssreflect all_algebra.
Require Import FunctionalExtensionality.
Require Import all_rs rs_reals_creals Rstruct under.
Require Import Qreals Reals Psatz ClassicalChoice.
Require Import Lists.Streams.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope R_scope.

Section Streams.
Notation "sds '=~=' sds'" := (EqSt sds sds').

Lemma eqst_ntheq A (s1 s2: Stream A):
	EqSt s1 s2 <-> forall n, Str_nth n s1 = Str_nth n s2.
Proof.
split => [ass n | ].
	by apply eqst_ntheq.
by apply ntheq_eqst.
Qed.

Context (A: Type).
(*Equality axiom for Streams. Hopefully unprobematic. *)
Axiom Stream_equal: forall (s s': Stream A), EqSt s s' -> s = s'.

CoFixpoint Seq2Str (u: nat -> A) := Cons (u 0%nat) (Seq2Str (fun n => u n.+1)).

Fixpoint Str2Seq_rec (p: Stream A) n := match p with
	| Cons t p' => match n with
		| 0%nat => t
		| S m => Str2Seq_rec p' m
	end
end.

Fact Str2Seq_key : unit. Proof. by []. Qed.
Definition Str2Seq := locked_with Str2Seq_key Str2Seq_rec.
Canonical Str2Seq_unlockable := [unlockable fun Str2Seq].

Lemma Str2SeqS' (s: Stream A) n :
	Str2Seq s n = match s with
	| Cons a s' => match n with
		| 0%nat => a
		| S n => Str2Seq s' n
	end
end.
Proof.
rewrite unlock.
by elim: n.
Qed.

Lemma Str2SeqS (s: Stream A) n :
	Str2Seq s n = match n with
		| 0%nat => hd s
		| S n => Str2Seq (tl s) n
	end.
Proof.
rewrite Str2SeqS'.
by case: s.
Qed.

Lemma Str2Seq0 (s: Stream A):
	Str2Seq s 0 = hd s.
Proof. by rewrite unlock. Qed.

Lemma Seq2StrS (u: nat -> A) :
	Seq2Str u = Cons (u 0%nat) (Seq2Str (fun n => u (S n))).
Proof.
by apply /Stream_equal /eqst; [ | apply EqSt_reflex].
Qed.

Lemma Str2SeqK (s: Stream A):
	Seq2Str (Str2Seq s) = s.
Proof.
apply /Stream_equal /eqst_ntheq => n; move: s.
elim: n {-2}n (leqnn n) => [n | n ih m ineq s].
	by rewrite leqn0 => /eqP -> s; rewrite /Str_nth/= Str2Seq0.
rewrite leq_eqVlt in ineq.
case /orP: ineq => [/eqP -> /= | ineq]; last exact: ih.
rewrite -{1}addn1 -Str_nth_plus /=.
suff ->: (fun n0 => Str2Seq s n0.+1) = Str2Seq (tl s) by rewrite ih.
by apply functional_extensionality => k; rewrite Str2SeqS.
Qed.

Fixpoint Str2fSeq s n :seq A := match n with
	| 0%nat => [::]
	| S m => match s with
		| Cons a s' => (a :: (Str2fSeq s' m))
	end
end.
End Streams.

Section rep_Stream.
Context (X: rep_space).

Check (F2MF (Seq2Str X)).
Definition rep_Stream := (F2MF (Seq2Str X)) o (rep (rep_space_usig_prod X)).

Lemma rep_Stream_is_rep:
	rep_Stream \is_representation.
Proof.
split.
rewrite /rep_Stream.
	apply/comp_sing.
		by apply F2MF_sing.
	by apply (rep_sing (rep_space_usig_prod X)).
move => p.
have sur:= rep_sur (rep_space_usig_prod X).
set u := (Str2Seq X p).
specialize (sur u).
have [phi phinu]:= sur.
exists phi; rewrite /rep_Stream.
split; last by move => v phinv; apply F2MF_tot.
by exists u; split; last by rewrite /u /F2MF; apply /Str2SeqK.
Qed.

Canonical rep_space_Stream := @make_rep_space
	(Stream X)
	_
	_
	rep_Stream
	(some_question _)
	(some_answer _)
	(countable_questions _)
	(countable_answers _)
	rep_Stream_is_rep.
End rep_Stream.

Section singed_digits.
Inductive SD := minusone | zero | one.

Definition SD2OB sd := match sd with
	| minusone => some false
	| zero => None
	| one => some true
end.

Lemma SD_eqClass: Equality.class_of SD.
Proof.
exists (fun sd sd' => (SD2OB sd == SD2OB sd')%bool).
by case; case; try exact: ReflectT; try exact: ReflectF.
Qed.

Canonical SD_eqType := Equality.Pack SD_eqClass Type.

Lemma SD_count:
	SD \is_countable.
Proof.
exists (fun n => match n with
	| 0%nat => Some minusone
	| S 0 => Some zero
	| S (S 0) => Some one
	| S (S (S n)) => None
end).
by case; [case; [exists 0%nat | exists 1%nat | exists 2%nat] | exists 3%nat].
Qed.

Canonical rep_space_SD := @make_rep_space
	SD
	_
	SD
	(@id_rep SD)
	star
	zero
	one_count
	SD_count
	(id_rep_is_rep SD).

Definition SDs := rep_space_Stream rep_space_SD.

Definition Ts := Stream T.

Definition Tflip (t: T):= match t with
	| TR => TL
	| TL => TR
	| Tbot => Tbot
end.

CoFixpoint nh (ts: Ts):= match ts with
	| Cons t ts' => Cons (Tflip t) (nh ts')
end.

CoFixpoint SDs2Ts sds := match sds with
	| Cons minusone sds' => Cons TR (SDs2Ts sds')
	| Cons one sds' => Cons TL (SDs2Ts sds')
	| Cons zero sds' => Cons Tbot (SDs2Ts sds')
end.

Fixpoint u n := match n with
	| 0%nat => TL
	| S 0 => Tbot
	| S (S 0) => TR
	| S (S (S n')) => u n'
end.

Definition s := Seq2Str T u.

Compute Str2fSeq T s 15.
Compute Str2fSeq T (nh s) 15.
End singed_digits.

Section signed_digit_representation.
Definition UI := { x | -1 <= x <= 1}.

Definition SD2R sd := match sd with
	| one => 1
	| zero => 0
	| minusone => -1
end.

Definition SDs2Rn (sds: SDs) n:= \sum_(i < n.+1) SD2R (Str2Seq SD sds i) * /2 ^ i.+1.

Definition SDs2R (u: SDs) (x: R) := forall n, Rabs (x - SDs2Rn u n) <= /2^(n.+1).

Definition accumulates_to_zero T f:= forall r, r > 0 -> exists t: T, Rabs (f t) < r.

Lemma cond_eq_f T f x y:
	accumulates_to_zero T f -> (forall z, Rabs (x - y) <= Rabs (f z)) -> x = y.
Proof.
move => acc cond.
apply cond_eq => eps epsg0.
have [t ineq]:= (acc eps epsg0).
by apply /Rle_lt_trans; first by apply: (cond t).
Qed.

Lemma pwr2gtz m: exists n, (2^n > m)%nat.
Proof.
elim: m => [ | m [n /leP ih]]; first by exists 0%nat; apply /leP => /=; lia.
exists n.+1; apply /leP => /=; lia.
Qed.

Lemma twopowern_accumulates_to_zero: accumulates_to_zero _ (fun n => /2^(n.+1)).
Proof.
move => r rgt0; pose z := Z.to_nat (up (1/r)).
have [n /leP nprp]:= pwr2gtz z; have : 0 < 2^n.+1 by apply pow_lt; lra.
exists (n).
rewrite Rabs_pos_eq; last by rewrite Rinv_pow; try lra; apply /pow_le; lra.
rewrite -[r]Rinv_involutive; try lra.
apply Rinv_lt_contravar; first by rewrite Rmult_comm; apply Rdiv_lt_0_compat.
apply /Rlt_trans; first by have:= (archimed (1 / r)).1 => ineq; rewrite -[/r]Rmult_1_l; apply ineq.
case E: (up (1/r)) => [ | p | p] //; have pos:= (Pos2Z.pos_is_pos p); last first.
	by apply /(@Rlt_le_trans _ (IZR 0)); [apply IZR_lt; lia | apply Rlt_le].
rewrite -[Z.pos _]Z2Nat.id; try lia; rewrite -E -/z -INR_IZR_INZ.
have ->: 2 = INR 2 by trivial.
by rewrite -pow_INR; apply lt_INR => /=; lia.
Qed.

Lemma cond_eq_pwr x y : (forall n, Rabs (x - y) <= /2 ^ n.+1) -> x = y.
Proof.
intros.
apply (cond_eq_f _ _ _ _ twopowern_accumulates_to_zero) => n.
rewrite [Rabs (/2 ^ n.+1)]Rabs_pos_eq => //.
by rewrite Rinv_pow; first apply: pow_le; lra.
Qed.

Lemma SDs2R_sing:
	SDs2R \is_single_valued.
Proof.
move => u x y unx uny.
apply /cond_eq_pwr => n.
pose q:= \sum_(i < n.+2) SD2R (Str2Seq SD u i) * /2 ^ i.+1.
have ->: x - y = x - q  + (q - y) by lra.
apply triang; rewrite [_ (q - y)]Rabs_minus_sym.
apply /Rle_trans; first by apply: Rplus_le_compat; [exact: unx | exact: uny].
have neq:= pow_lt 2 n; rewrite /= Rinv_mult_distr; try lra.
Qed.

Lemma SDs2R_UI u x: SDs2R u x -> -1 <= x <= 1.
Proof.
move => val; move: (val 0%nat); rewrite /SDs2R/SDs2Rn big_ord1 /=.
rewrite Str2Seq0; case: (hd u); rewrite /GRing.mul /=; split_Rabs; try lra.
Qed.

Lemma SDs2RS_UI u x: SDs2R u x -> - 1 <= 2 * x - SD2R (hd u) <= 1.
Proof.
move: x => x; rewrite /=/SDs2R/GRing.zero /= => unx.
specialize (unx 0%nat); move: unx; rewrite /SDs2Rn big_ord1 Str2Seq0 Rmult_1_r.
by case: (hd u) => /=; rewrite /GRing.mul /=; split_Rabs; lra.
Qed.

Lemma SDs2RS u x: SDs2R u x -> SDs2R (tl u) (2 * x - SD2R (hd u)).
Proof.
move => unx n/=.
have:= unx n.+1; rewrite /SDs2Rn big_ord_recl /= Str2Seq0.
rewrite Rmult_1_r.
suff <-: (2 * \sum_(i < n.+1)
       SD2R (Str2Seq SD u (bump 0 (nat_of_ord i))) *
       / (2 * (2 * 2 ^ nat_of_ord i)))%R =
\sum_(i < n.+1)
      SD2R (Str2Seq SD (tl u) (nat_of_ord i)) * / (2 * 2 ^ nat_of_ord i).
  have p2lt: 0 < 2^n by apply pow_lt; lra.
	rewrite /GRing.add /GRing.mul /= Rinv_mult_distr; try lra.
	by split_Rabs; lra.
elim: n => [ | n ih]; first by rewrite !big_ord1 Str2SeqS /GRing.mul /=; lra.
have p2lt: 0 < 2^n by apply pow_lt; lra.
rewrite big_ord_recr/= Rmult_plus_distr_l ih [RHS]big_ord_recr/=.
by congr (_ + _); rewrite Str2SeqS /GRing.mul/= !Rinv_mult_distr; lra.
Qed.

Definition SDs2UI u (x: UI):= SDs2R u (projT1 x).

Lemma SDs2UI_cotot: is_cotot SDs2UI.
Proof.
move => [x ineq]; apply not_all_not_ex; rewrite /SDs2R => fa.
have fa': forall n: space SDs, exists m, ~ Rabs (x - SDs2Rn n m) <=/2^m.+1.
	move => n; by apply /not_all_ex_not/fa.
have [f fprp]:= choice _ fa'.
move: fa fa' => _ _.
Admitted.

Lemma Rabs_SDs2Rn u n : Rabs (SDs2Rn u n) <= 1 - /2^n.+1.
Proof.
elim: n => [ | n ih].
	rewrite /SDs2Rn big_ord1/= Str2Seq0 /GRing.mul /=.
	by case: (hd u) => /=; split_Rabs; try lra.
rewrite /SDs2Rn big_ord_recr/=.
have p2lt: 0 < /2^n by apply /Rinv_0_lt_compat/pow_lt; lra.
have p2lt': 0 < 2^n by apply /pow_lt; lra.
apply triang.
rewrite Str2SeqS.
have ->: 1 - / (2 * (2 * 2 ^ n)) = 1 - /2^n.+1 + (/2^n.+1 -  / (2 * (2 * 2 ^ n))) by lra.
apply Rplus_le_compat; first exact ih; rewrite !Rinv_mult_distr; try lra.
case: (Str2Seq SD (tl u) n); rewrite /GRing.mul /= ?Rmult_0_l; split_Rabs; try lra.
Qed.

Search _ Un_cv.

Lemma SDs2R_tot: SDs2R \is_total.
Proof.
move => sds.
Admitted.

Lemma SDs2UI_tot: SDs2UI \is_total.
Proof.
move => sds; have [x val]:= SDs2R_tot sds.
by exists (exist _ x (SDs2R_UI sds x val)).
Qed.

Definition rep_sd := SDs2UI o (rep SDs).

Lemma rep_sd_sing: 	rep_sd \is_single_valued.
Proof.
apply comp_sing; last exact: (rep_sing _).
by rewrite /SDs2UI => sds [x ineqx] [y ineqy]; rewrite eq_sub /=; apply: SDs2R_sing.
Qed.

Lemma rep_sd_is_rep:
	rep_sd \is_representation.
Proof.
split => [ | x]; first exact :rep_sd_sing.
have [sds val]:= SDs2UI_cotot x.
have [phi phinsds]:= rep_sur _ sds.
exists phi; split => [ | a b]; last exact: SDs2UI_tot.
by exists sds; split.
Qed.

Canonical rep_space_UIsd := @make_rep_space
	UI
	_
	_
	rep_sd
	(some_question _)
	zero
	(countable_questions _)
	SD_count
	rep_sd_is_rep.

Definition T2R t := match t with
	| TL => -1
	| TR => 1
	| Tbot => 0
end.

Coercion T2R: T >-> R.

Definition UI_Tomega_rep (p: rep_space_Tomega) (x: UI) :=
	forall n, Rabs (projT1 x - sum_f 0 n (fun i => -(prod_f_R0 (fun j => - p j) n) * (pow (1/2) i))) <= pow (1/2) n.

Definition sg (u: names rep_space_UIsd) (p: rep_space_Tomega) :=
	exists (x: UI), rep_sd u x /\ UI_Tomega_rep p x.

Definition tent x := 1 - 2 * Rabs x.

Lemma tenttoUI (x: UI):
	-1<= tent (projT1 x) <= 1.
Proof.
move: x => [x ineq].
rewrite /tent /=.
split_Rabs; lra.
Qed.

Definition tentUI (x: UI) := @exist R _ (tent (projT1 x)) (tenttoUI x): UI.

Lemma tentUI_correct (x: UI):
	projT1 (tentUI x) = tent (projT1 x).
Proof. done. Qed.

Fixpoint UI2Tomega_rec (x: UI) n:= match n with
	| 0%nat => if Rlt_dec (projT1 x) 0 then TL else if Rlt_dec 0 (projT1 x) then TR else Tbot
	| S n => UI2Tomega_rec (tentUI x) n
end.

Definition UI2Tomega (x: rep_space_UIsd) := (fun n => UI2Tomega_rec x n): rep_space_Tomega.

Definition SDSDtoT (sd sd': SD):= if sd == zero then Tbot else
	if sd == sd' then TL else TR.

Definition UI2Tomega_rlzr (u: names rep_space_UIsd) : names rep_space_Tomega :=
	fun an => match an.2 with
		| 0%nat => match u 0%nat with
			| one => TR
			| minusone => TL
			| zero => SDSDtoT (u an.1) (minusone)
		end
		| S n => if u n == zero then
				match n with
					| 0%nat => TR
					| S m => if u m == zero then TL else TR
				end
			else
				if u an.2 == zero then SDSDtoT (u (an.2 + an.1)%nat) (u n) else SDSDtoT (u an.2) (u n)
		end.

Lemma UI2Tomega_frlzr:
	UI2Tomega_rlzr \is_realizer_function_for UI2Tomega.
Proof.
move => u [x xinUI] unx n.
elim: n => /=.
case: ifP => [ineq | ].

exists 0%nat.
split => //.
rewrite /UI2Tomega_rlzr/=.
rewrite /SDSDtoT /=.
rewrite /=/rep_sd in unx.
case E: (u 0%nat) => [b | ] /=. case E': b; rewrite E' in E; move: E' => _//.
	exfalso.
	specialize (unx 0%nat).
	rewrite /sum_f/interp/= in unx.
	move: unx.
	rewrite E.
	rewrite Rmult_1_l.
	have : x < 0  by rewrite /is_true/is_left in ineq; move: ineq; case: Rlt_dec.
	move: ineq => _ ineq.
	by split_Rabs; lra.
admit.
move => ineq.
case: ifP; last first.
	rewrite -ineq /is_true/is_left //; case Rlt_dec; case Rlt_dec; move => //; try lra.
	move => xl0 olx _.
	have eq: x = 0 by lra.
	move: xl0 olx => _ _.
	admit.
move => ineq'.
	rewrite ineq.

	move/eqP: ineq.
	rewrite /Rlt_dec.
	Check Rlt_dec.
	rewrite /Rlt_dec in ineq.
	split_Rabs; lra.
case: ifP => /=.
Admitted.

Lemma sg_correct: sg \tightens ((rep rep_space_Tomega) o (F2MF UI2Tomega_rlzr)).
Proof.
rewrite /sg.
apply /tight_trans; last first.
	have:= UI2Tomega_frlzr.

rewrite frlzr_rlzr /rlzr.

Definition hn sd:= match sd with
	| TR => false
	| Tbot => true
	| TL => true
end.

Definition flip t:= match t with
	| TL => TR
	| Tbot => Tbot
	| TR => TL
end.

Fixpoint flip_digit (u: rep_space_Tomega) n := match n with
	| 0%nat => true
	| S n => xorb (hn (u (S n))) (flip_digit u n)
end.

Definition flip_sequence u n:= if flip_digit u n then flip (u n) else u n.

Definition nh (L: seq T):= match L with
	| [::] => [::]
	| (a :: K) => (flip a :: K)
end.

Lemma flip_sequence_spec L i a:
	(i < size L)%nat -> flip_sequence (fun j => nth a L j) i = nth a (nh L) i.
Proof.
elim: L => // b L /=.
elim: i => //= n ih1 ih2 ineq.
rewrite /flip_sequence /=.
case: ifP => [A | ].
rewrite /hn.
Admitted.


Definition UI2G_rlzr' (u: names rep_space_Rsd):
	fun an => match u an.2 with
		| one => if flip_digit u an.2 then some true else some false
		| minusone => if  flip_digit u an.2 then some false else some true
		| zero => if flip_digit u an.2 then SDtoob (u (an.2 + an.1)%nat) else SDtoob (flip (u (an.2 + an.1)%nat))
	end.


Definition one_fun: names (rep_space_Rsd) := (fun n => one).

Compute UI2G_rlzr one_fun (0,4)%nat.


Fixpoint sgfirst (p: nat -> SD) n := match n with
	

Fixpoint sg (p: nat -> SD) n := match n with
	| 0 => 
	

End Gray_code.