From mathcomp Require Import all_ssreflect all_algebra.
Require Import Psatz under Poly_complements.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

Section RBase.

Variable R : ringType.
Variable F : nat -> {poly R}.

Lemma polybase_widen (p : {poly R}) n :
    (size p <= n)%N -> \sum_(i < n) p`_i *: F i = \sum_(i < size p) p`_i *: F i.
Proof.
move=> Hs.
rewrite -(big_mkord xpredT (fun i => p`_i *: F i)).
rewrite (big_cat_nat _ _ _ _ Hs) //= big_mkord.
rewrite addrC big_nat_cond big1 ?add0r // => i.
rewrite andbT => /andP[/(@leq_sizeP R) // H1 H2].
by rewrite H1 ?scale0r.
Qed.

Lemma sumrA (p q: {poly R}):
	\sum_(i < size (p + q)) (p + q)`_i *: F i = \sum_(i < size p) p`_i *: F i + \sum_(i < size q) q`_i *: F i.
Proof.
rewrite -(@polybase_widen (p + q) (maxn (size p) (size q))); last exact: size_add.
rewrite -(@polybase_widen p (maxn (size p) (size q))); last by rewrite leq_maxl.
rewrite -(@polybase_widen q (maxn (size p) (size q))); last by rewrite leq_maxr.
elim: (maxn (size p) (size q)) => [ | n ih]; first by rewrite !big_ord0 rm0.
rewrite !big_ord_recr/= ih coefD scalerDl.
rewrite -addrA.
rewrite ![p`_n *: F n  + _]addrC.
by rewrite !addrA.
Qed.

Lemma sumrZ a (p: {poly R}):
	\sum_(i < size (a *: p)) (a *: p)`_i *: F i = a*: (\sum_(i < size p) p`_i *: F i).
Proof.
rewrite -(@polybase_widen (a *: p) (size p)); last exact: size_scale_leq.
elim: (size p) => [ | n ih]; first by rewrite !big_ord0 rm0.
by rewrite !big_ord_recr/= ih -!mul_polyC mulrDr !mul_polyC scalerA -!mul_polyC coefCM.
Qed.
End RBase.

Section Base.
Variable R : unitRingType.
Variable F : nat -> {poly R}.
Hypothesis F_size : forall n, size (F n) = n.+1.
Hypothesis F_lead: forall n r, r * lead_coef (F n) = 0 -> r = 0.

Lemma size_seqbase n l : 
   size (\sum_(i < n) l`_ i *: F i) = \max_(i < n | l`_i != 0) i.+1.
Proof.
elim: n => [|n IH]; first by rewrite !big_ord0 size_poly0.
rewrite [RHS]big_mkcond /= !big_ord_recr /= -big_mkcond /=.
have [/eqP Hp| /eqP Hnp /=] := boolP (l`_n == 0).
  by rewrite Hp scale0r addr0 IH /= maxn0.
have lp : l`_ n * (F n)`_n != 0.
	apply /eqP => eq; apply Hnp.
	apply (@F_lead n).
	by rewrite lead_coefE F_size.
have Hs: size (l`_n *: F n) = n.+1.
	suff/leP: (n.+1 <= size (l`_n *: F n))%nat.
		have/leP:= @size_scale_leq _ (l`_n) (F n).
		rewrite F_size; lia.
	by apply gtn_size; rewrite coefZ.
case: (n) Hs IH => [Hs _|n1 Hs IH].
  by rewrite !big_ord0 add0r Hs.
rewrite addrC size_addl Hs.
  rewrite (maxn_idPr _) //.
  apply/bigmax_leqP=> i _.
  by apply: leq_trans (ltn_ord i) _; rewrite ltnW.
rewrite ltnS IH.
by apply/bigmax_leqP => i _.
Qed.

Lemma size_polybase (p: {poly R}):
	size (\sum_(i < size p) p`_ i *: F i) = size p.
Proof.
rewrite size_seqbase.
case E: (size p) => [ | n]; first by rewrite big_ord0.
rewrite big_mkcond/=.
rewrite big_ord_recr /=.
rewrite -big_mkcond/=.
case: ifP => [_ | ].
apply/ maxn_idPr.
by apply/ bigmax_leqP => /= i _; rewrite ltnS ltnW.
case/ idP.
have ->: n = (size p).-1 by rewrite E.
by rewrite -lead_coefE lead_coef_eq0 -size_poly_eq0 E.
Qed.

Lemma Fneq0: forall n, F n != 0.
Proof.
by move => n; rewrite -size_poly_gt0 F_size.
Qed.

Lemma seqbase_coef_eq0 n (l: seq R) : 
   \sum_(i < n) l`_ i *: F i = 0 -> forall i, (i < n)%N -> l`_i = 0.
Proof.
move=> H i Hi.
suff P j : (0 < j < n)%N -> l`_j = 0.
  have := H.
  case: (n) Hi P => // n1 Hi P /eqP.
  rewrite big_ord_recl big1 => [|j _]; last first.
    by rewrite P ?scale0r // lift0 /= ltnS.
  rewrite addr0.
  move => /eqP eq; move: eq.
  rewrite -polyP => prp.
  specialize (prp 0%nat).
  rewrite coef0 coefZ in prp.
  move: prp.
  rewrite [0%nat]pred_Sn.
  rewrite -(F_size 0).
  rewrite -lead_coefE => prp.
 	have:= @F_lead 0 _ prp.
  case: i Hi => [_ ->//|i Hi _].
  by apply: P.
move=> /andP[HP1 HP2].
have /eqP := (H).
rewrite -size_poly_eq0 size_seqbase -leqn0 => /bigmax_leqP/(_ (Ordinal HP2)).
by rewrite /=; case: eqP => //= _ /(_ isT).
Qed.

Lemma polybase_eq0 (p: {poly R}) : 
   \sum_(i < size p) p`_ i *: F i = 0 <-> p = 0.
Proof.
split => [prp | ->]; last by rewrite big1 => // i _; rewrite coef0 rm0.
rewrite [LHS]coef_Xn_eq.
rewrite big1 => // i _.
by rewrite (seqbase_coef_eq0 prp); first by rewrite !rm0.
Qed.

End Base.
















