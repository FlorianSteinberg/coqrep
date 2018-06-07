From mathcomp Require Import all_ssreflect all_algebra.
Require Import under CPoly Poly_exec Poly_complements.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

Section CSHAW.
Variable R : ringType.
Implicit Types (l : seq R) (p: {poly R}) .

(* Interpret a list as Chebychev Coefficients of a polynomial: *)
Definition CPoly (l: seq R): {poly R} := \sum_(i < size l) l`_i *: 'T_i.

Lemma CPoly_nil : CPoly nil = 0 :> {poly R}.
Proof. by rewrite /CPoly big_ord0. Qed.

Lemma CPolyC c: CPoly [::c] = c%:P :> {poly R}.
Proof.
by rewrite /CPoly /= big_ord1 pT0 alg_polyC.
Qed.

Lemma size_CPoly_leq l : (size (CPoly l) <= size l)%N.
Proof.
apply: (leq_trans (size_sum _ _ _)).
apply/bigmax_leqP => i _.
apply: leq_trans (size_scale_leq _ _) _.
by apply: leq_trans (size_pT_leq _ _) _.
Qed.

Fixpoint Cb l (x : R) :=
 if l is a :: l' then
   let t := Cb l' x in
   let a1 := a + t.1 * x *+ 2 - t.2 in
   (a1, t.1) else (0, 0).

Lemma Cb_nil (r: R):
	Cb [::] r = (0, 0).
Proof. done. Qed.

Lemma Cb_eq0 q x : Poly q  = 0 -> Cb q x = 0.
Proof.
elim: q => //= a q IH.
rewrite cons_poly_def => H.
have := size_MXaddC (Poly q) a.
rewrite {}H size_poly0; case: eqP => // qZ.
case: eqP => // -> _.
by rewrite IH //= !rm0.
Qed.

Lemma Cb_eq q1 q2 x :
  Poly q1 = Poly q2 -> Cb q1 x = Cb q2 x.
Proof.
elim: q1 q2 => [/= q2 H|a q1 IH [/Cb_eq0->//|b q2]]; first by rewrite Cb_eq0.
rewrite /= !cons_poly_def => H.
have H1 : (Poly q1 - Poly q2) * 'X + (a - b)%:P = 0.
  by rewrite polyC_sub mulrBl addrAC addrA H addrK subrr.
have := size_MXaddC (Poly q1 - Poly q2) (a - b).
rewrite {}H1 size_poly0; case: eqP => // /subr0_eq/IH<-.
by case: eqP => // /subr0_eq <-.
Qed.

Definition lCshaw (L: seq R) x := (Cb L x).1 - (Cb L x).2 * x.

Lemma lCshaw_spec (k : seq R) r :
   lCshaw k r = (CPoly k).[r].
Proof.
rewrite /lCshaw /CPoly.
elim: {k}S {-2}k (leqnn (size k).+1) => // n IH [|a [|b l]] H.
- by rewrite /= big_ord0 horner0 !rm0.
- by rewrite /= !rm0 big_ord_recr big_ord0/= pT0 rm0 alg_polyC hornerC.
have /IH <- : (size (b :: l) < n)%N by rewrite -ltnS.
	rewrite 
  rewrite [_ * _ + _]addrC -subr_eq eq_sym.
  pose f (i : 'I_(size l)) := l`_i * ('T_i.+1).[r].
  rewrite (eq_bigr f) {}/f => [/eqP H1|i _] //.
rewrite [size _]/= 2!big_ord_recl.
pose f (i : 'I_(size l)) :=
  (l`_i * ('T_i.+1).[r] * (r *+2)) - (l`_i * ('T_i).[r]).
rewrite (eq_bigr f) {}/f => [|i _]; last first.
  rewrite pTSS !hornerE !mulrnAl hornerMn -commr_polyX hornerMX.
  by set x := 'T_i.+1; rewrite !lift0 /= {}/x mulrBr -mulrnAr mulrA.
rewrite !lift0 sumrB ![_ `_ _]/= -mulr_suml H1 -IH; last first.
  by rewrite -ltnS (ltn_trans _ H).
rewrite !hornerE /=.
(* This should be ring *)
set u := Cb _ _.
rewrite !mulr2n !(mulrDl, mulrDr, opprB, opprD, mulNr ) -!addrA.
do 40 (congr (_ + _); [idtac] || rewrite [RHS]addrC -![in RHS]addrA).
by rewrite addrA subrK.
Qed.

Definition ladd_Cpoly := ladd_poly.

Lemma ladd_Cpoly_spec (l k: seq R):
	CPoly (ladd_Cpoly l k) = (CPoly l) + (CPoly k).
Proof.
rewrite /ladd_Cpoly /CPoly.
under eq_bigr ? rewrite -coef_Poly.
rewrite polybase_widen; last exact: size_Poly.
rewrite ladd_poly_spec.
rewrite sumrA.
congr (_ + _).
	rewrite -(@polybase_widen _ _ _ (size l)); last exact: size_Poly.
	by under eq_bigr ? rewrite !coef_Poly.
rewrite -(@polybase_widen _ _ _ (size k)); last exact: size_Poly.
by under eq_bigr ? rewrite !coef_Poly.
Qed.

Fixpoint lpT2p_rec {R: ringType} l (p1 p2 : seq R) :=
match l with
|  a :: l =>
   ladd_poly (lscal_poly a p1)
     (lpT2p_rec l (lsub_poly (0 :: lscal_poly 2%:R  p1) p2) p1)
| _ => [::]
end.

Lemma lpT2p_rec_cons a (l l1 l2 : seq R) :
  lpT2p_rec (a :: l) l1 l2 =
   ladd_poly (lscal_poly a l1)
     (lpT2p_rec l (lsub_poly (0 :: lscal_poly 2%:R  l1) l2) l1).
Proof. by []. Qed.

Lemma lpT2p_rec_eq0 (q p1 p2 : seq R):
	Poly q = 0 -> Poly (lpT2p_rec q p1 p2) = 0.
Proof.
elim: q p1 p2 => // a q ih /= p1 p2.
move => /cons_poly_inj0 [-> eq].
rewrite ladd_poly_spec lscal_poly_spec.
by rewrite ih // -mul_polyC !rm0.
Qed.

Lemma lpT2p_rec_eq (q1 q2 p1 p2: seq R):
  Poly q1 = Poly q2 -> Poly (lpT2p_rec q1 p1 p2) = Poly (lpT2p_rec q2 p1 p2).
Proof.
elim: q1 q2 p1 p2 => // [q2 p1 p2 eq | a q1 ih q2 p1 p2 eq].
	by rewrite /= lpT2p_rec_eq0.
case: q2 eq.
	move => /cons_poly_inj0 [-> eq].
	rewrite ladd_poly_spec lscal_poly_spec.
	rewrite !rm0.
	by apply lpT2p_rec_eq0.
move => b q2 /cons_poly_inj [-> eq].
by rewrite !lpT2p_rec_cons !ladd_poly_spec !lscal_poly_spec (ih q2).
Qed.

Lemma lpT2p_rec_spec n (l: seq R):
   Poly (lpT2p_rec l (lpT R n.+1) (lpT R n)) =
      \sum_(i < size l) l`_i *: 'T_(n.+1 + i).
Proof.
elim: l n => [|a l IH] n.
  rewrite /= big1 // => i _.
  by rewrite nth_nil scale0r.
rewrite lpT2p_rec_cons ladd_poly_spec lscal_poly_spec.
rewrite (IH n.+1) //; last first.
rewrite big_ord_recl ?addn0.
congr (_ *: _ + _) => //.
by apply: eq_bigr => i _; rewrite addnS.
Qed.

Definition lpT2p {R : ringType} (l : seq R) :=
  match l with 
  | a :: l => 
     ladd_poly [::a] (lpT2p_rec l (lpT R 1) (lpT R 0))
  | _ => [::]
  end.

Lemma lpT2p_eq0 (q : seq R) :
  Poly q = 0 -> Poly (lpT2p q) = 0.
Proof.
case: q => // a q.
rewrite ladd_poly_spec =>/= /cons_poly_inj0 [-> eq].
rewrite cons_poly_def !rm0.
by rewrite lpT2p_rec_eq0.
Qed.

Lemma lpT2p_eq (q1 q2 : seq R) :
  Poly q1 = Poly q2 -> Poly (lpT2p q1) = Poly (lpT2p q2).
Proof.
case: q1 q2 => // [q2 /= eq | a q1 q2].
	by rewrite lpT2p_eq0.
case: q2 => // [/cons_poly_inj0 [-> eq] | b q2 /=/cons_poly_inj [-> eq]].
	rewrite ladd_const_poly_spec !rm0.
	by rewrite lpT2p_rec_eq0.
rewrite !ladd_const_poly_spec.
by rewrite (lpT2p_rec_eq _ _ eq).
Qed.

Lemma lpT2p_spec (l : seq R) :
   Poly (lpT2p l) = CPoly l.
Proof.
case: l => [ | a l]; first by	rewrite CPoly_nil.
rewrite /lpT2p.
rewrite ladd_poly_spec lpT2p_rec_spec.
rewrite /CPoly big_ord_recl ?add0n.
by f_equal; rewrite /= cons_poly_def !rm0 pT0 alg_polyC.
Qed.

End CPoly.

Compute (ncons 11 (0%:R: int) [::1]).

Compute lpT2p  (ncons 11 (0%:R: int) [::1]).

Section P2PT.

(*Variable R : unitRingType. This section works for unitRingType, only the proof of
is_Tmulx_uniqe needs R to be an idomainType and only because some of the
previous lemmas are stated in a weak form.*)
Variable R: idomainType.

Lemma size_CPoly_Poly (l: seq R) :
	(2%:R : R) \is a GRing.unit -> size (CPoly l) = size (Poly l).
Proof. 
move => I2.
rewrite /CPoly.
pose f (i: 'I_(size l)) := (Poly l)`_i  *: 'T_i.
rewrite (eq_bigr f) {}/f => [ | i _]; last by rewrite coef_Poly.
rewrite polybase_widen; last exact: size_Poly.
by rewrite size_sum_pT.
Qed.

Fixpoint lTmulx_rec (l : seq R) :=
  match l with 
  | a :: ((b :: c :: l) as l1) =>
      (a + c) / 2%:R :: lTmulx_rec l1 
  | l =>  [seq x /2%:R | x <- l]
  end.

Lemma lTmulx_rec_step a b c (l : seq R) :
	lTmulx_rec (a :: b :: c :: l) = (a + c) / 2%:R :: lTmulx_rec (b :: c :: l).
Proof. done. Qed.

Lemma pT_mulX n : 
   (2%:R : R) \is a GRing.unit -> 
   'X * 'T_n.+1 = 2%:R ^-1 *: 'T_n + 2%:R ^-1 *: 'T_n.+2 :> {poly R}.
Proof.
move=> H.
rewrite pTSS scalerDr addrCA scalerN subrr addr0.
by rewrite -scaler_nat -scalerAl scalerA mulVr // scale1r.
Qed.

Lemma lTmulx_rec_spec (l : seq R)  n :
  (2%:R : R) \is a GRing.unit -> 
  ('X * \sum_(i < size l) l`_i *: 'T_(n.+1 + i))%R =
  (l`_0 / 2%:R) *: 'T_n + (l`_1 / 2%:R) *: 'T_n.+1 +
  \sum_(i < size (lTmulx_rec l)) (lTmulx_rec l)`_i *: 'T_(n.+2 + i) :> {poly R}.
Proof.
move=> H.
elim: l n => [|a [|b [|c l]] IH] n.
- by rewrite !big_ord0 mul0r mulr0 !scale0r !add0r. 
- rewrite ![[:: _]`_ _]/= mul0r scale0r addr0.
  rewrite ![size _]/= !(big_ord0, big_ord_recl).
  rewrite ![_`_ _]/= !addr0 !addn0 -!scalerA -scalerDr.
  by rewrite -commr_polyX -scalerAl -pT_mulX // commr_polyX.
- rewrite ![[:: _; _]`_ _]/= ![size _]/= !(big_ord0, big_ord_recl).
  rewrite ![[:: _; _]`_ _]/= !addn1 !addn0 !addr0.
  rewrite -commr_polyX mulrDl -!scalerAl commr_polyX pT_mulX //.
  rewrite commr_polyX pT_mulX // scalerDr !scalerA -!addrA; congr (_ + _).
  rewrite [RHS]addrCA; congr (_ + _).
  by rewrite scalerDr !scalerA.
rewrite -[lTmulx_rec _]/((a + c) / 2%:R :: lTmulx_rec  [:: b, c & l]).
set u := [:: b, _ & _].
rewrite -[size _]/(size [:: b, c & l]).+1.
rewrite big_ord_recl mulrDr.
pose f (i : 'I_(size u)) := u`_i *: 'T_(n.+2 + i).
rewrite (eq_bigr f) => [|i _]; last first.
  by congr (_ *: 'T_ _); rewrite !addnS.
rewrite {f}IH.
rewrite ![_`_ _]/= addn0.
rewrite -/u.
set v := lTmulx_rec _.
rewrite -[size (_ :: _)]/(size v).+1.
rewrite [in RHS]big_ord_recl.
rewrite ![_`_ _]/= addn0.
pose f (i : 'I_(size v)) := v`_i *: 'T_(n.+3 + i).
rewrite [in RHS](eq_bigr f) => [|i _]; last first.
  by congr (_ *: 'T_ _); rewrite !addnS.
rewrite !addrA; congr (_ + _).
rewrite addrAC [in RHS] addrAC; congr (_ + _).
rewrite mulrDl scalerDl addrA; congr (_ + _).
rewrite -commr_polyX -scalerAl.
by rewrite commr_polyX pT_mulX // scalerDr !scalerA.
Qed.

Lemma size_lTmulx_rec l : size (lTmulx_rec l) = size l.
Proof. by elim: l => //= a [|b [|c l1]] IH //=; rewrite IH. Qed.

Lemma lTmulx_rec_eq0 L:
	Poly L = 0 -> Poly (lTmulx_rec L) = 0.
Proof.
elim: L => // a L ih.
rewrite [Poly _]/= => /= /cons_poly_inj0 [-> eq].
case: L eq ih => [_ /= | b L]; first by rewrite !cons_poly_def !rm0.
rewrite [Poly _]/= => /cons_poly_inj0 [-> eq] ih.
case: L eq ih => [_ /= | c L]; first by rewrite !cons_poly_def !rm0.
rewrite [Poly _]/= => /cons_poly_inj0 [-> eq]; rewrite !rm0.
by rewrite /= !cons_poly_def !rm0 => ->; try rewrite eq; rewrite !rm0.
Qed.

Lemma Poly_cons (a: R) K:
	Poly (a :: K) = cons_poly a (Poly K).
Proof. done. Qed.

Lemma lTmulx_rec_eq L K:
	Poly L = Poly K -> Poly (lTmulx_rec L) = Poly (lTmulx_rec K).
Proof.
elim: L K => [/= K eq | a L ih K]; first by rewrite lTmulx_rec_eq0.
case: K => [eq | a' K]; first by rewrite [lTmulx_rec [::]]/= lTmulx_rec_eq0.
rewrite ![Poly (_ :: _)]/= => /cons_poly_inj [-> eq].
case: L eq ih => [ | b L].
	case: K => // b' K; rewrite ![Poly _]/= => /esym /cons_poly_inj0 [-> eq] ih.
	case: K eq => [ | c' K]; first by rewrite /= !cons_poly_def !rm0.
	rewrite [Poly _]/= => /cons_poly_inj0 [-> /esym eq].
	rewrite lTmulx_rec_step !rm0.
	by rewrite !Poly_cons -ih; rewrite /= !cons_poly_def; try rewrite -eq; rewrite !rm0.
case: K.
	rewrite ![Poly _]/= => /cons_poly_inj0 [->].
	case: L => [ | c L]; first by rewrite /= !cons_poly_def !rm0.
	rewrite Poly_cons => /cons_poly_inj0 [-> eq] ih.
	by rewrite lTmulx_rec_step Poly_cons (ih nil); try rewrite eq; rewrite /= !cons_poly_def !rm0.
move => b' K.
rewrite !Poly_cons => /cons_poly_inj [->].
case: L => [ | c L].
	case: K => // c' K; rewrite ![Poly _]/= => /esym /cons_poly_inj0 [-> eq] ih.
	by rewrite lTmulx_rec_step !rm0 !Poly_cons -ih /=; try rewrite eq; rewrite !cons_poly_def !rm0.
case: K => [ | c' K].
	rewrite ![Poly _]/= => /cons_poly_inj0 [-> ->] ih.
	by rewrite lTmulx_rec_step Poly_cons (ih [:: b']) /= !cons_poly_def !rm0.
rewrite Poly_cons Poly_cons => /cons_poly_inj [-> eq] ih.
rewrite !lTmulx_rec_step !Poly_cons.
by rewrite (ih [:: b', c' & K]); last by rewrite /= !cons_poly_def eq.
Qed.

Definition lTmulx l :=
  lTmulx_rec (0 :: (if l is a :: l then (a *+ 2 :: l) else l)).

Lemma lTmulx_nil : lTmulx [::] = [:: 0].
Proof. by rewrite /lTmulx /= rm0. Qed.

Lemma size_lTmulx l : size (lTmulx l) = (size l).+1.
Proof. by case: l => // a l; rewrite size_lTmulx_rec. Qed.

Lemma lTmulx_eq L K:
	Poly L = Poly K -> Poly (lTmulx L) = Poly (lTmulx K).
Proof.
rewrite /lTmulx => eq.
apply lTmulx_rec_eq => /=; rewrite !cons_poly_def !rm0; congr (_ * _).
case: L K eq => [ | a L]; case => //=; last first.
		by move => b K /cons_poly_inj [-> ->].
	by move => /cons_poly_inj0 [-> ->]; rewrite !cons_poly_def !rm0.
by move => a L /esym/cons_poly_inj0 [-> ->]; rewrite !cons_poly_def !rm0.
Qed.

Lemma lTmulx_prop (l : seq R) :
  (2%:R : R) \is a GRing.unit -> 
  ('X * \sum_(i < size l) l`_i *: 'T_i)%R =
  \sum_(i < size (lTmulx l)) (lTmulx l)`_i *: 'T_i :> {poly R}.
Proof.
move=> H.
case: l => [|a l].
  by rewrite !(big_ord0, big_ord_recl) /= !rm0.
rewrite [size _]/= big_ord_recl.
rewrite (eq_bigr (fun i : 'I_(size l) => l`_i *: 'T_(1 + i))) => [|i _]; last first.
  by rewrite lift0.
rewrite mulrDr lTmulx_rec_spec // size_lTmulx_rec size_lTmulx //.
case: l => [|b l].
  rewrite !(big_ord0, big_ord_recl) /= !rm0 pT0 pT1.
  rewrite -[a *+ _]mulr_natl -commr_nat mulrK //.
  by rewrite -[RHS]mul_polyC alg_polyC commr_polyX.
rewrite ![size (_ :: _)]/= !(big_ord0, big_ord_recl) !addrA.
congr (_ + _ *: _ + _); last first.
- apply: eq_bigr => i _.
  by rewrite !lift0 !addnS; congr (_ *: _); case: l i.
- by case: l.
rewrite pT1 pT0 addrAC  addrC; congr (_ + _).
  by rewrite /= rm0.
rewrite -commr_polyX alg_polyC  mul_polyC -scalerDl; congr (_ *: _).
case: l => [|c l] /=.
  by rewrite !rm0 -[a *+ _]mulr_natl -commr_nat mulrK.
by rewrite mulrDl -[a *+ _]mulr_natl -commr_nat mulrK.
Qed.

Lemma lTmulx_spec l:
	(2%:R : R) \is a GRing.unit -> (CPoly (lTmulx l)) = 'X * (CPoly l).
Proof.
move=> H.
have H1 := lTmulx_prop l H.
by rewrite /CPoly H1.
Qed.

Definition lpXt i := iter i lTmulx [::1].

Lemma lpXt_step i:
	lpXt (S i) = lTmulx (lpXt i).
Proof.
by rewrite [LHS]iterS.
Qed.

Lemma lpXt_spec i:
	(2%:R : R) \is a GRing.unit -> (CPoly (lpXt i)) = 'X^i.
Proof.
move => u2.
elim: i => [ | i ih]; first by rewrite /CPoly big_ord1 pT0 expr0 /= alg_polyC.
rewrite lpXt_step lTmulx_spec => //.
rewrite [X in _ * X = _ ]ih.
by rewrite exprS.
Qed.

Fixpoint lp2pT (l : seq R) :=
  if l is a :: l1 then ladd_poly [:: a] (lTmulx (lp2pT l1))
  else [::].

Lemma lp2pT_cons a l :
  lp2pT (a :: l) = ladd_poly [:: a] (lTmulx (lp2pT l)).
Proof. by []. Qed.

Lemma size_CPoly l:
	(2%:R : R) \is a GRing.unit -> 
	(size (CPoly l :{poly R}) <= size l)%nat.
Proof.
by move => I2; rewrite size_CPoly_Poly; first apply: size_Poly.
Qed.

Lemma lp2pT_spec l :
  (2%:R : R) \is a GRing.unit -> CPoly (lp2pT l) = (Poly l).
Proof.
move => I2.
elim l => [ | a k ih]; first by rewrite CPoly_nil.
rewrite lp2pT_cons ladd_Cpoly_spec CPolyC/= cons_poly_def.
by rewrite lTmulx_spec => //; rewrite ih commr_polyX addrC.
Qed.

Definition p2pT' (p : {poly R}) : {poly R} := Poly (lp2pT p).

End P2PT.

Section pTab.
Variable R: fieldType.

Definition Tab (a b: R) := 	(1 + 1)/(b - a) *: 'X + (- (a + b) / (b - a))%:P.

Definition pTab a b n := 'T_n \Po (Tab a b).

Notation "''T^(' a ',' b ')_' n" := (pTab a b n)
  (at level 3, n at level 2, format "''T^(' a ',' b ')_' n").

Lemma horner_pTab a b n (x: R):
('T^(a,b)_n).[x] = ('T_n).[(x*+2 - a - b) / (b - a)].
Proof.
rewrite /pTab horner_comp /Tab.
rewrite hornerD hornerZ hornerX hornerC.
f_equal.
rewrite mulr2n -{2 3}[x]mul1r -[1 * x + 1 * x]mulrDl -addrA [RHS]mulrDl.
by rewrite -[-a-b]opprD -{3}[b-a]mulr1 -mulf_div divr1.
Qed.

Lemma horner_pTab_a a b n:
	b != a -> 	('T^(a,b)_n).[a] = ('T_n).[-1].
Proof.
move =>/eqP neq.
rewrite horner_pTab mulr2n -[a + a - a]addrA.
f_equal.
have -> : a - a = 0 by apply /eqP; rewrite (subr_eq0 a a).
rewrite rm0 -opprB mulNr divrr => //.
rewrite unitfE.
apply /eqP => /eqP eqn; apply /neq /eqP.
by rewrite -subr_eq0.
Qed.

Lemma horner_pTab_b a b n:
	b != a -> 	('T^(a,b)_n).[b] = ('T_n).[1].
Proof.
move =>/eqP neq.
rewrite horner_pTab mulr2n -!addrA [- a - b]addrC !addrA -[b + b - b]addrA.
have -> : b - b = 0 by apply /eqP; rewrite (subr_eq0 b b).
rewrite rm0 divrr => //.
rewrite unitfE.
apply /eqP => /eqP eqn; apply /neq /eqP.
by rewrite -subr_eq0.
Qed.
End pTab.

(* T_0(x)	=	1 *)
(* T_1(x)	=	x	 *)
(* T_2(x)	=	2 x^2 - 1 *)
(* T_3(x)	=	4 x^3 - 3 x *)
(* T_4(x)	=	8 x^4 - 8 x^2 + 1	*)
(* T_5(x)	=	16 x^5 - 20 x^3 + 5 x *)
(* T_6(x)	=	32 x^6 - 48 x^4 + 18 x^2 - 1 *)

Definition t0 := [:: ratz (Posz 1)].
Print t0.
Definition t1 := [:: 0; ratz (Posz 1)].
Definition t2 := [:: ratz (-(Posz 1)); 0; ratz (Posz 2)].
Definition t3 := [:: 0; ratz (- (Posz 3)); 0; ratz (Posz 4)].
Definition t4 := [:: ratz (Posz 1); 0; ratz (-(Posz 8)); 0; ratz (Posz 8)].
Definition t5 := [:: 0; ratz (Posz 5); 0; ratz (- (Posz 20)); 0; ratz (Posz 16)].
Definition t6 := [:: ratz (- (Posz 1)); 0; ratz (Posz 18); 0; ratz (- (Posz 48)); 0; ratz (Posz 32)].

Compute lp2pT t0.
Compute lp2pT t1.
Compute lp2pT t2.
Compute lp2pT t3.
Compute lp2pT t4.
Compute lp2pT t5.
Compute lp2pT t6.
