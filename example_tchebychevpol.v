From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Local Scope ring_scope.

Lemma gtn_size {R : ringType} (p : {poly R}) i : p`_i != 0 -> (i < size p)%N.
Proof.
rewrite leqNgt; apply: contra.
by rewrite ltnS => /leq_sizeP/(_ i)->.
Qed.

Definition rm0 :=
 (mulr0, mul0r, subr0, sub0r, add0r, addr0, mul0rn, mulr0n, oppr0,
  scale0r, scaler0).

Definition rm1 := (mulr1, mul1r, mulr1n).

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

End RBase.

Section Base.
Variable R : idomainType.
Variable F : nat -> {poly R}.
Hypothesis F0 : F 0 != 0.
Hypothesis F_size : forall n, size (F n) = n.+1.

Lemma size_polybase n p : 
   size (\sum_(i < n) p`_ i *: F i) = \max_(i < n | p`_i != 0) i.+1.
Proof.
elim: n => [|n IH]; first by rewrite !big_ord0 size_poly0.
rewrite [RHS]big_mkcond /= !big_ord_recr /= -big_mkcond /=.
have [/eqP Hp| Hnp /=] := boolP (p`_n == 0).
  by rewrite Hp scale0r addr0 IH /= maxn0.
have Hs : size (p`_ n *: F n) = n.+1 by rewrite size_scale.
case: (n) Hs IH => [Hs _|n1 Hs IH].
  by rewrite !big_ord0 add0r Hs.
rewrite addrC size_addl Hs.
  rewrite (maxn_idPr _) //.
  apply/bigmax_leqP=> i _.
  by apply: leq_trans (ltn_ord i) _; rewrite ltnW.
rewrite ltnS IH.
by apply/bigmax_leqP => i _.
Qed.

Lemma polybase_eq0 n (l: seq R) : 
   \sum_(i < n) l`_ i *: F i = 0 -> forall i, (i < n)%N -> l`_i = 0.
Proof.
move=> H i Hi.
suff P j : (0 < j < n)%N -> l`_j = 0.
  have := H.
  case: (n) Hi P => // n1 Hi P /eqP.
  rewrite big_ord_recl big1 => [|j _]; last first.
    by rewrite P ?scale0r // lift0 /= ltnS.
  rewrite addr0  scale_poly_eq0 (negPf F0) orbF.
  case: i Hi => [_ /eqP->//|i Hi _].
  by apply: P.
move=> /andP[HP1 HP2].
have /eqP := (H).
rewrite -size_poly_eq0 size_polybase -leqn0 => /bigmax_leqP/(_ (Ordinal HP2)).
by rewrite /=; case: eqP => //= _ /(_ isT).
Qed.

End Base.

Section Lpol.

Variable R : ringType.
Implicit Type p : {poly R}.

Definition ladd_const_poly a (l : seq R) := 
  if l is b :: l1 then (a + b) :: l1 else [:: a].

Lemma ladd_cons_poly_spec a l : Poly (ladd_const_poly a l) = a%:P + Poly l.
Proof.
by case: l => [|b l] /=; rewrite !cons_poly_def ?rm0 // polyC_add addrCA.
Qed.

Definition lopp_poly : seq R -> seq R := map -%R.

Lemma lopp_poly_spec l : Poly (lopp_poly l) = - Poly l.
Proof.
elim: l => [|a l IH]; rewrite /= ?rm0 //.
by rewrite !cons_poly_def IH opprD polyC_opp mulNr.
Qed.

Definition lscal_poly (a : R) := map (fun i => a * i).

Lemma lscal_poly_spec a l : Poly (lscal_poly a l) = a *: Poly l.
Proof.
elim: l => [|b l IH]; rewrite /= ?rm0 //.
by rewrite !cons_poly_def IH scalerDr scalerAl polyC_mul mul_polyC.
Qed.

(* l1 + l2 *)
Fixpoint ladd_poly (l1 l2 : seq R) :=
 if l1 is a :: l3 then
   if l2 is b :: l5 then a + b :: ladd_poly l3 l5
   else l1
 else l2.

Lemma ladd_poly_spec l1 l2 : Poly (ladd_poly l1 l2) = Poly l1 + Poly l2.
Proof.
elim: l1 l2 => [l2| a l1 IH [|b l2]]; rewrite /= ?rm0 //.
rewrite !cons_poly_def IH  polyC_add mulrDl.
by rewrite -addrA [Poly l2 * _ + _]addrCA addrA.
Qed.

(* l1 - l2 *)
Fixpoint lsub_poly (l1 l2 : seq R) :=
 if l1 is a :: l3 then
   if l2 is b :: l5 then a - b :: lsub_poly l3 l5
   else l1
 else lopp_poly l2.

Lemma lsub_poly_spec l1 l2 : Poly (lsub_poly l1 l2) = Poly l1 - Poly l2.
Proof.
elim: l1 l2 => [l2| a l1 IH [|b l2]]; rewrite /= ?rm0 //.
  by rewrite lopp_poly_spec.
rewrite !cons_poly_def IH  polyC_sub mulrBl.
by rewrite -addrA [-_ + _]addrCA opprD !addrA.
Qed.

End Lpol.

Section Tcheby.

Variable R : ringType.
Implicit Types (pl : seq R) (p: {poly R}) .

(* Chebychev *)

Definition pT {R: ringType} := fix pT_rec (n : nat) {struct n} : {poly R} :=
  if n is n1.+1 then
    if n1 is n2.+1 then 'X *+2 * pT_rec n1 - pT_rec n2
    else 'X
  else 1.

Notation "'T_ n" := (pT n) 
  (at level 3, n at level 2, format "''T_' n ").

Lemma pT0 : 'T_0 = 1 :> {poly R}.
Proof. done. Qed.

Lemma pT1 : 'T_1 = 'X :> {poly R}.
Proof. done. Qed.

Lemma pTSS : forall n, 'T_n.+2 = 'X *+2 * 'T_n.+1 - 'T_n :> {poly R}.
Proof. done. Qed.

Lemma horner1_pT n : ('T_n).[1: R] = 1.
Proof.
elim: n {-2}n (leqnn n) => [[] // _ |n IH]; first by rewrite hornerC.
move=> m; rewrite leq_eqVlt; case/orP => [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|n] IH; first by rewrite pT1 hornerX.
rewrite pTSS hornerD hornerN mulrnAl hornerMn.
by rewrite -commr_polyX hornerMX !IH // !mulr1 mulrS [1+ _]addrC addrK.
Qed.

Lemma commr_pT p n : GRing.comm p ('T_n).
Proof.
elim: n {-2}n (leqnn n)=> [[] // _ |n IH]; first  by exact: commr1.
move=> m; rewrite leq_eqVlt; case/orP=> [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|n] IH; first by exact: commr_polyX.
rewrite pTSS; apply: commrD; last by apply: commrN; apply: IH.
by rewrite mulrnAl; apply: commrMn; apply: commrM;
 [exact: commr_polyX | apply: IH].
Qed.

Definition pU := fix pU_rec (n : nat) {struct n} : {poly R} :=
  if n is n1.+1 then
    if n1 is n2.+1 then 'X *+ 2 * pU_rec n1 - pU_rec n2
    else 'X *+ 2
  else 1.

Notation "'U_ n" := (pU n) 
  (at level 3, n at level 2, format "''U_' n ").

Lemma pU0 : 'U_0 = 1.
Proof. by []. Qed.

Lemma pU1 : 'U_1 = 'X *+ 2.
Proof. by []. Qed.

Lemma pUSS n : 'U_n.+2 = 'X *+ 2 * 'U_n.+1 - 'U_n.
Proof. by []. Qed.

Lemma horner1_pU n : ('U_n).[1] = n.+1%:R.
Proof.
elim: n {-2}n (leqnn n)=> [[] // _ |n IH]; first by rewrite hornerC.
move=> m; rewrite leq_eqVlt; case/orP=> [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|n] IH.
  by rewrite pU1 hornerMn hornerX.
rewrite pUSS hornerD hornerN mulrnAl hornerMn.
rewrite -commr_polyX hornerMX mulr1 !IH //.
rewrite -mulr_natl -natrM -natrB; last first.
  by rewrite mulSn !addSnnS addnS ltnS leq_addr.
by rewrite mul2n -addnn -addSnnS addnK.
Qed.

Lemma commr_pU p n : GRing.comm p ('U_n).
Proof.
elim: n {-2}n (leqnn n)=> [[] // _ |n IH]; first  by exact: commr1.
move=> m; rewrite leq_eqVlt; case/orP=> [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|n] IH.
   rewrite pU1; apply: commrMn; exact: commr_polyX.
rewrite pUSS; apply: commrD; last by apply: commrN; apply: IH.
by rewrite mulrnAl; apply: commrMn; apply: commrM;
   [exact: commr_polyX | apply: IH].
Qed.

Lemma pT_pU n : 'T_n.+1 = 'U_n.+1 - 'X * 'U_n.
Proof.
have F: pU 1 - 'X * pU 0 = 'X by rewrite pU1 pU0 mulr1 addrK.
elim: n {-2}n (leqnn n)=> [[] // _ |m IH].
move=> n; rewrite leq_eqVlt; case/orP=> [|Hn]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; rewrite pTSS pUSS IH // mulrDr -!addrA; congr (_ + _).
case: m IH=> [_|m IH].
  rewrite pT0 pU0 pU1 addrC mulrN; congr (_ - _).
  by rewrite mulr1 mulrnAl mulrnAr.
rewrite IH // pUSS addrC opprD -!addrA; congr (_ + _).
rewrite mulrDr !mulrN opprB opprK; congr (_ - _).
by rewrite !mulrA commr_polyX.
Qed.

Lemma deriv_pT n: ('T_n.+1)^`() = 'U_n *+ n.+1.
Proof.
elim: n {-2}n (leqnn n)=> [[] // _ |m IH].
  by rewrite pT1 derivX.
move=> n; rewrite leq_eqVlt; case/orP=> [|Hn]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; rewrite pTSS derivD derivM derivMn derivX !IH //.
rewrite pT_pU.
case: m IH=> [_|m IH].
  by rewrite pU0 pU1 pT0 derivN derivC subr0 mulr_natl mulrnBl !mulr1 addrK.
rewrite derivN IH // pUSS mulr_natl !(mulrnDl, mulrnBl).
rewrite !(mulrnAl, mulrnAr) -!mulrnA.
set x := 'X * _; set y := pU m.
rewrite -[x *+ _ + _ *+ _]addrC -3!addrA addrC.
rewrite addrA -[(2 * 2)%N]/(2 + 2)%N mulrnDr.
rewrite mulNrn addrK.
rewrite -mulrnDr mulnC; rewrite -addrA; congr (_ + _)=> //.
  congr (_ *+ _); rewrite !mul2n //.
by rewrite -mulNrn -mulrnDr addnC.
Qed.

Lemma coef_pU : forall n i,
  ('U_n)`_i =
    if (n < i)%N || odd (n + i) then 0 else
    let k := (n - i)./2 in ((-1)^+k * (2^i * 'C(n-k,k))%:R).
Proof.
move=> n; elim: n {-2}n (leqnn n)=> [[] // _ |m IH].
  by case=>[|i]; rewrite pU0 ?coefC //= mul1r.
move=> n; rewrite leq_eqVlt; case/orP=> [|Hn]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: m IH=> [_ i|m IH i].
  by rewrite coefMn coefX; case: i=> [|[|i]] //=;
     rewrite ?mul0rn //= -mulr_natl mulr1 mul1r. 
rewrite pUSS coefB mulrnAl coefMn coefXM !IH //.
case: i=> [|i].
  rewrite !addn0 mul0rn sub0r subn0 /=; case O1: (odd _); first by rewrite oppr0.
  rewrite !mul1n /= exprS !mulNr subSS mul1r.
  rewrite -{2 6}[m]odd_double_half O1 add0n subSn -addnn ?leq_addr //.
  by rewrite  addnK !binn.
rewrite !addSn !addnS /=; case O1: (odd _); last first.
   by rewrite !orbT mul0rn  subrr.
rewrite !orbF !subSS; case: leqP=> Hm; last first.
  rewrite ltnS (leq_trans _ Hm); last by  exact: (leq_addl 2 m).
  by rewrite mul0rn  sub0r oppr0.
rewrite ltnS.
move: Hm; rewrite leq_eqVlt; case/orP.
  move/eqP->.
  by rewrite subnn leqnSn !mul1r !bin0 !muln1 subr0 -mulr_natl -natrM.
rewrite ltnS leq_eqVlt; case/orP; [move/eqP->|move=>Him].
  by rewrite leqnn subSnn !subn0 expr0 !bin0 
             subr0 !mul1r !muln1 -mulr_natl -natrM expnS.
rewrite leqNgt Him /= subSn; last by exact: ltnW.
have->: ((m - i).+1./2 = (m - i)./2.+1).
 rewrite -{1}[(m-i)%N]odd_double_half.
 rewrite (odd_sub (ltnW _)) // -odd_add O1.
 by rewrite /= (half_bit_double _ false).
have->: ((m - i.+1)./2 = (m - i)./2).
 rewrite subnS -{1}[(m-i)%N]odd_double_half.
 rewrite (odd_sub (ltnW _)) // -odd_add O1.
 by rewrite /= (half_bit_double _ false).
set u := (m - i)./2.
rewrite !subSS subSn.
  rewrite binS mulnDr mulrnDr mulrDr; congr (_ + _).
    by rewrite -mulrnAr -mulr_natl -natrM mulnA expnS.
  by rewrite -mulN1r mulrA exprS. 
apply: (leq_trans (half_leq (leq_subr i m))).
by rewrite -{2}[m]odd_double_half -addnn addnA leq_addl.
Qed.

Lemma coef_pUn n : ('U_n)`_n = (2^n)%:R.
Proof.
by rewrite coef_pU ltnn addnn odd_double subnn /= bin0 mul1r muln1.
Qed.

Lemma size_pU_leq n : (size ('U_n) <= n.+1)%N.
Proof. by apply/leq_sizeP=> j Hj; rewrite coef_pU Hj. Qed.

Lemma coef_pT n i :
  ('T_n)`_i =
    if (n < i)%N || odd (n + i) then 0 : R else
    if n is 0 then 1 else
    let k := (n - i)./2 in 
    (-1) ^+ k * ((2^i * n * 'C(n-k,k)) %/ (n-k).*2)%:R.
Proof.
case: n => [|n]; first by rewrite pT0 coefC; case: i.
rewrite pT_pU coefB coefXM !coef_pU.
case: leqP; last first.
  by case: i=> [|i] //; rewrite ltnS=> ->; exact: subrr.
case: i => [_|i Hi].
  rewrite addn0; case O1: (odd _); first by exact: subr0.
  rewrite !subr0 !subn0 !mul1n; congr (_ * _); congr (_%:R).
  have F: n.+1 = (n.+1)./2.*2 by rewrite-{1}[(n.+1)%N]odd_double_half O1.
  by rewrite {8}F -[_./2.*2]addnn addnK -F mulKn // mul1n.
rewrite subSS addnS /=; case O1: (odd _); first by rewrite orbT subr0.
rewrite orbF; move: (Hi); rewrite ltnS leqNgt; move/negPf->.
rewrite -mulrBr; congr (_ * _).
rewrite -natrB; last first.
  apply: leq_mul; first rewrite leq_exp2l //.
  by apply: leq_bin2l; apply: leq_sub2r.
congr (_%:R).
have F: (n-i = (n-i)./2.*2)%N
   by rewrite-{1}[(n-i)%N]odd_double_half odd_sub // -odd_add O1.
set u := (n - i)./2.
have F1: (u <= n)%N.
  by apply: leq_trans (leq_subr i _); rewrite F -addnn leq_addl.
rewrite subSn //.
have->: (n - u = i + u)%N.
  rewrite ltnS in Hi; rewrite -{1}(subnK Hi) [(_ + i)%N]addnC.
  by rewrite -addnBA;
     [rewrite {1}F -addnn addnK | rewrite F -addnn leq_addr].
set v := (i + u)%N.
rewrite {2}expnS -!mulnA -mul2n divnMl //.
pose k := (u`! * (v.+1 - u)`!)%N.
have Fk: k != 0%N.
  apply/eqP=> Hk; move: (leqnn k); rewrite {2}Hk leqNgt.
  by rewrite /k !(muln_gt0,fact_gt0).
apply/eqP; rewrite -[_ == _]orFb -(negPf Fk).
have F2: (u <= v)%N by apply: leq_addl.
have F3 : (u <= v.+1)%N   by apply: (leq_trans F2).
have F4: (u + v = n)%N by rewrite addnC -addnA addnn -F addnC subnK.
rewrite -eqn_mul2r mulnBl -!mulnA bin_fact //.
rewrite expnSr -mulnA -mulnBr {1}/k subSn // [(_ - _).+1`!]factS.
rewrite [((_ - _).+1 * _)%N]mulnC 2!mulnA -[('C(_,_) * _ * _)%N]mulnA.
rewrite bin_fact ?leqDl // [(2 * _)%N]mulnC.
rewrite factS [(v.+1 * _)%N]mulnC -!mulnA -mulnBr.
rewrite -subSn // subnBA //.
rewrite [(_ + u)%N]addnC muln2 -addnn !addnA addnK.
rewrite divn_mulAC.
  rewrite -!mulnA bin_fact //.
  rewrite factS [(v.+1 * _)%N]mulnC !mulnA mulnK //.
  by apply/eqP; rewrite -!mulnA addnS F4 [(v`! * _)%N]mulnC.
rewrite dvdn_mull // -F4 -addnS mulnDl dvdn_add //; last first.
  by rewrite /dvdn; apply/eqP; exact: modnMr.
case: {1 2}u=> [|u1]; first by exact: dvdn0.
rewrite -mul_Sm_binm.
by rewrite /dvdn; apply/eqP; exact: modnMr.
Qed.

Lemma coef_pTK  n i :
   ~~ odd (n + i) -> (i <= n)%N ->
  let k := (n - i)./2 in 
  ('T_n)`_i *+ (n-k).*2 = (-1)^+k * (2^i * n * 'C(n-k,k))%:R :> R.
Proof.
move=> O1 L1; rewrite coef_pT; move/negPf: (O1)->.
move: (L1); rewrite leqNgt; move/negPf->.
case: n L1 O1 => [|n] L1  O1 /=; first by rewrite !muln0 mulr0.
rewrite -mulrnAr; congr (_ * _); rewrite -mulr_natl -natrM; congr (_%:R).
case: i L1 O1 => [|i L1 O1].
  rewrite addn0 subn0=> _ O1.
  have F: n.+1 = (n.+1)./2.*2
    by rewrite-{1}[n.+1]odd_double_half // (negPf O1).
  have ->: (n.+1 - (n.+1)./2 = (n.+1)./2)%N by rewrite {1}F -addnn addnK.
  by rewrite -F mul1n mulKn //.
set u := (n.+1 -i.+1)./2.
have F: (n.+1 - i.+1 = u.*2)%N.
  by rewrite-{1}[(n.+1 - i.+1)%N]odd_double_half /u odd_sub // -odd_add (negPf O1).
have->: (n.+1 - u = i.+1 + u)%N.
  rewrite -{1}(subnK L1) [(_ + i.+1)%N]addnC.
  by rewrite -addnBA;
     [rewrite {1}F -addnn addnK | rewrite F -addnn leq_addr].
rewrite expnS -!mul2n -!mulnA divnMl //;  congr (_ * _)%N.
apply/eqP; rewrite mulnC -dvdn_eq.
have->: (n.+1 = u + (i.+1 + u))%N by rewrite addnC -addnA addnn -F addnC subnK.
apply: dvdn_mull.
case: {F}u=> [|u]; first by rewrite !muln1 !addn0 dvdnn.
by rewrite mulnDl dvdn_add //; first rewrite addnS -mul_Sm_binm;
   apply: dvdn_mulr; exact: dvdnn.
Qed.

Lemma coef_pTn n : ('T_n)`_n = (2 ^ n.-1)%:R :> R.
Proof.
case: n => [|n]; rewrite coef_pT ltnn addnn odd_double //= subnn subn0.
rewrite mul1r expnS [(2 * _)%N]mulnC -!mulnA [(2 * _)%N]mulnA mul2n.
by rewrite mulnC -!mulnA mulKn // bin0 mul1n.
Qed.

Lemma size_pT_leq n : (size (pT n : {poly R}) <= n.+1)%N.
Proof.
by apply/leq_sizeP => j Hj; rewrite coef_pT Hj.
Qed.

(* Pell equation *)

Lemma pell n : ('T_n.+1)^+2 - ('X^2 - 1) * ('U_n) ^+ 2 = 1.
Proof.
suff F: (pU n.+1)^+ 2 + (pU n)^+2 = 'X *+ 2 * pU n.+1 * pU n + 1.
  rewrite pT_pU exprS expr1 !mulrDl !mulrDr opprD !mulNr.
  rewrite !addrA addrC opprK mul1r !addrA [_^+2 + _]addrC F.
  apply: trans_equal (addr0 _); rewrite [_+1]addrC -!addrA; congr (_ + _).
  rewrite mulrN mulrA commr_polyX !addrA !mulrDl addrK.
  rewrite -mulrA -commr_pU mulrA addrN sub0r.
  by rewrite mulrN opprK -mulrA -commr_pU exprS expr1 exprS expr1 !mulrA addrN.
elim: n => [| n IH].
  by rewrite pU1 pU0 mulr1 expr1n exprS expr1.
rewrite pUSS exprS !mulrBr !mulrBl -!addrA; congr (_ + _).
  rewrite !(mulrnAl,mulrnAr); do 2 congr (_ *+ _).
  by rewrite -!mulrA; congr (_ * _); rewrite -commr_pU mulrA.
congr (_ + _); first by rewrite -commr_pU -!mulrA commr_pU.
by rewrite opprB addrC addrA IH [_+1]addrC addrK.
Qed.

Fixpoint Cb q (x : R) :=
 if q is a :: q' then
   let t := Cb q' x in
   let a1 := a + t.1 * x *+ 2 - t.2 in
   (a1, t.1) else (0, 0).

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

Definition Cshaw p x := (Cb p x).1 - (Cb p x).2 * x.

Lemma Cshaw_spec (p : {poly R}) r :
   Cshaw p r = \sum_(i < size p) p`_i  * ('T_i).[r].
Proof.
case: p; rewrite /Cshaw => /= l _.
elim: {l}S {-2}l (leqnn (size l).+1) => // n IH [|a [|b l]] H.
- by rewrite big_ord0 !rm0.
- by rewrite /= !rm0 big_ord_recr big_ord0 /= hornerC rm1 rm0.
have /IH/eqP : (size (b :: l) < n)%N by rewrite -ltnS.
  rewrite [size _]/= big_ord_recl. 
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

Lemma CshawC c r : Cshaw c%:P r = c.
Proof.
rewrite Cshaw_spec /= size_polyC.
case: eqP => [->|/eqP H] /=; first by rewrite big_ord0.
by rewrite big_ord_recr big_ord0 polyseqC (negPf H) !hornerE.
Qed.

Lemma Cshaw0 x : Cshaw 0 x = 0.
Proof. by rewrite CshawC. Qed.

Lemma CshawZ a p x : Cshaw (a *: p) x = a * Cshaw p x.
Proof.
rewrite !Cshaw_spec mulr_sumr.
rewrite -(big_mkord xpredT (fun i => a * (p`_i * ('T_i ).[x]))).
rewrite (big_cat_nat _ _ _ _ (size_scale_leq a p)) //= big_mkord.
rewrite [X in _ = _ + X]big_nat_cond [X in _ = _ + X]big1 ?addr0 => [|i].
  by apply: eq_bigr => i _; rewrite coefZ mulrA.
rewrite andbT => /andP[/(@leq_sizeP R) // H1 H2].
by rewrite mulrA -coefZ H1 ?rm0.
Qed.

Lemma CshawN p x : Cshaw (- p) x = - Cshaw p x.
Proof. by rewrite -scaleN1r CshawZ mulN1r. Qed.

Lemma CshawD p q x : Cshaw (p + q) x = Cshaw p x + Cshaw q x.
Proof.
rewrite !Cshaw_spec.
apply: etrans (_ : \sum_(i < maxn (size p) (size q)) (p + q)`_i * ('T_i ).[x] = _).
  rewrite -[RHS](big_mkord xpredT (fun i => (p + q)`_i * ('T_i ).[x])).
  rewrite (big_cat_nat _ _ _ _ (size_add p q)) //= big_mkord.
  rewrite [X in _ = _ + X]big_nat_cond [X in _ = _ + X]big1 ?addr0 // => i.
  rewrite andbT => /andP[/(@leq_sizeP R) // -> // _].
  by rewrite rm0.
pose f (i : 'I_ _) := p`_i * ('T_i ).[x] + q`_i * ('T_i ).[x].
rewrite (eq_bigr (f _)) {}/f => [|i _]; last by rewrite coefD mulrDl.
rewrite big_split /=; congr (_ + _).
  rewrite -(big_mkord xpredT (fun i => p`_i * ('T_i ).[x])).
  rewrite (big_cat_nat _ _ _ _ (leq_maxl _ _)) //= big_mkord.
  rewrite [X in _ + X = _]big_nat_cond [X in _ + X = _]big1 ?addr0 // => i.
  rewrite andbT => /andP[/(@leq_sizeP R) // -> // _].
  by rewrite rm0.
rewrite -(big_mkord xpredT (fun i => q`_i * ('T_i ).[x])).
rewrite (big_cat_nat _ _ _ _ (leq_maxr _ _)) //= big_mkord.
rewrite [X in _ + X = _]big_nat_cond [X in _ + X = _]big1 ?addr0 // => i.
rewrite andbT => /andP[/(@leq_sizeP R) // -> // _].
by rewrite rm0.
Qed.

Lemma CshawXn r n : Cshaw ('X^n) r = ('T_n).[r].
Proof.
rewrite Cshaw_spec size_polyXn.
rewrite (bigD1 (Ordinal (leqnn _))) //=.
rewrite coefXn eqxx rm1 big1 ?rm0 //= => i /eqP/val_eqP/= Hi.
by rewrite coefXn (negPf Hi) rm0.
Qed.

Lemma CshawX r : Cshaw ('X) r = ('T_1).[r].
Proof. by rewrite -CshawXn. Qed.

Section PT2P.

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

Lemma lpT2p_rec_spec n (l l1 l2 : seq R) :
   Poly l1 = 'T_n.+1 -> Poly l2 = 'T_n ->
   Poly (lpT2p_rec l l1 l2) =
      \sum_(i < size l) l`_i *: 'T_(n.+1 + i).
Proof.
elim: l l1 l2 n => [|a l IH] l1 l2 n Hl1 Hl2.
  rewrite /= big1 // => i _.
  by rewrite nth_nil scale0r.
rewrite lpT2p_rec_cons ladd_poly_spec lscal_poly_spec.
rewrite (IH _  _ n.+1) //; last first.
  rewrite lsub_poly_spec [Poly _]/= cons_poly_def lscal_poly_spec Hl1 Hl2 rm0.
  by rewrite commr_polyX pTSS scaler_nat mulrnAl -mulrnAr .
rewrite [size (_ :: _)]/= big_ord_recl ?addn0; congr (_ *: _ + _) => //.
by apply: eq_bigr => i _; rewrite addnS.
Qed.

Definition lpT2p {R : ringType} (l : seq R) :=
  match l with 
  | a :: l => 
     ladd_poly [::a] (lpT2p_rec l [::0; 1] [::1])
  | _ => [::]
  end.

Lemma lpT2p_spec (l : seq R) :
   Poly (lpT2p l) = \sum_(i < size l) l`_i *: 'T_i.
Proof.
case: l => [|a l]; first by rewrite /= big_ord0.
rewrite /lpT2p ladd_poly_spec /= cons_poly_def !rm0.
rewrite big_ord_recl; congr (_ + _).
  by rewrite alg_polyC.
by rewrite (@lpT2p_rec_spec 0) //= !cons_poly_def ?rm0 ?rm1.
Qed.

Definition pT2p (p : {poly R}) : {poly R} := Poly (lpT2p p).

Lemma pT2p_spec p : pT2p p = \sum_(i < size p) p`_i *: 'T_i.
Proof. by exact: lpT2p_spec. Qed. 

Lemma size_pT2p_leq p : (size (pT2p p) <= size p)%N.
Proof.
rewrite pT2p_spec.
apply: (leq_trans (size_sum _ _ _)).
apply/bigmax_leqP => i _.
apply: leq_trans (size_scale_leq _ _) _.
by apply: leq_trans (size_pT_leq _) _.
Qed.

Lemma pT2p0 : pT2p 0 = 0 :> {poly R}.
Proof. by rewrite /pT2p polyseq0. Qed.

Lemma Cshaw_horner p r : Cshaw p r = (pT2p p).[r].
Proof.
rewrite Cshaw_spec pT2p_spec horner_sum.
by apply: eq_bigr => i _; rewrite hornerE.
Qed.

End PT2P.

End Tcheby.

Compute (ncons 11 (0%:R: int) [::1]).

Compute lpT2p  (ncons 11 (0%:R: int) [::1]).

Notation "'T_ n " := (pT n) (at level 3, n at level 2, format "''T_' n").

Section P2PT.

Variable R : unitRingType.

Fixpoint Tmulx_rec (l : seq R) :=
  match l with 
  | a :: ((b :: c :: l) as l1) =>
      (a + c) / 2%:R :: Tmulx_rec l1 
  | l =>  [seq x /2%:R | x <- l]
  end.

Lemma XpT n : 
   (2%:R : R) \is a GRing.unit -> 
   'X * 'T_n.+1 = 2%:R ^-1 *: 'T_n + 2%:R ^-1 *: 'T_n.+2 :> {poly R}.
Proof.
move=> H.
rewrite pTSS scalerDr addrCA scalerN subrr addr0.
by rewrite -scaler_nat -scalerAl scalerA mulVr // scale1r.
Qed.

Lemma Tmulx_rec_spec (l : seq R)  n :
  (2%:R : R) \is a GRing.unit -> 
  ('X * \sum_(i < size l) l`_i *: 'T_(n.+1 + i))%R =
  (l`_0 / 2%:R) *: 'T_n + (l`_1 / 2%:R) *: 'T_n.+1 +
  \sum_(i < size (Tmulx_rec l)) (Tmulx_rec l)`_i *: 'T_(n.+2 + i) :> {poly R}.
Proof.
move=> H.
elim: l n => [|a [|b [|c l]] IH] n.
- by rewrite !big_ord0 mul0r mulr0 !scale0r !add0r. 
- rewrite ![[:: _]`_ _]/= mul0r scale0r addr0.
  rewrite ![size _]/= !(big_ord0, big_ord_recl).
  rewrite ![_`_ _]/= !addr0 !addn0 -!scalerA -scalerDr.
  by rewrite -commr_polyX -scalerAl -XpT // commr_polyX.
- rewrite ![[:: _; _]`_ _]/= ![size _]/= !(big_ord0, big_ord_recl).
  rewrite ![[:: _; _]`_ _]/= !addn1 !addn0 !addr0.
  rewrite -commr_polyX mulrDl -!scalerAl commr_polyX XpT //.
  rewrite commr_polyX XpT // scalerDr !scalerA -!addrA; congr (_ + _).
  rewrite [RHS]addrCA; congr (_ + _).
  by rewrite scalerDr !scalerA.
rewrite -[Tmulx_rec _]/((a + c) / 2%:R :: Tmulx_rec  [:: b, c & l]).
set u := [:: b, _ & _].
rewrite -[size _]/(size [:: b, c & l]).+1.
rewrite big_ord_recl mulrDr.
pose f (i : 'I_(size u)) := u`_i *: 'T_(n.+2 + i).
rewrite (eq_bigr f) => [|i _]; last first.
  by congr (_ *: 'T_ _); rewrite !addnS.
rewrite {f}IH.
rewrite ![_`_ _]/= addn0.
rewrite -/u.
set v := Tmulx_rec _.
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
by rewrite commr_polyX XpT // scalerDr !scalerA.
Qed.

Lemma size_Tmulx_rec l : size (Tmulx_rec l) = size l.
Proof.
elim: l => //= a [|b [|c l1]] IH //=.
by rewrite IH.
Qed.

Definition Tmulx l :=
  Tmulx_rec (0 :: (if l is a :: l then (a *+ 2 :: l) else l)).

Lemma size_Tmulx l : l != [::] -> size (Tmulx l) = (size l).+1.
Proof. by case: l => // a l; rewrite size_Tmulx_rec. Qed.

Lemma Tmulx_spec (l : seq R) :
  (2%:R : R) \is a GRing.unit -> 
  ('X * \sum_(i < size l) l`_i *: 'T_i)%R =
  \sum_(i < size (Tmulx l)) (Tmulx l)`_i *: 'T_i :> {poly R}.
Proof.
move=> H.
case: l => [|a l].
  by rewrite !(big_ord0, big_ord_recl) /= !rm0.
rewrite [size _]/= big_ord_recl.
rewrite (eq_bigr (fun i : 'I_(size l) => l`_i *: 'T_(1 + i))) => [|i _]; last first.
  by rewrite lift0.  
rewrite mulrDr Tmulx_rec_spec // size_Tmulx_rec size_Tmulx //.
case: l => [|b l].
  rewrite !(big_ord0, big_ord_recl) /= !rm0.
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

Lemma Tmulx_nil : Tmulx [::] = [:: 0].
Proof. by rewrite /Tmulx /= rm0. Qed.

Fixpoint lp2pT (l : seq R) :=
  if l is a :: l1 then ladd_const_poly a (Tmulx (lp2pT l1))
  else [::].

Lemma lp2pT_cons a l :
  lp2pT (a :: l) = ladd_const_poly a (Tmulx (lp2pT l)).
Proof. by []. Qed. 


Lemma lp2pT_spec l :
  (2%:R : R) \is a GRing.unit -> 
  Poly l =
  \sum_(i < size (lp2pT l)) (lp2pT l)`_i *: 'T_i :> {poly R}.
Proof.
move=> I2.
elim: l => [|a l IH] /=; first by rewrite big_ord0.
rewrite cons_poly_def IH commr_polyX Tmulx_spec //.
case: lp2pT => [|b l1].
  by rewrite Tmulx_nil !(big_ord_recr, big_ord0) /= !rm0 alg_polyC.
case: Tmulx (size_Tmulx (isT: (b :: l1) != [::])) => //= c l2 ->.
rewrite big_ord_recl [RHS]big_ord_recl addrAC /=; congr (_ + _).
by rewrite !alg_polyC polyC_add addrC.
Qed.

Definition p2pT (p : {poly R}) : {poly R} := Poly (lp2pT p).

Lemma p2pT_spec (p : {poly R}) :
  (2%:R : R) \is a GRing.unit -> 
  p =
  \sum_(i < size (p2pT p)) (p2pT p)`_i *: 'T_i :> {poly R}.
Proof.
move=> H.
rewrite -{1}[p]polyseqK [LHS]lp2pT_spec // /p2pT.
rewrite -(polybase_widen _ (size_Poly (lp2pT p))).
by apply: eq_bigr => i _; rewrite coef_Poly.
Qed.

Lemma p2pTK : 
  (2%:R : R) \is a GRing.unit -> 
  cancel p2pT (@pT2p R).
Proof. by move=> I2 p; rewrite {2}[p]p2pT_spec // pT2p_spec. Qed.

Lemma p2pT0 : p2pT 0 = 0 :> {poly R}.
Proof. by rewrite /p2pT polyseq0. Qed.

End P2PT.


Section LEMMAS.

Variable R: idomainType.
Variable V2 : (2%:R : R) \is a GRing.unit.

Lemma size_pT n : size ('T_ n : {poly R}) = n.+1.
Proof.
have := size_pT_leq R n.
rewrite leq_eqVlt => /orP[/eqP//|].
rewrite ltnS => /leq_sizeP/(_ _ (leqnn _))/eqP.
rewrite coef_pTn natrX expf_eq0 andbC.
have := divrr V2.
case: eqP => [->|//] /eqP.
by rewrite mul0r eq_sym oner_eq0.
Qed.

Lemma pT_eq (p q : {poly R}) :
  p = q <-> \sum_(i < size p) p`_i *: 'T_ i = 
            \sum_(i < size q) q`_i *: 'T_ i.
Proof.
split=> [->//|/eqP].
rewrite -(polybase_widen _ (leq_maxl (size p) (size q))).
rewrite -(polybase_widen _ (leq_maxr (size p) (size q))).
rewrite -subr_eq0 -sumrB.
pose f (i : 'I_(maxn (size p) (size q))) := ((p- q)`_i) *: 'T_ i.
rewrite (eq_bigr f) {}/f => [/eqP eq|i _]; last by rewrite coefB scalerBl.
apply: subr0_eq.
rewrite -polyP => i; rewrite coef0.
have [ineq|ineq]:= (ltnP i (maxn (size p) (size q))).
  apply: polybase_eq0 eq _ ineq; first by rewrite pT0 oner_eq0.
  by apply size_pT.
apply/ leq_sizeP; last apply ineq.
by rewrite -[size q]size_opp size_add.
Qed.

Lemma pTK2p : 
  (2%:R : R) \is a GRing.unit -> 
  cancel (@pT2p R) (@p2pT R).
Proof. by move=> I2 p; apply/pT_eq; rewrite -p2pT_spec // pT2p_spec. Qed.

Lemma size_pT2p (p : {poly R}) : size (pT2p p) = size p.
Proof.
have [/eqP->|pNZ] := boolP (p == 0); first by rewrite pT2p0.
rewrite pT2p_spec size_polybase => [|i]; last by apply: size_pT.
rewrite {-7}(polySpred pNZ).
rewrite big_mkcond big_ord_recr /= -big_mkcond /=.
rewrite -lead_coefE lead_coef_eq0 pNZ /= -(polySpred pNZ).
rewrite (maxn_idPr _) //.
apply/bigmax_leqP=> i _.
by apply: leq_trans (leq_pred  _).
Qed.

Lemma pT2pZ a (p : {poly R}) : pT2p (a *: p) = a *: pT2p p.
Proof.
have [->|/eqP aNZ] := (a =P 0); first by rewrite !rm0 pT2p0.
rewrite !pT2p_spec.
pose f (i : 'I_(size (a*: p))) := a *: (p`_ i *: 'T_i).
rewrite (eq_bigr f) {}/f => [|i _]; last by rewrite scalerA coefZ.
have ->: size (a *: p) =  size p by rewrite size_scale.
by rewrite scaler_sumr.
Qed.

Lemma pT2pD (p q : {poly R}) : pT2p (p + q) = pT2p p + pT2p q.
Proof.
rewrite !pT2p_spec.
rewrite -(polybase_widen _ (leq_maxl (size p) (size q))).
rewrite -(polybase_widen _ (leq_maxr (size p) (size q))).
rewrite -(polybase_widen _ (size_add p q)).
pose f (i : 'I_( maxn (size p) (size q))) := p`_ i *: 'T_i + q`_i *: 'T_i.
rewrite (eq_bigr f) {}/f => [|i _]; last by rewrite coefD scalerDl.
by rewrite big_split/=.
Qed.

Lemma pT2p_lin : linear (@pT2p R).
Proof. by move => a p q; rewrite pT2pD pT2pZ. Qed.

Lemma size_p2pT (p : {poly R}) : size (p2pT p) = size p.
Proof.
have [/eqP->|pNZ] := boolP (p == 0); first by rewrite p2pT0.
rewrite {2}[p]p2pT_spec //.
rewrite size_polybase => [|n]; last by apply: size_pT.
have [/eqP->|p2NZ] := boolP (p2pT p == 0); first by rewrite size_poly0 big_ord0.
rewrite {-1}(polySpred p2NZ).
rewrite big_mkcond big_ord_recr -big_mkcond.
rewrite -lead_coefE lead_coef_eq0 p2NZ /=.
rewrite -(polySpred p2NZ) (maxn_idPr _) //.
apply/bigmax_leqP=> i _.
by apply: leq_trans (leq_pred  _).
Qed.

End LEMMAS.

(* T_0(x)	=	1 *)
(* T_1(x)	=	x	 *)
(* T_2(x)	=	2 x^2 - 1 *)
(* T_3(x)	=	4 x^3 - 3 x *)
(* T_4(x)	=	8 x^4 - 8 x^2 + 1	*)
(* T_5(x)	=	16 x^5 - 20 x^3 + 5 x *)
(* T_6(x)	=	32 x^6 - 48 x^4 + 18 x^2 - 1 *)

Definition t0 := [:: ratz (Posz 1)].
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













