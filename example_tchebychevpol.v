From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Local Scope ring_scope.

Section Tcheby.

Variable R : ringType.
Implicit Types (pl : seq R) (p: {poly R}) .

(* Chebychev *)

Definition pT {R: ringType} := fix pT_rec (n : nat) {struct n} : {poly R} :=
  if n is n1.+1 then
    if n1 is n2.+1 then 'X *+2 * pT_rec n1 - pT_rec n2
    else 'X
  else 1.

Notation "`T_ n " := (pT n) (at level 10).

Lemma pT0 : pT 0 = 1 :> {poly R}.
Proof. done. Qed.

Lemma pT1 : pT 1 = 'X :> {poly R}.
Proof. done. Qed.

Lemma pTSS : forall n, pT n.+2 = 'X *+2 * pT n.+1 - pT n :> {poly R}.
Proof. done. Qed.

Lemma horner1_pT n : (pT n).[1: R] = 1.
Proof.
elim: n {-2}n (leqnn n) => [[] // _ |n IH]; first by rewrite hornerC.
move=> m; rewrite leq_eqVlt; case/orP => [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|n] IH; first by rewrite pT1 hornerX.
rewrite pTSS hornerD hornerN mulrnAl hornerMn.
by rewrite -commr_polyX hornerMX !IH // !mulr1 mulrS [1+ _]addrC addrK.
Qed.

Lemma commr_pT p n : GRing.comm p (pT n).
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

Lemma pU0 : pU 0 = 1.
Proof. by []. Qed.

Lemma pU1 : pU 1 = 'X *+ 2.
Proof. by []. Qed.

Lemma pUSS n : pU n.+2 = 'X *+ 2 * pU n.+1 - pU n.
Proof. by []. Qed.

Lemma horner1_pU n : (pU n).[1] = n.+1%:R.
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

Lemma commr_pU p n : GRing.comm p (pU n).
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

Lemma pT_pU n : pT n.+1 = pU n.+1 - 'X * pU n.
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

Lemma deriv_pT n: (pT n.+1)^`() = pU n *+ n.+1.
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
  (pU n)`_i =
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

Lemma coef_pUn n : (pU n)`_n = (2^n)%:R.
Proof.
by rewrite coef_pU ltnn addnn odd_double subnn /= bin0 mul1r muln1.
Qed.

Lemma size_pU_leq n : (size (pU n) <= n.+1)%N.
Proof. by apply/leq_sizeP=> j Hj; rewrite coef_pU Hj. Qed.

Lemma coef_pT n i :
  (pT n)`_i =
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
   ~~odd(n + i) -> (i <= n)%N ->
  let k := (n - i)./2 in 
  (pT n)`_i *+ (n-k).*2 = (-1)^+k * (2^i * n * 'C(n-k,k))%:R :> R.
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

Lemma coef_pTn n : (pT n)`_n = (2^n.-1)%:R :> R.
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

Lemma pell n : (pT n.+1)^+2 - ('X^2 - 1) * (pU n)^+2 = 1.
Proof.
suff F: (pU n.+1)^+ 2 + (pU n)^+2 = 'X *+ 2 * pU n.+1 * pU n + 1.
  rewrite pT_pU exprS expr1 !mulrDl !mulrDr opprD !mulNr.
  rewrite !addrA addrC opprK mul1r !addrA [_^+2 + _]addrC F.
  apply: trans_equal (addr0 _); rewrite [_+1]addrC -!addrA; congr (_ + _).
  rewrite mulrN mulrA commr_polyX !addrA !mulrDl addrK.
  rewrite -mulrA -commr_pU mulrA addrN sub0r.
  by rewrite mulrN opprK -mulrA -commr_pU exprS expr1 exprS expr1 !mulrA addrN.
elim:n=> [| n IH].
  by rewrite pU1 pU0 mulr1 expr1n exprS expr1.
rewrite pUSS exprS !mulrBr !mulrBl -!addrA; congr (_ + _).
  rewrite !(mulrnAl,mulrnAr); do 2 congr (_ *+ _).
  by rewrite -!mulrA; congr (_ * _); rewrite -commr_pU mulrA.
congr (_ + _); first by rewrite -commr_pU -!mulrA commr_pU.
by rewrite opprB addrC addrA IH [_+1]addrC addrK.
Qed.

Fixpoint b q (x: R) :=
 if q is a :: q' then
   let t := b q' x in
   let a1 := a + x *+ 2 * t.1 - t.2 in
   (a1, t.1) else (0, 0).

Definition Cshaw_rec q x := (b q x).1 - x * (b q x).2.

Definition Cshaw p := Cshaw_rec p.

Definition CP2P p := \sum_(0 <= i < size p) (nth 0%R p i *: (pT i)).

Definition rm0 :=
 (mulr0, mul0r, subr0, sub0r, add0r, addr0, mul0rn, mulr0n, oppr0).

Definition rm1 := (mulr1, mul1r, mulr1n).

Lemma Cshaw0:
	forall r, Cshaw 0%:P r = 0.
Proof.
move => r; rewrite /Cshaw/Cshaw_rec/b/=.
by rewrite polyseq0 /= !rm0.
Qed.

Lemma Cshawc c:
	forall r, Cshaw c%:P r = c.
Proof.
case E: (c == 0).
	have ->: c = 0 by apply /eqP.
	exact Cshaw0.
move => r; rewrite /Cshaw/Cshaw_rec/b/=.
have neq: (c != 0) by rewrite E.
by rewrite polyseqC neq/= !rm0.
Qed.

Lemma CshawX:
	forall r, Cshaw 'X r = r.
Proof.
by move => r; rewrite /Cshaw/Cshaw_rec/b polyseqX/= !rm0 !rm1 (mulr2n r) addrK.
Qed.

Section PT2P.

Lemma last_poly (p : {poly R}) : last 1 p != 0.
Proof. by case: p. Qed.

(* c + X * l *)
Definition lcons {R : ringType} (c : R) l :=
  if l is _ :: _ then c :: l
  else if c == 0 then [::] else [:: c].

Lemma lcons_neq0 c p : p != 0 -> lcons c p = c :: p.
Proof.
move/eqP/val_eqP => /=.
by rewrite polyseq0; case: polyseq.
Qed.

Lemma lcons_spec c (p : {poly R}) : lcons c p = p * 'X + c%:P.
Proof.
apply: (@eq_from_nth _ 0) => [|i].
  have [->|/eqP pN] := (p =P 0).
    by rewrite mul0r add0r polyseq0 polyseqC /=; case: eqP.
  rewrite size_addl size_mulX //.
    by case: p pN; case => //= i /eqP/val_eqP; rewrite /= polyseq0.
  rewrite polyseqC; case: eqP => //= _.
  by rewrite ltnS size_poly_gt0.
rewrite coef_add_poly coefMX polyseqC /= nth_nseq.
case: p; case => //= [|a l].
  case: (c =P 0) => //=.
  by case: i => //=; rewrite add0r.
case: i => //= [|i].
  by rewrite add0r; case: (c =P 0) => [->|].
rewrite !ltnNge // (leq_trans (leq_b1 _)) //=.
by rewrite addr0.
Qed.

(* c + l *)
Definition ladd_const {R: ringType} (c : R) l :=
 if l is a :: l1 then
   lcons (c + a) l1
 else
   if c == 0 then [::] else [:: c].

Lemma ladd_const_spec c (p : {poly R}) : ladd_const c p = c%:P + p.
Proof.
elim/poly_ind: p => [|p a IH].
  by rewrite addr0 polyseq0 polyseqC /=; case: eqP.
rewrite addrCA -polyC_add -!lcons_spec /=.
case: (polyseq _) => //=.
by case: eqP => [->|] //=; rewrite addr0.
Qed.

(* l1 + l2 *)
Fixpoint ladd_poly {R : ringType} (l1 l2 : seq R) :=
 if l1 is a :: l3 then
   if l2 is b :: l5 then
     lcons (a + b) (ladd_poly l3 l5)
   else l1
 else l2.

Lemma ladd_poly_spec (p1 p2 : {poly R}) : 
  ladd_poly p1 p2 = p1 + p2.
Proof.
elim/poly_ind: p1 p2  => [p2|p1 a IH p2].
  by rewrite polyseq0 add0r.
elim/poly_ind: p2 => [|p2 b _].
  rewrite addr0 -lcons_spec polyseq0.
  by case: (polyseq _) => //=; case: eqP.
rewrite addrAC addrA -mulrDl -addrA -polyC_add -!lcons_spec -IH.
(case: (polyseq p1); case: (polyseq p2)) => //= => [|b1 l1|b1 l1|b1 l1 b2 l2].
- case: eqP => [->|]; first by rewrite addr0.
  case: eqP => [->|] /=; first by rewrite add0r=> /eqP/negPf ->.
  by rewrite addrC.
- case: eqP => [->|/=]; first by rewrite addr0.
  by rewrite addrC.
- case: eqP => [->|/=]; first by rewrite add0r.
  by rewrite addrC.
by rewrite addrC.
Qed.

(* -l *)
Fixpoint lopp_poly {R : ringType} (l : seq R) :=
 if l is a :: l1 then -a :: (lopp_poly l1) else [::].

Lemma lopp_poly_spec (p : {poly R}) : lopp_poly p = - p.
Proof.
elim/poly_ind: p  => [|p a IH]; first by rewrite oppr0 polyseq0.
rewrite opprD -mulNr -polyC_opp -!lcons_spec -IH.
by case: polyseq; rewrite //= oppr_eq0; case: eqP.
Qed.

(* a *: l *)
Fixpoint lscal_poly {R : ringType} (a : R) l :=
 if l is b :: l1 then
     lcons (a * b) (lscal_poly a l1)
 else [::].

Lemma lscal_poly_spec a (p : {poly R}) : lscal_poly a p = a *: p.
Proof.
elim/poly_ind: p  => [|p b IH].
  by rewrite scaler0 polyseq0.
rewrite scalerDr scalerAl -mul_polyC -polyC_mul -!lcons_spec -IH.
case: polyseq => //=.
by case: eqP => [->|] //; rewrite mulr0 eqxx.
Qed.

(* l1 - l2 *)
Fixpoint lsub_poly {R: ringType} (l1 l2 : seq R) :=
 if l1 is a :: l3 then
   if l2 is b :: l5 then
     lcons (a - b) (lsub_poly l3 l5)
   else l1
 else lopp_poly l2.

Lemma lsub_poly_spec (p1 p2 : {poly R}) : 
  lsub_poly p1 p2 = p1 - p2.
Proof.
elim/poly_ind: p1 p2  => [p2|p1 a IH p2].
  by rewrite polyseq0 sub0r /= lopp_poly_spec.
elim/poly_ind: p2 => [|p2 b _].
  rewrite subr0 -lcons_spec polyseq0.
  by case: (polyseq _) => //=; case: eqP.
rewrite opprD -mulNr.
rewrite addrAC addrA -mulrDl -addrA -polyC_opp -polyC_add -!lcons_spec -IH.
(case: (polyseq p1); case: (polyseq p2)) => //= => [|b1 l1|b1 l1|b1 l1 b2 l2].
- case: eqP => [->|].
    by rewrite addr0 oppr_eq0; case: eqP.
  case: eqP => [->|/=].
    by rewrite oppr0 add0r => /eqP/negPf->.
  by rewrite addrC.
- case: eqP => [->|/=]; first by rewrite addr0.
  by rewrite addrC.
- case: eqP => [->|/=]; first by rewrite oppr0 add0r.
  by rewrite addrC.
by rewrite addrC.
Qed.

Fixpoint lpT2p_rec {R: ringType} l (p1 p2 : seq R) :=
match l with
|  a :: l =>
   ladd_poly (lscal_poly a p1)
     (lpT2p_rec l (lsub_poly (lscal_poly 2%:R (lcons 0 p1)) p2) p1)
| _ => [::]
end.

Lemma lpT2p_rec_spec (p : {poly R}) n :
   lpT2p_rec p (pT n.+1) (pT n) =
      \sum_(i < size p) p`_i *: `T_(n.+1 + i).
Proof.
elim/poly_ind: p n => [n|p c IH n].
  rewrite polyseq0 big1 /= ?polyseq0 // => i.
  by rewrite nth_nil scale0r.
rewrite  size_MXaddC.
case: eqP => [->|pNz].
  rewrite mul0r add0r polyseqC.
  case: eqP => [->|]; first by rewrite big_ord0 polyseq0.
     rewrite polyseq0 big_ord_recl big1 => [|i].
     rewrite !addn0 addr0 //=.
     by rewrite lscal_poly_spec; case: polyseq.
  by rewrite /= nth_nil scale0r.
have H1 : p <> [::] :> list _.
  by have /val_eqP/eqP /= := pNz; rewrite polyseq0.
rewrite -lcons_spec.
rewrite big_ord_recl.
pose f (i : 'I_(size p)) := p`_i *: `T_ (n.+2 + i).
rewrite (eq_bigr f) => [|i _]; last first.
  rewrite lift0 addnS; congr (_ *: _).
  by case: {1 2 4}polyseq H1.
rewrite {}/f -ladd_poly_spec -IH addn0.
set T1 := `T_ _; set T2 := `T_ _; set T3 := `T_ _.
case: polyseq H1 => //= a l _.
congr (ladd_poly _ _); first by apply: lscal_poly_spec.
rewrite (_ : lsub_poly _ _ = T3) //.
rewrite [T3]pTSS.
rewrite -lsub_poly_spec; congr lsub_poly.
rewrite -['X *+ _]mulr_natl -mulrA.
rewrite (_ : _%:R = 2%:R%:P); last first.
  by rewrite (polyC_add 1 1) polyC1.
rewrite mul_polyC -lscal_poly_spec; congr lscal_poly.
rewrite lcons_spec.
by rewrite addr0 commr_polyX.
Qed.

Definition lpT2p {R : ringType} (l : seq R) :=
 match l with 
 | a :: l => 
    ladd_poly
    (lcons a [::])
    (lpT2p_rec l [::0; 1] [::1])
  | _ => [::]
  end.

Lemma lpT2p_spec (p : {poly R}) :
   lpT2p p = \sum_(i < size p) p`_i *: `T_i.
Proof.
elim/poly_ind: p => [|p c _].
rewrite polyseq0 big1 ?polyseq0 // => i.
  by rewrite nth_nil scale0r.
rewrite -lcons_spec.
case: (p =P 0) => [->|/eqP pNZ].
  rewrite polyseq0 /=; case: eqP => [|/eqP cNZ] //.
    by rewrite big_ord0 polyseq0.
  rewrite big_ord_recl big_ord0 /= addr0 (negPf cNZ) /=.
  by rewrite alg_polyC polyseqC cNZ.
rewrite lcons_neq0 //= big_ord_recl.
rewrite -ladd_poly_spec; congr ladd_poly.
  by rewrite alg_polyC polyseqC /=; case: eqP.
rewrite -lpT2p_rec_spec; congr lpT2p_rec.
  by rewrite /= polyseqX.
by rewrite polyseq1.
Qed.

Lemma last_lpT2p_spec (p : {poly R}) :
  last 1 (lpT2p p) != 0.
Proof. by rewrite lpT2p_spec; case: (\sum_ (_ < _) _). Qed.

Definition pT2p (p : {poly R}) : {poly R} := Polynomial (last_lpT2p_spec p).

Lemma pT2p_spec (p : {poly R}) :
   pT2p p = \sum_(i < size p) p`_i *: `T_i.
Proof. by apply/val_eqP/eqP/lpT2p_spec. Qed.

End PT2P.

End Tcheby.

Compute lpT2p  (ncons 11 (0%:R: int) [::1]).

Notation "`T_ n " := (pT n) (at level 10).

Section P2PT.

Variable R : unitRingType.
Hypothesis I2 : (2%:R : R) \is a GRing.unit.

Fixpoint Tmulx_rec (l : seq R) :=
  match l with 
  | a :: ((b :: c :: l) as l1) =>
      (a + c) / 2%:R :: Tmulx_rec l1 
  | l =>  [seq x /2%:R | x <- l]
  end.

Lemma XpT n : 'X * `T_n.+1 = 2%:R ^-1 *: `T_n + 2%:R ^-1 *: `T_n.+2 :> {poly R}.
Proof.
rewrite pTSS scalerDr addrCA scalerN subrr addr0.
by rewrite -scaler_nat -scalerAl scalerA mulVr // scale1r.
Qed.

Lemma last_Tmulx_rec l :
  last 1 l != 0 -> last 1 (Tmulx_rec l) != 0.
Proof.
elim: l => //= a [|b [|c l]] IH //.
  rewrite /=; apply: contra => H.
  by rewrite -[a](divrK I2) (eqP H) mul0r.
by move=> /IH; case: {IH}l.
Qed.

Lemma Tmulx_rec_spec (l : seq R)  n :
  ('X * \sum_(i < size l) l`_i *: `T_(i + n.+1))%R =
  (l`_0 / 2%:R) *: `T_n + (l`_1 / 2%:R) *: `T_n.+1 +
  \sum_(i < size (Tmulx_rec l)) (Tmulx_rec l)`_i *: `T_(i + n.+2) :> {poly R}.
Proof.
elim: l n => [|a [|b [|c l]] IH] n.
- by rewrite !big_ord0 mul0r mulr0 !scale0r !add0r. 
- rewrite ![[:: _]`_ _]/= mul0r scale0r addr0.
  rewrite ![size _]/= !(big_ord0, big_ord_recl).
  rewrite ![_`_ _]/= !addr0 !add0n -!scalerA -scalerDr.
  by rewrite -commr_polyX -scalerAl -XpT commr_polyX.
- rewrite ![[:: _; _]`_ _]/= ![size _]/= !(big_ord0, big_ord_recl).
  rewrite ![[:: _; _]`_ _]/= !add1n !add0n !addr0.
  rewrite -commr_polyX mulrDl -!scalerAl commr_polyX XpT.
  rewrite commr_polyX XpT scalerDr !scalerA -!addrA; congr (_ + _).
  rewrite [RHS]addrCA; congr (_ + _).
  by rewrite scalerDr !scalerA.
rewrite -[Tmulx_rec _]/((a + c) / 2%:R :: Tmulx_rec  [:: b, c & l]).
set u := [:: b, _ & _].
rewrite -[size _]/(size [:: b, c & l]).+1.
rewrite big_ord_recl mulrDr.
pose f (i : 'I_(size u)) := u`_i *: `T_ (i + n.+2).
rewrite (eq_bigr f) => [|i _]; last first.
  by congr (_ *: `T_ _); rewrite !addnS.
rewrite {f}IH.
rewrite ![_`_ _]/= add0n.
rewrite -/u.
set v := Tmulx_rec _.
rewrite -[size (_ :: _)]/(size v).+1.
rewrite [in RHS]big_ord_recl.
rewrite ![_`_ _]/= add0n.
pose f (i : 'I_(size v)) := v`_i *: `T_ (i + n.+3).
rewrite [in RHS](eq_bigr f) => [|i _]; last first.
  by congr (_ *: `T_ _); rewrite !addnS.
rewrite !addrA; congr (_ + _).
rewrite addrAC [in RHS] addrAC; congr (_ + _).
rewrite mulrDl scalerDl addrA; congr (_ + _).
rewrite -commr_polyX -scalerAl.
by rewrite commr_polyX XpT scalerDr !scalerA.
Qed.

Lemma size_Tmulx_rec l : size (Tmulx_rec l) = size l.
Proof.
elim: l => //= a [|b [|c l1]] IH //=.
by rewrite IH.
Qed.

Definition Tmulx l :=
  Tmulx_rec (lcons 0 (if l is a :: l then (a *+ 2 :: l) else l)).

Lemma last_Tmulx l :
  last 1 l != 0 -> last 1 (Tmulx l) != 0.
Proof.
case: l => [|a l] H.
  by rewrite /Tmulx /= eqxx /=.
apply: last_Tmulx_rec =>  /=.
case: l H => //=.
apply: contra => H.
by rewrite -[a](mulrK I2) [a * _%:R]mulr_natr (eqP H) mul0r.
Qed.

Lemma Tmulx_spec (l : seq R) :
  ('X * \sum_(i < size l) l`_i *: `T_i)%R =
  \sum_(i < size (Tmulx l)) (Tmulx l)`_i *: `T_i :> {poly R}.
Proof.
rewrite /Tmulx.
case: l => [|a [|b [|c l]]].
- by rewrite /lcons eqxx !big_ord0 mulr0.
- rewrite !(big_ord0, big_ord_recl) /=.
  rewrite mul0r scale0r add0r !addr0.
  rewrite -[a *+ _]mulr_natl -commr_nat mulrK //.
  by rewrite -[RHS]mul_polyC alg_polyC commr_polyX.
- rewrite /= add0r !(big_ord0, big_ord_recl).
  rewrite ![(_ :: _)`_ _]/= !lift0 !addr0.
  rewrite ![nat_of_ord ord0]/= pTSS [RHS]addrCA.
  rewrite -scalerDr [`T_ _ + _]addrC subrK mulrDr; congr (_ + _).
    rewrite pT0 pT1 -[a *+ _]mulr_natl -commr_nat mulrK //.
    by rewrite -[RHS]mul_polyC alg_polyC commr_polyX.
  rewrite -commr_polyX -['X *+ _]scaler_nat -[in RHS]scalerAl scalerA.
  by rewrite divrK // -scalerAl.
set u := b :: _.
rewrite -[size _]/(size u).+1.
rewrite big_ord_recl mulrDr.
pose f (i : 'I_(size u)) := u`_ i *: `T_(i + 1).
rewrite (eq_bigr f) => [|i _]; last first.
  by congr (_ *: `T_ _); rewrite addn1.
rewrite {f}Tmulx_rec_spec.
rewrite !size_Tmulx_rec.
rewrite -[size (0 :: _)]/(size u).+2.
rewrite 2!big_ord_recl.
rewrite 5![_`_ _]/= ![nat_of_ord _]/=.
pose f (i : 'I_(size u)) := (Tmulx_rec u)`_ i *: `T_(i + 2).
rewrite [in RHS](eq_bigr f) => [|i _]; last first.
  by congr (_ *: `T_ _); rewrite !addnS addn0.
rewrite !addrA; congr (_ + _).
rewrite pT0 pT1 add0r addrAC addrC; congr (_ + _).
rewrite mulrDl scalerDl; congr (_ + _).
rewrite -commr_polyX mulr_algl; congr (_ *: _).
by rewrite -[a *+ _]mulr_natl -commr_nat mulrK.
Qed.

Lemma size_Tmulx l : l != [::] -> size (Tmulx l) = (size l).+1.
Proof. by case: l => // a l; rewrite size_Tmulx_rec. Qed.

Lemma Tmulx_nil : Tmulx [::] = [::].
Proof. by rewrite /Tmulx /= eqxx. Qed.

Fixpoint lp2pT (l : seq R) :=
 match l with 
   a :: l => ladd_const a (Tmulx (lp2pT l))
 | _ => [::]
end.

Lemma lp2pT_cons a l :
  lp2pT (a :: l) = ladd_const a (Tmulx (lp2pT l)).
Proof. by []. Qed.

Lemma last_lp2pT l :
  last 1 l != 0 -> last 1 (lp2pT l) != 0.
Proof.
elim: l => // a [|b l] IH H.
  move: H.
  rewrite /= Tmulx_nil /= => H.
  by rewrite (negPf H).
rewrite lp2pT_cons.
have /last_Tmulx U := IH H.
have /=-> := ladd_const_spec a (Polynomial U).
by case: (_ + _).
Qed.

Lemma lp2pT_spec p :
  p =
  \sum_(i < size (lp2pT p)) (lp2pT p)`_i *: `T_i :> {poly R}.
Proof.
elim/poly_ind: p => /= [|p c IH].
  by rewrite polyseq0 big_ord0.
rewrite {1}IH -{IH}lcons_spec.
case: polyseq => [|a l].
  rewrite /= big_ord0 mul0r add0r.
  case: eqP => [->| /eqP cNZ /=].
    by rewrite big_ord0.
  rewrite (_ : Tmulx [::] = [::]); last first.
    by rewrite /Tmulx /= eqxx.
  rewrite /= (negPf cNZ).
  by rewrite big_ord_recl big_ord0 pT0 addr0 /= alg_polyC.
rewrite [lcons _ _]/= lp2pT_cons.
rewrite commr_polyX Tmulx_spec.
case: Tmulx => /= [|b [|b1 l1]].
- rewrite big_ord0 add0r; case: eqP => [->|].
    by rewrite big_ord0.
  by rewrite big_ord_recl big_ord0 addr0 pT0 /= alg_polyC.
- rewrite big_ord_recl big_ord0 pT0 addr0 /=.
  rewrite alg_polyC -polyC_add addrC.
  case: eqP => [->|]; first by rewrite big_ord0.
  rewrite big_ord_recl big_ord0 pT0 addr0 /=.
  by rewrite alg_polyC.
rewrite [lcons _ _]/= big_ord_recl [_`_ _]/= pT0.
rewrite addrAC alg_polyC -polyC_add [b + _]addrC.
rewrite -[size (_ + _ :: _)]/(size (b1 :: l1)).+1.
rewrite [RHS]big_ord_recl; congr (_ + _).
by rewrite pT0 alg_polyC.
Qed.

Definition p2pT (p : {poly R}) : {poly R} := Polynomial (last_lp2pT (last_poly p)).

Lemma p2pT_spec (p : {poly R}) :
  p =
  \sum_(i < size (p2pT p)) (p2pT p)`_i *: `T_i :> {poly R}.
Proof. by apply: lp2pT_spec. Qed.

Lemma pT2p_p2pT (p : {poly R}):
	pT2p (p2pT p) = p.
Proof.
rewrite {2}[p]p2pT_spec.
by rewrite pT2p_spec.
Qed.

End P2PT.

Section LEMMAS.

Variable R: idomainType.

Lemma pT2p0:
	pT2p 0 = 0:> {poly R}.
Proof.
by apply /val_eqP; rewrite /= polyseq0.
Qed.

Lemma pT2pZ:
	forall (a: R) (p q : {poly R}), pT2p (a *: p) = a *: pT2p p.
Proof.
move => a p q.
case: (boolP (a == 0)) => ass.
rewrite (eqP ass) !scale0r; exact: pT2p0.
rewrite !pT2p_spec.
pose f (i : 'I_(size (a*: p))) := a *: (p`_ i *: `T_i).
rewrite (eq_bigr f) {}/f.
have eq: ((size (a *: p)) = (size p)) by rewrite size_scale => //.
	by rewrite eq scaler_sumr.
by move => i _; rewrite scalerA coefZ.
Qed.

Lemma pT2p_lin:
	linear (@pT2p R).
Proof.
move => a p q.
rewrite -pT2pZ.
rewrite !pT2p_spec.
Admitted.

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













