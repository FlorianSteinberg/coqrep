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

Definition pT := fix pT_rec (n : nat) {struct n} : {poly R} :=
  if n is n1.+1 then
    if n1 is n2.+1 then 'X *+2 * pT_rec n1 - pT_rec n2
    else 'X
  else 1.

Notation "`T_ n " := (pT n) (at level 10).

Lemma pT0 : pT 0 = 1.
Proof. done. Qed.

Lemma pT1 : pT 1 = 'X.
Proof. done. Qed.

Lemma pTSS : forall n, pT n.+2 = 'X *+2 * pT n.+1 - pT n.
Proof. done. Qed.

Lemma horner1_pT: forall n, (pT n).[1] = 1.
Proof.
move=> n; elim: n {-2}n (leqnn n) => [[] // _ |n IH]; first by rewrite hornerC.
move=> m; rewrite leq_eqVlt; case/orP => [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|n] IH; first by rewrite pT1 hornerX.
rewrite pTSS hornerD hornerN mulrnAl hornerMn.
by rewrite -commr_polyX hornerMX !IH // !mulr1 mulrS [1+ _]addrC addrK.
Qed.

Lemma commr_pT: forall p n, GRing.comm p (pT n).
Proof.
move=> p n; elim: n {-2}n (leqnn n)=> [[] // _ |n IH]; first  by exact: commr1.
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
Proof. done. Qed.

Lemma pU1 : pU 1 = 'X *+ 2.
Proof. done. Qed.

Lemma pUSS : forall n, pU n.+2 = 'X *+ 2 * pU n.+1 - pU n.
Proof. done. Qed.

Lemma horner1_pU: forall n, (pU n).[1] = (n.+1)%:R.
Proof.
move=> n; elim: n {-2}n (leqnn n)=> [[] // _ |n IH]; first by rewrite hornerC.
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

Lemma commr_pU: forall p n, GRing.comm p (pU n).
Proof.
move=> p n; elim: n {-2}n (leqnn n)=> [[] // _ |n IH]; first  by exact: commr1.
move=> m; rewrite leq_eqVlt; case/orP=> [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|n] IH.
   rewrite pU1; apply: commrMn; exact: commr_polyX.
rewrite pUSS; apply: commrD; last by apply: commrN; apply: IH.
by rewrite mulrnAl; apply: commrMn; apply: commrM;
   [exact: commr_polyX | apply: IH].
Qed.

Lemma pT_pU: forall n, pT n.+1 = pU n.+1 - 'X * pU n.
Proof.
have F: pU 1 - 'X * pU 0 = 'X by rewrite pU1 pU0 mulr1 addrK.
move=> n; elim: n {-2}n (leqnn n)=> [[] // _ |m IH].
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

Lemma coef_pUn: forall n, (pU n)`_n = (2^n)%:R.
Proof.
by move=> n; rewrite coef_pU ltnn addnn odd_double subnn /= bin0 mul1r muln1.
Qed.

Lemma size_pU_leq: forall n, (size (pU n) <= n.+1)%N.
Proof.
by move=> n; apply/leq_sizeP=> j Hj; rewrite coef_pU Hj.
Qed.

Lemma coef_pT : forall n i,
  (pT n)`_i =
    if (n < i)%N || odd (n + i) then 0 else
    if n is 0 then 1 else
    let k := (n - i)./2 in (-1)^+k * ((2^i * n * 'C(n-k,k)) %/ (n-k).*2)%:R.
Proof.
case=> [|n] i; first by rewrite pT0 coefC; case: i.
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


Lemma coef_pTK : forall n i, ~~odd(n + i) -> (i <= n)%N ->
  let k := (n - i)./2 in 
  (pT n)`_i *+ (n-k).*2 = (-1)^+k * (2^i * n * 'C(n-k,k))%:R.
Proof.
move=> n i O1 L1; rewrite coef_pT; move/negPf: (O1)->.
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

Lemma coef_pTn: forall n, (pT n)`_n = (2^n.-1)%:R.
Proof.
case=> [|n]; rewrite coef_pT ltnn addnn odd_double //= subnn subn0.
rewrite mul1r expnS [(2 * _)%N]mulnC -!mulnA [(2 * _)%N]mulnA mul2n.
by rewrite mulnC -!mulnA mulKn // bin0 mul1n.
Qed.

Lemma size_pT_leq: forall n, (size (pT n) <= n.+1)%N.
Proof.
by move=> n; apply/leq_sizeP => j Hj; rewrite coef_pT Hj.
Qed.

(* Pell equation *)

Lemma pell: forall n, (pT n.+1)^+2 - ('X^2 - 1) * (pU n)^+2 = 1.
Proof.
move=> n.
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
   let a1 := a + x * t.1 - t.2 in
   (a1, t.1) else (0, 0).

Definition Cshaw_rec q x := (b q x).1 - x * (b q x).2.

Definition Cshaw p := Cshaw_rec p.

Definition CP2P p := \sum_(0 <= i < size p) (nth 0%R p i *: (pT i)).

Lemma Cshaw_CP2P p :
	forall r, p.[r] = Cshaw (CP2P p) r.
Proof.
move => r.
Admitted.

Lemma Cshaw0:
	forall r, Cshaw 0%:P r = 0.
Proof.
move => r; rewrite /Cshaw/Cshaw_rec/b/=.
rewrite polyseq0 /=.
by rewrite mulr0 subr0.
Qed.

Lemma Cshawc c:
	forall r, Cshaw c%:P r = c.
Proof.
case E: (c == 0).
	have ->: c = 0 by apply /eqP.
	exact Cshaw0.
move => r; rewrite /Cshaw/Cshaw_rec/b/=.
have neq: (c != 0) by rewrite E.
rewrite polyseqC neq/=.
by rewrite !mulr0 !subr0 addr0.
Qed.

Lemma CshawX:
	forall r, Cshaw 'X r = 0.
Proof.
move => r.
rewrite /Cshaw/Cshaw_rec/b.
rewrite polyseqX/=.
by rewrite !mulr0 !subr0 !addr0 !mulr1 add0r subrr.
Qed.


Section PT2P.

Variable R1 : ringType.

(* c + X * l *)
Definition pconst (c : R1) l :=
  if l is _ :: _ then c :: l
  else if c == 0 then [::] else [:: c].

(* c + l *)
Definition add_const (c : R1) l :=
 if l is a :: l1 then
   pconst (c + a) l1
 else
   if c == 0 then [::] else [:: c].

(* l1 + l2 *)
Fixpoint ladd_poly (l1 l2 : seq R1) :=
 if l1 is a :: l3 then
   if l2 is b :: l5 then
     pconst (a + b) (ladd_poly l3 l5)
   else l1
 else l2.

(* -l *)
Fixpoint lopp_poly (l : seq R1) :=
 if l is a :: l1 then
     -a :: (lopp_poly l1)
 else [::].

(* a *: l *)
Fixpoint lscal_poly (a : R1) l :=
 if l is b :: l1 then
     pconst (a * b) (lscal_poly a l1)
 else [::].

(* l1 - l2 *)
Fixpoint lsub_poly (l1 l2 : seq R1) :=
 if l1 is a :: l3 then
   if l2 is b :: l5 then
     pconst (a - b) (lsub_poly l3 l5)
   else l1
 else lopp_poly l2.

Fixpoint pT2p_rec l (p1 p2 : seq R1) :=
match l with
|  a :: l =>
   ladd_poly (lscal_poly a p1)
     (pT2p_rec l (lsub_poly (lscal_poly 2%:R (pconst 0 p1)) p2) p1)
| _ => [::]
end.

Definition pT2p l :=
 match l with 
 | a :: l => 
    ladd_poly
    (pconst a [::])
    (pT2p_rec l [::0; 1] [::1])
  | _ => [::]
  end.

End PT2P.

Compute pT2p  (ncons 11 (0%:R: int) [::1]).

Section P2PT.

Variable R1 : unitRingType.

Fixpoint Tmulx_rec (l : seq R1) :=
  match l with 
  | a :: ((b :: c :: l) as l1) =>
      2%:R^-1 * (a + c) :: Tmulx_rec l1 
  | l =>  [seq 2%:R^-1 * x | x <- l]
  end.

Lemma size_Tmulx_rec l : size (Tmulx_rec l) = size l.
Proof.
elim: l => //= a [|b [|c l1]] IH //=.
by rewrite IH.
Qed.

Definition Tmulx l :=
  Tmulx_rec (0 :: if l is a :: l then (a *+ 2 :: l) else l).

Lemma size_Tmulx l : size (Tmulx l) = (size l).+1.
Proof. by case: l => // a l; rewrite size_Tmulx_rec. Qed.

Definition Tadd_const a (l : seq R1) :=
  match l with (b :: l) => (a + b :: l) | _ => [::a] end.

Fixpoint p2pT_rec (l1 l2 : seq R1) :=
 match l1 with 
   a :: l1 => Tadd_const a (Tmulx (p2pT_rec l1 l2))
 | _ => [::]
end.

Definition p2pT l := p2pT_rec l [::].

Fixpoint Tmulx_rec1 (l : seq R1) :=
  match l with 
  | a :: ((b :: c :: l) as l1) => (a + c) :: Tmulx_rec1 l1 
  | l =>  l
  end.

Lemma size_Tmulx_rec1 l : size (Tmulx_rec1 l) = size l.
Proof.
elim: l => //= a [|b [|c l1]] IH //=.
by rewrite IH.
Qed.

Definition Tmulx1 l :=
  Tmulx_rec1 (0 :: if l is a :: l then (a *+ 2 :: l) else l).

Lemma size_Tmulx1 l : size (Tmulx1 l) = (size l).+1.
Proof. by case: l => // a l; rewrite size_Tmulx_rec1. Qed.

Definition Tadd_const1 a (l : seq R1) :=
  match l with (b :: l) => (a + b :: l) | _ => [::a] end.

Fixpoint p2pT_rec1 (l1 l2 : seq R1) :=
 match l1 with 
   a :: l1 => Tadd_const a (Tmulx (p2pT_rec l1 l2))
 | _ => [::]
end.

Definition p2pT1 l := p2pT_rec1 l [::].

End P2PT.

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

Compute p2pT t0.
Compute p2pT t1.
Compute p2pT t2.
Compute p2pT t3.
Compute p2pT t4.
Compute p2pT t5.
Compute p2pT t6.


End Tcheby.













