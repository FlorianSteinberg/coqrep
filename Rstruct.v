(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (c) 2010-2013, ENS de Lyon and Inria.

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

Require Import Rdefinitions Raxioms RIneq Rbasic_fun Zwf.
Require Import Epsilon FunctionalExtensionality Ranalysis1 Rsqrt_def.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice bigop.
From mathcomp Require Import ssrnum ssralg fintype poly mxpoly.
Require Import Rtrigo1 Reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.


Local Open Scope R_scope.

Lemma Req_EM_T (r1 r2 : R) : {r1 = r2} + {r1 <> r2}.
Proof.
case: (total_order_T r1 r2) => [[r1Lr2 | <-] | r1Gr2].
- by right=> r1Er2; case: (Rlt_irrefl r1); rewrite {2}r1Er2.
- by left.
by right=> r1Er2; case: (Rlt_irrefl r1); rewrite {1}r1Er2.
Qed.

Definition eqr (r1 r2 : R) : bool :=
  if Req_EM_T r1 r2 is left _ then true else false.

Lemma eqrP : Equality.axiom eqr.
Proof.
by move=> r1 r2; rewrite /eqr; case: Req_EM_T=> H; apply: (iffP idP).
Qed.

Canonical Structure R_eqMixin := EqMixin eqrP.
Canonical Structure R_eqType := Eval hnf in EqType R R_eqMixin.

Fact inhR : inhabited R.
Proof. exact: (inhabits 0). Qed.

Definition pickR (P : pred R) (n : nat) :=
  let x := epsilon inhR P in if P x then Some x else None.

Fact pickR_some P n x : pickR P n = Some x -> P x.
Proof. by rewrite /pickR; case: (boolP (P _)) => // Px [<-]. Qed.

Fact pickR_ex (P : pred R) :
  (exists x : R, P x) -> exists n, pickR P n.
Proof. by rewrite /pickR; move=> /(epsilon_spec inhR)->; exists 0%N. Qed.

Fact pickR_ext (P Q : pred R) : P =1 Q -> pickR P =1 pickR Q.
Proof.
move=> PEQ n; rewrite /pickR; set u := epsilon _ _; set v := epsilon _ _.
suff->: u = v by rewrite PEQ.
by congr epsilon; apply: functional_extensionality=> x; rewrite PEQ.
Qed.

Definition R_choiceMixin : choiceMixin R :=
  Choice.Mixin pickR_some pickR_ex pickR_ext.

Canonical R_choiceType := Eval hnf in ChoiceType R R_choiceMixin.

Fact RplusA : associative (Rplus).
Proof. by move=> *; rewrite Rplus_assoc. Qed.

Definition R_zmodMixin := ZmodMixin RplusA Rplus_comm Rplus_0_l Rplus_opp_l.

Canonical Structure R_zmodType := Eval hnf in ZmodType R R_zmodMixin.

Fact RmultA : associative (Rmult).
Proof. by move=> *; rewrite Rmult_assoc. Qed.

Fact R1_neq_0 : R1 != R0.
Proof. by apply/eqP/R1_neq_R0. Qed.

Definition R_ringMixin := RingMixin RmultA Rmult_1_l Rmult_1_r
  Rmult_plus_distr_r Rmult_plus_distr_l R1_neq_0.

Canonical Structure R_ringType := Eval hnf in RingType R R_ringMixin.
Canonical Structure R_comRingType := Eval hnf in ComRingType R Rmult_comm.

Import Monoid.

Canonical Radd_monoid := Law RplusA Rplus_0_l Rplus_0_r.
Canonical Radd_comoid := ComLaw Rplus_comm.

Canonical Rmul_monoid := Law RmultA Rmult_1_l Rmult_1_r.
Canonical Rmul_comoid := ComLaw Rmult_comm.

Canonical Rmul_mul_law := MulLaw Rmult_0_l Rmult_0_r.
Canonical Radd_add_law := AddLaw Rmult_plus_distr_r Rmult_plus_distr_l.

Definition Rinvx r := if (r != 0) then / r else r.

Definition unit_R r := r != 0.

Lemma RmultRinvx : {in unit_R, left_inverse 1 Rinvx Rmult}.
Proof.
move=> r; rewrite -topredE /unit_R /Rinvx => /= rNZ /=.
by rewrite rNZ Rinv_l //; apply/eqP.
Qed.

Lemma RinvxRmult : {in unit_R, right_inverse 1 Rinvx Rmult}.
Proof.
move=> r; rewrite -topredE /unit_R /Rinvx => /= rNZ /=.
by rewrite rNZ Rinv_r //; apply/eqP.
Qed.

Lemma intro_unit_R x y : y * x = R1 /\ x * y = R1 -> unit_R x.
Proof.
move=> [yxE1 xyE1]; apply/eqP=> xZ.
by case/eqP: R1_neq_0; rewrite -yxE1 xZ Rmult_0_r.
Qed.

Lemma Rinvx_out : {in predC unit_R, Rinvx =1 id}.
Proof. by move=> x; rewrite inE /= /Rinvx -if_neg => ->. Qed.

Definition R_unitRingMixin :=
  UnitRingMixin RmultRinvx RinvxRmult intro_unit_R Rinvx_out.

Canonical Structure R_unitRing :=
  Eval hnf in UnitRingType R R_unitRingMixin.

Canonical Structure R_comUnitRingType :=
  Eval hnf in [comUnitRingType of R].

Lemma R_idomainMixin x y : x * y = 0 -> (x == 0) || (y == 0).
Proof.
(do 2 case: (boolP (_ == _))=> // /eqP)=> yNZ xNZ xyZ.
by case: (Rmult_integral_contrapositive_currified _ _ xNZ yNZ).
Qed.

Canonical Structure R_idomainType :=
   Eval hnf in IdomainType R R_idomainMixin.

Lemma R_fieldMixin : GRing.Field.mixin_of [unitRingType of R].
Proof. by done. Qed.

Definition R_fieldIdomainMixin := FieldIdomainMixin R_fieldMixin.

Canonical Structure R_fieldType := FieldType R R_fieldMixin.

(** Reflect the order on the reals to bool *)

Definition Rleb r1 r2 := if Rle_dec r1 r2 is left _ then true else false.
Definition Rltb r1 r2 := Rleb r1 r2 && (r1 != r2).
Definition Rgeb r1 r2 := Rleb r2 r1.
Definition Rgtb r1 r2 := Rltb r2 r1.

Lemma RlebP r1 r2 : reflect (r1 <= r2) (Rleb r1 r2).
Proof. by rewrite /Rleb; apply: (iffP idP); case: Rle_dec. Qed.

Lemma RltbP r1 r2 : reflect (r1 < r2) (Rltb r1 r2).
Proof.
rewrite /Rltb /Rleb; apply: (iffP idP); case: Rle_dec=> //=.
- by case=> // r1Er2 /eqP[].
- by move=> _ r1Lr2; apply/eqP/Rlt_not_eq.
by move=> Nr1Lr2 r1Lr2; case: Nr1Lr2; left.
Qed.

Lemma RgebP r1 r2 : reflect (r1 >= r2) (Rgeb r1 r2).
Proof.
rewrite /Rgeb /Rleb; apply: (iffP idP); case: Rle_dec=> //=.
  by move=> r2Lr1 _; apply: Rle_ge.
by move=> Nr2Lr1 r1Gr2; case: Nr2Lr1; apply: Rge_le.
Qed.

Lemma RgtbP r1 r2 : reflect (r1 > r2) (Rgtb r1 r2).
Proof.
rewrite /Rleb; apply: (iffP idP) => r1Hr2; first by apply: Rlt_gt; apply/RltbP.
by apply/RltbP; apply: Rgt_lt.
Qed.

(*
Ltac toR := rewrite /GRing.add /GRing.opp /GRing.zero /GRing.mul /GRing.inv
  /GRing.one //=.
*)

Section ssreal_struct.
 
Import GRing.Theory.
Import Num.Theory.
Import Num.Def.
 
Local Open Scope R_scope.
 
Lemma Rleb_norm_add x y : Rleb (Rabs (x + y)) (Rabs x + Rabs y).
Proof. by apply/RlebP/Rabs_triang. Qed.
 
Lemma addr_Rgtb0 x y : Rltb 0 x -> Rltb 0 y -> Rltb 0 (x + y).
Proof. by move/RltbP=> Hx /RltbP Hy; apply/RltbP/Rplus_lt_0_compat. Qed.
 
Lemma Rnorm0_eq0 x : Rabs x = 0 -> x = 0.
Proof. by move=> H; case: (x == 0) /eqP=> // /Rabs_no_R0. Qed.
 
Lemma Rleb_leVge x y : Rleb 0 x -> Rleb 0 y -> (Rleb x y) || (Rleb y x).
Proof.
move/RlebP=> Hx /RlebP Hy; case: (Rlt_le_dec x y).
by move/Rlt_le/RlebP=> ->.
by move/RlebP=> ->; rewrite orbT.
Qed.
 
Lemma RnormM : {morph Rabs : x y / x * y}.
exact: Rabs_mult. Qed.
 
Lemma Rleb_def x y : (Rleb x y) = (Rabs (y - x) == y - x).
apply/(sameP (RlebP x y))/(iffP idP)=> [/eqP H| /Rle_minus H].
  apply: Rminus_le; rewrite -Ropp_minus_distr.
  apply/Rge_le/Ropp_0_le_ge_contravar.
  by rewrite -H; apply: Rabs_pos.
apply/eqP/Rabs_pos_eq.
rewrite -Ropp_minus_distr.
by apply/Ropp_0_ge_le_contravar/Rle_ge.
Qed.
 
Lemma Rltb_def x y : (Rltb x y) = (y != x) && (Rleb x y).
apply/(sameP (RltbP x y))/(iffP idP).
  case/andP=> /eqP H /RlebP/Rle_not_gt H2.
  by case: (Rtotal_order x y)=> // [][] // /esym.
move=> H; apply/andP; split; [apply/eqP|apply/RlebP].
  exact: Rgt_not_eq.
exact: Rlt_le.
Qed.
 
Definition R_numMixin := NumMixin Rleb_norm_add addr_Rgtb0 Rnorm0_eq0
Rleb_leVge RnormM Rleb_def Rltb_def.
Canonical Structure R_numDomainType := NumDomainType R R_numMixin.

Lemma RleP : forall x y, reflect (Rle x y) (Num.le x y).
Proof. exact: RlebP. Qed.
 
Lemma RltP : forall x y, reflect (Rlt x y) (Num.lt x y).
Proof. exact: RltbP. Qed.
 
Canonical Structure R_numFieldType := [numFieldType of R].
 
Lemma Rreal_axiom (x : R) : (Rleb 0 x) || (Rleb x 0).
Proof.
case: (Rle_dec 0 x)=> [/RlebP ->|] //.
by move/Rnot_le_lt/Rlt_le/RlebP=> ->; rewrite orbT.
Qed.
 
Canonical Structure R_realDomainType := RealDomainType R Rreal_axiom.
 
Canonical Structure R_realFieldType := [realFieldType of R].
 
Lemma Rarchimedean_axiom : Num.archimedean_axiom R_realFieldType.
Proof.
move=> x; exists (Zabs_nat (up x) + 2)%N.
have [Hx1 Hx2]:= (archimed x).
have Hz (z : Z): z = (z - 1 + 1)%Z by rewrite Zplus_comm Zplus_minus.
have Zabs_nat_Zopp z : Zabs_nat (- z)%Z = Zabs_nat z by case: z.
apply/RltbP/Rabs_def1.
  apply: (Rlt_trans _ ((Zabs_nat (up x))%:R)%R); last first.
    rewrite -[((Zabs_nat _)%:R)%R]Rplus_0_r mulrnDr.
    by apply/Rplus_lt_compat_l/Rlt_0_2.
  apply: (Rlt_le_trans _ (IZR (up x)))=> //.
  elim/(well_founded_ind (Zwf_well_founded 0)): (up x) => z IHz.
  case: (Z_lt_le_dec 0 z) => [zp | zn].
    rewrite [z]Hz plus_IZR Zabs_nat_Zplus //; last exact: Zlt_0_le_0_pred.
    rewrite plusE mulrnDr.
    apply/Rplus_le_compat_r/IHz; split; first exact: Zlt_le_weak.
    exact: Zlt_pred.
  apply: (Rle_trans _ (IZR 0)); first exact: IZR_le.
  by apply/RlebP/(ler0n R_numDomainType (Zabs_nat z)).
apply: (Rlt_le_trans _ (IZR (up x) - 1)).
  apply: Ropp_lt_cancel; rewrite Ropp_involutive.
  rewrite Ropp_minus_distr /Rminus -opp_IZR -{2}(Zopp_involutive (up x)).
  elim/(well_founded_ind (Zwf_well_founded 0)): (- up x)%Z => z IHz .
  case: (Z_lt_le_dec 0 z) => [zp | zn].
  rewrite [z]Hz Zabs_nat_Zopp plus_IZR.
  rewrite Zabs_nat_Zplus //; last exact: Zlt_0_le_0_pred.
    rewrite plusE -Rplus_assoc -addnA [(_ + 2)%N]addnC addnA mulrnDr.
    apply: Rplus_lt_compat_r; rewrite -Zabs_nat_Zopp.
    apply: IHz; split; first exact: Zlt_le_weak.
    exact: Zlt_pred.
  apply: (Rle_lt_trans _ 1).
    rewrite -{2}[1]Rplus_0_r; apply: Rplus_le_compat_l.
    by rewrite -/(IZR 0); apply: IZR_le.
  rewrite mulrnDr; apply: (Rlt_le_trans _ 2).
    by rewrite -{1}[1]Rplus_0_r; apply/Rplus_lt_compat_l/Rlt_0_1.
  rewrite -[2]Rplus_0_l; apply: Rplus_le_compat_r.
  by apply/RlebP/(ler0n R_numDomainType (Zabs_nat _)).
apply: Rminus_le.
rewrite /Rminus Rplus_assoc [- _ + _]Rplus_comm -Rplus_assoc -!/(Rminus _ _).
exact: Rle_minus.
Qed.
 
Canonical Structure R_archiFieldType := ArchiFieldType R Rarchimedean_axiom.
 
(** Here are the lemmas that we will use to prove that R has
the rcfType structure. *)
 
Lemma continuity_eq f g : f =1 g -> continuity f -> continuity g.
Proof.
move=> Hfg Hf x eps Heps.
have [y [Hy1 Hy2]]:= Hf x eps Heps.
by exists y; split=> // z; rewrite -!Hfg; exact: Hy2.
Qed.
 
Lemma continuity_sum (I : finType) F (P : pred I):
(forall i, P i -> continuity (F i)) ->
continuity (fun x => (\sum_(i | P i) ((F i) x)))%R.
Proof.
move=> H; elim: (index_enum I)=> [|a l IHl].
  set f:= fun _ => _.
  have Hf: (fun x=> 0) =1 f by move=> x; rewrite /f big_nil.
  by apply: (continuity_eq Hf); exact: continuity_const.
set f := fun _ => _.
case Hpa: (P a).
  have Hf: (fun x => F a x + \sum_(i <- l | P i) F i x)%R =1 f.
    by move=> x; rewrite /f big_cons Hpa.
  apply: (continuity_eq Hf); apply: continuity_plus=> //.
  exact: H.
have Hf: (fun x => \sum_(i <- l | P i) F i x)%R =1 f.
  by move=> x; rewrite /f big_cons Hpa.
exact: (continuity_eq Hf).
Qed.
 
Lemma continuity_exp f n: continuity f -> continuity (fun x => (f x)^+ n)%R.
Proof.
move=> Hf; elim: n=> [|n IHn]; first exact: continuity_const.
set g:= fun _ => _.
have Hg: (fun x=> f x * f x ^+ n)%R =1 g.
  by move=> x; rewrite /g exprS.
by apply: (continuity_eq Hg); exact: continuity_mult.
Qed.
 
Lemma Rreal_closed_axiom : Num.real_closed_axiom R_archiFieldType.
Proof.
move=> p a b; rewrite !ler_eqVlt.
case Hpa: ((p.[a])%R == 0%R).
  by move=> ? _ ; exists a=> //; rewrite lerr ler_eqVlt.
case Hpb: ((p.[b])%R == 0%R).
  by move=> ? _; exists b=> //; rewrite lerr ler_eqVlt andbT.
case Hab: (a == b).
  by move=> _; rewrite (eqP Hab) eq_sym Hpb (ltrNge 0) /=; case/andP=> /ltrW ->.
rewrite eq_sym Hpb /=; clear=> /RltbP Hab /andP [] /RltbP Hpa /RltbP Hpb.
suff Hcp: continuity (fun x => (p.[x])%R).
  have [z [[Hza Hzb] /eqP Hz2]]:= IVT _ a b Hcp Hab Hpa Hpb.
  by exists z=> //; apply/andP; split; apply/RlebP.
rewrite -[p]coefK poly_def.
set f := fun _ => _.
have Hf: (fun (x : R) => \sum_(i < size p) (p`_i * x^+i))%R =1 f.
  move=> x; rewrite /f horner_sum.
  by apply: eq_bigr=> i _; rewrite hornerZ hornerXn.
apply: (continuity_eq Hf); apply: continuity_sum=> i _.
apply:continuity_scal; apply: continuity_exp=> x esp Hesp.
by exists esp; split=> // y [].
Qed.
 
Canonical Structure R_rcfType := RcfType R Rreal_closed_axiom.

(* proprietes utiles de l'exp *)

Open Scope ring_scope.

Lemma expR0 :
    exp(GRing.zero R_zmodType) = 1.
Proof. by rewrite exp_0. Qed.

Lemma expRD x y :
    exp(x) * exp(y) = exp(GRing.add x y).
Proof. by rewrite exp_plus. Qed.

Lemma expRX x :
  forall n : nat,
    exp(x) ^+ n = exp(x *+ n).
Proof.
elim => [|n Ihn].
  by rewrite expr0 mulr0n exp_0.
by rewrite exprS Ihn mulrS expRD.
Qed.

 Lemma Rplus_add x y :
  Rplus x y = GRing.add x y.
Proof. by done. Qed.

Lemma Rmult_mul x y :
  Rmult x y = GRing.mul x y.
Proof. by done. Qed.

Lemma Ropp_opp x :
  Ropp x = GRing.opp x.
Proof. by done. Qed.

Lemma Rdiv_div x y :
  y != 0 -> Rdiv x y = x / y.
Proof.
move=> Hneq0.
apply: (@mulIr _ y).
  by rewrite unitfE.
rewrite -!mulrA.
rewrite mulVr;
  last by rewrite unitfE.
rewrite -[X in _*X]Rmult_mul.
rewrite Rinv_l //.
by apply: (elimN eqP Hneq0).
Qed.

Lemma sin_add x y : 
   sin (GRing.add x y) = sin x * cos y + cos x * sin y.
Proof. by rewrite sin_plus. Qed. 

Lemma cos_add x y : 
   cos (GRing.add x y) = (cos x * cos y - sin x * sin y).
Proof. by rewrite cos_plus. Qed. 

End ssreal_struct.