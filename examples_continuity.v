(*This file considers Baire space nat -> nat as example for
a space that can be thought about continuity on. *)
From Coq.micromega Require Import Psatz.
From mathcomp Require Import all_ssreflect.
Require Import all_core.
Require Import Classical.

Open Scope coq_nat_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BAIRE_SPACE.
Context (Q A Q' A': Type).
Inductive one := star.
Notation B := (nat -> nat).
Notation N := (one -> nat).
Notation "'init_seg' phi" := (in_seg id phi) (at level 2).

Lemma min_sec: @is_min_sec nat id id.
Proof. split => // s m ineq; apply /leP; lia. Qed.

Lemma melt_init_seg:
	forall n, max_elt id (init_seg n) = n.
Proof.
elim => //= n ->; rewrite /maxn; case: ifP => // ineq.
by exfalso; apply /PeanoNat.Nat.nlt_succ_diag_l/leP /ineq.
Qed.

(* This is the more conventional continuity using intial segments.
It is equivalent to the corresponding multifunction being continuous
in the sense of "continuity.v" *)
Definition is_cont1 (G: (nat -> nat) -> nat -> nat) :=
  forall phi n, exists m, forall psi,
    phi \and psi \coincide_on (init_seg m) -> (G phi) \and (G psi) \coincide_on (init_seg n).

Lemma continuity1 (F: B -> B):
	is_cont1 F <-> is_cont (F2MF F).
Proof.
split => [ cont phi fd s' | cont phi].
	have [m cont']:= (cont phi (S s')).
	exists (init_seg m); split => // Fphi /= iv psi coin Fpsi iv'.
	move: cont' (cont' psi coin) => _ coinv; rewrite iv iv' in coinv.
	by apply /((inseg_coin _ _ _ _).2 coinv)/ltnSn.
elim; first by exists 0 => psi coin; apply: (inseg_coin id (F phi) (F psi) 0).1.
move => n [m] ih.
have [L [/=phifd cond]]:= (cont phi (F2MF_tot F phi) n).
exists (max_elt id (app (init_seg m) L)) => psi coin.
move: ((inseg_coin id phi psi (max_elt id (init_seg m ++ L))).2 coin) => coin'.
apply: (inseg_coin id (F phi) (F psi) (S n)).1=> n0 ineq.
case: (Compare_dec.le_lt_eq_dec n0 n _) => [ | neq | eq]; first by move/leP: ineq; lia.
	move: ineq neq => _; move: n0.
	move => n0 /leP ineq; move: n0 ineq.
	apply/inseg_coin; apply ih; apply/inseg_coin => n1 n1ls.
	by apply coin'; rewrite melt_app melt_init_seg; apply/leq_trans; last exact: leq_maxl.
have coin'': phi \and psi \coincide_on (init_seg (max_elt id L)).
	apply: (inseg_coin id phi psi (max_elt id L)).1 => n1 n1ls.
	by apply coin'; rewrite (melt_app); apply/leq_trans;last exact: leq_maxr.
rewrite eq; apply/ (cond (F phi)) => //=.
by apply/ list_melt; first apply min_sec.
Qed.

(* The following uses lists for regular functions and is easier to prove equal to the
continuity from "continuity.v" *)
Definition is_cont2 (G: (Q-> A) -> Q' -> A') :=
  forall phi (q': Q'), exists (L : list Q), forall psi,
    phi \and psi \coincide_on L -> G phi q' = G psi q'.

Lemma continuity2 (F: (Q-> A) -> Q' -> A'):
	is_cont2 F <-> is_cont (F2MF F).
Proof.
split => [cont psi fd s' | cont psi s'].
	have [L cond]:= (cont psi s').
	by exists L; split =>// Fpsi /= <- phi coin Fphi <-; apply (cond phi).
have [L [/=_ cond]] := (cont psi (F2MF_tot F psi) s').
by exists L => phi coin; apply/ (cond (F psi) _) => //=.
Qed.

(*To have function from baire space to natural numbers, we identify nat with one -> nat.*)
Definition F phi n := phi (n star) = 0 /\ forall m, phi m = 0 -> n star <= m.
(* F is a partial function: if phi is never zero, the right hand side is always false and
phi is not assinged any value. On the other hand the function is single valued, as only
the smalles number where phi is zero allowed as return value. More generally, the function
is continuous:*)

Lemma F_is_continuous: F \is_continuous.
Proof.
set L := in_seg (fun n:nat => n) => phi phifd str.
case: (classic (exists m, phi m = 0)) => [[m me0]| neq0]; last first.
	by exists nil; split =>// fp1 /= v1; exfalso; apply neq0; exists (fp1 star); apply v1.
exists (L m.+1); split =>// Fphi /= [v1 c1] psi pep Fpsi [v2 c2].
have cond:= ((inseg_coin (fun n:nat => n) phi psi m.+1).2 pep).
have le1: Fphi star <= m by apply (c1 m); lia.
have leq2: Fpsi star <= m	by apply: (c2 m); replace (psi m) with (phi m) by by apply (cond m).
have /leP l2: Fpsi star < m.+1 by lia.
rewrite -((cond (Fpsi star) l2)) in v2.
have/leP l1: Fphi star < m.+1 by lia.
rewrite (cond (Fphi star) l1) in v1.
move: (c1 (Fpsi star) v2) (c2 (Fphi star) v1) => ieq1 ieq2.
replace str with star by by elim str.
by lia.
Qed.

Lemma F_is_single_valued: F \is_single_valued.
Proof.
exact: cont_sing F_is_continuous.
Qed.

Lemma no_extension :
	~ exists G, (F2MF G) \extends F /\ (F2MF G) \is_continuous.
Proof.
move => [] G [] ext cont.
set psi := fun n:nat => 1.
have [L [/=_ Lprop]]:= (cont psi (F2MF_tot G psi) star).
set sL := max_elt id L.
set m := (max ((G psi) star).+1 sL).
set psi' := fun n => if (leq m n) then 0 else 1.
have coin: psi \and psi' \coincide_on init_seg sL.
	apply/inseg_coin => n nls; rewrite /psi /psi'.
	case E: (leq m n); last by trivial.
	suffices ineq: (m <= n)%N.
		rewrite /m in ineq.
		by move/leP: nls; move/leP: ineq; lia.
	by rewrite E.
have coin': psi \and psi' \coincide_on L by apply/list_melt; last by apply/ coin.
have neq: (G psi') = fun star => m.
	apply: (ext psi' (fun star => m)); rewrite /F /psi'.
	split => [ | m0]; last by case E: (leq m m0) => // _; apply /leP; rewrite E.
	replace (leq m m) with true => //.
	by have: (leq m m) by apply /leP; lia.
suffices: G psi star = G psi' star.
	by rewrite neq /m; lia.
by apply/ Lprop => //.
Qed.

(* Since classically, any multi function can be extended to a total multi function and
we get the following:
Lemma no_extension':
	~ exists G, G extends F /\ G is_continuous /\ G is_total.
But I don't feel like proving that now. *)
End BAIRE_SPACE.