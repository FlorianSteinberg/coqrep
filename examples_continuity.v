(*This file considers Baire space nat->nat as example for
a space that can be thought about continuity on. *)
From Coq.micromega Require Import Psatz.
From mathcomp Require Import all_ssreflect.
Require Import baire_space continuity initial_segments multi_valued_functions.
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
Proof.
split => //.
move => s m.
lia.
Qed.

Lemma melt_init_seg:
	forall n, max_elt id (init_seg n) = n.
Proof.
elim => // => n ih.
rewrite -{2}ih.
replace (init_seg (S n)) with (cons n (init_seg n)) by trivial.
by replace (max_elt id (n :: init_seg n)) with (max n.+1 (max_elt id (init_seg n))) by trivial; lia.
Qed.

Definition is_cont1 (G: (nat -> nat) -> nat -> nat) :=
  forall phi n, exists m, forall psi,
    phi \and psi \coincide_on (init_seg m) -> (G phi) \and (G psi) \coincide_on (init_seg n).
(* This is the more conventional continuity using intial segments.
It is equivalent to the corresponding multifunction being continuous
in the sense of "continuity.v" *)

Lemma continuity1 (F: B -> B):
	is_cont1 F <-> is_cont (F2MF F).
Proof.
split => cont.
	move => phi s' fd.
	move: cont (cont phi (S s')) => _ [m cont].
	exists (init_seg m) => Fphi /= [] iv /= psi coin Fpsi iv'.
	move: cont (cont psi coin) => _ coinv.
	rewrite iv iv' in coinv.
	by move: ((inseg_coin id Fphi Fpsi (S s')).2 coinv s') => /=; lia.
move => phi.
elim; first by exists 0 => psi coin; apply: (inseg_coin id (F phi) (F psi) 0).1 => n; lia.
move => n [m] ih.
move: (cont phi n (fun_total F phi)) => [L cond].
exists (max_elt id (app (init_seg m) L)) => psi coin.
move: ((inseg_coin id phi psi (max_elt id (init_seg m ++ L))).2 coin) => coin'.
apply: (inseg_coin id (F phi) (F psi) (S n)).1=> n0 ineq.
have: n0 <= n by lia.
move: ineq => _ ineq.
case: (Compare_dec.le_lt_eq_dec n0 n ineq) => ass; last first.
	have coin'': phi \and psi \coincide_on (init_seg (max_elt id L)).
		apply: (inseg_coin id phi psi (max_elt id L)).1 => n1 n1ls.
		by apply coin';	rewrite (melt_app); lia.
	rewrite ass.
	apply/ (cond (F phi)) => //=.
	by apply (@list_melt nat (fun n:nat => n) (fun n:nat => n)).
move: ineq ass => _; move: n0.
apply: (inseg_coin id (F phi) (F psi) n).2; apply: ih.
apply: (inseg_coin id phi psi m).1 => n1 n1ls.
by apply coin'; rewrite (melt_app) (melt_init_seg m); lia.
Qed.

(*The above relied on specific properties of the involved functions. I am pretty sure that
it can be recovered for arbitrary countable types. I mean: it is always possible to use a
bijection with nat, right? Anyway, the following uses lists for regular functions and
is easier to prove equal to the continuity from "continuity.v" *)
Definition is_cont2 (G: (Q-> A) -> Q' -> A') :=
  forall phi (q': Q'), exists (L : list Q), forall psi,
    phi \and psi \coincide_on L -> G phi q' = G psi q'.

Lemma continuity2 (F: (Q-> A) -> Q' -> A'):
	is_cont2 F <-> is_cont (F2MF F).
Proof.
split => cont.
	move => psi s' fd.
	move: cont (cont psi s') => _ [L cond].
	exists L => Fpsi /= FpsiFpsi phi coin Fphi FphiFphi.
	by rewrite -FphiFphi -FpsiFpsi; apply (cond phi).
move => psi s'.
move: cont (cont psi s' (fun_total F psi)) => _ [L cond].
exists L => phi coin.
by apply/ (cond (F psi) _) => //=.
Qed.

(*To have function from baire space to natural numbers, we identify nat with one -> nat.*)
Definition F phi n := phi (n star) = 0 /\ forall m, phi m = 0 -> n star <= m.
(*This is a partial function: if phi is never zero, the right hand side is always false and
phi is not assinged any value. On the other hand the function is single valued, as only
the smalles number where phi is zero allowed as return value. More generally, the function
is continuous:*)

Lemma F_is_continuous: F \is_continuous.
Proof.
set L := in_seg (fun n:nat => n).
move => phi str.
case: (classic (exists m, phi m = 0)); last first.
	move => false.
	exists nil => fp1 /= v1.
  by exfalso; apply false; exists (fp1 star); apply v1.
move => [m me0].
exists (L m.+1) => Fphi /= [v1 c1] psi pep.
move: ((inseg_coin (fun n:nat => n) phi psi m.+1).2 pep) => cond Fpsi [v2 c2].
have: Fphi star <= m by apply (c1 m); lia.
move => le1.
have leq2: Fpsi star <= m	by apply: (c2 m); replace (psi m) with (phi m) by by apply (cond m).
have l2: Fpsi star < m.+1 by lia.
rewrite -(cond (Fpsi star) l2) in v2.
have l1: Fphi star < m.+1 by lia.
rewrite (cond (Fphi star) l1) in v1.
move: (c1 (Fpsi star) v2) (c2 (Fphi star) v1) => ieq1 ieq2.
replace str with star by by elim str.
by lia.
Qed.

Lemma F_is_single_valued: F \is_single_valued.
Proof.
exact: cont_to_sing F_is_continuous.
Qed.

Lemma no_extension :
	~ exists G, (F2MF G) \extends F /\ (F2MF G) \is_continuous.
Proof.
move => [] G [] ext cont.
set psi := fun n:nat => 1.
move: (cont psi star (fun_total G psi)) => []L Lprop.
set sL := max_elt id L.
set m := (max ((G psi) star).+1 sL).
set psi' := fun n => if (leq m n) then 0 else 1.
have: psi \and psi' \coincide_on init_seg sL.
	apply: (inseg_coin id psi psi' sL).1.
	move => n nls.
	rewrite /psi /psi'.
	case_eq (leq m n); intros hyp_ab => //.
	have: m <= n by apply /leP.
	rewrite /m; lia.
move => coin.
have: psi \and psi' \coincide_on L.
	have: forall (n: nat), id id n = n by trivial.
	move => true.
	apply: (list_melt true coin).
move: coin => _ coin.
have neq: (G psi') = fun star => m.
	apply: (ext psi' (fun star => m)); rewrite /F /psi'.
	split.
		replace (leq m m) with true => //.
		by have: (leq m m) by apply /leP; lia.
	move => m0;	case E: (leq m m0) => // _.
	by apply /leP; rewrite E.
suffices: G psi star = G psi' star by rewrite neq /m; lia.
by apply/ Lprop => //.
Qed.

(* Since classically, any multi function can be extended to a total multi function,
we get the following when using classical reasoning:
Lemma no_extension':
	~ exists G, G extends F /\ G is_continuous /\ G is_total.
But I don't feel like proving that now. *)
End BAIRE_SPACE.