(*This file considers Baire space nat->nat as example for
a space that can be thought about continuity on. *)
From Coq.micromega Require Import Psatz.
From mathcomp Require Import all_ssreflect.
Require Import continuity initial_segments multi_valued_functions.
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

Lemma size_init_seg:
	forall n, size id (init_seg n) = n.
Proof.
elim => //.
move => n ih.
rewrite -{2}ih.
replace (init_seg (S n)) with (cons n (init_seg n)) by trivial.
replace (size id (n :: init_seg n)) with (max n.+1 (size id (init_seg n))) by trivial.
lia.
Qed.

Definition is_cont1 (G: (nat -> nat) -> nat -> nat) :=
  forall phi n, exists m, forall psi,
    phi and psi coincide_on (init_seg m) -> (G phi) and (G psi) coincide_on (init_seg n).
(* This is the more conventional continuity using intial segments.
It is equivalent to the corresponding multifunction being continuous
in the sense of "continuity.v" *)

Lemma continuity1 (F: B -> B):
	is_cont1 F <-> is_cont (fun phi => some (F phi)).
Proof.
split.
- move => cont psi s'.
  move: cont (cont psi (S s')) => _ [m cont].
  exists (init_seg m) => phi coin Fpsi isv Fphi isv'.
  move: cont (cont phi coin) => _ coinv.
	have iv: F psi = Fpsi by apply Some_inj.
	have iv': F phi = Fphi by apply Some_inj.
  rewrite iv iv' in coinv.
 	apply: ((initial_segments id Fpsi Fphi (S s')).2 coinv s').
 	lia.
move => cont phi.
elim.
	exists 0 => psi coin.
	apply: (initial_segments id (F phi) (F psi) 0).1.
	move => n.
	lia.
move => n [m] ih.
move:(cont phi n) => [L cond].
exists (size id (app (init_seg m) L)) => psi coin.
move: ((initial_segments id phi psi (size id (init_seg m ++ L))).2 coin) => coin'.
apply: (initial_segments id (F phi) (F psi) (S n)).1.
move => n0 ineq.
have: n0 <= n by lia.
move: ineq => _ ineq.
case: (Compare_dec.le_lt_eq_dec n0 n ineq) => ass; last first.
	have: phi and psi coincide_on (init_seg (size id L)).
		apply: (initial_segments id phi psi (size id L)).1.
		move => n1 n1ls.
		apply coin'.
		rewrite (size_app).
		lia.
	move => coin''.
	have triv: forall psi', (Some (F psi') = Some (F psi')) by trivial.
	have true: forall (n: nat), id id n = n by trivial.
	move: (cond psi (list_size true coin'') (F phi) (triv phi) (F psi) (triv psi)).
	by rewrite ass.
move: ineq ass => _.
move: n0.
apply: (initial_segments id (F phi) (F psi) n).2.
apply: ih.
apply: (initial_segments id phi psi m).1.
move => n1 n1ls.
apply coin'.
rewrite (size_app).
rewrite (size_init_seg m).
lia.
Qed.

(*The above relied on specific properties of the involved functions. I am pretty sure that
it can be recovered for arbitrary countable types. I mean: it is always possible to use a
bijection with nat, right? Anyway, the following uses lists for regular functions and
is easier to prove equal to the continuity from "continuity.v" *)
Definition is_cont2 (G: (Q-> A) -> Q' -> A') :=
  forall phi (q': Q'), exists (L : list Q), forall psi,
    phi and psi coincide_on L -> G phi q' = G psi q'.

Lemma continuity2 (F: (Q-> A) -> Q' -> A'):
	is_cont2 F <-> is_cont (fun phi => Some (F phi)).
Proof.
split => cont psi s'.
	move: cont (cont psi s') => _ [L cond].
	exists L => phi coin Fpsi isv Fphi isv'.
	have iv: F psi = Fpsi by apply Some_inj.
	have iv': F phi = Fphi by apply Some_inj.
	rewrite -iv -iv'.
	by apply (cond phi).
move: cont (cont psi s') => _ [L cond].
exists L => phi coin.
have triv: forall psi', (Some (F psi') = Some (F psi')) by trivial.
move: cond (cond phi coin (F psi) (triv psi)) => _ cond.
by apply: (cond (fun s' => F phi s')).
Qed.

(*To have function from baire space to natural numbers, we identify nat with one -> nat.*)
Definition F phi n := phi (n star) = 0 /\ forall m, phi m = 0 -> n star <= m.
(*This is a partial function: if phi is never zero, the right hand side is always false and
phi is not assinged any value. On the other hand the function is single valued, as only
the smalles number where phi is zero allowed as return value. More generally, the function
is continuous:*)


Lemma F_is_continuous: F is_continuous.
Proof.
  move => phi str.
  set cnt := (fun n:nat => n).
  set sec := (fun n:nat => n).
  set L := in_seg cnt.
  case: (classic (exists m, phi m = 0)); last first.
  	move => false.
    exists nil => psi _ fp1 [v1] cond.
    exfalso; apply false.
    by exists (fp1 star).
  move => [m me0].
  exists (L m.+1).
  move => psi pep.
  move: ((initial_segments cnt phi psi m.+1).2 pep).
  move => cond Fphi [v1 c1].
  have: Fphi star <= m by apply (c1 m); lia.
  move => le1.
  move => Fpsi [v2 c2].
	have: Fpsi star <= m.
		apply: (c2 m).
    replace (psi m) with (phi m) => //.
    by apply (cond m).
  move => leq2.
  have: Fpsi star < m.+1 by lia.
  move => l2.
	rewrite -(cond (Fpsi star) l2) in v2.
  have: Fphi star < m.+1 by lia.
  move => l1.
	rewrite (cond (Fphi star) l1) in v1.
	move: (c1 (Fpsi star) v2) (c2 (Fphi star) v1) => ieq1 ieq2.
  replace str with star.
  lia.
by elim str.
Qed.

Lemma F_is_single_valued: F is_single_valued.
Proof.
	exact: cont_to_sing F_is_continuous.
Qed.

Lemma no_extension :
	~ exists G, (F2MF G) extends F /\ (F2MF G) is_continuous.
Proof.
move => [] G [] ext cont.
set psi := fun n:nat => 1.
move: (cont psi star) => []L Lprop.
set sL := size id L.
set m := (max ((G psi) star).+1 sL).
set psi' := fun n => if (leq m n) then 0 else 1.
have: psi and psi' coincide_on init_seg sL.
	apply: (initial_segments id psi psi' sL).1.
	move => n nls.
	rewrite /psi /psi'.
	case_eq (leq m n); intros hyp_ab => //.
	have: m <= n by apply /leP.
	rewrite /m; lia.
move => coin.
have: psi and psi' coincide_on L.
	have: forall (n: nat), id id n = n by trivial.
	move => true.
	apply: (list_size true coin).
move: coin => _ coin.
have: forall psi', (F2MF G psi' (G psi')) by trivial.
move => triv.
have: (G psi') = fun star => m.
	apply: (ext psi' (fun star => m)).
 	rewrite /F.
	split.
		rewrite /psi'.
		replace (leq m m) with true => //.
		by have: (leq m m) by apply /leP; lia.
	move => m0.
	rewrite /psi'.
	case_eq (leq m m0); intros hyp_ab => // wahr.
	by apply /leP; rewrite hyp_ab.
move => neq.
move: (Lprop psi' coin (G psi) (triv psi) (G psi') (triv psi')).
rewrite neq /m.
lia.
Qed.

(* Since classically, any multi function can be extended to a total multi function,
we get the following when using classical reasoning:
Lemma no_extension':
	~ exists G, G extends F /\ G is_continuous /\ G is_total.
But I don't feel like proving that now. *)
End BAIRE_SPACE.