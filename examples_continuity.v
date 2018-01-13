(*This file considers Baire space nat->nat as example for
a space that can be thought about continuity on. *)

Load initial_segments.

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

Lemma continuity1 (F: (nat -> nat) -> nat -> nat):
	is_cont1 F <-> is_cont (F2MF F).
Proof.
split.
- move => cont psi s'.
  move: cont (cont psi (S s')) => _ [m cont].
  exists (init_seg m) => phi coin Fpsi iv Fphi iv'.
  move: cont (cont phi coin) => _ coinv.
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
	have: forall psi', (F2MF F psi' (F psi')) by trivial.
	move => triv.
	have: forall (n: nat), id id n = n => //.
	move => true.
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
Definition is_cont2 Q A Q' A' (G: (Q-> A) -> Q' -> A') :=
  forall phi (q': Q'), exists (L : list Q), forall psi,
    phi and psi coincide_on L -> G phi q' = G psi q'.

Lemma continuity2 Q A Q' A' (F: (Q-> A) -> Q' -> A'):
	is_cont2 F <-> is_cont (F2MF F).
Proof.
  split.
  - move => cont psi s'.
    move: cont (cont psi s') => _ [L cond].
    exists L => phi coin Fpsi iv.
    move => Fphi iv'.
    rewrite -iv -iv'.
    by apply (cond phi).
  move => cont phi s'.
  move: cont (cont phi s') => _ [L cond].
  exists L => psi coin.
  have: forall psi', (F2MF F psi' (F psi')) by trivial.
  move => triv.
  move: cond (cond psi coin (F phi) (triv phi)) => _ cond.
  by apply: (cond (fun s' => F psi s')).
Qed.

Inductive one := star.

Lemma example: is_cont (fun phi Fphi => phi (Fphi star) = 0 /\ forall m, phi m = 0 -> m > Fphi star).
Proof.
  move => phi star.
  set cnt := (fun n:nat => n).
  set sec := (fun n:nat => n).
  set L := in_seg cnt.
  replace Top.star with star; last first.
  - by elim star.
  case: (classic (exists m, phi m = 0)); last first.
  - move => false.
    exists nil => psi _ fp1 [v1] cond.
    exfalso; apply false.
    by exists (fp1 star).
  move => [m me0].
  exists (L m).
  move => psi coin.
  move: (initial_segments cnt phi psi m) => [_ cond].
  move: cond coin (cond coin) => _ _ cond Fphi [v1 c1].
  move: v1 c1 (c1 (Fphi star) v1) => _ _ ge1.
  exfalso; lia.
Qed.