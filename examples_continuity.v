Load initial_segments.

Definition iscont Q A Q' A' (G: (Q-> A) -> Q' -> A') :=
  forall phi (q': Q'), exists (L : list Q), forall psi,
    phi and psi coincide_on L -> G phi q' = G psi q'.

Lemma continuity Q A Q' A' (F: (Q-> A) -> Q' -> A'):
	iscont F <-> is_cont (F2MF F).
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