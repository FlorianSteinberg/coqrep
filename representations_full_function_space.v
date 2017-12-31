Load representations.
(* This stopped working when I started to allow representing subsets. *)

Require Import ClassicalChoice.
(* These are only needed to guarantee that it is always possible to provide a
realizer of a function. *)

Lemma is_realizer_is_rep (X Y : rep_space):
  (@is_realizer X Y)
    is_representation_wrt
  (fun f g => forall x y, x is_element -> y is_element -> equals x y -> equals (f x) (g y))
    of
  (fun f => (forall x, (x is_element) -> (f x) is_element)
     /\ forall x y, equals x y -> equals (f x) (f y)).
Proof.
  move: (@rep_space.representation_is_valid X) (@rep_space.representation_is_valid Y)
    => [xsing [xeq xsur]] [ysing [yeq ysur]].
  split.
  - move => phi f g [cond _] [cond' _] irx iry x y xif yif xey.
    move: (xsur x xif) => [a anx].
    apply: (ysing (phi a) (f x) (g y)).
    - by apply: cond.
    - by apply: cond'.
    - by apply: irx.
    - apply: iry.
      - by apply: (xeq x y a xey).
      - done.
  - split.
    - move => f g F cond real phi x inx xif.
      apply: (yeq (f x) (g x) (F phi)).
      - apply: (cond x x) => //.
        apply: (xsing phi x x) => //.
      - by apply: (real phi x).
  - move => f [cond cond'].
    set R := fun a b => forall x, x is_element -> delta a x -> delta b (f x).
    have: forall a, exists b, R a b.
    move => a.
    case: (classic (exists x, delta a x /\ x is_element)).
    - move => [x [anx xie]].
      move: (cond x xie) => fxie.
      move: (ysur (f x) fxie) => [b bnx].
      exists b.
      move => y yifx any.
      move: (cond y yifx) => fyify.
      move: (xsing a x y xie yifx anx any) => xey.
      move : (ysur (f y) fyify) => [c cnfy].
      apply: (yeq (f x) (f y) b).
      - by apply: cond'.
      - done.
    - move => eq.
      exists (@rep_space.inhe Y).
      move => y yifx any.
      exfalso.
      apply eq.
      by exists y.
  - move => fe.
    move: (@choice (names X) (names Y) R fe) => [F Fir].
    exists F.
    move => a x anx xie.
    apply: (Fir a x xie anx).
Qed.

Arguments is_realizer_is_rep {X Y}.

(* Using this lemma it is possible to provide a full functionspace construction
This functionspace construction will usually be utterly useless as the types
of names become higher and higher type objects. For a better function space one
should at least restrict to the continuously realizable functions. But for to make
that function space construction work a lot more work is needed. *)

Canonical rep_space_all_functions X Y := @rep_space.make_rep_space
  (space X -> space Y)
  (fun f => (forall x, (x is_element) -> (f x) is_element)
     /\ forall x y, equals x y -> equals (f x) (f y))
  (fun f g => forall x y, x is_element -> y is_element -> equals x y -> equals (f x) (g y))
  (names X -> names Y)
  (fun x => @rep_space.inhe Y)
  (is_realizer)
  (is_realizer_is_rep).