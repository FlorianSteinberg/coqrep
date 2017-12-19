From mathcomp Require Import all_ssreflect ssrnat.
Require Import Reals Classical ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Inductive str : Type :=
  | es : str
  | sO : str -> str
  | sI : str -> str.

Fixpoint un a:= match a with
  |es => 0
  |sO b => (un b).+1
  |sI b => (un b).+1
end.

Fixpoint unenc n := match n with
  | 0 => es
  | S m => sI (unenc m)
end.

Lemma uncircunenc : forall n, un (unenc n) = n.
Proof.
  elim.
  done.
  move => n IHn /=.
  by rewrite IHn.
Qed.

Fixpoint i a := match a with
  | es => sI (sI es)
  | sO b => sO (sO (i b))
  | sI b => sO (sI (i b))
end.

Fixpoint invi a := match a with
  | es => es
  | sO es => es
  | sO (sO b) => sO (invi b)
  | sO (sI b) => sI (invi b)
  | sI es => es
  | sI (sO b) => es
  | sI (sI b) => es
end.

Lemma scinvi : forall a, invi (i a) = a.
Proof.
  elim => // s ihs /=; by rewrite ihs.
Qed.

Fixpoint concat a b := match a with
  | es => b
  | sO c => sO (concat c b)
  | sI c => sI (concat c b)
end.

Definition pair a b := concat (i a) (i b).

Definition append a b := concat a (i b).

Definition p1 a := invi a.

Lemma scp1 b : forall a, p1 (pair a b) = a.
Proof.
  elim => //= s H; by rewrite H.
Qed.

Fixpoint is_sequence a := match a with
  | es => false
  | sO es => false
  | sO (sO b) => is_sequence b
  | sO (sI b) => is_sequence b
  | sI es => false
  | sI (sO b) => false
  | sI (sI b) => is_sequence b
end.

Fixpoint p2 a := match a with
  | es => es
  | sO es => es
  | sO (sO b) => p2 b
  | sO (sI b) => p2 b
  | sI es => es
  | sI (sO b) => es
  | sI (sI b) => p1 b
end.

Lemma scp2 b : forall a, p2 (pair a b) = b.
Proof.
  elim => //=; by rewrite /p1 scinvi.
Qed.

Fixpoint numberelts a := match a with
  | es => 0
  | sO es => 0
  | sO (sO b) => numberelts b
  | sO (sI b) => numberelts b
  | sI es => 1
  | sI (sO b) => match b with
    | es => 0
    | sO c => numberelts c
    | sI c => numberelts c
  end
  | sI (sI b) => numberelts b + 1
end.

Lemma inumberelts : forall b, numberelts (i b) = 1.
Proof.
  by elim.
Qed.

Fixpoint elt a n := match n with
  | 0 => p1 a
  | S n => p1 (p2 a)
end.

Fixpoint bin a := match a with
  | es => xH
  | sI b => xI (bin b)
  | sO b => xO (bin b)
end.

Fixpoint binenc n := match n with
  | xH => es
  | xI m => sI (binenc m)
  | xO m => sO (binenc m)
end.

Notation B := (str -> str).

Definition pairing : B -> B -> B :=
  fun phi psi a => match a with
    | es => es
    | sO b => phi b
    | sI b => psi b
  end.

Definition proj0 : (str -> str) -> (str -> str) :=
  fun phi a => phi(sO a).

Lemma projection0 phi psi : (proj0 (pairing phi psi)) =1 phi.
Proof.
  done.
Qed.

Definition proj1 : (str -> str) -> str -> str :=
  fun phi a => phi(sI a).

Lemma projection1 : forall phi psi, proj1 (pairing phi psi) = psi.
Proof.
  done.
Qed.

Fixpoint begseg phi n := match n with
  | 0 => es
  | S m => append (begseg phi m) (phi (binenc(Pos.of_nat m + 1)))
end.

Lemma begsegnumberelts phi: forall n, numberelts (begseg phi n) = n.
Proof.
  elim => //.
  move => n ihn /=.


Definition iscon F := forall phi n, exists m, forall psi,
  begseg psi m = begseg phi m -> begseg (F phi) n = begseg (F psi) n.

Notation operator := (nat -> B -> str -> option str).

Definition dom (F : operator) (phi : B) :=
  forall a b, exists n, F n phi a = some b.

Definition is_value (F : operator) phi psi :=
  forall a, exists k, F k phi a = Some (psi a)
    /\ forall n, n <= k -> F n phi a = None.

Fixpoint U n psi a := match n with
  | 0 => None
  | S n => match proj0 psi a with
    | es => None
    | sO c => Some c
    | sI c => U n psi (pair a c)
  end
end.

Definition psi_ F m a : option str :=
  if numberelts a <= m then None
    else Some(F (fun b => elt(a)(nat_of_pos(bin b)+1))(elt(a)(0))).

Lemma psigood F: iscon F -> forall a phi,
  exists m, psi_ F m (pair a (begseg phi m)) = Some(F phi a).

Lemma universaloperator F : iscon F -> 
  exists psiF : B, forall phi,
    is_value U (pairing psiF phi) (F phi).
Proof.
  move => isc.
  move: choice => whatever.
  set R := fun a b => exists k : nat,
    U k (pairing psiF phi) a = Some (F phi a) /\
    (forall n : nat, n <= k -> U n (pairing psiF phi) a = None).
  exists (fun m => psi_ F (2^m)).
  move => phi n.
  move: (isc phi n).
  case.
  move => m ismod.
  exists m.
  move => b bln.
  move: psigood => psigd.