From mathcomp Require Import all_ssreflect ssrnat.
Require Import Reals Lra Classical ClassicalFacts.

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
  by elim => // n ihn /=; rewrite ihn.
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

Compute invi (sO (sO (sI es))).

Lemma scinvi : forall a, invi (i a) = a.
Proof.
  by elim => // s ihs; rewrite /= ihs.
Qed.

Fixpoint concat a b := match a with
  | es => b
  | sO c => sO (concat c b)
  | sI c => sI (concat c b)
end.

Definition pair a b := concat (i a) b.

Compute pair (sO es) (sO es).

Definition p1 a := invi a.

Compute p1 (pair (sO (sI es)) (sI (sO es))).

Lemma scp1 b : forall a, p1 (pair a b) = a.
Proof.
   by elim => // s inv; rewrite /= inv.
Qed.

Fixpoint p2 a := match a with
  | es => es
  | sO es => es
  | sO (sO b) => p2 b
  | sO (sI b) => p2 b
  | sI es => es
  | sI (sO b) => es
  | sI (sI b) => b
end.

Compute p2 (pair (sO (sI es)) (sO (sO es))).

Lemma scp2 b : forall a, p2 (pair a b) = b.
Proof.
  by elim.
Qed.

Fixpoint numberelts a := match a with
  | es => 1
  | sO es => 1
  | sO (sO b) => numberelts b
  | sO (sI b) => numberelts b
  | sI es => 1
  | sI (sO b) => 1
  | sI (sI b) => numberelts b + 1
end.

Lemma scnumberelts: forall a b, numberelts (pair a b) = numberelts b + 1.
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

Definition bseg (phi : B) (n : nat) := fun a => if un a <= n then phi a else es.

Definition psi F b a := 
  if numberelts a <= nat_of_pos(bin b) then binenc (bin b+1) else F (fun b => elt(a)(nat_of_pos(bin b))).

Notation operator := (nat -> B -> str -> option str).

Definition dom (F : operator) (phi : B) := forall a b, exists n, F n phi a = some b.

Definition isvalue (F : operator) phi psi :=
  forall a, exists k, F k phi a = Some (psi a) /\ forall n, n <= k -> F n phi a = None.

Definition U' psi a := match a with
  | es => es
  | sO c => sO c
  | sI b => match proj0 psi b with
    | es => es
    | sO c => sO c
    | sI c => sI (pair a (proj1 psi c))
  end
end.

Fixpoint U'' n psi a := match n with
  | 0 => a
  | S m => U' psi (U'' m psi a)
end.

Definition U n psi a := match n with
  | 0 => None
  | S n => match U'' n (proj1 psi) a with
    | es => None
    | sO c => Some c
    | sI c => None
  end
end.

Lemma universaloperator F :
  (forall phi, iscon F phi) -> exists psiF, forall phi psi, F phi = psi -> isvalue U (pairing psiF phi)  psi.
Proof.
  move => isc.
  move: (continuity F) => conti.
  move: (isc phi).
  move: (conti isc).
Definition iscont (F : operator) := forall phi phi' psi, eqB phi phi' -> isvalue F phi psi <-> isvalue F phi' psi.

Definition extends F G := 
  forall phi psi, isvalue G phi psi -> isvalue F phi psi.
