(* This file is supposed to contain the definition of a universal machine and the proof
that the machine is actually universal. The universal machine is a machine of type two
and it should work for any continuous function from B -> B. Usually B is the Baire space,
here, i.e. the set of all mappings from strings to strings. However, since I don't want
to rely on a handwritten type of strings as I attempted in the file "operators.v", and
use more generaly a space S -> T as substitute for B, I have to make some assumptions
about the types S and T. This is why I came up with "SizeTypes", that are defined in the
separate file "SizeTypes.v" and are used here. *)
Load size_types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Fixpoint equal_on S T (phi : S -> T) (psi : S -> T) (L : list S) :=
  match L with
    | nil => True
    | cons s K => (phi s = psi s) /\ (equal_on phi psi K)
  end.
Notation "phi 'and' psi 'coincide_on' L" := (equal_on phi psi L) (at level 2).

Definition is_continuous (S : size_type) (S' T T' :Type) (F: (S -> T) -> S' -> T') :=
  forall phi s', exists (L : list S),
  forall psi, phi and psi coincide_on L ->  F phi s' = F psi s'.
(* This notion is porbably way to inefficient to be of any use. *)

Notation operator S T S' T' := (nat -> (S -> T) -> S' -> option T').

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