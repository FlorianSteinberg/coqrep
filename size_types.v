Load functions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Module Major.
Structure type:= Pack {
  sort :> Type;
  major : sort -> sort -> Prop;
  zero : sort;
  max : sort -> sort -> sort;
  add : sort -> sort -> sort;
  mult : sort -> sort -> sort
}.
End Major.
Coercion Major.sort : Major.type >-> Sortclass.
Definition major {M : Major.type} : M -> M -> Prop :=
  match M with Major.Pack _ rel _ _ _ _ => rel end.
(* The Major type will be used to measure sizes. The most instructive
Examples is nat, which is the most common measure for sizes. But Major
works in a more general setting: also N->N is sometimes used to measure
sizes. The operations are there because at some point I want to be able
to talk about Polynomials over a Major type. Note that the Major type
is taken from the file about second-order polynomials. *)

Canonical Major_nat := @Major.Pack nat leq 0 max plus mult.
(* The most basic example of a Major type: the natural numbers *)
Canonical Major_prod M1 M2 := @Major.Pack
  (Major.sort M1 * Major.sort M2)
  (fun m n => major m.1 n.1 /\ major m.2 n.2)
  (pair (Major.zero M1) (Major.zero M2))
  (fun m n => pair (Major.max m.1 n.1) (Major.max m.2 n.2))
  (fun m n => pair (Major.add m.1 n.1) (Major.add m.2 n.2))
  (fun m n => pair (Major.mult m.1 n.1) (Major.mult m.2 n.2))
.
Canonical Major_arrow M1 M2 := @Major.Pack
  (Major.sort M1 -> Major.sort M2)
  (fun l k => forall n m, major n m -> major (l n) (k m))
  (fun n => Major.zero M2)
  (fun l k => fun n => Major.max (l n) (k n))
  (fun l k => fun n => Major.add (l n) (k n))
  (fun l k => fun n => Major.mult (l n) (k n))
.

Definition const_inc_major M (b : M) := (fun (b':M) => b).
(* I want to write this:
Coercion const_inclusion_major: M >-> (Major_arrow M M).
but it does not work *)

Notation "b 'majorizes' a" := (major a b) (at level 2): major_scope.
Notation "b 'is_monotone'" := (major b b) (at level 2): major_scope.
(* In most situations it is probably enough to consider the monotone bounds. *)

Structure size_type := make_size_type {
  elems :> Type;
  bounds : Major.type;
  is_size : elems ->> bounds;
  inh: elems
  }.
(* If there is a way to measure the size of an element by something of Major type
then a size type can be constructed. Size types provide enough structure such
that it is possible to form products, arrows. *)
Notation "b 'is_size_of' s" := (is_size s b) (at level 2).
Notation "b 'is_bound_of' s" := (forall k, is_size s k -> major k b) (at level 2).
Notation "s 'is_bounded'" := (exists b, b is_bound_of s) (at level 2).

Canonical size_type_prod S T := @make_size_type
  (elems S * elems T)
  (Major_prod (bounds S) (bounds T))
  (fun s b => is_size s.1 b.1 /\ is_size s.2 b.2)
  (pair (inh S) (inh T) ).

Canonical size_type_arrow S T := @make_size_type
  (elems S -> elems T)
  (Major_arrow (bounds S) (bounds T))
  (fun f b => forall k, exists s, k is_size_of s /\ (b k) is_size_of (f s))
  (fun s => inh T).

(* It is also possible to form a list over a size type. We need the lists for
the universal machines, so this is important. Unfortunatelly it is also a
little complicated. Since is_size is a mathematical function there need not
be a way to get a value from an element whose size one wants to measure.
Fortunatelly we are mostly interested in finite lists. So we proceed as
follows: we say that a function f: elems S-> bounds S is consistent on a
list if it produces the sizes of the elements of the list. *)

Fixpoint consistent_with_list (S : size_type) (f: elems S -> bounds S) (L : list S) :=
match L with
  | nil => True
  | cons s K => is_size s (f s) /\ (consistent_with_list f K)
end.

(* Next we define the size of a list to be the sum of the sizes of the elements.
We may use any function that is consistent on the list. *)

Fixpoint list_size (S : size_type) (f : elems S -> bounds S) (L : list S) :=
match L with
  | nil => Major.zero (bounds S)
  | cons s K => Major.add (f s) (list_size f K)
end.

(* We can use these both two to define the size type of lists. *)

Canonical size_type_list S := @make_size_type
  (list (elems S))
  (bounds S)
  (fun L b => exists (f: elems S -> bounds S),
    consistent_with_list f L /\ b = list_size f L)
  (nil).