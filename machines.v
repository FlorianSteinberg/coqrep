Load size_types.

Structure dict_type := make_dict_type {
  type : size_type;
  questions : size_type;
  answers : size_type;
  type_check : eq (elems questions -> elems answers) (elems type)
}.

Canonical dict_type_prod S T := @make_dict_type
  (size_type_prod (questions S) (questions T))
  (size_type_prod (answers S) (answers T))
.
(* I think the products should be replaced by sums at some point. *)

Canonical dict_type_arrow S T := @make_dict_type
  (size_type_prod (size_type_arrow (questions S) (answers S)) (questions T))
  (answers T).

Canonical dict_type_list S := @make_dict_type
  (size_type_list (questions S))
  (size_type_list (answers S)).
(* I am neither sure that this type is appropriate nor that it is necessary. *)

Notation "B ~> B'" := (nat -> questions (dict_type_arrow B B') ->
  option(answers (dict_type_arrow B B'))) (format "B ~> B'", at level 2).
(* I think about this type as a type of machines: For M : B ~> B' I "read M s n = nothing" as
"the Machine can't say anything about the return value yet" and "M s n = some t" as "after n
steps the machine considers t to be the best answer". Since no assumption about concurrency
have been made, in general a machine will produce an infinite list of return values. *)

Definition eval B B' (M : B ~> B') : ((questions B -> answers B) ->> (questions B' -> answers B')) :=
  fun phi a => forall (phi : questions B -> answers B) (a : questions B'),
    exists n (b : answers B'), M n (phi,a) = some b.
(* if M is a machine then eval M is the function the machine computes. Since no assumptions
about convergence or concurrency have been made, the computed multivalued function need
neither be singlevalued nor total. *)

Definition is_comp B B' (F: (questions B -> answers B) ->> (questions B' -> answers B')):=
  exists M, forall phi, (exists psi, F phi psi) -> forall psi, eval M phi psi -> F phi psi.
(* This is the best candidate for computability I have come up with so far: If there are eligible
return values then the machine produces one of these, but if there are none, the machine may behave
arbitrarily. I am not one hundred percent sure this is the right notion, but pretty confident. *)
Notation "F 'is_computable'" := (is_comp F) (at level 2).