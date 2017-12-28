Load example_size_types.

Structure machine_type := make_machine_type {
  type :> size_type;
  input_type : size_type;
  output_type : size_type;
}.

Canonical machine_type_prod S T := @make_machine_type
  (size_type_prod (type S) (type T))
  (size_type_prod (input_type S) (input_type T))
  (size_type_prod (output_type S) (output_type T)).

Canonical machine_type_arrow S T := @make_machine_type
  (size_type_arrow (type S) (type T))
  (size_type_prod (type S) (input_type T))
  (output_type T).

Canonical machine_type_list S := @make_machine_type
  (size_type_list (type S))
  (size_type_list (input_type S))
  (size_type_list (output_type S)).

Canonical machine_type_one := @make_machine_type
  size_type_one
  size_type_one
  size_type_one.

Canonical machine_type_nat := @make_machine_type
  size_type_nat
  size_type_one
  size_type_nat.

Notation "S ~> T" := (nat -> input_type (machine_type_arrow S T) -> 
  option(output_type (machine_type_arrow S T))) (format "S ~> T", at level 2).
(* I think about this type as a type of machines: For M : S ~> T I read M s n = nothing as
"the Machine can't say anything about the return value yet" and M s n = some t as "after n
steps the machine considers t to be the best answer". Since no assumption about concurrency
have been made, in general a machine will produce an infinite list of return values. *)

Definition eval S T (M : S ~> T) : ((type S) ->> (type T)) :=
  fun a b => forall (a : type S) (b : input_type T), exists n (c : output_type T), M n (a,b) = some c.
(* if M is a machine then eval M is the function the machine computes. Since no assumptions
about convergence or concurrency have been made, the computed multivalued function need
neither be singlevalued nor total. *)

Definition is_comp S T (f: (type S) ->> (type T)):=
  exists M, forall s, (exists t, f s t) -> forall t, eval M s t -> f s t.
(* This is the best candidate for computability I have come up with so far: If there are eligible
return values then the machine produces one of these, but if there are none, the machine may behave
arbitrarily. I am not one hundred percent sure this is the right notion, but pretty confident. *)