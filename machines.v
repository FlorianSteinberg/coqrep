Notation "S ~> T" := (S -> nat -> option T) (format "S ~> T", at level 2).
(* I think about this type as a type of machines: For M : S ~> T I read M s n = nothing as
"the Machine can't say anything about the return value yet" and M s n = some t as "after n
steps the machine considers t to be the best answer". Since no assumption about concurrency
have been made, in general a machine will produce an infinite list of return values. *)

Definition eval S T (M : S ~> T) : (S ->> T) := fun a b => exists n b, M a n = some b.
(* if M is a machine then eval M is the function the machine computes. Since no assumptions
about convergence or concurrency have been made, the computed multivalued function need
neither be singlevalued nor total. *)

Definition is_comp S T (f: S ->> T):=
  exists M, forall s, (exists t, f s t) -> forall t, eval M s t -> f s t.
(* This is the best candidate for computability I have come up with so far: If there are eligible
return values then the machine produces one of these, but if there are none, the machine may behave
arbitrarily. I am not one hundred percent sure this is the right notion, but pretty confident. *)