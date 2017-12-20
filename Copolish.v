(* This file contains an alternative to the Compspace file, that seems to be closer to
Matthias Schroeders Copolish spaces. That's where the name is taken from. It will have
to become clear from the applications which approach is nicer to use. *)

Load representations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicits Defensive.

Structure copolish_space := make_copolish_space {
  elts :> rep_space;
  size : (@names elts) ~> nat;
  (* The notation S ~> T is introduced in functions.v and requires the existence of a machine that computes a
  multivalued function. Matthias uses continuous functions instead, but I don't know how to formulate continuity. *)
  size_matches : (is_sing (eval size) /\ (forall phi, dom (@is_name elts) phi -> dom (eval size) phi))
  (* If spelled out this requires the domain of the size function to contain the domain of the representation. *)
}.

(* I'll have to define basic copolish spaces at some point. It may be necessary to include an assumption about the
domain of the representation being closed. *)