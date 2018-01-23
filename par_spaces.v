(* This file provides an alternative formulation of represented spaces that saves
the input and output types of the names *)
From mathcomp Require Import all_ssreflect.
Require Import multi_valued_functions universal_machine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section REPRESENTED_SPACES.
Definition is_rep S T (delta: S ->> T) :=
  delta is_single_valued /\ delta is_surjective.
Notation "delta 'is_representation'" := (is_rep delta) (at level 2).
(* S ->> T is a notation for S -> T -> Prop. This defines a representation to be a
surjective and singlevalued multi-valued function. Due to delta being single-valued
this can also be phrased as a representation being a partial surjection. *)

Definition is_rep_of S T (delta: S ->> T) (P : T -> Prop) :=
  delta is_single_valued_wrt (fun t t' => t = t') /\ delta is_surjective_wrt P.
Notation "delta 'is_representation_of' elements" := (is_rep_of delta elements) (at level 2).
(* To make subspaces work, we allow predicates as the underlying set of a represented space. *)

Definition is_rep_of_wrt S T (delta: S ->> T) (P: T -> Prop) (R: T-> T -> Prop) :=
  delta is_single_valued_wrt R /\ delta is_surjective_wrt P.
Notation "delta 'is_representation_wrt' equals 'of' elements" := 
  (is_rep_of_wrt delta elements equals) (at level 2).
(* This is to make it possible to identify elements arbirarily, i.e. make quotients work. *)

Lemma sur_rep_b S T (delta: S ->> T) :
  delta is_representation <-> delta is_representation_of (fun x => True).
Proof.
split.
- move => [issing issur].
	split.
		split.
 			move => s t t' dst dst'.
 			by apply: (issing.1 s t t').
 		move => s t t' dst eq.
 		by rewrite -eq.
  move => t _ .
  move: (issur t) => [] s dst.
  by exists s.
move => [issing issur].
split.
	split.
		move => s t t' dst dst'.
  	by apply: (issing.1 s t t').
	move => s t t' dst eq.
	by rewrite -eq.
move => t.
have: True.
	done.
move => true.
move: (issur t true) => []s []dst_.
by exists s.
Qed.

Lemma sur_rep S T (delta: S ->> T) :
  delta is_representation -> delta is_representation_of (fun x => True).
Proof.
  move: (sur_rep_b delta) => [cond cond'].
  exact: cond.
Qed.

Lemma sur_rep_sing_b S T (delta: S ->> T) (P: T -> Prop) :
  delta is_representation_of P <-> delta is_representation_wrt (fun x y => x = y) of P.
Proof.
done.
Qed.

Lemma sur_rep_sing S T (delta: S ->> T) (P: T -> Prop) :
  delta is_representation_of P -> delta is_representation_wrt (fun x y => x = y) of P.
Proof.
move: (sur_rep_sing_b delta P) => [cond cond'].
exact: cond.
Qed.
(* To construct a represented space it is necessary to provide a proof that the
representation is actually a representation. The names can be an arbitrary type
but will usually be something that can be computed on, i.e. Baire space or something.
At some point I will probably change the names to be a size_type. The type of names
must be inherited for the rather irrelevant full function-space construction to
work. This may change depending on whether other function space constructions also
need this or not. *)
Structure type := make_comp_space {
  space : Type;
  elements : space -> Prop;
  equals : space -> space -> Prop;
  questions : Type;
  answer_type : Type;
  delta : (questions -> option(answer_type)) ->> space;
  countable_questions: questions is_countable;
  countable_answers: answer_type is_countable;
  representation_is_valid : delta is_representation_wrt equals of elements
  }.
Notation answers X := (option (answer_type X)).
Notation names X := ((questions X) -> (answers X)).

Require Import FunctionalExtensionality.

Lemma prod_rep (X Y : type):
  (fun (phipsi : (questions X + questions Y -> option(answer_type X + answer_type Y))) x =>
      delta (fun q => match phipsi (inl q) with
        | None => None
        | Some (inl a) => Some a
        | Some (inr b) => None
      end) x.1 /\ delta (fun q => match phipsi (inr q) with
        | None => None
        | Some (inl a) => None
        | Some (inr b) => Some b
      end) x.2)
    is_representation_wrt
  (fun x y => equals x.1 y.1 /\ equals x.2 y.2)
    of
  (fun x => elements x.1 /\ elements x.2).
Proof.
move: (@representation_is_valid X) (@representation_is_valid Y)
  => [xsing xsur] [ysing ysur].
split.
	split.
		move => phipsi [x y] [x' y'] /= [inx iny] [inx' iny'].
    split.
      apply: xsing.1 => //.
      	by apply: inx.
      by apply: inx'.
    apply: ysing.1 => //.
      by apply iny.
    by apply iny'.
	move => phipsi.
	move => [] x y [] x' y' /=[] inx iny [] ex ey.
	split.
		apply/ xsing.2.
			by apply inx.
		done.
	apply/ ysing.2.
		by apply iny.
	done.
move => [] x y /=[Px Py].
move: (xsur x Px) => [] phi []dphix phiprop.
move: (ysur y Py) => [] psi []dpsiy psiprop.
exists (fun q => match q with
	| inl qx => match phi qx with
		| Some a => Some (inl a)
		| None => None
	end
	| inr qy => match psi qy with
		| Some a => Some (inr a)
		| None => None
	end
end).
split => /=.
	replace (fun q : questions X =>
  match
		match phi q with
			| Some a => Some (inl a)
			| None => None
		end
	with
		| Some (inl a) => Some a
		| Some (inr _) => None
		| None => None
	end) with phi.
	split => //.
		replace (fun q : questions Y =>
			match
				match psi q with
					| Some a => Some (inr a)
					| None => None
				end
			with
				| Some (inr a) => Some a
				| Some (inl _) => None
				| None => None
			end) with psi.
		done.
	apply: functional_extensionality => q.
	by elim (psi q).
apply: functional_extensionality => q.
by elim (phi q).
move => phipsi [] x' y' []dphix' dpsiy' [] ano ther.
split.
	apply/ phiprop.
		by apply dphix'.
	done.
apply/ psiprop.
	by apply dpsiy'.
done.
Qed.

(* This is the product of represented spaces. At some point I should prove that this
is the product in some category, but I am unsure what the morphisms are supposed to be. *)

Notation rep_space := type.
Notation "'rep'" := @delta (at level 2).
Notation "phi 'is_name_of' x" := (delta phi x) (at level 2).
Notation "x 'is_element'" := (elements x) (at level 2).
Notation "x 'is_from' X" := (@elements X x) (at level 2).
Notation "x 'equal' y" := (@equals x y) (at level 2).

Lemma sum_is_countable Q Q':
  Q is_countable -> Q' is_countable -> (Q + Q') is_countable.
Proof.
move => [cnt1] sur1 [cnt2] sur2.
set cnt' := fix cnt' n := match n with
	| 0 => (inl (cnt1 0),0)
	| 1 => (inr (cnt2 0),0)
	| S (S n') => match cnt' n' with
		| (inl s,m) => (inl (cnt1 (S m)),S m)
		| (inr t,m) => (inr (cnt2 (S m)),S m)
	end
end.
have: forall n, 2 * (cnt' n).2 = n <-> exists s, (cnt' n).1 = inl s.
	elim.
		split.
			move => eq.
			by exists (cnt1 0).
		by move => [] s eq.
	move => n ih.
		split.
			move => eq.
			exists ((cnt' n).1).
	
exists (fun n => (cnt' n).1).
rewrite /is_sur.
apply sum_rect.
	move => s.
	move: (sur1 s) => [n] idx.
	exists (2*n).
	move: n s idx.
	rewrite /F2MF.
	elim.
		move => s idx.
		by rewrite -idx.
	move => n ih s idx.
	replace (2 * n.+1) with ((2 * n).+2).
		rewrite -idx.
		replace (inl (cnt1 n.+1)) with ((@inl Q Q' (cnt1 (S n)),S n).1).
		replace ((@inl Q Q' (cnt1 (S n)),S n).1) with (cnt 
		done.
		replace (cnt (2 * n).+2) with (@inl S T (cnt1 (n.+1))) => //.
		replace (cnt1 n.+1) with (cnt1 (2 * n)) => //.
		

    have 
 (ih (cnt1 n)).
    have (cnt (2*n)) = inl s
    case: ih.
    rewrite /cnt /=.
    by rewrite -idx.
    replace (inl (cnt1 n.+1)) with (cnt (2*n.+1)).
    
    replace (cnt (2*n).+1) with (@inr S T (cnt2 n)).
    exists cnt 
    - rewrite -idx.
      replace 
      
    

Canonical rep_space_prod X Y := @make_rep_space
  (space X * space Y)
  (fun x => x.1 is_element /\ x.2 is_element)
  (fun x y => equals x.1 y.1 /\ equals x.2 y.2)
  (@questions X + @questions Y)
  (@answer_type X + @answer_type Y)
  (fun (phipsi : (questions X + questions Y -> option(answer_type X + answer_type Y))) x =>
      delta (fun q => match phipsi (inl q) with
        | None => None
        | Some (inl a) => Some a
        | Some (inr b) => None
      end) x.1 /\ delta (fun q => match phipsi (inr q) with
        | None => None
        | Some (inl a) => None
        | Some (inr b) => Some b
      end) x.2)
  (@prod_rep X Y).

Definition make_rep_space_from_sur
  (space : Type)
  (questions : Type)
  (answers : Type)
  (delta : (questions->option(answers)) ->> space) (representation_is_valid : is_rep delta) :=
  @make_rep_space space
    (fun x=> True)
    (fun x y => x= y)
    questions
    answers
    delta
    (sur_rep_sing (sur_rep representation_is_valid))
  .

Lemma fun_rep_on_range S X (f : S -> X) :
  (F2MF f) is_representation_of (range (F2MF f)).
Proof.
  split.
  - move => s t t' tfr t'fr fst fst'.
    by rewrite -fst -fst'.
  - by move => t tfrf.
Qed.

Definition make_rep_space_from_fun
  (space : Type)
  (questions : Type)
  (answers : Type)
  (delta: (questions->option answers) -> space) :=
    @make_rep_space
      space
      (range (F2MF delta))
      (fun x y => x = y)
      questions
      answers
      (F2MF delta)
      (sur_rep_sing (fun_rep_on_range delta))
    .

Lemma single_valued_rep_on_range S T (f : S ->> T) :
  f is_single_valued -> f is_representation_of (range f).
Proof.
  move => sing.
  split.
  - move => s t t' tfr t'fr.
    by apply sing.
  - done.
Qed.

Definition make_rep_space_from_mfun
  (space : Type)
  (questions : Type)
  (answers : Type)
  (delta: (questions -> option answers) ->> space)
  (sing: delta is_single_valued) :=
    @make_rep_space
      space
      (range delta)
      (fun x y => x = y)
      questions
      answers
      delta
      (sur_rep_sing (single_valued_rep_on_range sing)).

Definition is_mf_realizer (X Y : rep_space) F (f : (space X) ->> (space Y)) :=
  forall phi x y, delta phi x -> delta (F phi) y -> f x y.
(* One candidate for the morphisms: The multivalued realizable functions. *)

Definition is_realizer (X Y : rep_space) F (f: space X -> space Y) := is_mf_realizer F (F2MF f).
(* A second candidate: the total singlevalued realizable functions *)
Notation "F 'is_realizer_of' f" := (is_realizer F f) (at level 2).
Arguments is_realizer {X Y}.

Definition is_comp (X Y : rep_space) (f : space X -> space Y) :=
  exists F, is_realizer F f.
Notation "f 'is_computable'" := (is_comp f) (at level 2).

Notation "X ~> Y" := (nat -> (names X) -> (questions Y) -> answers Y) (format "X ~> Y", at level 2).
(* I think about this type as a type of machines: For M : B ~> B' I "read M s n = nothing" as
"the Machine can't say anything about the return value yet" and "M s n = some t" as "after n
steps the machine considers t to be the best answer". Since no assumption about concurrency
have been made, in general a machine will produce an infinite list of return values. *)

Definition eval (X Y : rep_space) (M : X ~> Y) : ((names X) ->> (names Y)) :=
  fun (phi : names X) (psi : names Y) => forall (a : questions Y), exists n, M n phi a = psi a.
(* if M is a machine then eval M is the function the machine computes. Since no assumptions
about convergence or concurrency have been made, the computed multivalued function need
neither be singlevalued nor total. *)

Definition is_comput (X Y : rep_space) (F: (names X) ->> (names Y)):=
  exists M, forall phi, (exists psi, F phi psi) -> forall psi, (eval M phi psi -> F phi psi).
(* This is the best candidate for computability I have come up with so far: If there are eligible
return values then the machine produces one of these, but if there are none, the machine may behave
arbitrarily. I am not one hundred percent sure this is the right notion, but pretty confident. *)
Notation "F 'is_computable'" := (is_comput F) (at level 2).