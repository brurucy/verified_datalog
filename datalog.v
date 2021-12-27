(* This is a tremendously simple certified implementation of a unipredicate datalog engine. *)

Require Import String.
Require Import Datalog.Maps.
Require Import List.
Import ListNotations.

Module Datalog.

(* First we need to define the building blocks of datalog, Terms. *)
Inductive term : Type :=
  | const : string -> term
  | var : string -> term
.

Check const "Professor".
Check var "X".

(* a Variable cannot ever equal a Constant, but a variable can equal another Variable. *)
Definition eqb_term (lterm : term) (rterm: term) : bool :=
  match lterm, rterm with
  | var _, const _ => false
  | const _, var _ => false
  | var lvalue, var rvalue => eqb_string lvalue rvalue
  | const lvalue, const rvalue => eqb_string lvalue rvalue
  end.

Compute eqb_term (const "Professor") (var "Professor").
Compute eqb_term (var "Professor") (const "Professor").
Compute eqb_term (const "Professor") (const "Professor").
Compute eqb_term (var "Professor") (var "Professor").
Compute eqb_term (const "X") (const "Y").
Compute eqb_term (var "X") (const "Y").

(* Atoms are just triples of terms. *)

Definition atom := list term.     

(* An atom equals another one if all of its terms equal the other's *)
Fixpoint eqb_atom (latom : atom) (ratom : atom) : bool :=
  match latom, ratom with
  | nil, nil => true
  | h :: l, h' :: r => if eqb_term h h' then eqb_atom l r else false
  | _, _ => false                                                           
  end.

Compute eqb_atom ([ var "X" ; var "Y" ]) ([ var "X" ; var "Y"]).
Compute eqb_atom ([ var "X" ]) ([ var "X" ; var "Y"]).
Compute eqb_atom ([ var "X"]) ([const "X"]).

(* An atom is ground, if all of its terms are constant *)
Fixpoint is_ground (a : atom) : bool :=
  match a with
  | nil => true
  | (const _) :: l => is_ground l
  | _ => false
  end.

Compute is_ground ([ var "X" ; const "X" ]).
Compute is_ground ([ const "X"  ; const "Y" ]).

Fixpoint not_ground (a : atom) : bool :=
  negb(is_ground a).

Compute not_ground ([ var "X" ; const "X" ]).
Compute not_ground ([ const "X" ; const "Y" ]).

(* A rule has a head and a body. the head is a single non-ground atom, and the body is a list of atoms *)
Record rule := Rule { head : atom ; body : list atom }.

(* A trigger is a homomorphism from an atom to another atom *)

(* This is the classic datalog example rule. *)
Definition transitivity_rule := Rule ([ var "X" ; var "Z" ]) ([[var "X" ; var "Y"] ; [var "Y" ; var "Z"]]).

Definition EDB := [ ([( const "x" ) ; ( const "y" )]) ; ([( const "y" ) ; ( const "z" )]) ; ([( const "z" ) ; ( const "w" )]) ].
