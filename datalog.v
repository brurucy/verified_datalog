(* This is a tremendously simple certified implementation of a unipredicate datalog engine. *)

Require Import String.
Require Import Datalog.Maps.
Require Import List.
Import ListNotations.

Module Datalog.

(* First we need to define the building blocks of datalog, Terms. *)

Inductive tm : Type :=
  (* A term is either a constant  *)
  | tm_const : string -> tm
  (* Or a variable. *)
  | tm_var : string -> tm
.

(* It's commonplace for constants to have an uppercase-non-single-letter name *)
Check tm_const "Professor".
(* And variables usually have uppercase single-letter names *)
Check tm_var "X".

(* A variable cannot ever equal a constant, but a variable can equal another variable, and the same also holds true for constants. *)
Definition eqb_term (lterm : tm) (rterm: tm) : bool :=
  match lterm, rterm with
  | tm_var _, tm_const _ => false
  | tm_const _, tm_var _ => false
  | tm_var lvalue, tm_var rvalue => eqb_string lvalue rvalue
  | tm_const lvalue, tm_const rvalue => eqb_string lvalue rvalue
  end.

Compute eqb_term (tm_const "Professor") (tm_var "Professor").
Compute eqb_term (tm_var "Professor") (tm_const "Professor").
Compute eqb_term (tm_const "Professor") (tm_const "Professor").
Compute eqb_term (tm_var "Professor") (tm_var "Professor").
Compute eqb_term (tm_const "X") (tm_const "Y").
Compute eqb_term (tm_var "X") (tm_const "Y").

(* Atoms are just lists of terms with a symbol *)

Inductive atom : Type :=
  (* They can be ground, if all terms are constants *)
  | atom_ground : string -> list tm -> atom
  (* Or regular, if else *)                                   
  | atom_regular : string -> list tm -> atom
.                                 

(* Atoms' symbols are lowercase.*)
Check (atom_regular "ancestor" [tm_var "X" ; tm_var "Y"]).

(* An atom equals another one if all of its terms equal the other's *)
Fixpoint eqb_term_list (l1 l2 : list tm) : bool :=
  match l1, l2 with
  | nil, nil => true
  | h :: l, h' :: r => if eqb_term h h' then eqb_term_list l r else false
  | _, _ => false                                                                 
  end.

Definition eqb_atom (latom : atom) (ratom : atom) : bool :=
  match latom, ratom with
  | atom_ground _ _, atom_regular _ _ => false
  | atom_regular _ _, atom_ground _ _ => false                                        
  | atom_ground sym l1, atom_ground sym' l2 => if eqb_string sym sym' then eqb_term_list l1 l2 else false
  | atom_regular sym l1, atom_regular sym' l2 => if eqb_string sym sym' then eqb_term_list l1 l2 else false                                                                                                    
  end.

(* A substitution is a mapping from a regular atom to a ground atom*)
Definition substitution := partial_map string.

Definition testmap := ("X" |-> "Albert"%string ; "Y" |-> "Alabart"%string).

Definition hasKey (m : partial_map string)
           (x : string) :=
  match (m x) with
  | Some _ => true
  | None => false
  end.           

Definition hasKeyValue (m : partial_map string)
           (x v : string) :=
  match (m x) with
  | Some v' => eqb_string v v'
  | None => false
  end.

Compute hasKey testmap "X".
Compute hasKeyValue testmap "X" "Albert".
Compute ("Z" |-> "Einstein"%string ; testmap).

Fixpoint ground_terms (l1 l2 : list tm)(s : substitution) : option substitution :=
  match l1, l2 with
  | nil, nil => Some s
  | (tm_const h) :: l, (tm_const h') :: r => if eqb_string h h' then ground_terms l r s else None
  | (tm_var h) :: l, (tm_const h') :: r => if hasKey s h
                                  then
                                    (if hasKeyValue s h h'
                                     then ground_terms l r s else None) else
                                    ground_terms l r (h |-> h' ; s)
  | _, _ => None    
  end.
                                       
(* A rule has a head and a body. the head is a single non-ground atom, and the body is a list of atoms *)
Record rule := Rule { head : atom ; body : list atom }.
                                                                          
(* This is the classic datalog example rule. *)
Definition transitivity_rule := Rule ([ var "X" ; var "Z" ]) ([[var "X" ; var "Y"] ; [var "Y" ; var "Z"]]).

Definition EDB := [ ([( const "x" ) ; ( const "y" )]) ; ([( const "y" ) ; ( const "z" )]) ; ([( const "z" ) ; ( const "w" )]) ].
