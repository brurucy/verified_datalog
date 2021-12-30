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
  | atom_ground sym l1, atom_ground sym' l2 => if eqb_string sym sym' then eqb_term_list l1 l2 else false
  | atom_regular sym l1, atom_regular sym' l2 => if eqb_string sym sym' then eqb_term_list l1 l2 else false
  | _, _ => false                              
  end.

(* A substitution is a mapping from a regular atom to a ground atom *)
(* I could have used a map, but maps don't have an easy way to recurisvely traverse them, so it is of no use. *)
Definition substitution := list (tm * tm).

Fixpoint hasKey (s : substitution) (t1 : tm) : bool :=
  match s with
  | nil => false
  | (t, _) :: l => if eqb_term t t1 then true else hasKey l t
  end.

Fixpoint hasValue (s : substitution) (t1 : tm) : bool :=
  match s with
  | nil => false
  | (_, t') :: l => if eqb_term t' t1 then true else hasValue l t'
  end.

Fixpoint getValue (s : substitution) (t1 : tm) : option tm :=
  match s with
  | nil => None
  | (t, t') :: l => if eqb_term t t1 then Some t' else getValue l t
  end.

Fixpoint hasKeyValue (s : substitution) (t1 t2 : tm) : bool :=
  match s with
  | nil => false
  | (t, t') :: l => if eqb_term t t1 then eqb_term t' t2 else hasKeyValue l t1 t2
  end.                                                         

Fixpoint make_term_substitution (l1 l2 : list tm)(s : substitution) : option substitution :=
  match l1, l2 with
  | nil, nil => Some s
  | (tm_const h) :: l, (tm_const h') :: r => if eqb_string h h' then make_term_substitution l r s else None
  | h :: l, h' :: r => match (getValue s h) with
                    | Some t => if eqb_term h' t then make_term_substitution l r s else None
                    | None => make_term_substitution l r (s ++ [(h, h')])
                    end                      
  | _, _ => None    
  end.

Definition make_atom_substitution (a1 a2 : atom) (s : substitution) : option substitution :=
  match a1, a2 with
  | atom_regular sym l1, atom_ground sym' l2 => if eqb_string sym sym' then make_term_substitution l1 l2 s else None
  | _, _ => None    
  end.    

Definition example_regular_atom := (atom_regular "ancestor" [ tm_var "X"; tm_var "Y" ]).
Definition example_ground_atom := (atom_ground "ancestor" [ tm_const "Frederick"; tm_const "Roderick" ]).
Definition example_regular_atom_two := (atom_regular "ancestor" [ tm_var "X" ; tm_const "Roderick" ]).
Definition example_substitution := match (make_atom_substitution example_regular_atom example_ground_atom []) with
                                   | Some s => s
                                   | None => []
                                   end.
Definition example_substitution_two := match (make_atom_substitution example_regular_atom_two example_ground_atom []) with
                                       | Some s => s
                                       | None => []
                                       end.

Fixpoint substitute_term (l1 acc : list tm) (s : substitution) : list tm :=
  match l1 with
  | nil => acc
  | h :: l => substitute_term l (match (getValue s h) with
            | Some t => acc ++ [t]
            | None => acc ++ [h]
            end) s
  end.            

Definition substitute_atom (a1 : atom) (s : substitution) : option atom :=
  match a1 with
  | atom_regular sym l1 => Some (atom_ground sym (substitute_term l1 [] s))
  | _ => None    
  end.

Compute match (substitute_atom example_regular_atom_two example_substitution) with
        | Some a => a
        | None => (atom_regular ""%string [])
        end.



(* A rule has a head and a body. the head is a single non-ground atom, and the body is a list of atoms *)


(* This is the classic datalog example rule. *)
