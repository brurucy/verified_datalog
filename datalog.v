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

(* Atoms are just conjunctions of of terms with a symbol *)
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

(* A substitution is a mapping from a regular term to another regular or ground term *)
(* I could have used a map, but maps don't have an easy way to recurisvely traverse them. *)
Definition substitution := list (tm * tm).

Fixpoint getValue (s : substitution) (t1 : tm) : option tm :=
  match s with
  | nil => None
  | (t, t') :: l => if eqb_term t t1 then Some t' else getValue l t1
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
Definition example_regular_atom_three := (atom_regular "ancestor" [ tm_var "Y" ; tm_var "Z" ]).
(* [(tm_var "X", tm_const "Frederick"), (tm_var "Y", tm_const "Roderick")] *)
Definition example_substitution := match (make_atom_substitution example_regular_atom example_ground_atom []) with
                                   | Some s => s
                                   | None => []
                                   end.
(* [(tm_var "X", tm_const "Frederick")] *)
Definition example_substitution_two := match (make_atom_substitution example_regular_atom_two example_ground_atom []) with
                                       | Some s => s
                                       | None => []
                                       end.
Fixpoint substitute_term (l1 acc : list tm) (s : substitution) : list tm :=
  match l1 with
  | nil => acc
  | h :: l => let value_lookup := match getValue s h with
                                | Some t => t
                                | None => h
                                end in
              substitute_term l (acc ++ [value_lookup]) s
  end.                          
                     
Fixpoint is_ground (l1 : list tm) : bool :=
  match l1 with
  | nil => true
  | (tm_const _) :: l => is_ground l
  | _ => false
  end.        

Definition substitute_atom (a1 : atom) (s : substitution) : option atom :=
  match a1 with
  | atom_regular sym l1 => Some (
      let substitution_attempt := substitute_term l1 [] s in
        if is_ground substitution_attempt
          then atom_ground sym substitution_attempt
          else atom_regular sym substitution_attempt
      )
  | _ => None    
  end.

Compute substitute_atom example_regular_atom example_substitution.

Compute substitute_atom example_regular_atom_three example_substitution.
(* The Knowledge base is just a list of atoms. *)
Definition KnowledgeBase := list atom.

(* In this function we iterate over the knowledge base
   and, for every atom in it, try to make a substitution
   with some regular atom.

   For instance,

   Let's say that we have this regular atom: ancestor(X, jumala)

   Now, we have a knowledge base like this:

   [ ancestor(adam, jumala), ancestor(eve, adam), ancestor(vanasarvik, jumala) ]

   calling extend_regular_atom will generate the following substitution:

   [ (X, adam), (X, vanasarvik) ]

 *)
Fixpoint substitution_step (kb : KnowledgeBase) (a1 : atom) (acc : list substitution): list substitution :=
  match kb with
  | nil => acc
  | h :: l =>  let augmentation_attempt := make_atom_substitution a1 h [] in
             match augmentation_attempt with
             | Some s => substitution_step l a1 (acc ++ [s])
             | None => substitution_step l a1 acc
             end                           
  end.

Definition example_ground_atom_two := atom_ground "ancestor" [ tm_const "adam" ; tm_const "jumala"].
Definition example_ground_atom_three := atom_ground "ancestor" [ tm_const "eve" ; tm_const "adam"].
Definition example_ground_atom_four := atom_ground "ancestor" [ tm_const "vanasarvik" ; tm_const "jumala"].

Definition example_kb := [ example_ground_atom_two; example_ground_atom_three; example_ground_atom_four ].

Compute substitution_step example_kb (atom_regular "ancestor" [ tm_var "X" ; tm_const "jumala" ]) [].

(* Now that we have a function that generates substitutions, we can finally make use of them.

   The next function uses substitution_step to possibly generate more substitutions.

   This is done by iterating over a list of substitutions, and, for each, attempting to make a fresh atom
   that will have new substitutions derived from it, by running substitution_step against it.

   Building up on the previous example, let us have the following RDF triple as the regular atom:

   T(X, Y, PLlab)

   With substitutions:

   [ (X, student) ],

   [ (X, professor) ],

   With the following kb:

   [ T(student, takesClassesFrom, PLlab), T(professor, worksAt, PLlab)  ]

   The first iteration of eval_atom will:

   1. make a fresh atom with the first substitution, yielding T(student, Y, PLlab)

   2. call substitution_step on it, yielding the substitution [ (Y, takesClassesFrom) ]

   On the second it will do the same, but with worksAt.

   Thus, the final output would be [ [("Y", "takesClassesFrom")] ; [("Y", "worksAt")] ]

 *)
Fixpoint eval_atom (kb : KnowledgeBase) (a1 : atom) (ls acc : list substitution) : list substitution :=
  match ls with
  | nil => acc
  | h :: l => match substitute_atom a1 h with
            (* If the atom is not ground, then there is a substitution  *)
            | Some a => let new_substitution := substitution_step kb a [] in
                       eval_atom kb a1 l (acc ++ new_substitution)
            (* Else, skip this substitution *)
            | None => eval_atom kb a1 l acc
            end                   
  end.         

Definition example_ground_atom_five := atom_ground "T" [ tm_const "student" ; tm_const "takesClassesFrom" ; tm_const "PLlab"].
Definition example_ground_atom_six := atom_ground "T" [ tm_const "professor" ; tm_const "worksAt" ; tm_const "PLlab"].

Definition example_regular_atom_four := atom_regular "T" [ tm_var "X" ; tm_var "Y" ; tm_const "PLlab" ].

Definition example_substitution_three := [ (tm_var "X", tm_const "student") ].
Definition example_substitution_four := [ (tm_var "X", tm_const "professor") ].
Definition example_substitution_list := [ example_substitution_three ; example_substitution_four ].

Definition example_kb_two := [ example_ground_atom_five ; example_ground_atom_six ].

Compute eval_atom example_kb_two example_regular_atom_four example_substitution_list [].

(* A rule has a head and a body. the head is a single non-ground atom, and the body is a list of atoms *)


(* This is the classic datalog example rule. *)
