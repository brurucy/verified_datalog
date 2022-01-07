Require Import String.
Require Import List.
Require Import Bool.Bool.
Import ListNotations.

Module Datalog.

(* eqb_string and the following three theorems are not my work. *)
Definition eqb_string (x y : string) : bool := if string_dec x y then true else false.

Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
  intros s. unfold eqb_string.
  destruct (string_dec s s) as [Hs_eq | Hs_not_eq].
  - reflexivity.
  - destruct Hs_not_eq. reflexivity.
Qed.

Theorem eqb_string_sym : forall s s' : string,
    eqb_string s s' = eqb_string s' s.
Proof.
  intros.
  unfold eqb_string.
  destruct (string_dec s s').
  destruct (string_dec s' s).
  auto.
  exfalso.
  apply n.
  auto.
  destruct (string_dec s' s).
  exfalso.
  apply n.
  auto.
  auto.
Qed.

Theorem eqb_string_true_iff : forall x y : string,
  eqb_string x y = true <-> x = y.
Proof.
  intros x y.
  unfold eqb_string.
  destruct (string_dec x y) as [Hs_eq | Hs_not_eq].
  - rewrite Hs_eq. split. reflexivity. reflexivity.
  - split.
    + intros contra. discriminate contra.
    + intros H. exfalso. apply Hs_not_eq. apply H.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
  eqb_string x y = false <-> ~(x = y).
Proof.
  intros x y.
  rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false.
  reflexivity.
Qed.

(* Datalog is a decidable subset of prolog, whose core use is to take
   Atoms as an input, and materialize the logical consequences of rules
   applied to them.
 *)

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

Theorem eqb_term_sym : forall t t' : tm,
    eqb_term t t' = eqb_term t' t.
Proof.
  intros.
  induction t, t'; simpl.
  apply eqb_string_sym.
  auto.
  auto.
  apply eqb_string_sym.
Qed.

Lemma var_const_ineq : forall v1 v2 : string,
    eqb_term (tm_var v1) (tm_const v2) = false.
Proof.
  trivial.
Qed.

Lemma const_var_ineq : forall v1 v2 : string,
    eqb_term (tm_const v1) (tm_var v2) = false.
Proof.
  trivial.
Qed.

Compute eqb_term (tm_const "Professor") (tm_var "Professor").
Compute eqb_term (tm_var "Professor") (tm_const "Professor").
Compute eqb_term (tm_const "Professor") (tm_const "Professor").
Compute eqb_term (tm_var "Professor") (tm_var "Professor").
Compute eqb_term (tm_const "X") (tm_const "Y").
Compute eqb_term (tm_var "X") (tm_const "Y").

(* Atoms are just conjunctions of terms with a symbol *)
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

Theorem eqb_term_list_sym : forall t t' :  list tm,
    eqb_term_list t t' = eqb_term_list t' t.
Proof.
  intros.
  generalize dependent t'.
  induction t; intros.
  - destruct t'.
    auto.
    auto.
  - destruct t'.
    auto.
    assert (H1: eqb_term a t0 = eqb_term t0 a).
    apply eqb_term_sym.
    simpl.
    destruct (eqb_term a t0).
    destruct (eqb_term t0 a).
    specialize IHt with t'.
    apply IHt.
    discriminate.
    rewrite H1.
    destruct (eqb_term t0 a).
    discriminate.
    auto.
Qed.

Definition eqb_atom (latom : atom) (ratom : atom) : bool :=
  match latom, ratom with                                       
  | atom_ground sym l1, atom_ground sym' l2  => if eqb_string sym sym' then eqb_term_list l1 l2 else false
  | atom_regular sym l1, atom_regular sym' l2 => if eqb_string sym sym' then eqb_term_list l1 l2 else false
  | _, _ => false                              
  end.

Theorem eqb_atom_sym : forall a a' : atom,
    eqb_atom a a' = eqb_atom a' a.
Proof.
  intros.
  destruct a, a'; simpl.
  - rewrite eqb_term_list_sym.
    rewrite eqb_string_sym.
    auto.
  - auto.
  - auto.
  - rewrite eqb_term_list_sym.
    rewrite eqb_string_sym.
    auto.
Qed.

Lemma regular_ground_ineq : forall (sym1 sym2 : string) (l1 l2 : list tm),
    eqb_atom (atom_ground sym1 l1) (atom_regular sym2 l2) = false.
Proof.
  trivial.
Qed.

Lemma ground_regular_ineq : forall (sym1 sym2 : string) (l1 l2 : list tm),
    eqb_atom (atom_ground sym1 l1) (atom_regular sym2 l2) = false.
Proof.
  trivial.
Qed.

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
  | h :: l, h' :: r => match getValue s h with
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

   calling subsitute_step will generate the following substitutions:

   [ [(X, adam)], [(X, vanasarvik)] ]

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

   Thus, the final output would be [ [("X", "student"), ("Y", "takesClassesFrom")] ; [("X", professor), ("Y", "worksAt")] ]

 *)

Fixpoint eval_atom (kb : KnowledgeBase) (a1 : atom) (ls acc : list substitution) : list substitution :=
  match ls, acc with
  | nil, _ => acc
  | h :: l, _ => match substitute_atom a1 h with
            (* If the atom is not ground, then there is a substitution  *)
            | Some a => let new_substitutions := substitution_step kb a [] in
                       eval_atom kb a1 l (acc ++ (map (fun x => h ++ x) new_substitutions))
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

(* A rule is a clause that has a body, a list of atoms, and a head, a single regular atom.

   ancestor(X, Y), ancestor(Y, Z) -> ancestor(X, Z)

   It reads as "if ancestor(X, Y) and ancestor(Y, Z) are true, then  so does ancestor(X, Z) "

   the left-hand side is called the body, and the right-hand side is the head of the rule.

   This is the last part of datalog syntax.
 *)
Inductive cl : Type :=
  | cl_rule : atom -> list atom -> cl
.

Definition example_rule_body := [atom_regular "ancestor" [ tm_var "X" ; tm_var "Y"] ; atom_regular "ancestor" [ tm_var "Y" ; tm_var "Z"] ].
Definition example_rule_head := atom_regular "ancestor" [ tm_var "X" ; tm_var "Z"].

Definition example_rule := cl_rule example_rule_head example_rule_body.

(*
  In eval_body all we do is walk through the rule's body in order to get all substitutions.

  Given the following list of atoms:

  ancestor(X, Y), ancestor(Y, Z)

  And knowledge base:

  [ (adam, jumala) ; (vanasarvik, jumala) ; (eve, adam) ; (jumala, cthulu) ]

  We should get the following long list of substitutions:

  [ [ (X, adam) ; (X, vanasarvik) ; (X, eve) ; (X, jumala) ; (Y, jumala) ; (Y, adam) ; (Y, cthulu) ] ;
  [ (Y, adam) ; (Y, vanasarvik) ; (Y, eve) ; (Y, jumala) ; (Z, jumala) ; (Z, adam) ; (Z, cthulu) ] ]

 *)
Fixpoint eval_body (kb : KnowledgeBase) (l1 : list atom) (ls : list substitution) : list substitution :=
  match l1 with
  | nil => ls  
  | h :: l => let atom_evaluation := eval_atom kb h ls [] in
                  eval_body kb l atom_evaluation
  end.

Definition example_ground_atom_seven := atom_ground "ancestor" [ tm_const "jumala" ; tm_const "cthulu" ].

Definition example_kb_three := [ example_ground_atom_two ; example_ground_atom_three ; example_ground_atom_four ; example_ground_atom_seven ].

Compute example_kb_three.

Compute eval_body example_kb_three [(atom_regular "ancestor" [ tm_var "X" ; tm_var "Y"]);(atom_regular "ancestor" [ tm_var "Y" ; tm_var "Z"])] [[]].

(*

  Evaluating a rule is quite straightforward.
  
  We will evaluate the body of the rule, and then attempt to use the substitutions to generate new atoms.

  The function substitute_head does nothing special.

  It is the same as substitute_atom, except that instead of returning an option, and acting on a signle substitution
  it takes in a list of substitutions and applies them to a single atom.

  For instance, evaluating the rule ancestor(X, Y), ancestor(Y, Z) -> ancestor(X, Z)
  over the same knowledge base will yield the following substitutions:

  [[(X, adam), (Y, jumala), (Z, cthulu)];
   [(X, eve), (Y, adam), (Z, jumala)];
   [(X, vanasarvik), (Y, jumala), (Z, cthulu)]]

  Which will be substituted against ancestor(X, Z), deriving the following facts:

  [ancestor(adam, cthulu),
   ancestor(eve, jumala),
   ancestor(vanasarvik, cthulu)]

 *)

Fixpoint substitute_head (head : atom) (substitutions: list substitution) ( acc : KnowledgeBase ): KnowledgeBase :=
  match substitutions with
  | nil => acc
  | h :: l => match substitute_atom head h with
            | Some fresh_atom => substitute_head head l (acc ++ [fresh_atom])
            | None => substitute_head head l (acc)
            end
  end.

Definition previous_substitutions := eval_body example_kb_three [atom_regular "ancestor" [ tm_var "X" ; tm_var "Y" ] ; atom_regular "ancestor" [ tm_var "Y" ; tm_var "Z" ]] [[]].

Compute previous_substitutions.

Compute substitute_head example_rule_head previous_substitutions [].

Definition eval_rule (kb : KnowledgeBase) (r : cl) : KnowledgeBase :=
  match r with
  | cl_rule head body =>
      let substitutions := eval_body kb body [[]] in
      (substitute_head head substitutions [])
  end.

(* A datalog rule MUST have all of the terms in its head show up in the body, otherwise eval_rule will not yield only ground atoms!! *)

Fixpoint is_term_in_term_list (l : list tm) (t : tm) : bool :=
  match l with
  | nil => false
  | h :: l' => if eqb_term t h then true else is_term_in_term_list l' t
  end.

Fixpoint is_there_some_true (l : list bool) : bool :=
  match l with
  | nil => false
  | h :: l' => if h then true else is_there_some_true l'
  end.

Fixpoint is_it_all_true (l : list bool) : bool :=
  match l with
  | nil => true
  | h :: l' => if h then is_it_all_true l' else false
  end.

Definition is_datalog_rule (r : cl) : bool :=
  match r with
  | cl_rule (atom_regular _ l) body =>
      let body_check := map (fun term =>
                               map (fun x =>
                                      match x with
                                      | atom_regular sym l | atom_ground sym l => is_term_in_term_list l term
                                      end ) body ) l in
      let head_check := map (fun term_truth_list => is_there_some_true term_truth_list) body_check in
      is_it_all_true head_check
  | cl_rule (atom_ground  _ _) _    => false                                        
  end.

Compute eval_rule example_kb_three (cl_rule (atom_regular "ancestor" [tm_var "X"; tm_var "W"]) example_rule_body).

Compute eval_rule example_kb_three example_rule.

Compute eval_rule (example_kb_three ++ (eval_rule example_kb_three example_rule)) example_rule.

Compute eval_rule (eval_rule (example_kb_three ++ (eval_rule example_kb_three example_rule)) example_rule) example_rule.
  
Fixpoint eqb_kb (kb1 kb2 : KnowledgeBase) : bool :=
  match kb1, kb2 with
  | nil, nil => true
  | h :: l, h' :: l' => if eqb_atom h h' then eqb_kb l l' else false
  | _, _ => false                                                            
  end.

Fixpoint has (kb : KnowledgeBase) (a : atom) : bool :=
  match kb with
  | nil => false
  | h :: l => if eqb_atom h a then true else has l a
  end.

Fixpoint distinct (kb : KnowledgeBase) (acc : KnowledgeBase) : KnowledgeBase :=
  match kb, acc with
  | nil, _ => []
  | h :: l, acc => match has acc h with
                 | true => distinct l acc
                 | false => h :: (distinct l (h :: acc))
                 end
  end.

Fixpoint calculate_minimal_model (kb : KnowledgeBase) (r : cl)
  : KnowledgeBase :=
  let clean_kb := distinct kb [] in
  let evaluation := eval_rule clean_kb r in
  match evaluation with
  | nil => kb
  | _ => calculate_minimal_model (clean_kb ++ evaluation) r
  end.
