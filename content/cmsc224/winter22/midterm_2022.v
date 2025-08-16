(** ** Library *)

(* The library is just for use and reference. 
   Scroll down to Midterm Examination for the midterm. *)

(** ** Logic *)

Inductive and (X Y : Prop) : Prop :=
  conj : X -> Y -> and X Y.

Inductive or (X Y : Prop) : Prop :=
 | or_introl : X -> or X Y
 | or_intror : Y -> or X Y.

Arguments conj {X Y}.
Arguments or_introl {X Y}.
Arguments or_intror {X Y}.

Notation "A /\ B" := (and A B). 
Notation "A \/ B" := (or A B).

Definition iff (A B : Prop) := (A -> B) /\ (B -> A).
Notation "A <-> B" := (iff A B) (at level 95).

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

(** ** Unit **)

Inductive unit : Type :=
  | tt.

(** ** Booleans **)

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

Definition eqb (b1 b2 : bool) : bool :=
  if b1
  then if b2 then true else false
  else if b2 then false else true.

Lemma eqb_spec : forall (b b' : bool), reflect (b = b') (eqb b b').
Proof. intros b b'. destruct b, b'; constructor; easy. Qed.

(** ** Numbers **)

(* For convenience, we'll use Coq's nats, recalling their definition 
   here:
Inductive nat : Type :=
  | O
  | S (n : nat).
 *)

Definition pred (n : nat) : nat :=
   match n with
   | O => O
   | S n' => n'
   end.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity).
Notation "x - y" := (minus x y) (at level 50, left associativity).
Notation "x * y" := (mult x y) (at level 40, left associativity).

Fixpoint eqb_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb_nat n' m'
            end
  end.

Notation "x =? y" := (eqb_nat x y) (at level 70).

Fixpoint leb_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb_nat n' m'
            end
  end.

Definition ltb_nat (n m : nat) : bool :=
  leb_nat (S n) m.

Notation "x <=? y" := (leb_nat x y) (at level 70).
Notation "x <? y" := (ltb_nat x y) (at level 70).

Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m : le n m -> le n (S m).

Notation "m <= n" := (le m n).

(** ** Pairs and Sums **)

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

Notation "A * B" := (prod A B) : type_scope.
Notation "( x , y )" := (pair x y).

Inductive sum (A B : Type) : Type :=
  | inl (a : A)
  | inr (b : B). 

Arguments inl {A B}.
Arguments inr {A B}.

Notation "A + B" := (sum A B) : type_scope.

(** ** Lists} **)

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X} _ _.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)  (at level 60, right associativity).

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Fixpoint map {X Y: Type} (f : X -> Y) (l : list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint filter {X : Type} (test : X -> bool) (l : list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

Fixpoint fold {X Y} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** ** Maps **)

(* NOTE: Uses nats, not strings. *)

Definition total_map (A : Type) := nat -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : nat) (v : A) :=
  fun x' => if eqb_nat x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v) (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : nat) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

(** ** Midterm Specific Notations *)

Inductive empty_type : Type := .
Notation "! x" := (x -> empty_type) (at level 100).

Definition fill_in_term {T: Type} : T. Admitted.
Definition fill_in_type {T: Type} : T. Admitted.
Definition fill_in_prop {T: Type} : T. Admitted.





(*********************** 

   CMSC 22400/32400 Winter 2022
   Midterm Examination 

 ************************)


(** ** Question 1 (15 points) *)

(** In functional programming "currying is the technique of converting
a function that takes multiple arguments into a sequence of functions
that each takes a single argument". *)

(* (a) Write a function to curry a function that takes in a pair of
   arguments *)

Definition curry {A B C} (f : A * B -> C) : A -> B -> C := fill_in_term.

(* (b) Fill in the function that goes in the opposite direction. *)

Definition uncurry {A B C} (f : A -> B -> C) : A * B -> C := fill_in_term.

(* (c) What do these functions correspond to logically? 
   Use English and logic symbols. *)


(* (d) State and (e) prove the corresponding theorem (as one theorem). *)



(** ** Question 2 (15 points)} *)

(* In ProofObjects, we talked briefly about _sum types_ and how they
   could be used to express other datatypes. *)

(* (a) Use sum types to create a datatype that is isomorphic
   (equivalent) to [bool] *)

Definition bool' : Type := fill_in_type.

(* (b) Use Coq notations to treat true' and false' as notation for
    your equivalents to [true] and [false]. *)


(* (c) Define [and'], [or'], and [neg'] for [bool'] without using
   match statements (or the proof environment) *)


(* (d) State and prove that [andb'] is commutative *)


(* (e) Prove using [Definition] (without the proof environment) that
   double negation on [bool'] is the identity *)



(** ** Question 3 (20 points) *)

(* The following terms are all ill-typed.  Expand the term or type
   to return a well-typed expression. (DO NOT delete content) *)

(* NOTE: "Clever" solutions that, say, wrap a function around a term
   and throw it out or change [true] to [truedeau] which is defined as
   notation for 42 will receive no credit. *)

Fail Definition q3a := nil.

Fail Definition q3b (b : bool) := if b then true else 4. 

Fail Definition q3c (A B : Type) := A * B. 

Fail Definition q3d := inl 8.

Fail Definition q3e (l : list nat) : list nat := map plus l.

Fail Definition q3f : forall (A : Type), A -> A := fun x => x.

Fail Definition q3g : total_map bool := true.

Fail Definition q3h : partial_map := fun x => Some x.

Fail Definition q3i (A B : Prop) : Prop := A B. 



(** ** Question 4 (20 points) **)

(* For each of the types below, write a Coq expression that has that
   type. If there are no such expressions, show it, using [~] or [!]
   (an equivalent to [~] defined for Types). 

   You should only use the proof environment for proving non-existence.
*)

Definition q4a: True := fill_in_term.

Definition q4b : forall (A B : Type), A -> (A -> B) -> B := fill_in_term.

Definition q4c : forall (A B : Type), option A -> option (A -> B) -> option B :=
  fill_in_term.

Definition q4d : forall (A B : Type), A + B := fill_in_term.

Definition q4e : forall (A B : Type), A -> B -> unit := fill_in_term.

Definition q4f : 9 = 1 + 8 := fill_in_term.

Definition q4g : ex (le 4) := fill_in_term.

Definition q4h : forall A, partial_map A := fill_in_term.

Definition q4i : forall (A : Type), partial_map A -> A := fill_in_term.



(** ** Question 5 (30 points) **)

(* The following questions concern the following tree data
   structure *)

Inductive tree (A : Type) : Type :=
| leaf : A -> tree A
| node : A -> tree A -> tree A -> tree A.

Arguments leaf {A}.
Arguments node {A}.

(* (a) Define a fixpoint [in_tree] that takes in a nat and a
   tree of nats and returns true if the given nat is in the tree. *)

Fixpoint in_tree (n : nat) (t : tree nat) : bool := fill_in_term.

(* (b) Define an inductive proposition [In_Tree] that states
   that a given nat is in a given tree of nats. 

   It should not use the fixpoint above *)

Inductive In_Tree : nat -> tree nat -> Prop := (* FILL IN *). 

(* (c) State as a lemma that your two definitions of In_Tree reflect
   one another.  (You don't have to prove this (use Admitted).) *)


(* (d) Write an proposition that says that a tree is perfectly
   balanced (i.e. the left and right subtrees of any node have the
   same height). You may want to write an intermediate inductive
   definition first. *)

(* Your definition(s) shouldn't involve any fixpoints *)

Definition balanced (A : Type) (t : tree A) : Prop := fill_in_term.

(* (e) Prove one of the following two lemmas correct *)

Lemma in_tree_eq : forall (t1 t2 : tree nat),
    (forall n, In_Tree n t1 <-> In_Tree n t2) ->
    t1 = t2.
Abort.

Lemma in_tree_neq : ~ forall (t1 t2 : tree nat),
    (forall n, In_Tree n t1 <-> In_Tree n t2) ->
    t1 = t2.
Abort.



(** ** BONUS *)

(* If you had any clever solutions to Question 3, please post them
   here. We may award extra credit to particularly clever ones. *)
