(** * ProofObjects: The Curry-Howard Correspondence *)

Require Import LF.IndProp.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality, -local-declaration".
From LF Require Export IndProp.

(** "Algorithms are the computational content of proofs."
    (Robert Harper) *)

(** Let's start off with the most basic philosophical question:
    What is True?  *)

Print True.
(* ==>
  Inductive True : Prop :=  I : True
*)

(** Straightforward enough. 
    What is False? *)
Print False.
(* ==>
  Inductive False : Prop := .
*)

(** We're not missing anything. 
    [False] is simply an inductive type with no constructors. *)

(** Like booleans and natural numbers, [True] and [False] have no special
    status. Let's define our own versions. *)

Inductive True' : Prop := yes.
Inductive False' : Prop := .

(** We can think of Coq Propositions as simply Types where we only care 
    _whether_ there is a term of of that type, not what that term is. 

    Hence, we can equally well define as True as follows: *)

Inductive True'' :=
| of_course
| naturally.

(** Traditionally, if we want to show that True'' is true, we state it as a 
    lemma: *)

Lemma True''_is_True : True''.
Proof. apply naturally. Qed.

(** But we could also 'prove' it directly by exhibiting a term of type
    True'' *)

Definition True''_is_True' : True'' := naturally.

(** This is actually what [apply naturally] produces! *)

Print True''_is_True.
Print True''_is_True'.

(* ################################################################# *)
(** * Arrows, Functions and Implication *)

Module functions.

(** So far, we've portrayed Coq's arrow notation [->] as 
    having two distinct meanings: *)

Variable f : nat -> bool.

(** declares f as a function from [nat] to [bool] while *)

Axiom P : False -> True.

(** states the axiom P that False implies True. *)

(** But in practice, these are the same. *)

(** Here are the direct proofs of two basic theorems about True and
    False *)

Definition then_True : forall A, A -> True := fun _ _ => I.

Definition if_False : forall A, False -> A :=
  fun _ F =>
    match F with
    end.

(** Compare... *)

Lemma ex_falso_quodlibet : forall A, False -> A.
Proof. intros ? F. destruct F. Qed.

Print ex_falso_quodlibet.

(** Note that the following are the same:

           forall (x:nat), nat
        =  forall (_:nat), nat
        =  nat          -> nat
*)

(* QUIZ

    What is the type of this expression?

  fun (A : Prop) (P : A) => P

  (1) [P -> P]

  (2) [forall A, A]

  (3) [forall A, A -> A]

  (4) [A -> A -> A]

  (5) Not typeable

*)

(** What does this correspond to computationally? *)

(** You're probably familiar with these basic rules of logic, but we
    can easily express them as definitions: *)

Definition modus_ponens {X Y : Prop} : (X -> Y) -> X -> Y :=
  fun f x => f x.

Definition chain_rule {X Y Z : Prop}  : (X -> Y) -> (Y -> Z) -> (X -> Z) :=
  fun fxy fyz x => fyz (fxy x).

(** Note that the chain rule is simply function composition. *)

End functions.

(* ################################################################# *)
(** * Logical Connectives as Inductive Types *)

(* ================================================================= *)
(** ** Conjunction *)

(** To prove that [P /\ Q] holds, we must present evidence for both
    [P] and [Q].  Thus, it makes sense to define a proof object for [P
    /\ Q] as consisting of a pair of two proofs: one for [P] and
    another one for [Q]. This leads to the following definition. *)

Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

(** Notice the similarity with the definition of the [prod] type,
    given in chapter [Poly]; the only difference is that [prod] takes
    [Type] arguments, whereas [and] takes [Prop] arguments. *)

Print and.
Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)

(** This similarity should clarify why [destruct] can be used on a
    conjunctive hypothesis.  Case analysis allows us to consider all
    possible ways in which [P /\ Q] was proved -- here just one (the
    [conj] constructor). *)

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.

(** Similarly, the [split] tactic actually works for any inductively
    defined proposition with exactly one constructor.  In particular,
    it works for [and]: *)

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros pq. destruct pq as [p q]. split.
    + apply q.
    + apply p.
  - intros qp. destruct qp as [q p]. split.
    + apply p.
    + apply q.
Qed.

End And.

(** This shows why the inductive definition of [and] can be
    manipulated by tactics as we've been doing.  We can also use it to
    build proofs directly, using pattern-matching.  For instance: *)

Definition and_comm'_aux P Q (pq : P /\ Q) : Q /\ P :=
  match pq with
  | conj p q => conj q p
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(* QUIZ

    What is the type of this expression?

        fun P Q R (pq: and P Q) (qr: and Q R) =>
          match (pq,qr) with
          | (conj p _, conj  _ r) => conj p r
          end.

  (1) [forall P Q R, P /\ Q -> Q /\ R -> P /\ R]

  (2) [forall P Q R, Q /\ P -> R /\ Q -> P /\ R]

  (3) [forall P Q R, P /\ R]

  (4) [forall P Q R, P \/ Q -> Q \/ R -> P \/ R]

  (5) Not typeable

*)

(* ================================================================= *)
(** ** Disjunction *)

Module Or.

(** The inductive definition of disjunction uses two constructors, one
    for each side of the disjunct. This corresponds to a sum type in 
    functional programming. *)

Inductive sum (A B : Type) : Type :=
| inl : A -> sum A B
| inr : B -> sum A B.
Arguments inl {A B}.
Arguments inr {A B}.
Notation "P + Q" := (sum P Q) : type_scope.

(** A quick example of a sum type in functional programming: *)

Fixpoint remove_bools (l : list (nat + bool)) : list nat
(* WORK IN CLASS *). Admitted.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

Arguments or_introl [P Q].
Arguments or_intror [P Q].

Notation "P \/ Q" := (or P Q) : type_scope.

(** This declaration explains the behavior of the [destruct] tactic on
    a disjunctive hypothesis, since the generated subgoals match the
    shape of the [or_introl] and [or_intror] constructors. *)

(** Once again, we can also directly write proof objects for theorems
    involving [or], without resorting to tactics. *)

Definition or_false_r : forall P, P \/ False -> P
  (* WORK IN CLASS *). Admitted.

Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R poq pr qr  =>
    match poq  with
    | or_introl p => pr p
    | or_intror q => qr q
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R poq pr qr.
  destruct poq as [p | q].
  - apply pr. apply p.
  - apply qr. apply q.
Qed.

End Or.

(* QUIZ

    What is the type of this expression?

    fun P Q (poq : P \/ Q) =>
      match poq with
      | or_introl p => or_intror p
      | or_intror q => or_introl q
      end.

  (1) [forall P Q H, Q \/ P \/ H]

  (2) [forall P Q, P \/ Q -> P \/ Q]

  (3) [forall P Q H, P \/ Q -> Q \/ P -> H]

  (4) [forall P Q, P \/ Q -> Q \/ P]

  (5) Not typeable

*)

(* ################################################################# *)
(** * Predicate Calculus and Dependent Types *)
    
(** So far, the logic we've expressed has been the simplest form of
    logic: Propositional Logic. In fact, we could write the proofs
    above in a simple polymorphic language like OCaml. 

    To state more complicated propositions we will need _dependent types_.
    Consider the following inductive relations: *)

Inductive beautiful : nat -> Prop :=
| b2 : beautiful 2
| b4 : beautiful 4
| b8 : beautiful 8.

Inductive wonderous : nat -> Prop :=
| w8 : wonderous 8.

(** [beautiful] itself is not a proposition (or type), [beautiful 2]
    and [beautiful 3] are. That is, Coq allows our Props (and our
    types) to depend on _terms_. This allows us to state, and attempt
    to prove, the following: *)

Definition beautiful2 : beautiful 2 := b2.
Fail Definition beautiful2 : beautiful 3 := b4.

(** In the second case we can state that three is beautiful, but we
    can't prove it. We can also try something more complex: *)

Definition wonderous_then_beautiful : forall n, wonderous n -> beautiful n :=
  fun n w => match w with
               w8 => b8
             end.

(** Note that the typechecker recognizes that in the only case of the match, 
    n is 8. *)

Print wonderous_then_beautiful.
(* ==>
  fun (n : nat) (w : wonderous n) =>
  match w in (wonderous n0) return (beautiful n0) with
  | w8 => b8
  end
 *)

(** Most of the propositions we have looked at in this course use dependent 
    types. Let's try to directly prove something about [ev]: *)

Print ev.
(* ==>
Inductive ev : nat -> Prop :=
| ev_0 : ev 0 
| ev_SS : forall n : nat, ev n -> ev (S (S n))
*)

Definition ev_plus_four : forall n, ev n -> ev (4 + n) 
  (* WORK IN CLASS *). Admitted.

(* ================================================================= *)
(** ** Existential Quantification *)

(** To give evidence for an existential quantifier, we package a
    witness [x] together with a proof that [x] satisfies the property
    [P]: *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

(** In English, for any predicate [P], given an [x] and a term/proof
    of [P x], we can construct a term/proof of [ex P]. *)

(** Let's show that there is an x satisfying [ev]: *)

Definition something_is_even : ex ev := ex_intro ev 0 ev_0.

End Ex.

(** The more familiar form [exists x, P x] desugars to an expression
    involving [ex]: *)

Check ex (fun n => ev n) : Prop.

(* ################################################################# *)
(** * Equality *)

Module MyEquality.

(** Even Coq's equality relation is not built in.  It has the
    following inductive definition. *)

Inductive eq {A : Type} : A -> A -> Prop :=
  | eq_refl : forall {a : A}, eq a a.

Notation "x == y" := (eq x y) (at level 70): type_scope.

(** Of course, there are other, arguably more useful ways to define
    equality.  Here's Leibniz's definition (and, as far as we know, not
    Newton's): *)

Definition eqL {A : Type} (a b : A) : Prop := forall (P : A -> Prop), P a -> P b.  

Notation "x =L y" := (eqL x y) (at level 70): type_scope.

(** That is, 'a' is equal to 'b' if everything true of 'a' is true of
    'b'. *) 

(** Let's show that eqL is at least as strong as eq. *)

Lemma eqL_then_eq : forall (A : Type) (a b : A), a =L b -> a == b.
Proof.
  (* WORK IN CLASS *) Admitted.

(** This is actually easier to express definitionally, if harder to
    come up with. *)

Definition eqL_then_eq' (A : Type) (a b : A) (PLe : a =L b) : a == b :=
  PLe (fun x => a == x) eq_refl.

Print eqL_then_eq.

(** Let's try going in the opposite direction. *)

Lemma eq_then_eqL : forall (A : Type) (a b : A), a == b -> a =L b.
Proof.
  intros A a b H.
  unfold eqL.
  intros P p.
  destruct H.
  apply p.
Qed.

Definition eq_then_eqL' : forall (A : Type) (a b : A), a == b -> a =L b
  (* WORK IN CLASS *). Admitted.

Print eq_then_eqL.

(** For convenience, we can package these up into a single claim. *)

Definition eq_eqL (A : Type) (a b : A) : a == b <-> a =L b :=
  conj (eq_then_eqL A a b) (eqL_then_eq A a b).

(** What does this tell us? It says that it's okay to replace a with b
    throughout a proposition if we know that [eq a b]. Let's try it
    out. *)

Lemma eq_2_beautiful : forall (x : nat), 2 == x -> beautiful x.
Proof.
  (* WORK IN CLASS *) Admitted.

End MyEquality.

(* ################################################################# *)
(** * Interlude: Dependent Types and Programming in the Proof Environment *)

(** What else can we do with dependent types? *)

Inductive ilist (X : Type) : nat -> Type :=
| inil : ilist X 0
| icons (n : nat) (x : X) (l : ilist X n) : ilist X (S n).

Arguments inil {X}.
Arguments icons {X n}.

Notation "x ::: l" := (icons x l)
                      (at level 60, right associativity).
Notation "[[ ]]" := inil.
Notation "[[ x ; .. ; y ]]" := (icons x .. (icons y inil) ..).

Definition ihd {X n} (l : ilist X (S n)) : X :=
  match l with
  | x ::: l => x
  end.

(** Unfortunately, Coq isn't great at recognizing impossible cases: *)

Fail Fixpoint izip {X Y n} (l1 : ilist X n) (l2 : ilist Y n) : ilist (X * Y) n :=
  match l1 with
  | [[]]        => [[]]
  | x ::: l1'   => match l2 with
                  | [[]]      => [[]]
                  | y ::: l2' => (x,y) ::: (izip l1 l2)
                  end
  end.

(** This is where the proof assistant comes in handy. *)

Fixpoint izip {X Y n} (l1 : ilist X n) (l2 : ilist Y n) : ilist (X * Y) n.
  destruct l1.
  - apply inil.
  - inversion l2; subst.
    apply icons.
    apply (x,x0).
    apply izip; assumption.
Defined.

(** Note that we ended our definition with [Defined]. 
    [Qed] makes a definition _opaque_, meaning that we can't read it off.
    This is fine for proofs, but not very desirable for functions that
    we intend to run. *)

Print izip.      

(* ================================================================= *)
(** ** Refine: Mixing the Program and Proof Environments *)

Fixpoint logicmap {X Y Z} (l1 : list X) (l2 : list (X -> Y + Z)) (l3 : list (X * Y -> Z)) : list Z.
  refine( match l1, l2, l3 with
          | [], _, _ => []
          | _, [], _ => []
          | _, _, [] => []
          | x :: l1', f :: l2', g :: l3' => _ :: logicmap X Y Z l1' l2' l3'
          end); tauto.
Defined.

(* ################################################################# *)
(** * Coq's Trusted Computing Base *)

(** The Coq typechecker is what actually checks our proofs.  We
    have to trust it, but it's relatively small and
    straightforward. *)

(** It prevents this broken proof: *)

Fail Definition or_bogus : forall P Q, P \/ Q -> P :=
  fun (P Q : Prop) (pq : P \/ Q) =>
    match pq with
    | or_introl p => p
    end.

(** And this one: *)

Fail Fixpoint infinite_loop {X : Type} (n : nat) {struct n} : X :=
  infinite_loop n.

Fail Definition falso : False := infinite_loop 0.

(** User-written tactics could produce invalid proof objects.
    [Qed] runs the type checker to detect that. *)
