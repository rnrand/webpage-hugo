(* ###################################################################### *)
(** * Arithmetic Proofs *)

(** (We use [admit] and [Admitted] to hide solutions from exercises.) *)

Axiom admit : forall {T}, T.

Module Nat.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Check (S (S O)).

Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity).

Notation "x * y" := (mult x y) (at level 40, left associativity).


(** Exercise: Define exponentiation *)

Fixpoint exp (n m : nat) : nat :=
(* FILL IN HERE *) admit.

Notation "x ^ y" := (exp x y) (at level 30, right associativity).

(* Let's show that O is a left and right identity for addition. *)

Lemma plus_0_l: forall n : nat, O + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

(** **** Exercise: 1 star (plus_O_r)  *)
Lemma plus_O_r: forall n : nat, n + O = n.
Proof.
(* FILL IN HERE *) Admitted.


(** **** Exercise: 1 star (n_plus_S_m)  *)
Theorem n_plus_S_m: forall n m, n + S m = S (n + m). 
Proof.
(* FILL IN HERE *) Admitted.

Theorem plus_assoc: forall m n o, m + (n + o) = (m + n) + o.
Proof.
  intros m n o.
  induction m as [| m' IH]. (* m is the right choice here, since [plus] is defined
                               by recursion on the first argument. *)
  + simpl.
    reflexivity.
  + simpl.
    rewrite IH.
    reflexivity.
Qed.

(** **** Exercise: 2 stars (plus_comm)  *)
(* Show that plus is commutative. *)

Theorem plus_comm: forall n m, n + m = m + n.
Proof.
(* FILL IN HERE *) Admitted.

(** Additional exercises: Show that mult has an identity 
    [S O], a annihilator [O] and associative, commutative and
    distributive properties. *)

(** The next function tests whether a number [m] is equal to [n]. *)

Fixpoint beq_nat (m n : nat) : bool :=
  match m, n with
  | O, O => true
  | S m', S n' => beq_nat m' n'
  | _, _ => false
  end.

Lemma beq_nat_refl : forall n, beq_nat n n = true.
Proof.
  intros n.
  induction n as [|n IH].
  - reflexivity.
  - simpl. apply IH.
Qed.

(** **** Exercise: 2 stars (beq_nat_true).  *)
(* Show the reverse direction. Remember to ensure a sufficiently general 
   induction hypothesis *)
Lemma beq_nat_true :
  forall m n, beq_nat m n = true -> m = n.
Proof.
(* FILL IN HERE *) Admitted.


Definition pred (n : nat) :=
  match n with
  | O => O
  | S n => n
  end.


Fixpoint minus (m n : nat) : nat :=
  match m, n with
  | O, _ => m
  | _, O => m
  | S m', S n' => minus m' n'
  end.

Notation "x - y" := (minus x y) (at level 50, left associativity).

(** The next function tests whether a number [m] is less than or equal
    to [n]. *)

Fixpoint ble_nat (m n : nat) : bool :=
  match m, n with
  | O, _ => true
  | _, O => false
  | S n', S m' => ble_nat n' m'
  end.

(* Exercises: Show that ble_nat is reflexive, transitive and antisymmetric. *)

(** The simple definition of div fails due to Coq's termination checker, 
    so we go with the more complicated one below. *)

Fail Fixpoint div (m n: nat) : nat :=
  match n with
  | O => O
  | S n' => if ble_nat n m then S (div (m - n) n) else O
  end.

Fixpoint div (m n: nat) : nat :=
  match n with
  | O => O
  | S n' => match m with
            | O => O
            | S m' => S (div (S m' - S n') (S n'))
            end
  end.

(** Here, Coq is able to figure out that [S m' - S n'] is a valid
    recursive argument because [minus] only returns results that are
    syntatic sub-terms of [m]. Unfortunately, this criterion is pretty
    fragile: replacing [m] by [O] or [S m'] in the above definition of
    [minus] causes this definition of [div] to break; try it!.

    This kind of rewriting doesn't always work, alas. We can make Coq
    accept less obvious recursive definitions by providing an
    explicit, separate proof that they always terminate, or by
    supplying an extra argument that gives an upper bound on how many
    recursive calls can be performed. We won't cover this feature here
    but you can find more about recursive definitions in Coq on the Internet. *)

Notation "x / y" := (div x y) (at level 40, left associativity).


(** **** Exercise: 2 stars (n_div_n)  *)
(* Show that n / n = 1, for all n > 0. 
   You will need a lemma. *)

(* FILL IN HERE *)
    
Lemma n_div_n: forall n, ble_nat (S O) n = true -> n / n = (S O).
Proof.
(* FILL IN HERE *) Admitted.

(** **** Exercise: 2 stars (factorial).  *)
(* The simplest version of factorial also fails. 
   Try to write a strictly decreasing factorial function. *)
Fixpoint factorial (n : nat) : nat :=
(* FILL IN HERE *) admit.
    
(** Well done! 
    We know that 2^n <= fact(n) <= n^n for all n>0. 
    For a challenge, try to prove both. *)

End Nat.


(** As mentioned previously, [nat] is already defined in Coq's
    standard library. Coq provides special, arabic-numeral syntax for
    [nat], which is translated in terms of the [O] and [S]
    constructors. For instance, [3] is just special syntax for [S (S
    (S O))]. Similarly: *)

Compute (S (S O)).
Compute (S (S O) + S O).

(* Additionally nat has 'less than' and 'greater than' defined as Props in 
   addition to bool, using the standard syntax [x < y]. Check out the Coq 
   standard library for more. *)