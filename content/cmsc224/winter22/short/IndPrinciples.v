(** * IndPrinciples: Induction Principles *)

(** With the Curry-Howard correspondence and its realization in Coq in
    mind, we can now take a deeper look at induction principles. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export ProofObjects.

(* ################################################################# *)
(** * Proof by Recursion *)

(** In the previous chapter we saw most of our favorite tactics 
    explained as simple programs: 
    
    - destruct is just case analysis (match)
    - apply is function application
    - rewrite is an application of eq_eqL 
    - split, left, right, and reflexivity are just applying constructors

    But what about induction?
    
*)

(** Let's start by writing out a suitable inductive predicate.
    A nice option is the Coq standard library's definition of even and odd. *)

Inductive even : nat -> Prop :=
| eO : even 0
| eS : forall n, odd n -> even (S n)

with odd : nat -> Prop :=
| oS : forall n, even n -> odd (S n).

(** We just wrote a "mutually inductive" definition.  In short, it
    says that [O] is [Even], the successor of an [Odd] number is
    [Even] and then successor of an [Even] number is [Odd]. *)

(** Here's the lemma we'd like to prove. *)

Lemma even_or_odd : forall (n : nat), even n \/ odd n.
Abort.

(** The proof of even_or_odd is actually quite easy to program! *)

Fixpoint even_or_odd (n : nat) : even n \/ odd n 
  (* WORK IN CLASS *). Admitted.

(** Unfortunately, writing entire proofs in the programming language
    can be quite hard. Fortunately, there is a simple program that 
    makes these proofs easy. *)

Check nat_ind.

(** nat_ind takes four arguments:

    1) A proposition P over natural numbers
    2) A proof of P  
    3) A proof that P m -> P (S m). 
    4) An arbitrary n

    and it constructs a recursive proof that P n.

    Let's try to prove nat_ind ourselves.

 *)

Fixpoint nat_ind (P : nat -> Prop)
                 (p0 : P 0)
                 (pS : forall m, P m -> P (S m))
                 (n : nat)
                 {struct n}
                 : P n
  (* WORK IN CLASS *). Admitted.

(** We can now use nat_ind to prove even_or_odd in the proof environment *)

Lemma even_or_odd' (n : nat) : even n \/ odd n.
Proof.
  apply nat_ind with (n := n).
  - apply or_introl.
    apply eO.
  - intros n' IHn.
    destruct IHn as [He | Ho].
    + apply or_intror. apply oS. apply He.
    + apply or_introl. apply eS. apply Ho.
Defined.

(* ################################################################# *)
(** * Induction in Depth *)

(** The automatically generated _induction principle_ for [list]: *)

Check list_ind.
(*  ===> list_ind
     : forall (X : Type) (P : list X -> Prop),
       P [ ] ->
       (forall (x : X) (l : list X), P l -> P (x :: l)) -> 
       forall l : list X, P l *)

(** We can directly use the induction principle with [apply]: *)

Theorem app_0_r' : forall {X : Type} (l : list X),
  l ++ [] = l.
Proof.
  intros X.
  apply list_ind.
  - (* l = [] *) reflexivity.
  - (* l = x :: l' *) simpl. intros x l' IH. rewrite -> IH.
    reflexivity.  Qed.

(** Why the [induction] tactic is nicer than [apply]:
     - [apply] requires extra manual bookkeeping (the [intros] in the
       inductive case)
     - [apply] requires [l] to be left universally quantified or explicitly named 
       using [with (l := _)]
     - [apply] requires us to manually specify the name of the induction
       principle. *)

(** Coq generates induction principles for every datatype defined with
    [Inductive], including those that aren't recursive. *)

(** If we define type [t] with constructors [c1] ... [cn],
    Coq generates:

    t_ind : forall P : t -> Prop,
              ... case for c1 ... ->
              ... case for c2 ... -> ...
              ... case for cn ... ->
              forall n : t, P n

    The specific shape of each case depends on the arguments to the
    corresponding constructor. *)

(** An example with no constructor arguments: *)

Inductive time : Type :=
  | day
  | night.

Check time_ind :
  forall P : time -> Prop,
    P day ->
    P night ->
    forall t : time, P t.

(** In general, the automatically generated induction principle for
    inductive type [t] is formed as follows:

    - Each constructor [c] generates one case of the principle.
    - If [c] takes no arguments, that case is:

      "P holds of c"

    - If [c] takes arguments [x1:a1] ... [xn:an], that case is:

      "For all x1:a1 ... xn:an,
          if [P] holds of each of the arguments of type [t],
          then [P] holds of [c x1 ... xn]"

      But that oversimplifies a little.  An assumption about [P]
      holding of an argument [x] of type [t] actually occurs
      immediately after the quantification of [x].
*)

(** For example, suppose we had written the definition of [natlist] a little
    differently: *)

Inductive natlist' : Type :=
  | nnil'
  | nsnoc (l : natlist') (n : nat).

(** Now the induction principle case for [nsnoc1] is a bit different
    than the earlier case for [ncons]: *)

Check natlist'_ind :
  forall P : natlist' -> Prop,
    P nnil' ->
    (forall l : natlist', P l -> forall n : nat, P (nsnoc l n)) ->
    forall n : natlist', P n.

(* ################################################################# *)
(** * Induction Principles in [Prop] *)

(** From what we've said so far, you might expect the
    inductive definition of [ev]...

      Inductive ev : nat -> Prop :=
      | ev_0 : even 0
      | ev_SS : forall n : nat, even n -> even (S (S n)).

    ...to give rise to an induction principle that looks like this...

    ev_ind_max : forall P : (forall n : nat, even n -> Prop),
         P O ev_0 ->
         (forall (m : nat) (E : ev m),
            P m E ->
            P (S (S m)) (ev_SS m E)) ->
         forall (n : nat) (E : ev n),
         P n E
*)

(** The induction priniciples Coq also automatically produces
   for inductively defined properties differ a little bit
   from the induction principles for data types. They are slightly
   less general than you might expect, but consequently easier to use: *)

Print ev.

(* ===>

  Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)))

*)

Check ev_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, ev n -> P n -> P (S (S n))) ->
    forall n : nat, ev n -> P n.

(** In English, [ev_ind] says: Suppose [P] is a property of natural
    numbers.  To show that [P n] holds whenever [n] is even, it suffices
    to show:

      - [P] holds for [0],

      - for any [n], if [n] is even and [P] holds for [n], then [P]
        holds for [S (S n)]. *)

(* ################################################################# *)
(** * Strengthening Induction Principles *)

(** Sometimes the default kind of induction that Coq gives you
    isn't sufficient for a given task. Let's try to prove a 
    simple theorem about our definition of [even] from the 
    beginning of this chapter. *)

(* Try #1 *)

Lemma even_divides_two_try1 : forall n, even n -> exists m, n = m * 2.
Proof.
  (* WORK IN CLASS *) Admitted.

(** We're going to need a better induction principle. *)

Fixpoint even_ind' 
         (P : nat -> Prop)
         (p0 : P 0)
         (pSS : forall m, even m -> P m -> P (S (S m)))
         (n : nat)
         (e : even n)
         {struct e}
  : P n.
  refine (match e with
          | eO => p0
          | eS n' po => match po with
                       | oS n'' e' => _
                       end
          end).
  apply pSS.
  apply e'.
  apply even_ind'; auto.
Defined.

Lemma even_divides_two : forall n, even n -> exists m, n = m * 2.
Proof.
(* WORK IN CLASS *) Admitted.

(** Let's look at a more interesting example: an arbitrarily branching tree: *)

Require Import List.
Import ListNotations.

Inductive Tree :=
| Leaf : nat -> Tree
| Node : list Tree -> Tree.

Check Tree_ind.
(*
Tree_ind
     : forall P : Tree -> Prop,
       (forall n : nat, P (Leaf n)) -> 
       (forall l : list Tree, P (Node l)) -> 
     forall t : Tree, P t
 *)

(** Let's see if we can use this to prove the correctness of a tree
    mapping function: *)

Fixpoint map_Tree (f : nat -> nat) (t : Tree) {struct t} : Tree :=
  match t with
  | Leaf n => Leaf (f n)
  | Node l => Node (map (map_Tree f) l)
  end.

Inductive In_Tree : nat -> Tree -> Prop :=
| In_Tree_Leaf : forall n, In_Tree n (Leaf n)
| In_Tree_Node : forall n t l, In_Tree n t -> In t l -> In_Tree n (Node l).

Theorem map_correct :
  forall t m f, In_Tree m t -> In_Tree (f m) (map_Tree f t).
Proof.
  intros t.
  induction t.
  - intros m f HIn. simpl.
    inversion HIn; subst.
    constructor.
  - intros m f HIn. simpl.
    inversion HIn; subst.
    (* Now what? *)
Abort.

Fixpoint Tree_ind'
         (P : Tree -> Prop)
         (f : forall n, P (Leaf n))
         (g : forall l, (forall x, In x l -> P x) -> P (Node l))
         (t : Tree)
         {struct t} : P t.
  refine (match t with
          | Leaf n => f n
          | Node l => g l _
          end).
  induction l.
  + intros t' H; inversion H. 
  + intros t' H.
    destruct H.
    rewrite <- H.
    apply Tree_ind'; auto.
    apply IHl; auto.
Defined.    

Theorem map_correct :
  forall t m f, In_Tree m t -> In_Tree (f m) (map_Tree f t).
Proof.
  intros t.
  induction t using Tree_ind'.
  - intros m f HIn. simpl.
    inversion HIn; subst.
    constructor.
  - intros m f HIn. simpl.
    inversion HIn; subst.
    econstructor.
    + apply H; eauto.
    + apply in_map.
      assumption.
Qed.    

