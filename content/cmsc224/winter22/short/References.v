(** * References: Typing Mutable References *)

(** Most real languages include _impure_
    features ("computational effects")...
       - mutable pointer structures
       - non-local control constructs (exceptions, continuations, etc.)
       - process synchronization and communication
       - etc.

    Goal for this chapter: formalize pointers. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From LF Require Import Maps.
From LF Require Import Smallstep.
From Coq Require Import Lists.List.
Import Nat.

(* ################################################################# *)
(** * Definitions *)

(** In most real-world programming languages, the mechanisms of
    _name binding_ and _storage allocation_ are (intentionally)
    confused: every name refers to a mutable piece of storage.

    Conceptually, it's cleaner to separate the two:
       - use the mechanisms we already have for name binding
         (abstraction, let);
       - introduce new, explicit operations for allocating, changing,
         and looking up the contents of references (pointers). *)

(* ################################################################# *)
(** * Syntax *)

Module STLCRef.

(** The basic operations on references are _allocation_,
    _dereferencing_, and _assignment_.

       - To allocate a reference, we use the [ref] operator, providing
         an initial value for the new cell.

         For example, [ref 5] creates a new cell containing the value
         [5], and reduces to a reference to that cell.

       - To read the current value of this cell, we use the
         dereferencing operator [!].

         For example, [!(ref 5)] reduces to [5].

       - To change the value stored in a cell, we use the assignment
         operator.

         If [r] is a reference, [r := 7] will store the value [7] in
         the cell referenced by [r]. *)

(* ----------------------------------------------------------------- *)
(** *** Types *)

(** If [T] is a type, then [Ref T] is the type of references to
    cells holding values of type [T].

      T ::= Nat
          | Unit
          | T -> T
          | Ref T
*)

Inductive ty : Type :=
  | Ty_Nat   : ty
  | Ty_Unit  : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Ref   : ty -> ty.

(* ----------------------------------------------------------------- *)
(** *** Terms *)

(** Besides variables, abstractions, applications,
    natural-number-related terms, and [unit], we need four more sorts
    of terms in order to handle mutable references:

      t ::= ...              Terms
          | ref t              allocation
          | !t                 dereference
          | t := t             assignment
          | l                  location
*)

Inductive tm  : Type :=
  (* STLC with numbers: *)
  | tm_var    : string -> tm
  | tm_app    : tm -> tm -> tm
  | tm_abs    : string -> ty -> tm -> tm
  | tm_const  : nat -> tm
  | tm_succ    : tm -> tm
  | tm_pred    : tm -> tm
  | tm_mult    : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
  (* New terms: *)
  | tm_unit   : tm
  | tm_ref    : tm -> tm
  | tm_deref  : tm -> tm
  | tm_assign : tm -> tm -> tm
  | tm_loc    : nat -> tm.

Declare Custom Entry stlc.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom stlc at level 0, x constr).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

Notation "'Nat'" := Ty_Nat (in custom stlc at level 0).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "'pred' x" := (tm_pred x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Coercion tm_const : nat >-> tm.

Notation "'Ref' t" :=
  (Ty_Ref t) (in custom stlc at level 4).
Notation "'loc' x" := (tm_loc x) (in custom stlc at level 2).
Notation "'ref' x" := (tm_ref x) (in custom stlc at level 2).
Notation "'!' x " := (tm_deref x) (in custom stlc at level 2).
Notation " e1 ':=' e2 " := (tm_assign e1 e2) (in custom stlc at level 21).


(* ----------------------------------------------------------------- *)
(** *** Typing (Preview) *)

(** Informally, the typing rules for allocation, dereferencing, and
    assignment will look like this:

                           Gamma |- t1 : T1
                       ------------------------                       (T_Ref)
                       Gamma |- ref t1 : Ref T1

                        Gamma |- t1 : Ref T1
                        --------------------                        (T_Deref)
                          Gamma |- !t1 : T1

                        Gamma |- t1 : Ref T2
                          Gamma |- t2 : T2
                       ------------------------                    (T_Assign)
                       Gamma |- t1 := t2 : Unit

    The rule for locations will require a bit more machinery, and this
    will motivate some changes to the other rules; we'll come back to
    this later. *)

(* ----------------------------------------------------------------- *)
(** *** Values and Substitution *)

(** Besides abstractions, numbers, and the unit value, we have one new
    type of value: locations.  *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_nat : forall n : nat ,
      value <{ n }>
  | v_unit :
      value <{ unit }>
  | v_loc : forall l,
      value <{ loc l }>.

Hint Constructors value : core.

(** Extending substitution to handle the new syntax of terms is
    straightforward: substituting in a pointer leaves it
    unchanged.  *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  (* numbers *)
  | tm_const _ =>
      t
  | <{succ t1}> =>
      <{succ [x := s] t1}>
  | <{pred t1}> =>
      <{pred [x := s] t1}>
  | <{t1 * t2}> =>
      <{ ([x := s] t1) * ([x := s] t2)}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}>
  (* unit *)
  | <{ unit }> =>
    <{ unit }>
  (* references *)
  | <{ ref t1 }> =>
      <{ ref ([x:=s] t1) }>
  | <{ !t1 }> =>
      <{ !([x:=s] t1) }>
  | <{ t1 := t2 }> =>
    <{ ([x:=s] t1) := ([x:=s] t2) }>
  | <{ loc _ }> =>
      t
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ################################################################# *)
(** * Pragmatics *)

(* ================================================================= *)
(** ** Side Effects and Sequencing *)

(** We can write (for example)

       r:=succ(!r); !r

   as an abbreviation for

       (\x:Unit. !r) (r := succ(!r)).
*)

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Definition tseq t1 t2 :=
  <{ (\ x : Unit, t2)  t1 }>.

Notation "t1 ; t2" := (tseq t1 t2) (in custom stlc at level 3).

(* ================================================================= *)
(** ** References and Aliasing *)

(** It is important to bear in mind the difference between the
    _reference_ that is bound to some variable [r] and the _cell_
    in the store that is pointed to by this reference.

    If we make a copy of [r], for example by binding its value to
    another variable [s], what gets copied is only the _reference_,
    not the contents of the cell itself.

    For example, after reducing

      let r = ref 5 in
      let s = r in
      s := 82;
      (!r)+1

    the cell referenced by [r] will contain the value [82], while the
    result of the whole expression will be [83].  The references [r]
    and [s] are said to be _aliases_ for the same cell. *)

(** The possibility of aliasing can make programs with references
    quite tricky to reason about.  For example, the expression

      r := 5; r := !s

    assigns [5] to [r] and then immediately overwrites it with [s]'s
    current value; this has exactly the same effect as the single
    assignment

      r := !s

    _unless_ we happen to do it in a context where [r] and [s] are
    aliases for the same cell!

      let r = ref 0 in
      let s = r in
      r := 5; r := !s
*)

(* ================================================================= *)
(** ** Shared State *)

(** Of course, aliasing is also a large part of what makes references
    useful.  In particular, it allows us to set up "implicit
    communication channels" -- shared state -- between different parts
    of a program.  For example, suppose we define a reference cell and
    two functions that manipulate its contents:

      let c = ref 0 in
      let incc = \_:Unit. (c := succ (!c); !c) in
      let decc = \_:Unit. (c := pred (!c); !c) in
      ...
*)

(** The [Unit]-abstractions ("thunks") are used here to prevent
    reduction until later. *)

(* ================================================================= *)
(** ** Objects *)

(** We can go a step further and write a _function_ that creates [c],
    [incc], and [decc], packages [incc] and [decc] together into a
    record, and returns this record:

      newcounter =
          \_:Unit.
             let c = ref 0 in
             let incc = \_:Unit. (c := succ (!c); !c) in
             let decc = \_:Unit. (c := pred (!c); !c) in
             {i=incc, d=decc}
*)

(** Now, each time we call [newcounter], we get a new record of
    functions that share access to the same storage cell [c].  The
    caller of [newcounter] can't get at this storage cell directly,
    but can affect it indirectly by calling the two functions.  In
    other words, we've created a simple form of _object_.

      let c1 = newcounter unit in
      let c2 = newcounter unit in
      // Note that we've allocated two separate storage cells now!
      let r1 = c1.i unit in
      let r2 = c2.i unit in
      r2  // yields 1, not 2!
*)

(* ================================================================= *)
(** ** References to Compound Types *)

(** A reference cell need not contain just a number: the primitives
    we've defined above allow us to create references to values of any
    type, including functions.  For example, we can use references to
    functions to give an (inefficient) implementation of arrays
    of numbers, as follows.

    Write [NatArray] for the type [Ref (Nat->Nat)]. *)

(** To build a new array, we allocate a reference cell and fill
    it with a function that, when given an index, always returns [0].

      newarray = \_:Unit. ref (\n:Nat.0)
*)

(** To look up an element of an array, we simply apply
    the function to the desired index.

      lookup = \a:NatArray. \n:Nat. (!a) n
*)

(** The interesting part of the encoding is the [update] function.  It
    takes an array, an index, and a new value to be stored at that index, and
    does its job by creating (and storing in the reference) a new function
    that, when it is asked for the value at this very index, returns the new
    value that was given to [update], while on all other indices it passes the
    lookup to the function that was previously stored in the reference.

      update = \a:NatArray. \m:Nat. \v:Nat.
                   let oldf = !a in
                   a := (\n:Nat. if equal m n then v else oldf n);
*)

(** References to values containing other references can also be very
    useful, allowing us to define data structures such as mutable
    lists and trees. *)

(* ================================================================= *)
(** ** Null References *)

(** One more difference between our references and C-style
    mutable variables: _null pointers_.

      - In C, a pointer variable can contain either a valid pointer
        into the heap or the special value [NULL]

      - A source of many errors and much tricky reasoning
          - (any pointer may potentially be "not there")
          - but occasionally useful

      - Null pointers are easy to implement here using references
        plus options (which can be built out of disjoint sum types)

            Option T       =  Unit + T
            NullableRef T  =  Ref (Option T)
*)

(* ================================================================= *)
(** ** Garbage Collection *)

(** A last issue that we should mention before we move on with
    formalizing references is storage _de_-allocation.  We have not
    provided any primitives for freeing reference cells when they are
    no longer needed.  Instead, like many modern languages (including
    ML and Java) we rely on the run-time system to perform _garbage
    collection_, automatically identifying and reusing cells that can
    no longer be reached by the program. *)

(** This is _not_ just a question of taste in language design: it is
    extremely difficult to achieve type safety in the presence of an
    explicit deallocation operation.  One reason for this is the
    familiar _dangling reference_ problem: we allocate a cell holding
    a number, save a reference to it in some data structure, use it
    for a while, then deallocate it and allocate a new cell holding a
    boolean, possibly reusing the same storage.  Now we can have two
    names for the same storage cell -- one with type [Ref Nat] and the
    other with type [Ref Bool]. *)

(* ################################################################# *)
(** * Operational Semantics *)

(* ================================================================= *)
(** ** Locations *)

(** A reference names a location in the _store_ (a.k.a. heap).

    What is the store?

      - Concretely: An array of 8-bit bytes, indexed by 32-bit integers.

      - More abstractly: a list (or array) of values

      - Even more abstractly: a partial function from locations to values.

    We'll choose the middle way here: A store is a list of values, and
    a location is a natural-number index into this list.
*)

(* ================================================================= *)
(** ** Stores *)

(** A store is just a _list_ of values.  (This more concrete
    representation will be more convenient for proofs than the
    functional representation we used in Imp.) *)

Definition store := list tm.

(** We use [store_lookup n st] to retrieve the value of the reference
    cell at location [n] in the store [st].  Note that we must give a
    default value to [nth] in case we try looking up an index which is
    too large. (In fact, we will never actually do this, but _proving_
    that we don't will require a bit of work.) *)

Definition store_lookup (n:nat) (st:store) :=
  nth n st <{ unit }>.

(** To update the store, we use the [replace] function, which replaces
    the contents of a cell at a particular index. *)

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil    => nil
  | h :: t =>
    match n with
    | O    => x :: t
    | S n' => h :: replace n' x t
    end
  end.

Lemma replace_nil : forall A n (x:A),
  replace n x nil = nil.
Proof.
  destruct n; auto.
Qed.

Lemma length_replace : forall A n x (l:list A),
  length (replace n x l) = length l.
Proof with auto.
  intros A n x l. generalize dependent n.
  induction l; intros n.
    destruct n...
    destruct n...
      simpl. rewrite IHl...
Qed.

Lemma lookup_replace_eq : forall l t st,
  l < length st ->
  store_lookup l (replace l t st) = t.
Proof with auto.
  intros l t st.
  unfold store_lookup.
  generalize dependent l.
  induction st as [|t' st']; intros l Hlen.
  - (* st = [] *)
   inversion Hlen.
  - (* st = t' :: st' *)
    destruct l; simpl...
    apply IHst'. simpl in Hlen. lia.
Qed.

Lemma lookup_replace_neq : forall l1 l2 t st,
  l1 <> l2 ->
  store_lookup l1 (replace l2 t st) = store_lookup l1 st.
Proof with auto.
  unfold store_lookup.
  induction l1 as [|l1']; intros l2 t st Hneq.
  - (* l1 = 0 *)
    destruct st.
    + (* st = [] *) rewrite replace_nil...
    + (* st = _ :: _ *) destruct l2... contradict Hneq...
  - (* l1 = S l1' *)
    destruct st as [|t2 st2].
    + (* st = [] *) destruct l2...
    + (* st = t2 :: st2 *)
      destruct l2...
      simpl; apply IHl1'...
Qed.

(* ================================================================= *)
(** ** Reduction *)

(** First, we augment existing reduction rules with stores:

                               value v2
                -------------------------------------               (ST_AppAbs)
                (\x:T2.t1) v2 / st --> [x:=v2]t1 / st

                        t1 / st --> t1' / st'
                     ---------------------------                      (ST_App1)
                     t1 t2 / st --> t1' t2 / st'

                  value v1     t2 / st --> t2' / st'
                  ----------------------------------                  (ST_App2)
                     v1 t2 / st --> v1 t2' / st'
*)

(** Now we can give the rules for the new constructs:

                   ------------------------------                  (ST_RefValue)
                   ref v / st --> loc |st| / st,v

                        t1 / st --> t1' / st'
                    -----------------------------                    (ST_Ref)
                    ref t1 / st --> ref t1' / st'

                               l < |st|
                     ----------------------------------            (ST_DerefLoc)
                     !(loc l) / st --> lookup l st / st

                        t1 / st --> t1' / st'
                       -----------------------                       (ST_Deref)
                       !t1 / st --> !t1' / st'

                               l < |st|
                ------------------------------------------         (ST_Assign)
                loc l := v / st --> unit / replace l v st

                        t1 / st --> t1' / st'
                 -----------------------------------               (ST_Assign1)
                 t1 := t2 / st --> t1' := t2 / st'

                        t2 / st --> t2' / st'
                 -----------------------------------               (ST_Assign2)
                 v1 := t2 / st --> v1 := t2' / st'
*)

Reserved Notation "t '/' st '-->' t' '/' st'"
  (at level 40, st at level 39, t' at level 39).

Inductive step : tm * store -> tm * store -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2 st,
         value v2 ->
         <{ (\x : T2, t1) v2 }> / st --> <{ [x := v2] t1 }> / st
  | ST_App1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 t2 }> / st --> <{ t1' t2 }> / st'
  | ST_App2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 t2 }> / st --> <{ v1 t2' }> / st'
  (* numbers *)
  | ST_SuccNat : forall (n : nat) st,
         <{ succ n }> / st --> tm_const (S n) / st
  | ST_Succ : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ succ t1 }> / st --> <{ succ t1' }> / st'
  | ST_PredNat : forall (n : nat) st,
         <{ pred n }> / st --> tm_const (n - 1) / st
  | ST_Pred : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ pred t1 }> / st --> <{ pred t1' }> / st'
  | ST_MultNats : forall (n1 n2 : nat) st,
      <{ n1 * n2 }> / st -->  tm_const (n1 * n2) / st
  | ST_Mult1 : forall t1 t2 t1' st st',
         t1 / st --> t1' / st' ->
         <{ t1 * t2 }> / st --> <{ t1' * t2 }> / st'
  | ST_Mult2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 * t2 }> / st --> <{ v1 * t2' }> / st'
  | ST_If0 : forall t1 t1' t2 t3 st st',
         t1 / st --> t1' / st' ->
         <{ if0 t1 then t2 else t3 }> / st --> <{ if0 t1' then t2 else t3 }> / st'
  | ST_If0_Zero : forall t2 t3 st,
         <{ if0 0 then t2 else t3 }> / st --> t2 / st
  | ST_If0_Nonzero : forall n t2 t3 st,
         <{ if0 {S n} then t2 else t3 }> / st --> t3 / st
  (* references *)
  | ST_RefValue : forall v st,
         value v ->
         <{ ref v }> / st --> <{ loc { length st } }> / (st ++ v::nil)
  | ST_Ref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ref t1 }> /  st --> <{ ref t1' }> /  st'
  | ST_DerefLoc : forall st l,
         l < length st ->
         <{ !(loc l) }> / st --> <{ { store_lookup l st } }> / st
  | ST_Deref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         <{ ! t1 }> / st --> <{ ! t1' }> / st'
  | ST_Assign : forall v l st,
         value v ->
         l < length st ->
         <{ (loc l) := v }> / st --> <{ unit }> / replace l v st
  | ST_Assign1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         <{ t1 := t2 }> / st --> <{ t1' := t2 }> / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         <{ v1 := t2 }> / st --> <{ v1 := t2' }> / st'

where "t '/' st '-->' t' '/' st'" := (step (t,st) (t',st')).

Hint Constructors step : core.

Definition multistep := (multi step).
Notation "t '/' st '-->*' t' '/' st'" :=
               (multistep (t,st) (t',st'))
               (at level 40, st at level 39, t' at level 39).

(* ################################################################# *)
(** * Typing *)

(** The contexts assigning types to free variables are exactly the
    same as for the STLC: partial maps from identifiers to types. *)

Definition context := partial_map ty.

(* ================================================================= *)
(** ** Store typings *)

(**  Tersify! 

    Having extended our syntax and reduction rules to accommodate
    references, our last job is to write down typing rules for the new
    constructs (and, of course, to check that these rules are sound!).
    Naturalurally, the key question is, "What is the type of a location?"

    First of all, notice that this question doesn't arise when
    typechecking terms that programmers actually
    write.  Concrete location constants arise only in terms that are
    the intermediate results of reduction; they are not in the
    language that programmers write.  So we only need to determine the
    type of a location when we're in the middle of a reduction
    sequence, e.g., trying to apply the progress or preservation
    lemmas.  Thus, even though we normally think of typing as a
    _static_ program property, it makes sense for the typing of
    locations to depend on the _dynamic_ progress of the program too.

    As a first try, note that when we reduce a term containing
    concrete locations, the type of the result depends on the contents
    of the store that we start with.  For example, if we reduce the
    term [!(loc 1)] in the store [[unit, unit]], the result is [unit];
    if we reduce the same term in the store [[unit, \x:Unit.x]], the
    result is [\x:Unit.x].  With respect to the former store, the
    location [1] has type [Unit], and with respect to the latter it
    has type [Unit->Unit]. This observation leads us immediately to a
    first attempt at a typing rule for locations:

                             Gamma |- lookup  l st : T1
                            ----------------------------
                             Gamma |- loc l : Ref T1

    That is, to find the type of a location [l], we look up the
    current contents of [l] in the store and calculate the type [T1]
    of the contents.  The type of the location is then [Ref T1].

    Having begun in this way, we need to go a little further to reach a
    consistent state.  In effect, by making the type of a term depend on
    the store, we have changed the typing relation from a three-place
    relation (between contexts, terms, and types) to a four-place relation
    (between contexts, _stores_, terms, and types).  Since the store is,
    intuitively, part of the context in which we calculate the type of a
    term, let's write this four-place relation with the store to the left
    of the turnstile: [Gamma; st |- t : T].  Our rule for typing
    references now has the form

                     Gamma; st |- lookup l st : T1
                   --------------------------------
                     Gamma; st |- loc l : Ref T1

    and all the rest of the typing rules in the system are extended
    similarly with stores.  (The other rules do not need to do anything
    interesting with their stores -- just pass them from premise to
    conclusion.)

    However, this rule will not quite do.  For one thing, typechecking
    is rather inefficient, since calculating the type of a location [l]
    involves calculating the type of the current contents [v] of [l].  If
    [l] appears many times in a term [t], we will re-calculate the type of
    [v] many times in the course of constructing a typing derivation for
    [t].  Worse, if [v] itself contains locations, then we will have to
    recalculate _their_ types each time they appear.  Worse yet, the
    proposed typing rule for locations may not allow us to derive
    anything at all, if the store contains a _cycle_.  For example,
    there is no finite typing derivation for the location [0] with respect
    to this store:

   [\x:Nat. (!(loc 1)) x, \x:Nat. (!(loc 0)) x]
*)

(** **** Exercise: 2 stars, standard (cyclic_store)

    Can you find a term whose reduction will create this particular
    cyclic store? *)

(** [] *)

(** These problems arise from the fact that our proposed
    typing rule for locations requires us to recalculate the type of a
    location every time we mention it in a term.  But this,
    intuitively, should not be necessary.  After all, when a location
    is first created, we know the type of the initial value that we
    are storing into it.  Suppose we are willing to enforce the
    invariant that the type of the value contained in a given location
    _never changes_; that is, although we may later store other values
    into this location, those other values will always have the same
    type as the initial one.  In other words, we always have in mind a
    single, definite type for every location in the store, which is
    fixed when the location is allocated.  Then these intended types
    can be collected together as a _store typing_ -- a finite function
    mapping locations to types.

    As with the other type systems we've seen, this conservative typing
    restriction on allowed updates means that we will rule out as
    ill-typed some programs that could reduce perfectly well without
    getting stuck.

    Just as we did for stores, we will represent a store type simply
    as a list of types: the type at index [i] records the type of the
    values that we expect to be stored in cell [i]. *)

Definition store_ty := list ty.

(** The [store_Tlookup] function retrieves the type at a particular
    index. *)

Definition store_Tlookup (n:nat) (ST:store_ty) :=
  nth n ST <{ Unit }>.

(** Suppose we are given a store typing [ST] describing the store
    [st] in which some term [t] will be reduced.  Then we can use
    [ST] to calculate the type of the result of [t] without ever
    looking directly at [st].  For example, if [ST] is [[Unit,
    Unit->Unit]], then we can immediately infer that [!(loc 1)] has
    type [Unit->Unit].  More generally, the typing rule for locations
    can be reformulated in terms of store typings like this:

                                 l < |ST|
                   -------------------------------------
                   Gamma; ST |- loc l : Ref (lookup l ST)

    That is, as long as [l] is a valid location, we can compute the
    type of [l] just by looking it up in [ST].  Typing is again a
    four-place relation, but it is parameterized on a store _typing_
    rather than a concrete store.  The rest of the typing rules are
    analogously augmented with store typings. *)

(* ================================================================= *)
(** ** The Typing Relation *)

(**

                               l < |ST|
                  --------------------------------------              (T_Loc)
                  Gamma; ST |- loc l : Ref (lookup l ST)

                         Gamma; ST |- t1 : T1
                     ----------------------------                       (T_Ref)
                     Gamma; ST |- ref t1 : Ref T1

                      Gamma; ST |- t1 : Ref T1
                      -------------------------                         (T_Deref)
                        Gamma; ST |- !t1 : T1

                      Gamma; ST |- t1 : Ref T2
                        Gamma; ST |- t2 : T2
                    ----------------------------                     (T_Assign)
                    Gamma; ST |- t1 := t2 : Unit
*)

Reserved Notation "Gamma ';' ST '|-' t '\in' T"
                  (at level 40, t custom stlc, T custom stlc at level 0).

Inductive has_type (ST : store_ty) : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma ; ST |- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      update Gamma x T2 ; ST |- t1 \in T1 ->
      Gamma ; ST |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma ; ST |- t1 \in (T2 -> T1) ->
      Gamma ; ST |- t2 \in T2 ->
      Gamma ; ST |- t1 t2 \in T1
  | T_Nat : forall Gamma (n : nat),
      Gamma ; ST |- n \in Nat
  | T_Succ : forall Gamma t1,
      Gamma ; ST |- t1 \in Nat ->
      Gamma ; ST |- succ t1 \in Nat
  | T_Pred : forall Gamma t1,
      Gamma ; ST |- t1 \in Nat ->
      Gamma ; ST |- pred t1 \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma ; ST |- t1 \in Nat ->
      Gamma ; ST |- t2 \in Nat ->
      Gamma ; ST |- t1 * t2 \in Nat
  | T_If0 : forall Gamma t1 t2 t3 T0,
      Gamma ; ST |- t1 \in Nat ->
      Gamma ; ST |- t2 \in T0 ->
      Gamma ; ST |- t3 \in T0 ->
      Gamma ; ST |- if0 t1 then t2 else t3 \in T0
  | T_Unit : forall Gamma,
      Gamma ; ST |- unit \in Unit
  | T_Loc : forall Gamma l,
      l < length ST ->
      Gamma ; ST |- (loc l) \in (Ref {store_Tlookup l ST })
  | T_Ref : forall Gamma t1 T1,
      Gamma ; ST |- t1 \in T1 ->
      Gamma ; ST |- (ref t1) \in (Ref T1)
  | T_Deref : forall Gamma t1 T1,
      Gamma ; ST |- t1 \in (Ref T1) ->
      Gamma ; ST |- (! t1) \in T1
  | T_Assign : forall Gamma t1 t2 T2,
      Gamma ; ST |- t1 \in (Ref T2) ->
      Gamma ; ST |- t2 \in T2 ->
      Gamma ; ST |- (t1 := t2) \in Unit

where "Gamma ';' ST '|-' t '\in' T" := (has_type ST Gamma t T).

Hint Constructors has_type : core.

(* ################################################################# *)
(** * Properties *)

(** Standard theorems...
      - Progress -- pretty much same as always
      - Preservation -- needs to be stated more carefully! *)

(* ================================================================= *)
(** ** Well-Typed Stores *)

(** Evaulation and typing relations take more parameters now,
    so at a minumum we have to add these to the statement of
    preservation... *)

Theorem preservation_wrong1 : forall ST T t st t' st',
  empty ; ST |- t \in T ->
  t / st --> t' / st' ->
  empty ; ST |- t' \in T.
Abort.

(** Obviously wrong: no relation between assumed store typing
    and provided store! *)

(** We need a way of saying "this store satisfies the assumptions of
    that store typing"... *)

Definition store_well_typed (ST:store_ty) (st:store) :=
  length ST = length st /\
  (forall l, l < length st ->
     empty; ST |- { store_lookup l st } \in {store_Tlookup l ST }).

(** Informally, we will write [ST |- st] for [store_well_typed ST st]. *)

(** We can now state something closer to the desired preservation
    property: *)

Theorem preservation_wrong2 : forall ST T t st t' st',
  empty ; ST |- t \in T ->
  t / st --> t' / st' ->
  store_well_typed ST st ->
  empty ; ST |- t' \in T.
Abort.

(** This works... for all but _one_ of the reduction rules! *)

(* ================================================================= *)
(** ** Extending Store Typings *)

(** Intuition: Since the store can grow during reduction, we
    need to let the store typing grow too... *)

Inductive extends : store_ty -> store_ty -> Prop :=
  | extends_nil  : forall ST',
      extends ST' nil
  | extends_cons : forall x ST' ST,
      extends ST' ST ->
      extends (x::ST') (x::ST).

Hint Constructors extends : core.

(** We'll need a few technical lemmas about extended contexts.

    First, looking up a type in an extended store typing yields the
    same result as in the original: *)

Lemma extends_lookup : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  store_Tlookup l ST' = store_Tlookup l ST.
Proof with auto.
  intros l ST.
  generalize dependent l.
  induction ST as [|a ST2]; intros l ST' Hlen HST'.
  - (* nil *) inversion Hlen.
  - (* cons *) unfold store_Tlookup in *.
    destruct ST'.
    + (* ST' = nil *) inversion HST'.
    + (* ST' = a' :: ST'2 *)
      inversion HST'; subst.
      destruct l as [|l'].
      * (* l = 0 *) auto.
      * (* l = S l' *) simpl. apply IHST2...
        simpl in Hlen; lia.
Qed.

(** Next, if [ST'] extends [ST], the length of [ST'] is at least that
    of [ST]. *)

Lemma length_extends : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  l < length ST'.
Proof with eauto.
  intros. generalize dependent l. induction H0; intros l Hlen.
    - inversion Hlen.
    - simpl in *.
      destruct l; try lia.
        apply lt_n_S. apply IHextends. lia.
Qed.

(** Finally, [ST ++ T] extends [ST], and [extends] is reflexive. *)

Lemma extends_app : forall ST T,
  extends (ST ++ T) ST.
Proof.
  induction ST; intros T.
  auto.
  simpl. auto.
Qed.

Lemma extends_refl : forall ST,
  extends ST ST.
Proof.
  induction ST; auto.
Qed.

(* ================================================================= *)
(** ** Preservation, Finally *)

(** We can now give the final, correct statement of the type
    preservation property: *)

Definition preservation_theorem := forall ST t t' T st st',
  empty ; ST |- t \in T ->
  store_well_typed ST st ->
  t / st --> t' / st' ->
  exists ST',
     extends ST' ST /\
     empty ; ST' |- t' \in T /\
     store_well_typed ST' st'.

(** Note that this gives us just what we need to "turn the
    crank" when applying the theorem to multi-step reduction
    sequences. *)

(* ================================================================= *)
(** ** Substitution Lemma *)

(** To prove preservation, we need to re-develop the rest of
    the machinery that we saw for the pure STLC (plus a couple of new
    things about store typings and extension)... *)

Lemma weakening : forall Gamma Gamma' ST t T,
     includedin Gamma Gamma' ->
     Gamma  ; ST |- t \in T  ->
     Gamma' ; ST |- t \in T.
Proof.
  intros Gamma Gamma' ST t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Lemma weakening_empty : forall Gamma ST t T,
     empty ; ST |- t \in T  ->
     Gamma ; ST |- t \in T.
Proof.
  intros Gamma ST t T.
  eapply weakening.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma ST x U t v T,
  (update Gamma x U); ST |- t \in T ->
  empty ; ST |- v \in U   ->
  Gamma ; ST |- [x:=v]t \in T.
Proof.
  intros Gamma ST x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (String.eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y.
    destruct (String.eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.

(* ================================================================= *)
(** ** Assignment Preserves Store Typing *)

(** Next, we must show that replacing the contents of a cell in the
    store with a new value of appropriate type does not change the
    overall type of the store.  (This is needed for the [ST_Assign]
    rule.) *)

Lemma assign_pres_store_typing : forall ST st l t,
  l < length st ->
  store_well_typed ST st ->
  empty ; ST |- t \in {store_Tlookup l ST} ->
  store_well_typed ST (replace l t st).
Proof with auto.
  intros ST st l t Hlen HST Ht.
  inversion HST; subst.
  split. rewrite length_replace...
  intros l' Hl'.
  destruct (l' =? l) eqn: Heqll'.
  - (* l' = l *)
    apply eqb_eq in Heqll'; subst.
    rewrite lookup_replace_eq...
  - (* l' <> l *)
    apply eqb_neq in Heqll'.
    rewrite lookup_replace_neq...
    rewrite length_replace in Hl'.
    apply H0...
Qed.

(* ================================================================= *)
(** ** Weakening for Stores *)

(** Finally, we need a lemma on store typings, stating that, if a
    store typing is extended with a new location, the extended one
    still allows us to assign the same types to the same terms as the
    original.

    (The lemma is called [store_weakening] because it resembles the
    "weakening" lemmas found in proof theory, which show that adding a
    new assumption to some logical theory does not decrease the set of
    provable theorems.) *)

Lemma store_weakening : forall Gamma ST ST' t T,
  extends ST' ST ->
  Gamma ; ST |- t \in T ->
  Gamma ; ST' |- t \in T.
Proof with eauto.
  intros. induction H0; eauto.
  - (* T_Loc *)
    rewrite <- (extends_lookup _ _ ST')...
    apply T_Loc.
    eapply length_extends...
Qed.

(** We can use the [store_weakening] lemma to prove that if a store is
    well typed with respect to a store typing, then the store extended
    with a new term [t] will still be well typed with respect to the
    store typing extended with [t]'s type. *)

Lemma store_well_typed_app : forall ST st t1 T1,
  store_well_typed ST st ->
  empty ; ST |- t1 \in T1 ->
  store_well_typed (ST ++ T1::nil) (st ++ t1::nil).
Proof with auto.
  intros.
  unfold store_well_typed in *.
  destruct H as [Hlen Hmatch].
  rewrite app_length, add_comm. simpl.
  rewrite app_length, add_comm. simpl.
  split...
  - (* types match. *)
    intros l Hl.
    unfold store_lookup, store_Tlookup.
    apply le_lt_eq_dec in Hl; destruct Hl as [Hlt | Heq].
    + (* l < length st *)
      apply lt_S_n in Hlt.
      rewrite !app_nth1...
      * apply store_weakening with ST. apply extends_app.
        apply Hmatch...
      * rewrite Hlen...
    + (* l = length st *)
      injection Heq as Heq; subst.
      rewrite app_nth2; try lia.
      rewrite <- Hlen.
      rewrite minus_diag. simpl.
      apply store_weakening with ST...
      { apply extends_app. }
      rewrite app_nth2; [|lia].
      rewrite minus_diag. simpl. assumption.
Qed.

(* ================================================================= *)
(** ** Preservation! *)

(** Now that we've got everything set up right, the proof of
    preservation is actually quite straightforward.  *)

(** Begin with one technical lemma: *)

Lemma nth_eq_last : forall A (l:list A) x d,
  nth (length l) (l ++ x::nil) d = x.
Proof.
  induction l; intros; [ auto | simpl; rewrite IHl; auto ].
Qed.

(** And here, at last, is the preservation theorem: *)

Theorem preservation : forall ST t t' T st st',
  empty ; ST |- t \in T ->
  store_well_typed ST st ->
  t / st --> t' / st' ->
  exists ST',
     extends ST' ST /\
     empty ; ST' |- t' \in T /\
     store_well_typed ST' st'.
Proof with eauto using store_weakening, extends_refl.
  remember empty as Gamma.
  intros ST t t' T st st' Ht.
  generalize dependent t'.
  induction Ht; intros t' HST Hstep;
    subst; try solve_by_invert; inversion Hstep; subst;
    try (eauto using store_weakening, extends_refl).
  (* T_App *)
  - (* ST_AppAbs *) exists ST.
    inversion Ht1; subst.
    split; try split... eapply substitution_preserves_typing...
  - (* ST_App1 *)
    eapply IHHt1 in H0...
    destruct H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* ST_App2 *)
    eapply IHHt2 in H5...
    destruct H5 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* T_Succ *)
    + (* ST_Succ *)
      eapply IHHt in H0...
      destruct H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  - (* T_Pred *)
    + (* ST_Pred *)
      eapply IHHt in H0...
      destruct H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  (* T_Mult *)
  - (* ST_Mult1 *)
    eapply IHHt1 in H0...
    destruct H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* ST_Mult2 *)
    eapply IHHt2 in H5...
    destruct H5 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* T_If0 *)
    + (* ST_If0_1 *)
      eapply IHHt1 in H0...
      destruct H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'. split...
  (* T_Ref *)
  - (* ST_RefValue *)
    exists (ST ++ T1::nil).
    inversion HST; subst.
    split.
    { apply extends_app. }
    split.
    { replace <{ Ref T1 }>
        with <{ Ref {store_Tlookup (length st) (ST ++ T1::nil)} }>.
      { apply T_Loc.
        rewrite <- H. rewrite app_length, add_comm. simpl. lia. }
      unfold store_Tlookup. rewrite <- H. rewrite nth_eq_last.
      reflexivity. }
    apply store_well_typed_app; assumption.
  - (* ST_Ref *)
    eapply IHHt in H0...
    destruct H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  (* T_Deref *)
  - (* ST_DerefLoc *)
    exists ST. split; try split...
    destruct HST as [_ Hsty].
    replace T1 with (store_Tlookup l ST).
    apply Hsty...
    inversion Ht; subst...
  - (* ST_Deref *)
    eapply IHHt in H0...
    destruct H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  (* T_Assign *)
  - (* ST_Assign *)
    exists ST. split; try split...
    eapply assign_pres_store_typing...
    inversion Ht1; subst...
  - (* ST_Assign1 *)
    eapply IHHt1 in H0...
    destruct H0 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
  - (* ST_Assign2 *)
    eapply IHHt2 in H5...
    destruct H5 as [ST' [Hext [Hty Hsty]]].
    exists ST'...
Qed.

(** **** Exercise: 3 stars, standard (preservation_informal)

    Write a careful informal proof of the preservation theorem,
    concentrating on the [T_App], [T_Deref], [T_Assign], and [T_Ref]
    cases.

(* FILL IN HERE *)
 *)

(** [] *)

(* ================================================================= *)
(** ** Progress *)

(** As we've said, progress for this system is pretty easy to prove;
    the proof is very similar to the proof of progress for the STLC,
    with a few new cases for the new syntactic constructs. *)

Theorem progress : forall ST t T st,
  empty ; ST |- t \in T ->
  store_well_typed ST st ->
  (value t \/ exists t' st', t / st --> t' / st').
Proof with eauto.
  intros ST t T st Ht HST. remember empty as Gamma.
  induction Ht; subst; try solve_by_invert...
  - (* T_App *)
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve_by_invert.
      destruct IHHt2 as [Ht2p | Ht2p]...
      * (* t2 steps *)
        destruct Ht2p as [t2' [st' Hstep]].
        exists <{ (\ x0 : T0, t0) t2' }>, st'...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ t1' t2 }>, st'...
  - (* T_Succ *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve [ inversion Ht ].
      * (* t1 is a const *)
        exists <{ {S n} }>, st...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ succ t1' }>, st'...
  - (* T_Pred *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve [inversion Ht ].
      * (* t1 is a const *)
        exists <{ {n - 1} }>, st...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ pred t1' }>, st'...
  - (* T_Mult *)
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve [inversion Ht1].
      destruct IHHt2 as [Ht2p | Ht2p]...
      * (* t2 is a value *)
        inversion Ht2p; subst; try solve [inversion Ht2].
        exists <{ {n * n0} }>, st...
      * (* t2 steps *)
        destruct Ht2p as [t2' [st' Hstep]].
        exists <{ n * t2' }>, st'...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ t1' * t2 }>, st'...
  - (* T_If0 *)
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve [inversion Ht1].
      destruct n.
      * (* n = 0 *) exists t2, st...
      * (* n = S n' *) exists t3, st...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ if0 t1' then t2 else t3 }>, st'...
  - (* T_Ref *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ref t1'}>, st'...
  - (* T_Deref *)
    right. destruct IHHt as [Ht1p | Ht1p]...
    + (* t1 is a value *)
      inversion Ht1p; subst; try solve_by_invert.
      eexists. eexists. apply ST_DerefLoc...
      inversion Ht; subst. inversion HST; subst.
      rewrite <- H...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ ! t1' }>, st'...
  - (* T_Assign *)
    right. destruct IHHt1 as [Ht1p|Ht1p]...
    + (* t1 is a value *)
      destruct IHHt2 as [Ht2p|Ht2p]...
      * (* t2 is a value *)
        inversion Ht1p; subst; try solve_by_invert.
        eexists. eexists. apply ST_Assign...
        inversion HST; subst. inversion Ht1; subst.
        rewrite H in H4...
      * (* t2 steps *)
        destruct Ht2p as [t2' [st' Hstep]].
        exists <{ t1 := t2' }>, st'...
    + (* t1 steps *)
      destruct Ht1p as [t1' [st' Hstep]].
      exists <{ t1' := t2 }>, st'...
Qed.

(* ################################################################# *)
(** * References and Nontermination *)

(** An important fact about the STLC (proved in chapter [Norm]) is
    that it is is _normalizing_ -- that is, every well-typed term can
    be reduced to a value in a finite number of steps.

    What about STLC + references?  Surprisingly, adding references
    causes us to lose the normalization property: there exist
    well-typed terms in the STLC + references which can continue to
    reduce forever, without ever reaching a normal form! *)

(** How can we construct such a term?  The main idea is to make a
    function which calls itself.  We first make a function which calls
    another function stored in a reference cell; the trick is that we
    then smuggle in a reference to itself!

   (\r:Ref (Unit -> Unit).
        r := (\x:Unit.(!r) unit); (!r) unit)
   (ref (\x:Unit.unit))
*)

Module ExampleVariables.

Open Scope string_scope.

Definition x := "x".
Definition y := "y".
Definition r := "r".
Definition s := "s".

End ExampleVariables.

Module RefsAndNontermination.
Import ExampleVariables.

Definition loop_fun :=
  <{ \x : Unit, (!r) unit }>.

Definition loop :=
  <{ (\r : Ref (Unit -> Unit), (( r := loop_fun ); ( (! r) unit ) )) (ref (\x : Unit, unit)) }> .
(** This term is well typed: *)

Lemma loop_typeable : exists T, empty; nil |- loop \in T.
Proof with eauto.
  eexists. unfold loop. unfold loop_fun.
  eapply T_App...
  eapply T_Abs...
  eapply T_App...
    eapply T_Abs. eapply T_App. eapply T_Deref. eapply T_Var.
    rewrite update_neq; [|intros; discriminate].
    rewrite update_eq. reflexivity. auto.
  eapply T_Assign.
    eapply T_Var. rewrite update_eq. reflexivity.
  eapply T_Abs.
    eapply T_App...
      eapply T_Deref. eapply T_Var. reflexivity.
Qed.

(** To show formally that the term diverges, we first define the
    [step_closure] of the single-step reduction relation, written
    [-->+].  This is just like the reflexive step closure of
    single-step reduction (which we're been writing [-->*]), except
    that it is not reflexive: [t -->+ t'] means that [t] can reach
    [t'] by _one or more_ steps of reduction. *)

Inductive step_closure {X:Type} (R: relation X) : X -> X -> Prop :=
  | sc_one  : forall (x y : X),
                R x y -> step_closure R x y
  | sc_step : forall (x y z : X),
                R x y ->
                step_closure R y z ->
                step_closure R x z.

Definition multistep1 := (step_closure step).
Notation "t1 '/' st '-->+' t2 '/' st'" :=
        (multistep1 (t1,st) (t2,st'))
        (at level 40, st at level 39, t2 at level 39).

(** Now, we can show that the expression [loop] reduces to the
    expression [!(loc 0) unit] and the size-one store
    [[r:=(loc 0)]loop_fun]. *)

(** As a convenience, we introduce a slight variant of the [normalize]
    tactic, called [reduce], which tries solving the goal with
    [multi_refl] at each step, instead of waiting until the goal can't
    be reduced any more. Of course, the whole point is that [loop]
    doesn't normalize, so the old [normalize] tactic would just go
    into an infinite loop reducing it forever! *)

Ltac print_goal := match goal with |- ?x => idtac x end.
Ltac reduce :=
    repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; compute)];
            try solve [apply multi_refl]).

(** Next, we use [reduce] to show that [loop] steps to
    [!(loc 0) unit], starting from the empty store. *)

Lemma loop_steps_to_loop_fun :
  loop / nil -->*
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil.
Proof.
  unfold loop.
  reduce.
Qed.

(** Finally, we show that the latter expression reduces in
    two steps to itself! *)

Lemma loop_fun_step_self :
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil -->+
  <{ (! (loc 0)) unit }> / cons <{ [r := loc 0] loop_fun }> nil.
Proof with eauto.
  unfold loop_fun; simpl.
  eapply sc_step. apply ST_App1...
  eapply sc_one. compute. apply ST_AppAbs...
Qed.

(** **** Exercise: 4 stars, standard (factorial_ref)

    Use the above ideas to implement a factorial function in STLC with
    references.  (There is no need to prove formally that it really
    behaves like the factorial.  Just uncomment the example below to make
    sure it gives the correct result when applied to the argument
    [4].) *)

Definition factorial : tm
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma factorial_type : empty; nil |- factorial \in (Nat -> Nat).
Proof with eauto.
  (* FILL IN HERE *) Admitted.

(** If your definition is correct, you should be able to just
    uncomment the example below; the proof should be fully
    automatic using the [reduce] tactic. *)

(* 
Lemma factorial_4 : exists st,
  <{ factorial 4 }> / nil -->* tm_const 24 / st.
Proof.
  eexists. unfold factorial. reduce.
Qed.
*)
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 5 stars, standard, optional (garabage_collector)

    Challenge problem: modify our formalization to include an account
    of garbage collection, and prove that it satisfies whatever nice
    properties you can think to prove about it. *)

(** [] *)

End RefsAndNontermination.
End STLCRef.
