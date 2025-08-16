Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import ProofObjects.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From LF Require Import ProofObjects.
Import Check.

Goal True.

idtac "-------------------  A_then_A  --------------------".
idtac " ".

idtac "#> functions.A_then_A".
idtac "Possible points: 1".
check_type @functions.A_then_A ((forall A : Type, A -> A)).
idtac "Assumptions:".
Abort.
Print Assumptions functions.A_then_A.
Goal True.
idtac " ".

idtac "-------------------  modus_tollens  --------------------".
idtac " ".

idtac "#> functions.modus_tollens".
idtac "Possible points: 1".
check_type @functions.modus_tollens (
(forall X Y : Prop, (X -> Y) -> (Y -> False) -> X -> False)).
idtac "Assumptions:".
Abort.
Print Assumptions functions.modus_tollens.
Goal True.
idtac " ".

idtac "-------------------  and_assoc'  --------------------".
idtac " ".

idtac "#> and_assoc'".
idtac "Possible points: 1".
check_type @and_assoc' ((forall P Q R : Prop, (P /\ Q) /\ R -> P /\ Q /\ R)).
idtac "Assumptions:".
Abort.
Print Assumptions and_assoc'.
Goal True.
idtac " ".

idtac "-------------------  or_commut'  --------------------".
idtac " ".

idtac "#> or_commut'".
idtac "Possible points: 2".
check_type @or_commut' ((forall P Q : Prop, P \/ Q -> Q \/ P)).
idtac "Assumptions:".
Abort.
Print Assumptions or_commut'.
Goal True.
idtac " ".

idtac "-------------------  ev_two  --------------------".
idtac " ".

idtac "#> ev_two".
idtac "Possible points: 2".
check_type @ev_two ((ev 2)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_two.
Goal True.
idtac " ".

idtac "-------------------  eq_trans'  --------------------".
idtac " ".

idtac "#> MyEquality.eq_trans'".
idtac "Possible points: 1".
check_type @MyEquality.eq_trans' (
(forall (A : Type) (a b c : A),
 @MyEquality.eq A a b -> @MyEquality.eq A b c -> @MyEquality.eq A a c)).
idtac "Assumptions:".
Abort.
Print Assumptions MyEquality.eq_trans'.
Goal True.
idtac " ".

idtac "-------------------  ilastn  --------------------".
idtac " ".

idtac "#> test_ilastn1".
idtac "Possible points: 1".
check_type @test_ilastn1 ((@ilastn nat 2 3 [[2; 5; 8; 11; 14]] = [[8; 11; 14]])).
idtac "Assumptions:".
Abort.
Print Assumptions test_ilastn1.
Goal True.
idtac " ".

idtac "#> test_ilastn2".
idtac "Possible points: 1".
check_type @test_ilastn2 (
(forall x y : nat, @ilastn nat 1 4 [[x; 2; 1; y; 3]] = [[2; 1; y; 3]])).
idtac "Assumptions:".
Abort.
Print Assumptions test_ilastn2.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 10".
idtac "Max points - advanced: 10".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "plus_le".
idtac "le_trans".
idtac "le_plus_l".
idtac "add_le_cases".
idtac "Sn_le_Sm__n_le_m".
idtac "O_le_n".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- functions.A_then_A ---------".
Print Assumptions functions.A_then_A.
idtac "---------- functions.modus_tollens ---------".
Print Assumptions functions.modus_tollens.
idtac "---------- and_assoc' ---------".
Print Assumptions and_assoc'.
idtac "---------- or_commut' ---------".
Print Assumptions or_commut'.
idtac "---------- ev_two ---------".
Print Assumptions ev_two.
idtac "---------- MyEquality.eq_trans' ---------".
Print Assumptions MyEquality.eq_trans'.
idtac "---------- test_ilastn1 ---------".
Print Assumptions test_ilastn1.
idtac "---------- test_ilastn2 ---------".
Print Assumptions test_ilastn2.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2022-02-17 13:48 *)

(* 2022-02-17 13:48 *)
