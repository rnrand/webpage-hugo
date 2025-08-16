Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import IndPrinciples.

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

From LF Require Import IndPrinciples.
Import Check.

Goal True.

idtac "-------------------  len_app'  --------------------".
idtac " ".

idtac "#> len_app'".
idtac "Possible points: 2".
check_type @len_app' (
(forall (X : Type) (l1 l2 : list X),
 @length X (l1 ++ l2) = @length X l1 + @length X l2)).
idtac "Assumptions:".
Abort.
Print Assumptions len_app'.
Goal True.
idtac " ".

idtac "-------------------  booltree_ind  --------------------".
idtac " ".

idtac "#> Manually graded: booltree_ind".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_booltree_ind.
idtac " ".

idtac "-------------------  toy_ind  --------------------".
idtac " ".

idtac "#> Manually graded: toy_ind".
idtac "Possible points: 1".
print_manual_grade manual_grade_for_toy_ind.
idtac " ".

idtac "-------------------  odd_decomposition  --------------------".
idtac " ".

idtac "#> odd_decomposition".
idtac "Possible points: 3".
check_type @odd_decomposition ((forall n : nat, odd n -> exists m : nat, n = m * 2 + 1)).
idtac "Assumptions:".
Abort.
Print Assumptions odd_decomposition.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 7".
idtac "Max points - advanced: 7".
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
idtac "---------- len_app' ---------".
Print Assumptions len_app'.
idtac "---------- booltree_ind ---------".
idtac "MANUAL".
idtac "---------- toy_ind ---------".
idtac "MANUAL".
idtac "---------- odd_decomposition ---------".
Print Assumptions odd_decomposition.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2022-02-17 13:48 *)

(* 2022-02-17 13:48 *)
