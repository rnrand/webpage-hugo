Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import Induction.

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

From LF Require Import Induction.
Import Check.

Goal True.

idtac "-------------------  double_plus  --------------------".
idtac " ".

idtac "#> double_plus".
idtac "Possible points: 2".
check_type @double_plus ((forall n : nat, double n = n + n)).
idtac "Assumptions:".
Abort.
Print Assumptions double_plus.
Goal True.
idtac " ".

idtac "-------------------  binary_inverse  --------------------".
idtac " ".

idtac "#> nat_bin_nat".
idtac "Advanced".
idtac "Possible points: 4".
check_type @nat_bin_nat ((forall n : nat, bin_to_nat (nat_to_bin n) = n)).
idtac "Assumptions:".
Abort.
Print Assumptions nat_bin_nat.
Goal True.
idtac " ".

idtac "#> bin_nat_bin".
idtac "Advanced".
idtac "Possible points: 6".
check_type @bin_nat_bin ((forall b : bin, nat_to_bin (bin_to_nat b) = normalize b)).
idtac "Assumptions:".
Abort.
Print Assumptions bin_nat_bin.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 2".
idtac "Max points - advanced: 12".
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
idtac "---------- double_plus ---------".
Print Assumptions double_plus.
idtac "".
idtac "********** Advanced **********".
idtac "---------- nat_bin_nat ---------".
Print Assumptions nat_bin_nat.
idtac "---------- bin_nat_bin ---------".
Print Assumptions bin_nat_bin.
Abort.

(* 2022-02-17 13:47 *)

(* 2022-02-17 13:48 *)
