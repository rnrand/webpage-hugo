Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import Types.

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

From LF Require Import Types.
Import Check.

Goal True.

idtac "-------------------  some_term_is_stuck  --------------------".
idtac " ".

idtac "#> TM.some_term_is_stuck".
idtac "Possible points: 2".
check_type @TM.some_term_is_stuck ((exists t : TM.tm, TM.stuck t)).
idtac "Assumptions:".
Abort.
Print Assumptions TM.some_term_is_stuck.
Goal True.
idtac " ".

idtac "-------------------  value_is_nf  --------------------".
idtac " ".

idtac "#> TM.value_is_nf".
idtac "Possible points: 3".
check_type @TM.value_is_nf ((forall t : TM.tm, TM.value t -> TM.step_normal_form t)).
idtac "Assumptions:".
Abort.
Print Assumptions TM.value_is_nf.
Goal True.
idtac " ".

idtac "-------------------  finish_progress  --------------------".
idtac " ".

idtac "#> TM.progress".
idtac "Possible points: 3".
check_type @TM.progress (
(forall (t : TM.tm) (T : TM.ty),
 TM.has_type t T -> TM.value t \/ (exists t' : TM.tm, TM.step t t'))).
idtac "Assumptions:".
Abort.
Print Assumptions TM.progress.
Goal True.
idtac " ".

idtac "-------------------  finish_preservation  --------------------".
idtac " ".

idtac "#> TM.preservation".
idtac "Possible points: 2".
check_type @TM.preservation (
(forall (t t' : TM.tm) (T : TM.ty),
 TM.has_type t T -> TM.step t t' -> TM.has_type t' T)).
idtac "Assumptions:".
Abort.
Print Assumptions TM.preservation.
Goal True.
idtac " ".

idtac "-------------------  preservation_alternate_proof  --------------------".
idtac " ".

idtac "#> TM.preservation'".
idtac "Possible points: 3".
check_type @TM.preservation' (
(forall (t t' : TM.tm) (T : TM.ty),
 TM.has_type t T -> TM.step t t' -> TM.has_type t' T)).
idtac "Assumptions:".
Abort.
Print Assumptions TM.preservation'.
Goal True.
idtac " ".

idtac "-------------------  subject_expansion  --------------------".
idtac " ".

idtac "#> Manually graded: TM.subject_expansion".
idtac "Possible points: 2".
print_manual_grade TM.manual_grade_for_subject_expansion.
idtac " ".

idtac "-------------------  variation1  --------------------".
idtac " ".

idtac "#> Manually graded: TM.variation1".
idtac "Advanced".
idtac "Possible points: 2".
print_manual_grade TM.manual_grade_for_variation1.
idtac " ".

idtac "-------------------  variation2  --------------------".
idtac " ".

idtac "#> Manually graded: TM.variation2".
idtac "Advanced".
idtac "Possible points: 2".
print_manual_grade TM.manual_grade_for_variation2.
idtac " ".

idtac "-------------------  variation5  --------------------".
idtac " ".

idtac "#> Manually graded: TM.variation5".
idtac "Advanced".
idtac "Possible points: 2".
print_manual_grade TM.manual_grade_for_variation5.
idtac " ".

idtac "-------------------  remove_pred0  --------------------".
idtac " ".

idtac "#> Manually graded: TM.remove_pred0".
idtac "Advanced".
idtac "Possible points: 1".
print_manual_grade TM.manual_grade_for_remove_pred0.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 22".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "CSeq_congruence".
idtac "fold_constants_bexp_sound".
idtac "succ_hastype_nat__hastype_nat".
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
idtac "---------- TM.some_term_is_stuck ---------".
Print Assumptions TM.some_term_is_stuck.
idtac "---------- TM.value_is_nf ---------".
Print Assumptions TM.value_is_nf.
idtac "---------- TM.progress ---------".
Print Assumptions TM.progress.
idtac "---------- TM.preservation ---------".
Print Assumptions TM.preservation.
idtac "---------- TM.preservation' ---------".
Print Assumptions TM.preservation'.
idtac "---------- subject_expansion ---------".
idtac "MANUAL".
idtac "".
idtac "********** Advanced **********".
idtac "---------- variation1 ---------".
idtac "MANUAL".
idtac "---------- variation2 ---------".
idtac "MANUAL".
idtac "---------- variation5 ---------".
idtac "MANUAL".
idtac "---------- remove_pred0 ---------".
idtac "MANUAL".
Abort.

(* 2022-03-08 13:52 *)

(* 2022-03-08 13:53 *)
