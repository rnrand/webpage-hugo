Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import Equiv.

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

From LF Require Import Equiv.
Import Check.

Goal True.

idtac "-------------------  skip_right  --------------------".
idtac " ".

idtac "#> skip_right".
idtac "Possible points: 2".
check_type @skip_right ((forall c : com, cequiv <{ c; skip }> c)).
idtac "Assumptions:".
Abort.
Print Assumptions skip_right.
Goal True.
idtac " ".

idtac "-------------------  if_false  --------------------".
idtac " ".

idtac "#> if_false".
idtac "Possible points: 2".
check_type @if_false (
(forall (b : bexp) (c1 c2 : com),
 bequiv b <{ false }> -> cequiv <{ if b then c1 else c2 end }> c2)).
idtac "Assumptions:".
Abort.
Print Assumptions if_false.
Goal True.
idtac " ".

idtac "-------------------  swap_if_branches  --------------------".
idtac " ".

idtac "#> swap_if_branches".
idtac "Possible points: 3".
check_type @swap_if_branches (
(forall (b : bexp) (c1 c2 : com),
 cequiv <{ if b then c1 else c2 end }> <{ if ~ b then c2 else c1 end }>)).
idtac "Assumptions:".
Abort.
Print Assumptions swap_if_branches.
Goal True.
idtac " ".

idtac "-------------------  while_true  --------------------".
idtac " ".

idtac "#> while_true".
idtac "Possible points: 2".
check_type @while_true (
(forall (b : bexp) (c : com),
 bequiv b <{ true }> ->
 cequiv <{ while b do c end }> <{ while true do skip end }>)).
idtac "Assumptions:".
Abort.
Print Assumptions while_true.
Goal True.
idtac " ".

idtac "-------------------  assign_aequiv  --------------------".
idtac " ".

idtac "#> assign_aequiv".
idtac "Possible points: 2".
check_type @assign_aequiv (
(forall (X : String.string) (a : aexp),
 aequiv (AId X) a -> cequiv <{ skip }> <{ X := a }>)).
idtac "Assumptions:".
Abort.
Print Assumptions assign_aequiv.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 11".
idtac "Max points - advanced: 11".
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
idtac "---------- skip_right ---------".
Print Assumptions skip_right.
idtac "---------- if_false ---------".
Print Assumptions if_false.
idtac "---------- swap_if_branches ---------".
Print Assumptions swap_if_branches.
idtac "---------- while_true ---------".
Print Assumptions while_true.
idtac "---------- assign_aequiv ---------".
Print Assumptions assign_aequiv.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2022-03-03 13:02 *)

(* 2022-03-03 13:03 *)
