import Exercises.Problems
import Exercises.Autograder

def ex01 : IsValueOrHasDecompositionOfExp := ex_is_value_or_has_decomposition_of_exp
def ex02 : BinOpProgress := ex_bin_op_progress
def ex03 : BinOpProgress → RedexProgress := ex_redex_progress
def ex04 : IsValueOrHasDecompositionOfExp → RedexProgress → Progress := ex_progress
def ex05 : SubstPreservation := ex_subst_preservation
def ex06 : SubstPreservation → BinOpPreservation := ex_bin_op_preservation
def ex07 : BinOpPreservation → HeadPreservation := ex_head_preservation
def ex08 : HeadPreservation → Preservation := ex_preservation

#print_grade_results ex01 ex02 ex03 ex04 ex05 ex06 ex07 ex08
