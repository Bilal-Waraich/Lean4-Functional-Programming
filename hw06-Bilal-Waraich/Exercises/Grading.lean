import Exercises.Given
import Exercises.Problems
import Exercises.Autograder

def ex01 [ValidElemType α] {a : α} {t : BinTree α} : BSTNode low upp t → between low a upp → BSTNode low upp (t.insert a) := insert_preserves_BST
def ex02 [Ord β] {t : BinTree β} : DepthBound k t → DepthBound (k+1) (t.insert a) := insert_depth_increase_bounded
def ex03 {t : BinTree β} : DepthBound k t → t.size < 2 ^ k := depth_bounds_size
def ex04 [Inhabited β] {k : ℕ} : ∃ (t : BinTree β), t.size + 1 = 2^k ∧ DepthBound k t := depth_bound_is_strict
def ex05 [ValidElemType α] {a : α} {t : BinTree α} : t.contains a = true → t.linear_contains a = true := linear_contains_finds_if_contains_finds
def ex06 : ValidElemType ℕ := instVET_for_Nat

#print_grade_results ex01 ex02 ex03 ex04 ex05 ex06
