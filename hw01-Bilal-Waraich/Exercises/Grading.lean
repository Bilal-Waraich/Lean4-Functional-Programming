import Exercises.Autograder
import Exercises.Problems

open Exercises01

def ex01 {P Q : Prop} : P ∧ Q → Q ∧ P := and_commutes
def ex02 {P Q : Prop} : P ∨ Q → Q ∨ P := or_commutes
def ex03 {P Q R : Prop} : (P → Q) → (Q → R) → (P → R) :=  implication_transitive
def ex04 {P R : Nat → Prop} : (∀ n, P n ∧ R n) → (∀ n, P n) :=  forall_conjunction
def ex05 : (n m k : Nat) → maximum n (maximum m k) = maximum (maximum n m) k :=  maximum_associative
def ex06 : (lb ub k : Nat) → lb ≤ k → k ≤ ub → clamp lb ub k = k :=  clamp_within_bounds_is_identity
def ex07 : (lb ub k : Nat) → k ≤ lb → lb ≤ ub → clamp lb ub k = lb :=  clamp_below_lower_bound_is_lower_bound
def ex08 : (lb ub k : Nat) → ub ≤ k → lb ≤ ub → clamp lb ub k = ub :=  clamp_above_upper_bound_is_upper_bound

#eval student_name

#print_grade_results ex01 ex02 ex03 ex04 ex05 ex06 ex07 ex08
