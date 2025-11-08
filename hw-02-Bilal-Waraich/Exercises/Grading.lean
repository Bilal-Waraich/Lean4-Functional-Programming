import Exercises.Autograder
import Exercises.Problems
import Exercises.Given

open Exp

theorem ex01 : (n : ℕ) → 2 * triangle n = n * (n + 1) := triangle_closed_form
theorem ex02 : (n : ℕ) → (iota n).length = n + 1 := iota_length
theorem ex03 : (n : ℕ) → sum (iota n) = triangle n := sum_iota_triangle
theorem ex04a : (n : Nat) → (nat n).eval = n := Exp.eval_nat
theorem ex04b : {n₁ n₂ : ℕ} → {e₁ e₂ : Exp} → e₁.eval = n₁ → e₂.eval = n₂ → (plus e₁ e₂).eval = n₁ + n₂ := Exp.eval_plus
theorem ex04c : {n₁ n₂ : ℕ} → {e₁ e₂ : Exp} → e₁.eval = n₁ → e₂.eval = n₂ → (times e₁ e₂).eval = n₁ * n₂ := Exp.eval_times
theorem ex05 : {e : Exp} → e.to_polynomial.eval = e.eval := to_polynomial_correct
theorem ex06 : {e : Exp} → e.to_polynomial.is_polynomial := to_polynomial_is_polynomial

#eval student_name

#print_grade_results ex01 ex02 ex03 ex04a ex04b ex04c ex05 ex06
