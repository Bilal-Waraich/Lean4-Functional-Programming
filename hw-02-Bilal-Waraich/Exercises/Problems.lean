import LeanSearchClient.Basic
import Mathlib.Tactic.Linarith
import Exercises.Given

def student_name: String := "Bilal Waraich"

-- Define a function that takes n and returns the sum 1 + ... + n
def triangle : ℕ → ℕ
    | 0 => 0
    | (n+1) => (n+1) + triangle (n)

-- Exercise 1: 2 points
theorem triangle_closed_form (n : ℕ) : 2 * triangle n = n * (n + 1) := by
    induction n with
    | zero => simp [triangle]
    | succ =>
        simp [triangle]
        linarith

-- Exercise 2: 2 point
-- Hint: The function iota is defined in Given.lean.
theorem iota_length (n : ℕ) : (iota n).length = n + 1 := by
    induction n with
    | zero => simp [iota]
    | succ =>
        simp [iota]
        linarith

-- Define a function that takes the sum of a list.
-- You may use the standard library or write it by hand.
def sum : List ℕ → ℕ
    | [] => 0
    | x :: xs => x + sum xs

-- Exercise 3: 1 point
theorem sum_iota_triangle (n : Nat) : sum (iota n) = triangle n := by
    induction n with
    | zero =>
        simp [triangle]
        simp [iota]
        simp [sum]
    | succ n n_ih =>
        simp [iota , sum]
        rw[n_ih]
        rfl

def Exp.eval : Exp → ℕ
    | Exp.nat n     => n
    | Exp.plus e₁ e₂  => e₁.eval + e₂.eval
    | Exp.times e₁ e₂ => e₁.eval * e₂.eval

-- Exercise 4: 2 points
-- These three theorems are one exercise.
theorem Exp.eval_nat (n : Nat) : (nat n).eval = n := by
    rfl

theorem Exp.eval_plus {e₁ e₂ : Exp} :
    e₁.eval = n₁ → e₂.eval = n₂ → (plus e₁ e₂).eval = n₁ + n₂ := by
    intro h₁ h₂
    simp [eval]
    rw[h₁]
    rw[h₂]

theorem Exp.eval_times {e₁ e₂ : Exp} :
    e₁.eval = n₁ → e₂.eval = n₂ → (times e₁ e₂).eval = n₁ * n₂ := by
    intro h₁ h₂
    simp [eval]
    rw [h₁ , h₂]

-- Define a function that takes an expression and returns an equivalent polynomial,
-- i.e. a sum of products of natural numbers.
def Exp.to_polynomial : Exp → Exp
    | e => Exp.nat (e.eval)

    -- i gave up but had to cheese because exercise 6 didnt work
    -- | Exp.nat n     => Exp.nat n
    -- | Exp.plus e₁ e₂ => Exp.plus e₁.to_polynomial e₂.to_polynomial
    -- | Exp.times e₁ e₂ => Exp.times e₁.to_polynomial e₂.to_polynomial

-- Exercise 5: 1 point
-- It is possible to cheese this exercise by defining `e.to_polynomial = e.eval.nat`.
-- We won't punish you for doing so, but you also won't learn much. :)
theorem to_polynomial_correct {e : Exp} : e.to_polynomial.eval = e.eval := by
    simp [Exp.to_polynomial, Exp.eval]

    -- i tried but had to cheese
    -- induction e with
    -- | nat n => simp [Exp.to_polynomial,  Exp.eval]
    -- | plus e₁ e₂ ih₁ ih₂ => simp [Exp.to_polynomial, Exp.eval, ih₁, ih₂]
    -- | times e₁ e₂ ih₁ ih₂ => simp [Exp.to_polynomial, Exp.eval, ih₁, ih₂]

-- Exercise 6: 1 point

theorem to_polynomial_is_polynomial {e : Exp} : e.to_polynomial.is_polynomial := by
    simp [Exp.to_polynomial, Exp.is_polynomial]
