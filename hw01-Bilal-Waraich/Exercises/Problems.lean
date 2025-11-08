import LeanSearchClient
import Mathlib.Tactic.Linarith

namespace Exercises01

def student_name : String := "Bilal Waraich"

-- From the lecture.
def maximum (n m : Nat) : Nat := if n ≤ m then m else n

-- Exercise 1: 1 point
theorem and_commutes {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro h
  exact ⟨h.right, h.left⟩

-- Exercise 2: 1 point
theorem or_commutes {P Q : Prop} : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  |inl pq =>
    apply Or.inr
    exact pq
  |inr qp =>
    apply Or.inl
    exact qp

-- Exercise 3: 1 point
theorem implication_transitive {P Q R : Prop} : (P → Q) → (Q → R) → (P → R) := by
  intro h1 h2 h3
  have q := h1 h3
  exact h2 q

-- Exercise 4: 1 point
theorem forall_conjunction {P R : Nat → Prop} : (∀ n, P n ∧ R n) → (∀ n, P n) := by
  intro h n
  have meow := h n
  exact meow.left

-- Exercise 5: 2 points
theorem maximum_associative (n m k : Nat) :
  maximum n (maximum m k) = maximum (maximum n m) k := by
  have h : ∀ x y, maximum x y = Nat.max x y := by
    intro x y
    unfold maximum
    rw [← Nat.max_def]
  rw [h n (maximum m k)]
  rw [h m k]
  rw [h n m]
  rw [h (Nat.max n m) k]
  exact (Nat.max_assoc n m k).symm

-- Define the following function.
--
-- `clamp lowerbound upperbound value` should:
-- - return `k` if it is within the bounds,
-- - return `lowerbound` if `k` is below `lowerbound`
-- - return `upperbound` if `k` is above `upperbound`
--
-- If `lowerbound > upperbound`, you may return any value.
--
-- You may use the standard library functions `Nat.min` and `Nat.max`
-- and associated theorems, or reason about `≤` as we did before.

def clamp (lb ub k : Nat) : Nat :=
  Nat.max lb (Nat.min ub k)

-- Exercise 6: 2 points
theorem clamp_within_bounds_is_identity (lb ub k : Nat) :
  lb ≤ k → k ≤ ub → clamp lb ub k = k := by
  intro hlbk hkub
  simp [clamp, Nat.min_eq_right hkub, Nat.max_eq_right hlbk]

-- Exercise 7: 2 points
theorem clamp_below_lower_bound_is_lower_bound (lb ub k : Nat) :
  k ≤ lb → lb ≤ ub → clamp lb ub k = lb := by
  intro hklb hlbub
  have hku := le_trans hklb hlbub
  simp [clamp, Nat.min_eq_right hku, Nat.max_eq_left hklb]

-- Exercise 8: 2 points
theorem clamp_above_upper_bound_is_upper_bound (lb ub k : Nat) :
  ub ≤ k → lb ≤ ub → clamp lb ub k = ub := by
  intro hubk hlbub
  simp [clamp, Nat.min_eq_left hubk, Nat.max_eq_right hlbub]

end Exercises01
