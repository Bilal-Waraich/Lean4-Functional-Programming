import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation
import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas
import Exercises.Given

-- Exericse 1 (1 point)
-- Prove that if e₁ can reach e₂ in one step, it can reach e₂ in an unspecified number of steps.
def Steps.single : Step V e₁ e₂ → Steps V e₁ e₂ :=
  fun h => Steps.step h Steps.trivial

-- Define the `Trans` instances below.
-- This isn't an exercise, it just makes your own life easier.
instance : Trans (Steps V) (Steps V) (Steps V) where
  trans ss1 ss2 := by
    induction ss1 with
    | trivial =>
        exact ss2
    | step s rest ih =>
        exact Steps.step s (ih ss2)

instance : Trans (Step V) (Steps V) (Steps V) where
  trans s ss := Steps.step s ss

instance : Trans (Steps V) (Step V) (Steps V) where
  trans ss s := by
    induction ss with
    | trivial =>
        exact Steps.single s
    | step s' rest ih =>
        exact Steps.step s' (ih s)

instance : Trans (Step V) (Step V) (Steps V) where
  trans s1 s2 :=
  Steps.step s1 (Steps.single s2)


-- Define a lemma marked `@[refl]` to allow solving goals of the form `Steps V e e`
-- with the `rfl` tactic.
-- Again, not an exercise, just quality of life.
@[refl]
lemma Steps.reflexive : Steps V e e :=
  Steps.trivial


-- Exercise 2 (1 point)
-- Prove that if we can perform a sequence of reductions, we can also perform it on the left
-- of a binary operator.
lemma op_left_of_steps
    : Steps V e₁ e₁'
    → Steps V (.binOp op e₁ e₂) (.binOp op e₁' e₂) := by
    intro h
    induction h with
    | trivial =>
        exact Steps.trivial
    | step s rest ih =>
        apply Steps.step
        · exact Step.op_left s
        · exact ih

-- Exercise 3 (1 point)
-- Prove that if we can perform a sequence of reductions, we can also perform it on the right
-- of a binary operator, provided the left side is a constant.
lemma op_right_of_steps
    : Steps V e₂ e₂'
    → Steps V (.binOp op (.const lk) e₂) (.binOp op (.const lk) e₂') := by
    intro h
    induction h with
    | trivial =>
        exact Steps.trivial
    | step s rest ih =>
        apply Steps.step
        · exact Step.op_right s
        · exact ih

-- Exercise 4 (3 points)
-- Prove that the evaluation result does not change when we take a step.
lemma eval_eq_under_step
    : Step V e₁ e₂ → e₁.eval V = e₂.eval V := by
    intro step
    induction step
    case var_step x k h =>
      simp [Exp.eval, h]
    case op_step op lk rk k h =>
      simp [Exp.eval, h]
    case op_left e₁ e₂ op e₁' _ IH =>
      simp [Exp.eval, IH]
    case op_right op lk e₂ e₂' _ IH =>
      simp [Exp.eval, IH]

-- Exercise 5 (3 points)
-- In the lecture, we discussed that you could not use induction immediately in
-- the proof of `eval_eq_some_of_steps`, and instead had to generalize.
-- We can avoid that by defining a different recursor, which we can th
theorem Steps.rec_first {motive : Env → Exp → Prop}
    (trivial_case : motive V ef)
    (step_case : ∀ ea eb, Step V ea eb → Steps V eb ef → motive V eb → motive V ea)
    : Steps V e ef → motive V e := by
    intro h
    induction h with
    | trivial =>
        exact trivial_case
    | step step_ab steps_bc ih =>
        apply step_case
        · exact step_ab
        · exact steps_bc
        · exact ih trivial_case step_case

-- Exercise 6 (1 point)
-- Prove the theorem again, this time less painfully thanks to the new recursor.
theorem eval_eq_some_of_steps {V : Env}
    : Steps V e (.const n) → e.eval V = some n := by
  apply Steps.rec_first
  case trivial_case =>
    simp [Exp.eval]

  case step_case =>
    intro ea eb hStep _ IH
    have := eval_eq_under_step (V := V) (e₁ := ea) (e₂ := eb) hStep
    simpa [this] using IH

-- Exercise 7 (1 point)
-- Prove that if a binary operation evaluates to a value, then so does its left-hand side.
lemma lhs_eval_eq_some_of_eval_eq_some
    : (Exp.binOp op lhs rhs).eval V = some n → ∃ lk, lhs.eval V = some lk := by
    intro eval_eq
    simp [Exp.eval] at eval_eq
    cases lhs_eval : lhs.eval V
    case none =>
      simp [lhs_eval] at eval_eq
    case some k =>
      exists k

-- Exercise 8 (1 point)
-- Prove that if a binary operation evaluates to a value, then so does its right-hand side.
lemma rhs_eval_eq_some_of_eval_eq_some
    : (Exp.binOp op lhs rhs).eval V = some n → ∃ rk, rhs.eval V = some rk := by
    intro h
    simp [Exp.eval] at h
    cases hR : rhs.eval V with
    | none =>
        simp [hR] at h
    | some k =>
        exists k

-- Exercise 9 (2 points)
-- Prove that if an expression evaluates to some n, then it also steps to n.
-- Note that we proved a similar thing in the lecture, so you can just adapt that proof.
theorem steps_of_eval_eq_some {V : Env}
    : e.eval V = some n → Steps V e (.const n) := by
    intro eval_eq
    induction e generalizing n
    case const k =>
      simp [Exp.eval] at eval_eq
      cases eval_eq
      constructor
    case var x =>
      apply Steps.single
      constructor
      simpa using eval_eq
    case binOp op lhs rhs lIH rIH =>
      have ⟨lk, lsteps⟩ := lhs_eval_eq_some_of_eval_eq_some eval_eq
      have ⟨rk, rsteps⟩ := rhs_eval_eq_some_of_eval_eq_some eval_eq
      calc Steps V _ (.binOp op (.const lk) rhs) := by
              apply op_left_of_steps
              apply lIH
              exact lsteps
          Steps V _ (.binOp op (.const lk) (.const rk)) := by
              apply op_right_of_steps
              apply rIH
              exact rsteps
          Step V _ _ := by
              constructor
              simp [Exp.eval, lsteps, rsteps] at eval_eq
              rw [eval_eq]

-- Exercise 10 (2 points)
-- Prove that if e steps to two results, they are equal.
theorem determinism
    : Steps V e (.const n1) → Steps V e (.const n2)
    → n1 = n2 := by
    intro steps1 steps2
    have eq1 : e.eval V = some n1 :=
      eval_eq_some_of_steps (V := V) (e := e) (n := n1) steps1
    have eq2 : e.eval V = some n2 :=
      eval_eq_some_of_steps (V := V) (e := e) (n := n2) steps2
    rw [eq1] at eq2
    injection eq2


inductive OnlyVars (vars : List String) : Exp → Prop where
  | const : OnlyVars vars (.const n)
  | var : x ∈ vars → OnlyVars vars (.var x)
  | bin_op : OnlyVars vars lhs → OnlyVars vars rhs
        → OnlyVars vars (lhs.binOp op rhs)

def ContainsAll (vars : List String) (V : Env) := ∀ v, v ∈ vars → v ∈ V

-- Exercise 11 (2 points)
-- Prove that if e contains only variables from vars, and vars is a subset of vars',
-- then e contains only variables from vars'.
lemma weaken
    : (∀ x, x ∈ vars → x ∈ vars') → OnlyVars vars e → OnlyVars vars' e := by
    intro subset onlyVars
    induction onlyVars
    case const n =>
      constructor
    case var x h =>
      constructor
      apply subset
      assumption
    case bin_op op lhs rhs lv rv lIH rIH =>
      constructor
      · apply lIH
      · apply rIH

-- Exercise 12 (4 points)
-- Prove that every expression with variables from vars, in an environment where all vars
-- are present, evaluates to a result.
theorem totality
    : OnlyVars vars e → ContainsAll vars V
    → ∃ k, Steps V e (.const k) := by
    intro onlyVars containsAll
    induction e
    case const n =>
      exists n
    case var x =>
      cases onlyVars
      rename_i h
      have := containsAll x h
      exists V[x]
      apply Steps.single
      constructor
      apply Std.HashMap.getElem?_eq_some_getElem
    case binOp op lhs rhs lIH rIH =>
      cases onlyVars
      rename_i lv rv
      have ⟨lk, lsteps⟩ := lIH lv
      have ⟨rk, rsteps⟩ := rIH rv
      exists op.eval lk rk
      calc Steps V _ (.binOp op (.const lk) rhs) := by
              apply op_left_of_steps
              exact lsteps
          Steps V _ (.binOp op (.const lk) (.const rk)) := by
              apply op_right_of_steps
              exact rsteps
          Step V _ _ := by
              constructor
              rfl
