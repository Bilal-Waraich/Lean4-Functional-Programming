import Exercises.Problems
import Exercises.Autograder

def ex01 : Step V e₁ e₂ → Steps V e₁ e₂ := Steps.single
def ex02 : Steps V e₁ e₁' → Steps V (.binOp op e₁ e₂) (.binOp op e₁' e₂) := op_left_of_steps
def ex03 : Steps V e₂ e₂' → Steps V (.binOp op (.const lk) e₂) (.binOp op (.const lk) e₂') := op_right_of_steps
def ex04 : Step V e₁ e₂ → e₁.eval V = e₂.eval V := eval_eq_under_step
def ex05 : {motive : Env → Exp → Prop} → (trivial_case : motive V ef) → (step_case : ∀ ea eb, Step V ea eb → Steps V eb ef → motive V eb → motive V ea) → Steps V e ef → motive V e := Steps.rec_first
def ex06 : {V : Env} → Steps V e (.const n) → e.eval V = some n := eval_eq_some_of_steps
def ex07 : (Exp.binOp op lhs rhs).eval V = some n → ∃ lk, lhs.eval V = some lk := lhs_eval_eq_some_of_eval_eq_some
def ex08 : (Exp.binOp op lhs rhs).eval V = some n → ∃ rk, rhs.eval V = some rk := rhs_eval_eq_some_of_eval_eq_some
def ex09 : {V : Env} → e.eval V = some n → Steps V e (.const n) := steps_of_eval_eq_some
def ex10 : Steps V e (.const n1) → Steps V e (.const n2) → n1 = n2 := determinism
def ex11 : (∀ x, x ∈ vars → x ∈ vars') → OnlyVars vars e → OnlyVars vars' e := weaken
def ex12 : OnlyVars vars e → ContainsAll vars V → ∃ k, Steps V e (.const k) := totality

#print_grade_results ex01 ex02 ex03 ex04 ex05 ex06 ex07 ex08 ex09 ex10 ex11 ex12
