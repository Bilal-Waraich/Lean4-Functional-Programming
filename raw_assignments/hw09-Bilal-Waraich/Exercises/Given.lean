import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation
import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas


inductive BinOp where | add | mul

inductive Exp where
  | const (n : ℕ)
  | var (x : String)
  | binOp (op : BinOp) (lhs rhs : Exp)

abbrev Env := Std.HashMap String ℕ

@[reducible]
def BinOp.eval (v1 v2 : ℕ) : BinOp → ℕ
  | .add => v1 + v2
  | .mul => v1 * v2

@[reducible]
def Exp.eval (V : Env) : Exp → Option ℕ
  | .const n => some n
  | .var x => V[x]?
  | .binOp op lhs rhs => do
      let v1 ← lhs.eval V
      let v2 ← rhs.eval V
      pure $ op.eval v1 v2

-- Step V e1 e2: e1 can take one step to reach e2
inductive Step (V : Env) : Exp → Exp → Prop where
  | var_step : V[x]? = some k → Step V (.var x) (.const k)
  | op_step : k = op.eval lk rk → Step V (.binOp op (.const lk) (.const rk)) (.const k)
  | op_left : Step V e₁ e₁'
             → Step V (.binOp op e₁ e₂) (.binOp op e₁' e₂)
  | op_right : Step V e₂ e₂'
              → Step V (.binOp op (.const lk) e₂) (.binOp op (.const lk) e₂')

inductive Steps V : Exp → Exp → Prop where
  | trivial : Steps V e e
  | step : Step V e₁ e₂ → Steps V e₂ e₃ → Steps V e₁ e₃
