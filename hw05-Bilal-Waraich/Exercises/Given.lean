import Mathlib.Tactic.Linarith

inductive BinOp where
  | add | mul | sub | eq | lt | le
deriving instance Repr for BinOp

inductive Value where
  | nat (n : ℕ)
  | bool (b : Bool)
deriving instance Repr for Value
deriving instance DecidableEq for Value

inductive RuntimeError where
  | unknown_variable (name: String)
  | invalid_operands (op : BinOp) (v₁ v₂ : Value)
  | expected_boolean (unexpected_value : Value)

-- This allows us to use natural numbers and booleans as values.
instance : Coe ℕ Value where
  coe := .nat
instance : OfNat Value n where
  ofNat := .nat n
instance : Coe Bool Value where
  coe := .bool

instance : ToString Value where
  toString v := match v with
    | .nat n => toString n
    | .bool b => toString b

instance : Inhabited Value where
  default := .nat 0

mutual
  inductive Exp where
    | const (value : Value)
    | var (name : String)
    | bin_op (op : BinOp) (e₁ e₂ : Exp)
    | ifthenelse (ec et ee : Exp)
    | with_stmt (stmt : Stmt) (result : Exp)

  inductive Stmt where
    | exp_stmt (e : Exp)
    | assignment (name : String) (e : Exp) -- name = e
    | while (ec : Exp) (body : Stmt)
    | try_catch (try_body : Stmt) (catch_body : RuntimeError → Stmt)
    | print (e : Exp)
    | stmt_block (stmts : List Stmt)
end

-- Similar from Value to Exp and Exp to Stmt
instance : Coe Value Exp where
  coe := .const
instance : OfNat Exp n where
  ofNat := .const n
instance : Coe Exp Stmt where
  coe := .exp_stmt
-- And for variables
instance : Coe String Exp where
  coe := .var
-- And let's make blocks easier to work with
instance : Coe (List Stmt) Stmt where
  coe := .stmt_block
