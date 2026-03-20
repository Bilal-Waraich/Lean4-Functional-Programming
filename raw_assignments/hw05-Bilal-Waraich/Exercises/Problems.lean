import Mathlib.Tactic.Linarith
import Exercises.Given

def InterpState (m : Type → Type) σ α := σ → m (α × σ)
-- In the lecture, we defined InterpFail, that took a monad and added the possibility
-- of failure (by returning an Option α instead of an α).
-- InterpThrow should be similar, but the failure case should also carry information ε.
def InterpThrow (m : Type → Type) ε α := ε → m (Except ε α)

-- In the lecture, we used IO for output.  However, there is another possibliity:
-- we can have a monad that tracks the outputs produced so far.
-- We could use State for this, but that is overkill, since we don't need to be
-- able to modify the outputs after we've procuded them.
-- InterpWriter should be a monad that allows one to write messages of type μ.
def InterpWriter (m : Type → Type) μ α := m (α × List μ)

instance [Monad m] : Monad (InterpState m σ) where
  pure a := fun s => pure ⟨ a, s ⟩
  bind isa f := fun s => do
    let ⟨ a, s' ⟩ ← isa s
    f a s'

-- Define a monad instance for InterpThrow.
instance [Monad m] : Monad (InterpThrow m ε) where
  pure a := fun _ => pure (Except.ok a)
  bind ita f := fun err => do
    match ← ita err with
    | Except.error e => pure (Except.error e)
    | Except.ok a => f a err

-- Define a monad instance for InterpWriter.
instance [Monad m] : Monad (InterpWriter m μ) where
  pure a := (pure (a, []) : m (_ × List μ))
  bind iwa f :=  (do
    let (a, w₁) ← (iwa  : m (_ × List μ))
    let (b, w₂) ← (f a : m (_ × List μ))
    pure (b, w₁ ++ w₂) : m (_ × List μ)
  )

-- Implement functions to use m actions in InterpThrow m ε α and InterpWriter m μ α.
def liftState [Monad m] (act : m α) : InterpState m σ α := fun s => do pure ⟨ ←act, s ⟩
def liftThrow [Monad m] (act : m α) : InterpThrow m ε α :=
  fun _ => do
    let a ← act
    pure (Except.ok a)

def liftWriter [Monad m] (act : m α) : InterpWriter m μ α := (do
    let a ← act
    pure (a, ([] : List μ))
  : m (α × List μ))

def get [Monad m] : InterpState m σ σ := fun s => pure ⟨ s , s ⟩
def put [Monad m] (new_s : σ) : InterpState m σ Unit := fun _ => pure ⟨ ⟨⟩, new_s ⟩
def modify' [Monad m] (f : σ → σ) : InterpState m σ Unit := do
  let V <- get
  put $ f V

-- Implement functions for working with InterpThrow and InterpWriter.
def throw [Monad m] (e : ε) : InterpThrow m ε α :=
  fun _ => pure (Except.error e)

def write [Monad m] (msg : μ) : InterpWriter m μ Unit :=
  (Pure.pure (⟨⟩, [msg]) : m (Unit × List μ))


abbrev Env := Std.HashMap String Value
abbrev Interp := InterpState (InterpThrow (InterpWriter Id Value) RuntimeError)

-- Implement a function for interpreting try-catch.
-- Hint: you are working with a structure with multiple monads stacked on top of each other.  You can use
-- type annotations to control how much of that stack you add with `pure` / unfold with `bind`, but you
-- can also work on the structure directly.
def recover (interp_try : Interp σ α) (interp_catch : RuntimeError → Interp σ α): Interp σ α :=
  fun s err => do
    let r ← interp_try s err
    match r with
    | Except.ok (a, s') => pure (Except.ok (a, s'))
    | Except.error e    => interp_catch e s err


def BinOp.eval : BinOp → Value → Value → Interp Env Value
  | add, .nat n, .nat m => pure $ .nat (n + m)
  | mul, .nat n, .nat m => pure $ .nat (n * m)
  | sub, .nat n, .nat m => pure $ .nat (n - m)
  | eq, .bool b, .bool c => pure $ .bool (b = c)
  | eq, .nat n, .nat m => pure $ .bool (n = m)
  | lt, .nat n, .nat m => pure $ .bool (n < m)
  | le, .nat n, .nat m => pure $ .bool (n ≤ m)
  | op, lhs, rhs => liftState $ throw $ .invalid_operands op lhs rhs

mutual
  partial def Exp.eval : Exp → Interp Env Value
    | .const value => pure value
    | .var name => do
        let V ← get
        match V[name]? with
        | some v => pure v
        | none => liftState $ throw $ .unknown_variable name
    | .bin_op op e₁ e₂ => do
        let v₁ ← e₁.eval
        let v₂ ← e₂.eval
        op.eval v₁ v₂
    | .ifthenelse ec et ee => do
        let c ← ec.eval
        match c with
        | .bool true => et.eval
        | .bool false => ee.eval
        | v => liftState $ throw $ .expected_boolean v
    | .with_stmt stmt result => do
        stmt.eval
        result.eval

  partial def runWhile (ec : Exp) (body : Stmt) : Interp Env Unit := do
    let c ← ec.eval
    match c with
    | .bool true =>
        body.eval
        runWhile ec body
    | .bool false => pure ⟨⟩
    | v => liftState $ throw $ .expected_boolean v


  partial def Stmt.eval : Stmt → Interp Env Unit
    | .exp_stmt e => do
        let _ ← e.eval
        pure ⟨⟩
    | .assignment name e => do
        let v ← e.eval
        modify' fun V => V.insert name v
    | .while ec body => do
        runWhile ec body
    | .try_catch tb cb => recover tb.eval (fun e => (cb e).eval)
    | .print e => do liftState $ liftThrow $ write (←e.eval)
    | .stmt_block stmts => do
        forM stmts Stmt.eval
end

-- Implement a helper function for running a program and getting its outputs.
-- Note: even if the program ends up throwing an exception, things it has
-- output before that point should be maintained!
def runProgram (stmt : Stmt) : List Value :=
  let s0    : Env := {}
  let dummy : RuntimeError := .unknown_variable "<init>"
  let (_r, out) := (Stmt.eval stmt) s0 dummy
  out
