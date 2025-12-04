import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Lemma
import Std.Data.HashMap

-- Note: hashmaps in the standard library are not actually extensional,
-- that is, just because two hashmaps represent the same mapping doesn't
-- mean that they are equal.
--
-- This is because if you construct the same map in two different ways,
-- it may still behave differently with respect to functions like `toList`,
-- for example because of differences with how collisions were handled.
--
-- If you want, you can use this axiom to derive `False` and then "solve"
-- all the exercises like that.
axiom map_ext {m₁ m₂ : Std.HashMap String α}
    : (∀ x : String, m₁[x]? = m₂[x]?) → m₁ = m₂

inductive BinOp where | add | mul | app

mutual
  inductive Value where
    | nat (n : ℕ)
    | closure (x : String) (body : Exp)

  inductive Exp where
    | value (v : Value)
    | const (n : ℕ)
    | var (x : String)
    | binOp (op : BinOp) (lhs rhs : Exp)
    | abs (x : String) (body : Exp)
end

-- Because Exp is mutually recursive, Lean has a hard time doing induction on it directly.
-- Fortunately, defining your own recursor is straightforward.
def Exp.simple_rec.{l} {motive : Exp → Sort l}
     (value_case : ∀ v, motive (.value v))
     (const_case : ∀ n, motive (.const n))
     (var_case : ∀ x, motive (.var x))
     (bin_op_case : ∀ op lhs rhs, motive lhs → motive rhs → motive (.binOp op lhs rhs))
     (abs_case : ∀ x body, motive body → motive (.abs x body))
    : (e : Exp) → motive e := go
where go
  | .value v => value_case v
  | .const n => const_case n
  | .var x => var_case x
  | .binOp op lhs rhs => bin_op_case op lhs rhs (go lhs) (go rhs)
  | .abs x body => abs_case x body (go body)

@[reducible] def Exp.subst (x₀ : String) (v₀ : Value) : Exp → Exp
  | .value v => .value v
  | .const n => .const n
  | .var x => if x == x₀ then .value v₀ else .var x
  | .binOp op lhs rhs => .binOp op (lhs.subst x₀ v₀) (rhs.subst x₀ v₀)
  | .abs x body => if x == x₀
                   then .abs x body
                   else .abs x (body.subst x₀ v₀)

inductive ExCtx1 where
  | binOpLeft (op : BinOp) (rhs : Exp)
  | binOpRight (op : BinOp) (v : Value)

def ExCtx := List ExCtx1
@[reducible] def ExCtx1.fill (e : Exp) : ExCtx1 → Exp
  | .binOpLeft op rhs => .binOp op e rhs
  | .binOpRight op v => .binOp op (.value v) e
@[reducible] def ExCtx.fill (e : Exp) : ExCtx → Exp := List.foldr (flip ExCtx1.fill) e

abbrev Env := Std.HashMap String Value

inductive BinOpStep : BinOp → Value → Value → Exp → Prop
  | add_step : BinOpStep .add (.nat ln) (.nat rn) (.value (.nat (ln + rn)))
  | mul_step : BinOpStep .mul (.nat ln) (.nat rn) (.value (.nat (ln * rn)))
  | app_step (eq : e = body.subst x v) : BinOpStep .app (.closure x body) v e

inductive HeadStep : Exp → Exp → Prop
  | const_step : HeadStep (.const n) (.value (.nat n))
  | bin_op_step : BinOpStep op lv rv e → HeadStep (.binOp op (.value lv) (.value rv)) e
  | abs_step : HeadStep (.abs x body) (.value (.closure x body))

inductive Step : Exp → Exp → Prop
  | ctx_step (ctx : ExCtx) (eq_e₁ : e₁' = ctx.fill e₁) (eq_e₂ : e₂' = ctx.fill e₂)
      : HeadStep e₁ e₂ → Step e₁' e₂'

inductive RTC (R : Exp → Exp → Prop) : Exp → Exp → Prop where
  | trivial : RTC R e e
  | step : R e₁ e₂ → RTC R e₂ e₃ → RTC R e₁ e₃

abbrev Steps := RTC Step

inductive Ty where
  | nat
  | fn (argTy retTy : Ty)

abbrev TyCtx := Std.HashMap String Ty

mutual
  inductive BinOp.TyJdg : BinOp → Ty → Ty → Ty → Prop where
    | add_ty : BinOp.TyJdg .add .nat .nat .nat
    | mul_ty : BinOp.TyJdg .mul .nat .nat .nat
    | app_ty : BinOp.TyJdg .app (.fn argTy retTy) argTy retTy

  inductive Value.TyJdg : Value → Ty → Prop where
    | nat_ty : Value.TyJdg (.nat n) .nat
    | closure_ty
        : Exp.TyJdg {(x, argTy)} body retTy
        → Value.TyJdg (.closure x body) (.fn argTy retTy)

  inductive Exp.TyJdg : TyCtx → Exp → Ty → Prop where
    | value_ty : v.TyJdg ty → Exp.TyJdg Γ (.value v) ty
    | const_ty : Exp.TyJdg Γ (.const n) .nat
    | var_ty : Γ[x]? = some ty → Exp.TyJdg Γ (.var x) ty
    | bin_op_ty
        : BinOp.TyJdg op lhsTy rhsTy ty
        → lhs.TyJdg Γ lhsTy
        → rhs.TyJdg Γ rhsTy
        → Exp.TyJdg Γ (.binOp op lhs rhs) ty
    | abs_ty
        : Exp.TyJdg (Γ.insert x argTy) body retTy
        → Exp.TyJdg Γ (.abs x body) (.fn argTy retTy)
end

-- IsRedex stands for "reducible expression".
-- Here we mean an expression that can have a head step.
--
-- Note that everything that isn't a value is reducible.
inductive IsRedex : Exp → Prop where
  | const : IsRedex (.const n)
  | var : IsRedex (.var x)
  | bin_op : IsRedex (.binOp op (.value v₁) (.value v₂))
  | abs : IsRedex (.abs x body)

-- On the other hand, it's nice to have a predicate for everything that *is* a value.
inductive IsValue : Exp → Prop where
  | value : IsValue (.value v)

-- When we want to take a step, it's nice to be able to split out the part that will step
-- from the context.
-- This predicate states that an expression has such a decomposition,
-- and pattern-matching on it gives you the context and inner expression,
-- and a proof that the inner expression is a redex.
inductive HasDecomposition : Exp → Prop where
  | decomposition (ctx : ExCtx) : e = ctx.fill e' → IsRedex e' → HasDecomposition e

def IsValueOrHasDecompositionOfExp := ∀ e : Exp, IsValue e ∨ HasDecomposition e
def BinOpProgress := ∀ {op tyLhs tyRhs tyOut lhs rhs},
    BinOp.TyJdg op tyLhs tyRhs tyOut
    → Value.TyJdg lhs tyLhs
    → Value.TyJdg rhs tyRhs
    → ∃ e', BinOpStep op lhs rhs e'
def RedexProgress := ∀ {e ty}, e.TyJdg ∅ ty → IsRedex e → ∃ e', HeadStep e e'
def Progress := ∀ {e ty}, e.TyJdg ∅ ty → IsValue e ∨ ∃ e', Step e e'

def SubstPreservation := ∀ v ty e ty' Γ x,
    Value.TyJdg v ty → Exp.TyJdg (Γ.insert x ty) e ty' → Exp.TyJdg Γ (Exp.subst x v e) ty'
def BinOpPreservation := ∀ {op lhsTy rhsTy outTy lhs rhs e'},
    BinOp.TyJdg op lhsTy rhsTy outTy
    → Value.TyJdg lhs lhsTy
    → Value.TyJdg rhs rhsTy
    → BinOpStep op lhs rhs e'
    → Exp.TyJdg ∅ e' outTy
def HeadPreservation := ∀ {e e' ty}, e.TyJdg ∅ ty → HeadStep e e' → e'.TyJdg ∅ ty
def Preservation := ∀ {e e' ty}, e.TyJdg ∅ ty → Step e e' → e'.TyJdg ∅ ty
