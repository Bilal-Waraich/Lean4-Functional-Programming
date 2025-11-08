import Mathlib.Tactic.Linarith

def iota : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => (k + 1) :: iota k

inductive Exp : Type where
  | nat : ℕ → Exp
  | plus : Exp → Exp → Exp
  | times : Exp → Exp → Exp

def Exp.is_monomial : Exp → Prop
  | nat _ => True
  | plus _ _ => False
  | times e₁ e₂ => e₁.is_monomial ∧ e₂.is_monomial

def Exp.is_polynomial : Exp → Prop
  | nat _ => True
  | plus e₁ e₂ => e₁.is_polynomial ∧ e₂.is_polynomial
  | times e₁ e₂ => e₁.is_monomial ∧ e₂.is_monomial
