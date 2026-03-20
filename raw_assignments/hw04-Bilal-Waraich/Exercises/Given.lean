import Mathlib.Tactic.Linarith

-- In this exercise, we will look into how you can do parsing in Lean.
-- That is, we'll develop tools to turn strings into structured data.

-- Parser σ α is a parser that consumes a σ and turns it into an α.
-- Usually, σ will be String or List Char, while α may be any data.
--
-- Under the hood, a Parser σ α produces list of possible parses,
-- where each parse consists of a result α and a remainder of the input σ.
def Parser σ α := σ → List (α × σ)

-- When we run the parser, we take the first valid parse.
-- Note that the string may not yet be empty!
def runParser (p : Parser σ α) (s : σ) : Option α := (p s).head?.map (·.1)

def overFst (f : α → β) : α × γ → β × γ
  | ⟨ a, c ⟩ => ⟨ f a, c ⟩
def overSnd (f : α → β) : γ × α → γ × β
  | ⟨ c, a ⟩ => ⟨ c, f a ⟩

def Parser.ofListCharParser (p : Parser (List Char) α) : Parser String α :=
  fun s => (p s.toList).map (overSnd (·.toString))
