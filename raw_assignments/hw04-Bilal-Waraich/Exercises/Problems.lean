import Mathlib.Tactic.Linarith
import Mathlib.Control.Traversable.Basic
import Mathlib.Data.List.Monad
import Exercises.Given

-- See the Given.lean file for some more explanation.

-- Implement a parser that always fails.
def fail : Parser σ α :=
  λ _ => []

-- Implement a parser that gets the first α from the input.
def single α : Parser (List α) α :=
  fun s =>
    match s with
    | []      => []
    | x :: xs => [(x, xs)]

-- Implement a function that takes a parser, and only allows results that satisfy
-- the predicate pred.
def constrain (pred : α → Bool) (p : Parser σ α) : Parser σ α :=
  fun s => (p s).filter (fun (a, _) => pred a)

-- Implement a parser that succeeds, if the input is a specific symbol.
def symbol [DecidableEq α] (a : α) : Parser (List α) α :=
  fun s =>
  match s with
  | [] => []
  | x :: xs => if x = a then [(x, xs)] else []

-- Implement a parser that matches the end of the string (i.e. that succeeds
def endOfString : Parser (List α) Unit :=
  fun s =>
  match s with
  | [] => [((), [])]
  | _ :: _ => []

def Parser.map (f : α → β) (p : Parser σ α) : Parser σ β :=
  fun s =>
  p s |>.map (λ (x , y) => (f x , y))

def Parser.pure (a : α): Parser σ α :=
  fun s => [(a , s)]

def Parser.seq (pf : Parser σ (α → β)) (px : Unit → Parser σ α) : Parser σ β :=
  fun s =>
    let fs := pf s
    let lists :=
      List.map (fun ⟨f, s1⟩ =>
        List.map (fun ⟨x, s2⟩ => (f x, s2)) (px () s1)
      ) fs
    List.foldr (· ++ ·) [] lists

def Parser.bind (pa : Parser σ α) (f : α → Parser σ β) : Parser σ β :=
  fun s =>
    let branches :=
      (pa s).map (fun ⟨a, s1⟩ => f a s1)
    List.foldr (· ++ ·) [] branches

instance : Functor (Parser σ) where
  map := Parser.map

instance : Applicative (Parser σ) where
  pure := Parser.pure
  seq := Parser.seq

instance : Monad (Parser σ) where
  bind := Parser.bind

-- Implement a function that takes two parsers and provides the results of both.
def Parser.or (p1 p2 : Parser σ α) : Parser σ α :=
  fun s => (p1 s) ++ (p2 s)

-- Implement a function that takes a list of parsers and provides the result of any that succeed.
def choice (ps : List (Parser σ α)) : Parser σ α :=
  fun s =>
    let results := ps.map (fun p => p s)
    List.foldr (· ++ ·) [] results

-- Implement a function that takes a parser, and applies it zero or more times in sequence.
-- You probably want this parser to be greedy, though other solutions are possible.
-- If you go for a non-greedy approach, consider implementing `peek : Parser (List α) (Option α)`
-- that returns the next element (if any) without consuming it.
partial def Parser.many (p : Parser σ α) : Parser σ (List α) :=
  fun s =>
    let results := p s
    if results.isEmpty then
      [([], s)]
    else
      results.foldl
        (fun acc (a_s : α × σ) =>
          let (a, s₁) := a_s
          let tails := Parser.many p s₁
          let mapped := tails.map (fun (as, s₂) => (a :: as, s₂))
          acc ++ mapped)
        []

-- Hint.
def Parser.sequence : List (Parser σ α) → Parser σ (List α) := _root_.sequence

-- Implement a parser that accepts the string "hello"
-- 2 points
def hello : Parser (List Char) String := do
  let _ ← symbol 'h'
  let _ ← symbol 'e'
  let _ ← symbol 'l'
  let _ ← symbol 'l'
  let _ ← symbol 'o'
  pure "hello"

-- Implement a parser that parses natural numbers.
-- 3 points
def natural : Parser (List Char) ℕ := do
  let digitVal : Parser (List Char) ℕ :=
    choice [
      (do let _ ← symbol '0'; pure 0),
      (do let _ ← symbol '1'; pure 1),
      (do let _ ← symbol '2'; pure 2),
      (do let _ ← symbol '3'; pure 3),
      (do let _ ← symbol '4'; pure 4),
      (do let _ ← symbol '5'; pure 5),
      (do let _ ← symbol '6'; pure 6),
      (do let _ ← symbol '7'; pure 7),
      (do let _ ← symbol '8'; pure 8),
      (do let _ ← symbol '9'; pure 9)
    ]
  let ds ← Parser.many digitVal
  if ds.isEmpty then
    (fail : Parser (List Char) ℕ)
  else
    pure <| ds.foldl (fun acc d => acc * 10 + d) 0

-- This should work as is.
-- 2 points
def natural_pair : Parser (List Char) (ℕ × ℕ) := do
  let n1 <- natural
  let _ <- symbol ' '
  let n2 <- natural
  pure ⟨ n1 , n2 ⟩

-- Implement a parser for addition and subtraction expressions
-- 3 points
def arithExpr : Parser (List Char) ℕ := do
  let spaces : Parser (List Char) Unit := do
    let _ ← Parser.many (symbol ' ')
    pure ()

  let digitVal : Parser (List Char) ℕ :=
    choice [
      (do let _ ← symbol '0'; pure 0),
      (do let _ ← symbol '1'; pure 1),
      (do let _ ← symbol '2'; pure 2),
      (do let _ ← symbol '3'; pure 3),
      (do let _ ← symbol '4'; pure 4),
      (do let _ ← symbol '5'; pure 5),
      (do let _ ← symbol '6'; pure 6),
      (do let _ ← symbol '7'; pure 7),
      (do let _ ← symbol '8'; pure 8),
      (do let _ ← symbol '9'; pure 9)
    ]
  let naturalHere : Parser (List Char) ℕ := do
    let ds ← Parser.many digitVal
    if ds.isEmpty then (fail : Parser (List Char) ℕ)
    else pure <| ds.foldl (fun acc d => acc * 10 + d) 0

  let _ ← spaces
  let init ← naturalHere
  let tail ← Parser.many (do
    let _ ← spaces
    let op ←
      (do let _ ← symbol '+'; pure (fun (a b : ℕ) => a + b))
      |> Parser.or
      (do let _ ← symbol '-'; pure (fun (a b : ℕ) => a - b))
    let _ ← spaces
    let n ← naturalHere
    pure (op, n))
  pure (tail.foldl (fun acc (op, n) => op acc n) init)
