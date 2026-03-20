import Lean.Elab

open Lean Elab Command

-- Grading Command

def allowedAxioms : List Name := [
  `Classical.choice, `propext, `funext, `Quot.sound, `proof_irrel, `subsingleton.elim
]

syntax (name := printGradeResults) "#print_grade_results" ident* : command
elab_rules : command
| `(command | #print_grade_results $ids*) => do
  println! "Results:"
  for id in ids do
    let cs ← liftCoreM <| realizeGlobalConstWithInfos id
    let axioms ← cs.flatMapM (collectAxioms >=> (pure ∘ Array.toList))
    let restricted := axioms.filter λ n => not (allowedAxioms.contains n)
    let report := if restricted.isEmpty then "solved"
                  else s!"unsolved (prohibited axioms: {restricted})"
    println! s!"{id}: {report}"

def exercise [DecidableEq α] (ex : String) (actual expected : α) : String :=
  let result := if expected = actual then "solved" else "unsolved"
  s!"ex{ex}: {result}"

def exerciseIn [DecidableEq α] (ex : String) (actual : α) (expected : List α) : String :=
  let result := if actual ∈ expected then "solved" else "unsolved"
  s!"ex{ex}: {result}"
