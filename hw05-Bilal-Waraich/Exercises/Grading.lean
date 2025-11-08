import Exercises.Autograder
import Exercises.Problems
import Exercises.Given

open Value
open Exp
open Stmt
open BinOp
infix:50 "::=" => assignment
infix:60 "=ⁱ" => bin_op eq
infix:60 "<ⁱ" => bin_op lt
infix:60 "≤ⁱ" => bin_op le
infix:70 "+ⁱ" => bin_op add
infix:70 "-ⁱ" => bin_op sub
infix:75 "*ⁱ" => bin_op mul
def simple_example : Stmt := .print (↑5 +ⁱ ↑5 ≤ⁱ ↑20)
def unknown_var : Stmt := ↑5 +ⁱ "unknown"
def bad_op : Stmt := ↑5 +ⁱ ↑true
def to_error_code : RuntimeError → ℕ
  | .unknown_variable _ => 0
  | .invalid_operands _ _ _ => 1
  | .expected_boolean _ => 2
def identify_mistake (bad_code : Stmt) : Stmt := [
  Stmt.try_catch
    bad_code
    fun e => "error_code" ::= to_error_code e,
  Stmt.print "error_code"
]
def run_fail_then_run_more : Stmt := [
  Stmt.try_catch [
    Stmt.print 5,
    Stmt.print "x",
  ]
  fun _ => Stmt.print 10,
]

-- 2 points
#eval exercise "01" (runProgram simple_example) [Value.bool true]
-- 1 point
#eval exercise "02" (runProgram $ identify_mistake unknown_var) [Value.nat 0]
-- 1 point
#eval exercise "03" (runProgram $ identify_mistake bad_op) [Value.nat 1]
-- 3 points
#eval exercise "04" (runProgram run_fail_then_run_more) [Value.nat 5, Value.nat 10]
