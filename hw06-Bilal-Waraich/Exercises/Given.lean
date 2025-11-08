import Mathlib.Tactic.Linarith

--
-- The main types we work with
--

inductive BinTree (α : Type) where
  | leaf
  | node (a : α) (lst rst : BinTree α)

inductive WithBounds (α : Type) where
  | min
  | el (a : α)
  | max

--
-- Helper types
--

variable {α : Type} [Ord α] [BEq α] [LT α]

inductive BinTreeElem (a : α) : BinTree α → Prop where
  | node_here : BinTreeElem a (.node a lst rst)
  | node_left : BinTreeElem a lst → BinTreeElem a (.node a' lst rst)
  | node_right : BinTreeElem a rst → BinTreeElem a (.node a' lst rst)

inductive WithBounds.LessThan : WithBounds α → WithBounds α → Prop where
  | min_el : LessThan .min (.el a)
  | min_max : LessThan .min .max
  | el_preserved : a < a' → LessThan (.el a) (.el a')
  | el_max : LessThan (.el a) .max

--
-- Typeclasses and helpful stuff for them
--

instance : Membership α (BinTree α) where
  mem t a := BinTreeElem a t

instance : Ord (WithBounds α) where
  compare x y := match x, y with
    | .min, .min => .eq
    | .max, .max => .eq
    | .min, _ => .lt
    | .max, _ => .gt
    | _, .min => .gt
    | _, .max => .lt
    | .el al, .el ar => compare al ar

instance : BEq (WithBounds α) where
  beq x y := compare x y == .eq

instance : LT (WithBounds α) where
  lt := WithBounds.LessThan

def between low (a : α) upp := low < WithBounds.el a ∧ WithBounds.el a < upp

--
-- Algorithms
--

@[reducible] def BinTree.size : BinTree α → ℕ
  | .leaf => 0
  | .node _ lst rst => 1 + lst.size + rst.size

@[reducible] def BinTree.insert (a : α) : BinTree α → BinTree α
  | .leaf => .node a .leaf .leaf
  | .node a' lst rst => match compare a a' with
      | .lt => .node a' (lst.insert a) rst
      | .eq => .node a' lst rst
      | .gt => .node a' lst (rst.insert a)

@[reducible] def BinTree.linear_contains (a : α) : BinTree α → Bool
  | .leaf => false
  | .node a' lst rst => a == a' || lst.linear_contains a || rst.linear_contains a

@[reducible] def BinTree.contains (a : α) : BinTree α → Bool
  | .leaf => false
  | .node a' lst rst => match compare a a' with
      | .lt => lst.contains a
      | .eq => true
      | .gt => rst.contains a

--
-- Properties for reasoning about algorithms
--

inductive BSTNode : WithBounds α → WithBounds α → BinTree α → Prop where
  | leaf : BSTNode low upp .leaf
  | node : BSTNode low (.el a) lst → BSTNode (.el a) upp rst
          → between low a upp
          → BSTNode low upp (.node a lst rst)

def BST (t : BinTree α) : Prop := BSTNode .min .max t
