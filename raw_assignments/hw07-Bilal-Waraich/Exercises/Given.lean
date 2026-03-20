import Mathlib.Tactic.Linarith

namespace Structures
structure Triple α β γ where
  alpha : α
  beta : β
  gamma : γ
end Structures

namespace Inductive
inductive Funky (α β γ : Prop) : Prop where
  | alpha_beta (a : α) (b : β)
  | beta_gamma (b : β) (c : γ)

inductive ImplSeq : Prop → Prop → Prop where
  | id : ImplSeq α α
  | prepend : (α → β) → ImplSeq β γ → ImplSeq α γ
  | postpend : (β → γ) → ImplSeq α β → ImplSeq α γ

end Inductive


namespace Trees
inductive BinTree (α : Type) : Type where
  | leaf
  | node (a : α) (lst rst : BinTree α)

inductive BinTreeElem (a : α) : BinTree α → Prop where
  | node_left : BinTreeElem a lst → BinTreeElem a (.node a' lst rst)
  | node_here : BinTreeElem a (.node a lst rst)
  | node_right : BinTreeElem a rst → BinTreeElem a (.node a' lst rst)

instance : Membership α (BinTree α) where
  mem t a := BinTreeElem a t

@[reducible] def BinTree.size : BinTree α → ℕ
  | .leaf => 0
  | .node _ lst rst => 1 + lst.size + rst.size

variable {α : Type} [LinearOrder α]

def BinTree.insert (a : α) : BinTree α → BinTree α
  | .leaf => .node a .leaf .leaf
  | .node a' lst rst => match compare a a' with
      | .lt => .node a' (lst.insert a) rst
      | .eq => .node a' lst rst
      | .gt => .node a' lst (rst.insert a)

inductive WithBounds (α : Type) where
  | min
  | el (a : α)
  | max
  deriving DecidableEq

variable {α : Type}

inductive WithBounds.LessEqual [LE α] : WithBounds α → WithBounds α → Prop where
  | min_all : LessEqual .min b
  | el_el : a ≤ a' → LessEqual (.el a) (.el a')
  | all_max : LessEqual a .max

instance [LE α] : LE (WithBounds α) where
  le := WithBounds.LessEqual

theorem WithBounds.LessEqual.trans [LE α] [inst : @Trans α α α LE.le LE.le LE.le] (a b c : WithBounds α) :
    a ≤ b → b ≤ c → a ≤ c := by
  intro H1 H2
  cases H1 <;> cases H2 <;> constructor
  apply inst.trans <;> assumption

instance [Preorder α] : Preorder (WithBounds α) where
  le_refl := by rintro (_ | _ | _) <;> constructor; apply le_refl
  le_trans := WithBounds.LessEqual.trans

instance [PartialOrder α] : PartialOrder (WithBounds α) where
  le_antisymm a b Hab Hba := by
    cases Hab <;> cases Hba <;> try rfl
    congr
    apply le_antisymm <;> assumption

variable [LinearOrder α]

instance : LinearOrder (WithBounds α) where
  le_total a b := by
    cases a
    · left; constructor
    · rename_i a
      cases b
      · right; constructor
      · rename_i a'
        cases (le_total a a')
        · left; constructor; assumption
        · right; constructor; assumption
      · left; constructor
    · right; constructor
  toDecidableLE := by
    rintro (_ | a | _) (_ | b | _) <;> (try (right; constructor; done)) <;> (try (left; rintro (_|_); done))
    by_cases (a ≤ b)
    · right; constructor; assumption
    · left; rintro (_|_); contradiction

instance : Trans LE.le LE.le (LE.le : WithBounds α → WithBounds α → Prop) where
  trans := le_trans

instance : Trans LT.lt LT.lt (LT.lt : WithBounds α → WithBounds α → Prop) where
  trans := lt_trans

@[simp] lemma WithBounds.el_lt_iff_lt (a b : α) : WithBounds.el a < WithBounds.el b ↔ a < b := by
  constructor
  · intro ⟨ _, Hnba ⟩
    cases (lt_or_ge a b) <;> try assumption
    exfalso
    apply Hnba
    constructor
    assumption
  · intro Hab
    rw [lt_iff_le_and_ne]
    constructor
    · constructor
      apply le_of_lt
      assumption
    · intro H
      revert Hab
      cases H
      apply lt_irrefl

@[simp] lemma WithBounds.min_lt_el {a : α} : WithBounds.min < WithBounds.el a := by
  rewrite [lt_iff_le_and_ne]; tauto

@[simp] lemma WithBounds.el_lt_max {a : α} : WithBounds.el a < WithBounds.max := by
  rewrite [lt_iff_le_and_ne]; tauto

def between low (a : α) upp := low < WithBounds.el a ∧ WithBounds.el a < upp

lemma between_change_upp {a : α} (H : .el a < upp')
    : between low a upp → between low a upp' := fun ⟨ hl, _ ⟩ => ⟨ hl, H ⟩

lemma between_change_low {a : α} (H : low' < .el a)
    : between low a upp → between low' a upp := fun ⟨ _, hr ⟩ => ⟨ H, hr ⟩

lemma between_weaken_upp {a : α} upp (H : upp < upp')
    : between low a upp → between low a upp' := fun ⟨ hl, hr ⟩ => ⟨ hl, by apply lt_trans <;> assumption ⟩

lemma between_weaken_low {a : α} low (H : low' < low)
    : between low a upp → between low' a upp := fun ⟨ _, hr ⟩ => ⟨ by apply lt_trans <;> assumption, hr ⟩

inductive BSTNode : WithBounds α → WithBounds α → BinTree α → Prop where
  | leaf : BSTNode low upp .leaf
  | node : BSTNode low (.el a) lst → BSTNode (.el a) upp rst
          → between low a upp
          → BSTNode low upp (.node a lst rst)

def BST (t : BinTree α) : Prop := BSTNode .min .max t


inductive Direction where | left | right

--
-- Inserting into BSTs using ancestries (aka zippers).
-- Recall from the lecture that instead of trying to perform insertion in-place,
-- we can split up the work and do it in two phases:
-- 1. Find the place to insert in, tracking the nodes seen along the way.
--    (Since these are parents and grandparents of the node we insert, we call this the _ancestry_.)
-- 2. Place a new node there and then rebuild the tree.
--
structure Ancestor (α : Type) where
  pa : α
  dir : Direction
  sib : BinTree α

def Ancestry α := List (Ancestor α)

@[reducible] def Direction.order (f : α → α → β) (a₁ a₂ : α) : Direction → β
  | .left  => f a₁ a₂
  | .right => f a₂ a₁

def Ancestor.reconstruct (anc : Ancestor α) (t : BinTree α) : BinTree α :=
  anc.dir.order (.node anc.pa) t anc.sib

@[reducible] def reconstruct_deep (t : BinTree α) : Ancestry α → BinTree α
  | [] => t
  | anc :: ancs => reconstruct_deep (anc.reconstruct t) ancs

inductive InsertionPoint (α : Type) where
  | already_present : InsertionPoint α
  | insert_at : Ancestry α → InsertionPoint α

@[reducible] def BinTree.find_insertion_point_rec (ai : α) (ancs : Ancestry α) : BinTree α → InsertionPoint α
  | .leaf => .insert_at ancs
  | .node a lst rst => match compare ai a with
      | .lt => lst.find_insertion_point_rec ai <| ⟨ a, .left, rst ⟩ :: ancs
      | .eq => .already_present
      | .gt => rst.find_insertion_point_rec ai <| ⟨ a, .right, lst ⟩ :: ancs

def BinTree.find_insertion_point (ai : α) : BinTree α → InsertionPoint α := BinTree.find_insertion_point_rec ai []

@[reducible] def BinTree.insert_at_point (ai : α) (t : BinTree α) : InsertionPoint α → BinTree α
  | .already_present => t
  | .insert_at ancs => reconstruct_deep (.node ai .leaf .leaf) ancs

def BinTree.insert' (ai : α) (t : BinTree α) : BinTree α := t.insert_at_point ai (t.find_insertion_point ai)

end Trees
