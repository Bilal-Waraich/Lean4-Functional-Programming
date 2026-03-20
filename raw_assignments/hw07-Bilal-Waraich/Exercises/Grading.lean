import Exercises.Given
import Exercises.Problems
import Exercises.Autograder

section
open PropReasoning
variable (P Q R : Prop)
theorem ex01 : (P → Q) → (Q → R) → P → R := implication_transitive
theorem ex02 : P → ¬¬P := double_negation_introduction
theorem ex03 : (P → P → Q) → P → Q := contraction
theorem ex04 : ¬(P → Q) → Q → P := if_not_PtoQ_then_QtoP
theorem ex05 : ∃ P, P → ¬P := exists_self_negation
end

section
open Structures
def ex06 : Triple α β γ → Triple γ α β := Triple.rotate
def ex07 : α → Triple α α α := Triple.triplicate
def ex08 : Triple (α → β) (β → γ) α → γ := Triple.extract
def ex09 : Triple α (Triple β γ δ) ε → Triple (α × β) γ (δ × ε) := Triple.switch_nesting
def ex10 : (l r : Triple α β γ) → Triple (α × α) (β × β) (γ × γ) := Triple.pair_up
def ex11 : (p : DepPair α β) → β (p.alpha) := DepPair.snd
def ex12 : (p : DepPair α β) → p.alpha = a → β a := DepPair.snd_with_assumption
def ex13 : (n : ℕ) → DepPair ℕ fun k => n < k := exists_greater
end

section
open Inductive
theorem ex14 : Funky α β γ ↔ Funky γ β α := Funky.invert
theorem ex15 : Funky α β γ → ¬γ → α := Funky.not_gamma_gives_alpha
theorem ex16 : Funky α β γ → β := Funky.gives_beta
theorem ex17 : Funky α β γ → α ∨ γ := Funky.gives_alpha_or_gamma
theorem ex18 : (α → β) → ImplSeq α β := ImplSeq.single
theorem ex19 : ImplSeq α β → α → β := ImplSeq.gives_implication

theorem ex20 : ImplSeq α β → ImplSeq β γ → ImplSeq α γ := instTransImplSeq.trans

theorem ex21 : ImplSeq α β → ImplSeq (¬β) (¬α) := ImplSeq.reverse
theorem ex22 : (α →∗ β) → (β →∗ (γ ∨ δ)) → (γ → δ) → (δ →∗ ε) → (α →∗ ε) := ImplSeq.complicated_composition
end

section
open Lists
theorem ex23 {f : α → β} {xs' ys' : List β} {zs : List α} : zs.map f = xs' ++ ys' ↔ ∃ xs ys, zs = xs ++ ys ∧ xs.map f = xs' ∧ ys.map f = ys' := map_eq_append_iff'
end

section
open Trees
theorem ex24 {t : BinTree α} : id <$> t = t := BinTree.map_id_is_id
theorem ex25 {t : BinTree α} : f <$> g <$> t = (f ∘ g) <$> t := BinTree.map_comp_is_comp
theorem ex26 {t : BinTree α} : ae ∈ t ↔ ae ∈ t.inorder := BinTree.inorder_elem
theorem ex27 {f : α → β} {t : BinTree α} : (t.map f).inorder = t.inorder.map f := BinTree.inorder_nat_trans
variable {α : Type} [LinearOrder α]
theorem ex28 {t : BinTree α} : ai ∈ t.insert ai := BinTree.contained_after_insert
theorem ex29 {t : BinTree α} : ao ∈ t → ao ∈ t.insert ai := BinTree.insert_preserves_contains
theorem ex30 {t : BinTree α} : ao ≠ ai → ao ∈ t.insert ai → ao ∈ t := BinTree.insert_of_uneq_reflects_contains
theorem ex31 {t : BinTree α} : ao ∈ t.insert ai → ao ∈ t ∨ ao = ai := BinTree.insert_reflects_contains_unless_equal
theorem ex32 {t : BinTree α} : t.size ≤ (t.insert ai).size := BinTree.insert_monotonic_in_size
theorem ex33 {t : BinTree α} : (t.insert ai).size ≤ t.size + 1 := BinTree.insert_increases_size_by_at_most_one
theorem ex34 {t : BinTree α} : ai ∉ t → (t.insert ai).size = t.size + 1 := BinTree.insert_increases_size_when_missing
theorem ex35 {t : BinTree α} : BSTNode low upp t → ai ∈ t → between low ai upp := BST.all_between
theorem ex36 {t : BinTree α} : BSTNode low upp t → ai ∈ t → t.insert ai = t := BinTree.insert_existing_unchanged
theorem ex37 {t : BinTree α} : BSTNode low upp t → ai ∈ t → (t.insert ai).size = t.size := BinTree.insert_preserves_size_when_present
theorem ex38 {t : BinTree α} : BSTNode low upp t → ai ∈ t → t.find_insertion_point ai = .already_present := BinTree.find_insertion_point_detects_presence
theorem ex39 {t : BinTree α} : BSTNode low upp t → ai ∉ t → ∃ ancs', t.find_insertion_point ai = .insert_at ancs' ∧ t.insert ai = reconstruct_deep (.node ai .leaf .leaf) ancs' := BinTree.find_insertion_point_correct_if_absent
theorem ex40 {t : BinTree α} : BSTNode low upp t → t.insert ai = t.insert' ai := BinTree.insert'_correct
end

#print_grade_results ex01 ex02 ex03 ex04 ex05 ex06 ex07 ex08 ex09 ex10 ex11 ex12 ex13 ex14 ex15 ex16 ex17 ex18 ex19 ex20 ex21 ex22 ex23 ex24 ex25 ex26 ex27 ex28 ex29 ex30 ex31 ex32 ex33 ex34 ex35 ex36 ex37 ex38 ex39 ex40
