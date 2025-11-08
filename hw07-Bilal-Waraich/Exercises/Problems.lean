import Mathlib.Tactic.Linarith
import Exercises.Given

--
-- In general:
-- - Things marked `theorem` are exercises (to prove the theorem).
-- - Things marked `lemma` are hints about intermediate results you will need.
-- - Things marked `def` are definitions you will need to correctly implement for the theorems to work.
-- Please see `Grading.lean` for a full list.
--
-- While there are many exercises in this homework, most are - or at least should be - fairly easy.
--
-- You can see this homework as preparation for the exam.
--

--
-- Reasoning about propositions
--

namespace PropReasoning
variable {P Q R : Prop}

theorem implication_transitive : (P → Q) → (Q → R) → P → R := by
  intro h1 h2 h3
  have q := h1 h3
  exact h2 q

theorem double_negation_introduction : P → ¬¬P := by
  intro h1 h2
  exact h2 h1

theorem contraction : (P → P → Q) → P → Q := by
  intro h1 h2
  have q := h1 h2
  exact q h2

-- Note: you do not need to use classical reasoning to prove this.
theorem if_not_PtoQ_then_QtoP : ¬(P → Q) → Q → P := by
  intro h1 hQ
  cases h1 (fun _ => hQ)

theorem exists_self_negation : ∃ P, P → ¬P := by
  exists False

end PropReasoning


--
-- Defining functions on structures.
-- The `def`s in this namespace that contain `sorry` are exercises.
-- You can implement them however you like; the types will make sure you can't go (too) wrong.
--

namespace Structures

def Triple.rotate {α β γ} : Triple α β γ → Triple γ α β
  | ⟨α , β , γ⟩ => ⟨γ , α , β⟩

def Triple.triplicate : α → Triple α α α
  | α => ⟨α , α , α⟩

def Triple.extract : Triple (α → β) (β → γ) α → γ
  | ⟨ α , β , γ ⟩ => β (α γ)

def Triple.switch_nesting : Triple α (Triple β γ δ) ε → Triple (α × β) γ (δ × ε)
  | ⟨α , ⟨ β , γ , δ ⟩ , ε⟩ => ⟨(α , β) , γ , (δ , ε)⟩


def Triple.pair_up : (l r : Triple α β γ) → Triple (α × α) (β × β) (γ × γ)
  | ⟨α₁ , β₁ , γ₁⟩ , ⟨α₂ , β₂ , γ₂⟩ => ⟨ (α₁ , α₂) , (β₁ , β₂) , (γ₁ , γ₂) ⟩


-- Dep is short for dependent: it refers to the fact that the type of beta depends on the value of alpha.
-- The u is a universe: it lets us pass both things of type α → Prop and α → Type as β.
-- Typically, this is written Σ, but these exercises let you work with it with less syntactic strangeness.
structure DepPair.{u} α (β : α → Sort u) where
  alpha : α
  beta : β alpha

-- Example solutions.
def DepPair.fst : DepPair α β → α := fun ⟨ a, _ ⟩ => a
def DepPair.fst' : DepPair α β → α := fun p => p.alpha
def DepPair.fst'' : DepPair α β → α
  | ⟨ a, _ ⟩ => a
def DepPair.fst''' : DepPair α β → α := fun
  | ⟨ a, _ ⟩ => a
def DepPair.fst'''' : DepPair α β → α := (·.alpha)
def DepPair.fst''''' : DepPair α β → α := (·.1)

def DepPair.snd : (p : DepPair α β) → β (p.alpha) :=
  fun ⟨ _ , β⟩ => β


def DepPair.snd_with_assumption (p : DepPair α β) (Heq : p.alpha = a) : β a := by
  -- simpa [Heq] using p.beta
  rw [←Heq]
  exact p.beta

def exists_greater (n : ℕ) : DepPair ℕ fun k => n < k :=
  {alpha := n + 1, beta := Nat.lt_succ_self n}

end Structures


--
-- Proofs about inductive types.
--
namespace Inductive

theorem Funky.invert : Funky α β γ ↔ Funky γ β α := by
  constructor
  intro mp
  cases mp with
  | alpha_beta α β => exact ( beta_gamma β α )
  | beta_gamma β γ => exact ( alpha_beta γ β )
  intro mpr
  cases mpr with
  | alpha_beta α β => exact ( beta_gamma β α )
  | beta_gamma β γ => exact ( alpha_beta γ β )

theorem Funky.not_gamma_gives_alpha : Funky α β γ → ¬γ → α := by
  intro h ng
  cases h with
  | alpha_beta a _ => exact a
  | beta_gamma _ c => exact False.elim (ng c)

theorem Funky.gives_beta : Funky α β γ → β := by
  intro h
  cases h with
  | alpha_beta _ b => exact b
  | beta_gamma  b _ => exact b

theorem Funky.gives_alpha_or_gamma : Funky α β γ → α ∨ γ := by
  intro h
  cases h with
  | alpha_beta a _ => exact Or.inl a
  | beta_gamma _ c => exact Or.inr c

theorem ImplSeq.single : (α → β) → ImplSeq α β := by
  intro f
  exact ImplSeq.prepend f ImplSeq.id


theorem ImplSeq.gives_implication : ImplSeq α β → α → β := by
  intro h1 h2
  induction h1 with
  | id => exact h2
  | prepend a1 b1 ih => exact ih (a1 h2)
  | postpend a1 b1 ih => exact a1 (ih h2)

instance instTransImplSeq : Trans ImplSeq ImplSeq ImplSeq where
  trans := by
      intro α β γ h₁ h₂
      exact ImplSeq.postpend (ImplSeq.gives_implication h₂) h₁

theorem ImplSeq.reverse : ImplSeq α β → ImplSeq (¬β) (¬α) := by
  intro h
  have f := ImplSeq.gives_implication h
  exact ImplSeq.single (fun nb na => nb (f na))

-- this lets us use →∗ for ImplSeq
infix:90 " →∗ " => ImplSeq
theorem ImplSeq.complicated_composition : (α →∗ β) → (β →∗ (γ ∨ δ)) → (γ → δ) → (δ →∗ ε) → (α →∗ ε) := by
  intro hAlphaToBeta hBetaToOr hGammaToDelta hDeltaToEps
  have fAlphaToBeta : α → β := ImplSeq.gives_implication hAlphaToBeta
  have fBetaToOr    : β → γ ∨ δ := ImplSeq.gives_implication hBetaToOr
  have fDeltaToEps  : δ → ε := ImplSeq.gives_implication hDeltaToEps
  refine ImplSeq.single (fun a => ?_)
  cases fBetaToOr (fAlphaToBeta a) with
  | inl g  => exact fDeltaToEps (hGammaToDelta g)
  | inr d  => exact fDeltaToEps d

end Inductive

--
-- Defining functions on and proving properties about lists
-- These are taken from the standard library, but they are good exercises.
--

namespace Lists
lemma map_eq_cons_iff' {f : α → β} {xs' : List β} {zs : List α}
    : zs.map f = x' :: xs' ↔ ∃ x xs, zs = x :: xs ∧ x' = f x ∧ xs.map f = xs' := by
    constructor
    · intro h
      cases zs with
      | nil =>
          cases h
      | cons x xs =>
          cases h with
          | refl =>
            exact ⟨x, xs, rfl, rfl, rfl⟩
    · intro h
      rcases h with ⟨x, xs, rfl, hx, hxs⟩
      simp [hx, hxs]

-- This is a good example of where to use induction with generalization.
-- Compare the generated induction hypothesis if you remove `generalizing zs`.
theorem map_eq_append_iff' {f : α → β} {xs' ys' : List β} {zs : List α}
    : zs.map f = xs' ++ ys' ↔ ∃ xs ys, zs = xs ++ ys ∧ xs.map f = xs' ∧ ys.map f = ys' := by
  constructor
  · induction xs' generalizing zs with
    | nil =>
        intro h
        refine ⟨[], zs, ?_, rfl, ?_⟩
        · simp
        · simpa using h

    | cons x' xs' IH =>
        intro h
        have : ∃ x xs, zs = x :: xs ∧ x' = f x ∧ xs.map f = xs' ++ ys' := by
          have := h
          have hx : zs.map f = x' :: (xs' ++ ys') := by simpa using this
          rcases (map_eq_cons_iff' (f:=f) (x':=x') (xs':=xs' ++ ys') (zs:=zs)).1 hx with
            ⟨x, xs, hzs, hx', hrest⟩
          exact ⟨x, xs, hzs, hx', hrest⟩
        rcases this with ⟨x, xs, hz, hx', hrest⟩
        have : ∃ xs₁ ys₁, xs = xs₁ ++ ys₁ ∧ xs₁.map f = xs' ∧ ys₁.map f = ys' :=
          IH hrest
        rcases this with ⟨xs₁, ys₁, hsplit, hmapL, hmapR⟩
        refine ⟨x :: xs₁, ys₁, ?_, ?_, hmapR⟩
        · simp [hz, hsplit]
        · simp [hx', hmapL]

  · intro h
    rcases h with ⟨xs, ys, hzs, hmapL, hmapR⟩
    subst hzs
    simp [hmapL, hmapR, List.map_append]

end Lists

--
-- Defining functions on and proving properties about trees
--

namespace Trees

--
-- Results about membership
--
@[simp] lemma BinTree.not_in_leaf {ai : α} : ai ∉ BinTree.leaf := by
  intro h
  cases h

@[simp] lemma BinTree.in_singleton {ai : α} : ai ∈ BinTree.node a .leaf .leaf ↔ ai = a := by
  constructor
  · intro h
    cases h with
    | node_left hL => cases hL
    | node_here    => rfl
    | node_right hR => cases hR
  · intro h
    subst h
    exact BinTreeElem.node_here

-- Hint: try the `subst` tactic.
lemma BinTreeElem.node_here' {ai : α} (H : ai = a) : ai ∈ BinTree.node a lst rst := by
  subst H
  exact BinTreeElem.node_here

lemma BinTreeElem.node_elem : ae ∈ BinTree.node a lst rst ↔ ae ∈ lst ∨ ae = a ∨ ae ∈ rst := by
  constructor
  · intro h
    cases h with
    | node_left hl  => exact Or.inl hl
    | node_here     => exact Or.inr (Or.inl rfl)
    | node_right hr => exact Or.inr (Or.inr hr)
  · intro h
    cases h with
    | inl hl => exact BinTreeElem.node_left hl
    | inr h2 =>
        cases h2 with
        | inl heq =>
            subst heq
            exact BinTreeElem.node_here
        | inr hr =>
            exact BinTreeElem.node_right hr

lemma BinTreeElem.swap_left_subtree {lst lst' rst : BinTree α}
    : (ai ∈ lst → ai ∈ lst') → ai ∈ BinTree.node a lst rst → ai ∈ BinTree.node a lst' rst := by
  intro H h
  have := (BinTreeElem.node_elem (ae:=ai) (a:=a) (lst:=lst) (rst:=rst)).1 h
  cases this with
  | inl hL =>
      exact BinTreeElem.node_left (H hL)
  | inr h2 =>
      cases h2 with
      | inl heq =>
          subst heq
          exact BinTreeElem.node_here
      | inr hR =>
          exact BinTreeElem.node_right hR

-- With a bit of automation, you can make sure the same proof works for this lemma as for the lemma above.
lemma BinTreeElem.swap_right_subtree {lst rst rst' : BinTree α}
    : (ai ∈ rst → ai ∈ rst') → ai ∈ BinTree.node a lst rst → ai ∈ BinTree.node a lst rst' := by
  intro H h
  have h' := (BinTreeElem.node_elem (ae:=ai) (a:=a) (lst:=lst) (rst:=rst)).1 h
  cases h' with
  | inl hL =>
      exact BinTreeElem.node_left hL
  | inr h2 =>
      cases h2 with
      | inl heq =>
          subst heq
          exact BinTreeElem.node_here
      | inr hR =>
          exact BinTreeElem.node_right (H hR)

def BinTreeElem.decideElem [LinearOrder α] (ai : α) : (t : BinTree α) → Decidable (ai ∈ t) := fun
  | .leaf => .isFalse (by simp)
  | .node a lst rst =>
      match H : decide (ai = a), decideElem ai lst, decideElem ai rst with
      | true, _, _ => .isTrue (by apply BinTreeElem.node_here'; simpa using H)
      | _, .isTrue Hl, _ => .isTrue (by apply BinTreeElem.node_left; assumption)
      | _, _, .isTrue Hr => .isTrue (by apply BinTreeElem.node_right; assumption)
      | false, .isFalse Hl, .isFalse hr => .isFalse (by rewrite [BinTreeElem.node_elem]; rewrite [decide_eq_false_iff_not] at H; tauto)

instance [LinearOrder α] {ai : α} {t : BinTree α} : Decidable (ai ∈ t) := BinTreeElem.decideElem ai t

--
-- Map and results about it
--

@[reducible] def BinTree.map (f : α → β) : BinTree α → BinTree β
  | .leaf => .leaf
  | .node a lst rst => .node (f a) (BinTree.map f lst) (BinTree.map f rst)

instance : Functor BinTree where
  map := BinTree.map

-- Fun fact: `map_id_is_id` and `map_comp_is_comp` is enough to uniquely specify the implementation of `fmap`.

theorem BinTree.map_id_is_id {t : BinTree α} : id <$> t = t := by
  induction t with
  | leaf => rfl
  | node a lst rst ihL ihR =>
    calc
      id <$> BinTree.node a lst rst = BinTree.node (id a) (id <$> lst) (id <$> rst) := by rfl
      _ = BinTree.node a lst rst := by
        congr

theorem BinTree.map_comp_is_comp {t : BinTree α} : f <$> g <$> t = (f ∘ g) <$> t := by
  induction t with
  | leaf => rfl
  | node a l r ihL ihR =>
    calc
      f <$> g <$> BinTree.node a l r = BinTree.node (f (g a)) (f <$> g <$> l) (f <$> g <$> r) := by rfl
      _ = BinTree.node ((f ∘ g) a) ((f ∘ g) <$> l) ((f ∘ g) <$> r) := by
        congr

-- Return a list of the elements as they would be seen in an in-order traversal.
@[reducible] def BinTree.inorder : BinTree α → List α
  | leaf => []
  | node a lst rst => BinTree.inorder lst ++ a :: BinTree.inorder rst

theorem BinTree.inorder_elem {t : BinTree α} : ae ∈ t ↔ ae ∈ t.inorder := by
  induction t with
  | leaf =>
      constructor
      · intro h; cases h
      · intro h; cases h
  | node a l r ihL ihR =>
      constructor
      ·
        intro h
        cases h with
        | node_left hL =>
            have : ae ∈ l.inorder := (ihL.mp hL)
            exact List.mem_append.mpr (Or.inl this)
        | node_here =>
            exact
              List.mem_append.mpr <|
                Or.inr <| List.mem_cons.mpr <| Or.inl rfl
        | node_right hR =>
            have : ae ∈ r.inorder := (ihR.mp hR)
            exact
              List.mem_append.mpr <|
                Or.inr <| List.mem_cons.mpr <| Or.inr this
      ·
        intro h
        have h' : ae ∈ l.inorder ∨ ae = a ∨ ae ∈ r.inorder := by
          have := List.mem_append.mp h
          cases this with
          | inl hl => exact Or.inl hl
          | inr hr =>
              have := List.mem_cons.mp hr
              exact Or.inr this
        cases h' with
        | inl hl =>
            exact BinTreeElem.node_left (ihL.mpr hl)
        | inr h2 =>
            cases h2 with
            | inl heq =>
                simpa [heq] using
                  (BinTreeElem.node_here : BinTreeElem a (BinTree.node a l r))
            | inr hr =>
                exact BinTreeElem.node_right (ihR.mpr hr)

theorem BinTree.inorder_nat_trans {f : α → β} {t : BinTree α}
    : (t.map f).inorder = t.inorder.map f := by
  induction t with
  | leaf => rfl
  | node a l r ihL ihR =>
    simp [BinTree.inorder]
    rw [ihL, ihR]

--
-- Results about insert
--
variable {α : Type} [LinearOrder α]

-- Hints:
-- 1. The tactic `cases` can take an expression, like `compare ai a`.
-- 2. The tactic `cases` can "remember" the equality of what it matched.
--    The syntax for this is `cases H : compare ai a`.
theorem BinTree.contained_after_insert {t : BinTree α} : ai ∈ t.insert ai := by
    induction t with
    | leaf =>
        simp [BinTree.insert, Membership.mem, BinTreeElem.node_here]
    | node a lst rst ihL ihR =>
        dsimp [BinTree.insert]
        cases h : compare ai a with
        | lt =>
            exact BinTreeElem.node_left (by simpa [h] using ihL)
        | eq =>
          have : ai = a := (compare_eq_iff_eq (a:=ai) (b:=a)).1 h
          exact BinTreeElem.node_here' (a:=a) (ai:=ai) (lst:=lst) (rst:=rst) this
        | gt =>
            exact BinTreeElem.node_right (by simpa [h] using ihR)

theorem BinTree.insert_preserves_contains {t : BinTree α} : ao ∈ t → ao ∈ t.insert ai := by
  intro Hin
  induction t generalizing ao with
  | leaf => cases Hin
  | node a lst rst ihL ihR =>
    dsimp [BinTree.insert]
    cases Hin with
    | node_left hL =>
        cases h : compare ai a with
        | lt => exact BinTreeElem.node_left (ihL hL)
        | eq => exact BinTreeElem.node_left hL
        | gt => exact BinTreeElem.node_left hL
    | node_here =>
        cases h : compare ai a with
        | lt => exact BinTreeElem.node_here
        | eq => exact BinTreeElem.node_here
        | gt => exact BinTreeElem.node_here
    | node_right hR =>
        cases h : compare ai a with
        | lt => exact BinTreeElem.node_right hR
        | eq => exact BinTreeElem.node_right hR
        | gt => exact BinTreeElem.node_right (ihR hR)

theorem BinTree.insert_of_uneq_reflects_contains {t : BinTree α} (H : ao ≠ ai) : ao ∈ t.insert ai → ao ∈ t := by
    induction t with
    | leaf =>
      simp [BinTree.insert]
      intro h
      rcases h with (_ | rfl | _)
      contradiction
    | node a' lst rst ihL ihR =>
      simp [BinTree.insert]
      cases Hc : compare ai a' with
      | lt =>
        intro h
        rcases h with (hL | rfl | hR)
        · apply BinTreeElem.node_left
          exact ihL hL
        · apply BinTreeElem.node_here
        · apply BinTreeElem.node_right
          exact hR
      | gt =>
        intro h
        rcases h with (hL | rfl | hR)
        · apply BinTreeElem.node_left
          exact hL
        · apply BinTreeElem.node_here
        · apply BinTreeElem.node_right
          exact ihR hR
      | eq =>
        have : ai = a' := compare_eq_iff_eq.mp Hc
        subst this
        simp

theorem BinTree.insert_reflects_contains_unless_equal {t : BinTree α} : ao ∈ t.insert ai → ao ∈ t ∨ ao = ai := by
  intro Hin
  by_cases h : ao = ai
  · exact Or.inr h
  · exact Or.inl (BinTree.insert_of_uneq_reflects_contains (t:=t) (ai:=ai) (ao:=ao) h Hin)

-- Hint: given `match a with ...` in the goal, you can split up the cases using `split`.
theorem BinTree.insert_monotonic_in_size {t : BinTree α} : t.size ≤ (t.insert ai).size := by
  induction t with
  | leaf =>
      simp [BinTree.size, BinTree.insert]
  | node a lst rst ihL ihR =>
      dsimp [BinTree.insert]
      cases h : compare ai a with
      | lt =>
          have step :
            1 + (lst.insert ai).size + rst.size ≤ 1 + (lst.insert ai).size + rst.size := by
            exact Nat.le_refl _
          have step' :
            1 + lst.size + rst.size ≤ 1 + (lst.insert ai).size + rst.size :=
            by
              have := Nat.add_le_add_right (Nat.add_le_add_left ihL 1) rst.size
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
          exact by
            simpa [BinTree.size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, h] using step'
      | eq =>
          simp [BinTree.size]
      | gt =>
          have step' :
            1 + lst.size + rst.size ≤ 1 + lst.size + (rst.insert ai).size :=
            by
              have := Nat.add_le_add_left (Nat.add_le_add_right ihR lst.size) 1
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
          exact by
            simpa [BinTree.size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, h] using step'

theorem BinTree.insert_increases_size_by_at_most_one {t : BinTree α} : (t.insert ai).size ≤ t.size + 1 := by
  induction t with
  | leaf =>
      simp [BinTree.insert, BinTree.size]
  | node a lst rst ihL ihR =>
      dsimp [BinTree.insert]
      cases h : compare ai a with
      | lt =>
          have step :
              1 + (lst.insert ai).size + rst.size
            ≤ 1 + (lst.size + 1) + rst.size :=
            Nat.add_le_add_right (Nat.add_le_add_left ihL 1) rst.size
          simpa [BinTree.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, h] using step
      | eq =>
          simp [BinTree.size]
      | gt =>
          have step0 :
              lst.size + (rst.insert ai).size
            ≤ lst.size + (rst.size + 1) :=
            Nat.add_le_add_left ihR lst.size
          have step1 :
              1 + (lst.size + (rst.insert ai).size)
            ≤ 1 + (lst.size + (rst.size + 1)) :=
            Nat.add_le_add_left step0 1
          simpa [BinTree.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, h] using step1

theorem BinTree.insert_increases_size_when_missing {t : BinTree α} (Hnin : ai ∉ t)
    : (t.insert ai).size = t.size + 1 := by
    induction t with
    | leaf =>
        simp [BinTree.insert, BinTree.size]
    | node a lst rst ihL ihR =>
        dsimp [BinTree.insert]
        have not_in : ai ∈ lst ∨ ai = a ∨ ai ∈ rst → False := by
          intro h'
          have : ai ∈ BinTree.node a lst rst :=
            (BinTreeElem.node_elem (ae:=ai) (a:=a) (lst:=lst) (rst:=rst)).2 h'
          exact Hnin this
        cases h : compare ai a with
        | lt =>
            have HninL : ai ∉ lst := by intro hL; exact not_in (Or.inl hL)
            have ih := ihL HninL
            simp [BinTree.size, ih, Nat.add_assoc, Nat.add_comm]
        | eq =>
            have : ai = a := (compare_eq_iff_eq (a:=ai) (b:=a)).1 h
            exact (not_in (Or.inr (Or.inl this))).elim
        | gt =>
            have HninR : ai ∉ rst := by intro hR; exact not_in (Or.inr (Or.inr hR))
            have ih := ihR HninR
            simp [BinTree.size, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

---
--- Results that require assuming BSTNode
---

-- Remember that induction will not automatically generalize all variables:
-- you may want to use `induction t generalizing low upp` here.
-- You may also want to look at the lemmas provided in `Given.lean`.
theorem BST.all_between {t : BinTree α} (Hbst : BSTNode low upp t) (Hin : ai ∈ t) : between low ai upp := by
  induction Hbst generalizing ai
  case leaf =>
    cases Hin
  case node lst rst a Hlst Hrst Hbetween IHlst IHrst =>
    cases Hin with
    | node_here => exact Hbetween
    | node_left H =>
        have h1 := IHlst H
        have h2 := Hbetween
        exact ⟨ h1.left, lt_trans h1.right h2.right ⟩
    | node_right H =>
        have h1 := IHrst H
        have h2 := Hbetween
        exact ⟨ lt_trans h2.left h1.left, h1.right ⟩

lemma BinTree.bst_in_left_implies_lt {a : α} (Hbst : BSTNode low upp (.node a lst rst))
    : ai ∈ lst → ai < a := by
    intro Hin
    cases Hbst with
    | node Hlst _ Hbetween =>
        have hb : between low ai (.el a) := BST.all_between Hlst Hin
        simpa [WithBounds.el_lt_iff_lt] using hb.right

lemma BinTree.bst_in_right_implies_gt {a : α} (Hbst : BSTNode low upp (.node a lst rst))
    : ai ∈ rst → a < ai := by
  intro Hin
  cases Hbst with
  | node _ Hrst Hbetween =>
      have hb : between (.el a) ai upp := BST.all_between Hrst Hin
      simpa [WithBounds.el_lt_iff_lt] using hb.left

lemma BinTree.bst_lt_implies_in_left {a : α} (Hbst : BSTNode low upp (.node a lst rst))
    : ai < a → ai ∈ BinTree.node a lst rst → ai ∈ lst := by
    intro hlt hin
    cases hin with
  | node_left hL =>
      exact hL
  | node_here =>
      have hcontra : False := (lt_irrefl ai) (by simp at hlt)
      exact False.elim hcontra
  | node_right hR =>
      cases Hbst with
      | node Hlst Hrst Hbetween =>
          have hb : between (.el a) ai upp := BST.all_between Hrst hR
          have h_gt : a < ai := by
            simpa [WithBounds.el_lt_iff_lt] using hb.left
          exact (lt_asymm hlt h_gt).elim

lemma BinTree.bst_gt_implies_in_right {a : α} (Hbst : BSTNode low upp (.node a lst rst))
    : a < ai → ai ∈ BinTree.node a lst rst → ai ∈ rst := by
    intro hlt hin
    cases hin with
    | node_right hR =>
        exact hR
    | node_here =>
        have hcontra : False := (lt_irrefl ai) (by simp at hlt)
        exact False.elim hcontra
    | node_left hL =>
        cases Hbst with
        | node Hlst _ Hbetween =>
            have hb : between low ai (.el a) := BST.all_between Hlst hL
            have h_lt : ai < a := by
              simpa [WithBounds.el_lt_iff_lt] using hb.right
            exact (lt_asymm hlt h_lt).elim

theorem BinTree.insert_existing_unchanged {t : BinTree α} (Hbst : BSTNode low upp t): ai ∈ t → t.insert ai = t := by
  intro Hin
  induction t generalizing low upp with
  | leaf =>
      cases Hin
  | node a lst rst ihL ihR =>
      dsimp [BinTree.insert]
      cases Hbst with | node Hlst Hrst Hbetween =>
      cases Hin with
      | node_left hL =>
          have h_lt : ai < a := BinTree.bst_in_left_implies_lt (BSTNode.node Hlst Hrst Hbetween) hL
          have h_cmp : compare ai a = .lt := (compare_lt_iff_lt (a:=ai) (b:=a)).mpr h_lt
          have h_ihL : lst.insert ai = lst := ihL Hlst hL
          simp [h_cmp, h_ihL]
      | node_here =>
          have h_cmp : compare ai ai = .eq := compare_eq_iff_eq.mpr rfl
          simp []
      | node_right hR =>
          have h_gt : a < ai := BinTree.bst_in_right_implies_gt (BSTNode.node Hlst Hrst Hbetween) hR
          have h_cmp : compare ai a = .gt := (compare_gt_iff_gt (a:=ai) (b:=a)).mpr h_gt
          have h_ihR : rst.insert ai = rst := ihR Hrst hR
          simp [h_cmp, h_ihR]

theorem BinTree.insert_preserves_size_when_present {t : BinTree α} (Hbst : BSTNode low upp t) (Hin : ai ∈ t)
    : (t.insert ai).size = t.size := by
      have := BinTree.insert_existing_unchanged (t:=t) (ai:=ai) (Hbst:=Hbst) Hin
      simp [this]


--
-- Results about insertion points and ancestries.
-- These theorems may be quite challenging, but their proofs don't rely on anything not covered already.
-- It may help to think about what each result states, and how you would prove it on paper.
--

lemma BinTree.find_insertion_point_rec_detects_presence {t : BinTree α} (Hbst : BSTNode low upp t)
    : ai ∈ t → t.find_insertion_point_rec ai ancs = .already_present := by
      intro Hin
      revert ancs
      induction t generalizing low upp with
      | leaf =>
          intro ancs; cases Hin
      | node a lst rst ihL ihR =>
          intro ancs
          dsimp [BinTree.find_insertion_point_rec]
          cases Hbst with
          | node Hlst Hrst Hbetween =>
            cases Hin with
            | node_left hL =>
                have h_lt : ai < a :=
                  BinTree.bst_in_left_implies_lt
                    (Hbst := BSTNode.node Hlst Hrst Hbetween) hL
                have h_cmp : compare ai a = .lt :=
                  (compare_lt_iff_lt (a:=ai) (b:=a)).mpr h_lt
                simp [h_cmp]
                exact ihL Hlst hL (ancs := ⟨a, .left, rst⟩ :: ancs)
            | node_here =>
                have h_cmp : compare ai ai = .eq :=
                  (compare_eq_iff_eq (a:=ai) (b:=ai)).mpr rfl
                simp []
            | node_right hR =>
                have h_gt : a < ai :=
                  BinTree.bst_in_right_implies_gt
                    (Hbst := BSTNode.node Hlst Hrst Hbetween) hR
                have h_cmp : compare ai a = .gt :=
                  (compare_gt_iff_gt (a:=ai) (b:=a)).mpr h_gt
                simp [h_cmp]
                exact ihR Hrst hR (ancs := ⟨a, .right, lst⟩ :: ancs)

theorem BinTree.find_insertion_point_detects_presence {t : BinTree α} (Hbst : BSTNode low upp t)
    : ai ∈ t → t.find_insertion_point ai = .already_present := by
      intro Hin
      simpa [BinTree.find_insertion_point] using
        (BinTree.find_insertion_point_rec_detects_presence (t:=t) (ai:=ai) (ancs:=[]) Hbst Hin)

lemma BinTree.find_insertion_point_rec_correct_if_absent {t : BinTree α} (ancs : Ancestry α) (Hbst : BSTNode low upp t) (Hnin : ai ∉ t)
    : ∃ ancs', t.find_insertion_point_rec ai ancs = .insert_at ancs'
             ∧ reconstruct_deep (t.insert ai) ancs = reconstruct_deep (.node ai .leaf .leaf) ancs' := by
    revert ancs
    induction t generalizing low upp with
    | leaf =>
        intro ancs; refine ⟨ancs, by simp [BinTree.find_insertion_point_rec], by
          simp [BinTree.insert]⟩
    | node a lst rst ihL ihR =>
        intro ancs
        cases Hbst with
        | node Hlst Hrst Hbetween =>
          have not_in : (ai ∈ lst ∨ ai = a ∨ ai ∈ rst) → False := by
            intro h'
            have : ai ∈ BinTree.node a lst rst :=
              (BinTreeElem.node_elem (ae:=ai) (a:=a) (lst:=lst) (rst:=rst)).2 h'
            exact Hnin this
          cases hc : compare ai a with
          | lt =>
              have HninL : ai ∉ lst := by intro h; exact not_in (Or.inl h)
              rcases ihL Hlst HninL (ancs := ⟨a, .left, rst⟩ :: ancs) with
                ⟨ancs', hfp, hrec⟩
              refine ⟨ancs', ?_, ?_⟩
              · simp [BinTree.find_insertion_point_rec, hc, hfp]
              · simp [BinTree.insert, hc, reconstruct_deep] at hrec ⊢
                simpa [Ancestor.reconstruct, Direction.order] using hrec
          | gt =>
              have HninR : ai ∉ rst := by intro h; exact not_in (Or.inr (Or.inr h))
              rcases ihR Hrst HninR (ancs := ⟨a, .right, lst⟩ :: ancs) with
                ⟨ancs', hfp, hrec⟩
              refine ⟨ancs', ?_, ?_⟩
              · simp [BinTree.find_insertion_point_rec, hc, hfp]
              · simp [BinTree.insert, hc, reconstruct_deep] at hrec ⊢
                simpa [Ancestor.reconstruct, Direction.order] using hrec
          | eq =>
              have : ai = a := (compare_eq_iff_eq (a:=ai) (b:=a)).1 hc
              exact (not_in (Or.inr (Or.inl this)) |> False.elim)

theorem BinTree.find_insertion_point_correct_if_absent {t : BinTree α} (Hbst : BSTNode low upp t) (Hnin : ai ∉ t)
    : ∃ ancs', t.find_insertion_point ai = .insert_at ancs'
             ∧ t.insert ai = reconstruct_deep (.node ai .leaf .leaf) ancs' := by
               simpa [BinTree.find_insertion_point] using
                (BinTree.find_insertion_point_rec_correct_if_absent
                  (t:=t) (ai:=ai) (ancs:=[]) Hbst Hnin)

theorem BinTree.insert'_correct {t : BinTree α} (Hbst : BSTNode low upp t)
    : t.insert ai = t.insert' ai := by
    by_cases Hin : ai ∈ t
    · have hfind :
        t.find_insertion_point ai = .already_present :=
        BinTree.find_insertion_point_detects_presence (t:=t) (ai:=ai) Hbst Hin
      have hkeep :
        t.insert ai = t := BinTree.insert_existing_unchanged (t:=t) (ai:=ai) Hbst Hin
      simp [BinTree.insert', hfind, hkeep]
    · rcases BinTree.find_insertion_point_correct_if_absent (t:=t) (ai:=ai) Hbst Hin with
        ⟨ancs', hfp, hrec⟩
      simp [BinTree.insert', hfp, hrec]

end Trees
