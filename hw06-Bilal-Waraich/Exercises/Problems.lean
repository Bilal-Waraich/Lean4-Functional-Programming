import Mathlib.Tactic.Linarith
import Exercises.Given

-- Exercise (not graded)
-- Add properties that you require of α to complete the other proofs.
-- Keep in mind that in the last exercise, you will need to prove that these properties
-- hold of the natural numbers.
class ValidElemType (α : Type) extends LT α, Ord α, BEq α where
    beq_correct : ∀ {a : α}, (a == a) = true
    compare_eq_correct : ∀ {a : α}, compare a a = .eq
    compare_lt_iff_lt : ∀ a b : α, compare a b = .lt ↔ a < b
    compare_gt_iff_gt : ∀ a b : α, compare a b = .gt ↔ b < a
    lt_trans' : ∀ {x y z : α}, x < y → y < z → x < z
    beq_eq_true_iff_eq : ∀ a b : α, (a == b) = true ↔ a = b
    compare_eq_iff_eq : ∀ a b : α, compare a b = .eq ↔ a = b

-- Exercise (not graded)
-- Define a predicate that expresses that a tree has a particular depth.
inductive DepthBound : ℕ → BinTree α → Prop where
    | leaf {k} :
        DepthBound k (BinTree.leaf : BinTree α)
    | node {a : α} {l r : BinTree α} {k : ℕ} :
        DepthBound k l →
        DepthBound k r →
        DepthBound (k+1) (BinTree.node a l r)

--
-- Lemmas you may find useful
-- These are not exercises as such, but you may find them useful to do.
-- I've provided parts of solutions to help you along.
--

variable {α : Type} [ValidElemType α]

-- Hint: use the standard library.
lemma lt_iff_add_one_le {n m : ℕ} : n < m ↔ n + 1 ≤ m := by
    constructor
    intro h
    exact Nat.succ_le_of_lt h
    intro h
    exact Nat.lt_of_succ_le h

-- Hint: use omega
lemma pow2_iff_add {k} : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
    omega

lemma between_change_upp {a : α} (H : .el a < upp')
    : between low a upp → between low a upp' := fun ⟨ hl, _ ⟩ => ⟨ hl, H ⟩

lemma between_change_low {a : α} (H : low' < .el a)
    : between low a upp → between low' a upp := by
    intro h
    unfold between at *
    exact ⟨H, h.right⟩


lemma WithBounds.lt_transitive {a b c : WithBounds α}
    : a < b → b < c → a < c := by
    intro h1 h2
    cases h1 with
    | min_el =>
        cases h2 with
        | el_preserved _ => exact WithBounds.LessThan.min_el
        | el_max         => exact WithBounds.LessThan.min_max
    | min_max =>
        cases h2
    | el_preserved hxy =>
        cases h2 with
        | el_preserved hyz =>
            exact WithBounds.LessThan.el_preserved (ValidElemType.lt_trans' hxy hyz)
        | el_max =>
            exact WithBounds.LessThan.el_max
    | el_max =>
        cases h2

lemma between_weaken_upp {a : α} upp (H : upp < upp')
    : between low a upp → between low a upp' := fun ⟨ hl, hr ⟩ => ⟨ hl, by apply WithBounds.lt_transitive <;> assumption ⟩

lemma between_weaken_low {a : α} low (H : low' < low)
    : between low a upp → between low' a upp := fun ⟨hl, hr⟩ =>
        ⟨WithBounds.lt_transitive H hl, hr⟩


lemma bst_elements_in_bounds {a : α} (tv : BSTNode low upp t)
    : a ∈ t → between low a upp := by
    revert a
    induction tv with
    | leaf =>
        intro a ha; cases ha
    | node hL hR hbetween ihL ihR =>
        intro a ha
        cases ha with
        | node_here =>
            simpa using hbetween
        | node_left hLmem =>
            have hb := ihL hLmem
            exact between_weaken_upp _ hbetween.right hb
        | node_right hRmem =>
            have hb := ihR hRmem
            exact between_weaken_low _ hbetween.left hb

--
-- Lemmas and theorems from the tutorial session
--

theorem linear_contains_finds_if_present
    (a : α) (t : BinTree α) : a ∈ t → t.linear_contains a = true := by
    intro Hin
    induction Hin with
    | node_here =>
        unfold BinTree.linear_contains
        rewrite [ValidElemType.beq_correct]
        simp
    | node_left Hinl lIH =>
        unfold BinTree.linear_contains
        rewrite [lIH]
        simp
    | node_right Hinr rIH =>
        unfold BinTree.linear_contains
        rewrite [rIH]
        simp

theorem present_if_linear_contains_finds
    (a : α) (t : BinTree α) : t.linear_contains a = true → a ∈ t := by
  induction t with
  | leaf =>
      intro h
      simp [BinTree.linear_contains] at h
  | node a' l r ihL ihR =>
      intro h
      unfold BinTree.linear_contains at h
      repeat rw [Bool.or_eq_true_iff] at h
      rcases h with ((hHead | hLeft) | hRight)
      · have : a = a' := (ValidElemType.beq_eq_true_iff_eq a a').1 hHead
        subst this
        exact BinTreeElem.node_here
      · exact BinTreeElem.node_left (ihL hLeft)
      · exact BinTreeElem.node_right (ihR hRight)

theorem contains_finds_if_present_helper
    {a : α} {t : BinTree α} (tv : BSTNode low upp t)
    (cont : between low a upp)
    : a ∈ t → t.contains a = true := by
    intro Hin
    induction Hin generalizing low upp with
    | node_here =>
        unfold BinTree.contains
        rw [ValidElemType.compare_eq_correct]
    | @node_left lst a' rst Hinl lIH =>
        cases tv with
        | @node low upp a' lst rst hL hR hbetween =>
            have hb : between low a (.el a') :=
                bst_elements_in_bounds (tv := hL) Hinl
            have hlt : a < a' := by
                cases hb.right with
                | el_preserved h => exact h
            have hcmp : compare a a' = .lt :=
                (ValidElemType.compare_lt_iff_lt a a').2 hlt
            unfold BinTree.contains
            rw [hcmp]
            exact lIH hL hb
    | @node_right lst a' rst Hinr rIH =>
        cases tv with
        | @node low upp a' lst rst hL hR hbetween =>
            have hb : between (.el a') a upp :=
                bst_elements_in_bounds (tv := hR) Hinr
            have hgt : a' < a := by
                cases hb.left with
                | el_preserved h => exact h
            have hcmp : compare a a' = .gt :=
                (ValidElemType.compare_gt_iff_gt a a').2 hgt
            unfold BinTree.contains
            rw [hcmp]
            exact rIH hR hb

theorem contains_finds_if_present
    (a : α) (t : BinTree α) (tv : BST t)
    : a ∈ t → t.contains a = true := by
  apply (contains_finds_if_present_helper tv)
  repeat constructor

theorem present_if_contains_finds
    (a : α) (t : BinTree α)
    : t.contains a = true → a ∈ t := by
    induction t with
    | leaf =>
        intro h
        simp [BinTree.contains] at h
    | node a' l r ihL ihR =>
        intro h
        unfold BinTree.contains at h
        cases hcmp : compare a a' with
        | lt =>
            have : l.contains a = true := by simpa [hcmp] using h
            exact BinTreeElem.node_left (ihL this)
        | eq =>
            have : a = a' := (ValidElemType.compare_eq_iff_eq a a').1 hcmp
            subst this
            exact BinTreeElem.node_here
        | gt =>
            have : r.contains a = true := by simpa [hcmp] using h
            exact BinTreeElem.node_right (ihR this)

theorem depth_bound_closed_upwards :
    DepthBound k t → DepthBound (k+1) t := by
    intro h
    induction h with
    | leaf =>
        exact DepthBound.leaf
    | @node a l r k hl hr ihL ihR =>
        exact DepthBound.node ihL ihR

--
-- Theorems for homework
--

-- Exercise 1: 3 points
-- Prove the theorem.
theorem insert_preserves_BST {a : α} {t : BinTree α}
    (tv : BSTNode low upp t) (cont : between low a upp)
    : BSTNode low upp (t.insert a) := by
    induction t generalizing low upp with
    | leaf =>
        simp [BinTree.insert]
        exact BSTNode.node BSTNode.leaf BSTNode.leaf cont

    | node a' lst rst ihL ihR =>
        cases tv with
        | node hL hR h_between =>
        simp [BinTree.insert]
        cases hcmp : compare a a' with
        | lt =>
            have h_lt : a < a' := (ValidElemType.compare_lt_iff_lt a a').mp hcmp
            have h_between_l : between low a (.el a') :=
            ⟨cont.left, WithBounds.LessThan.el_preserved h_lt⟩
            have left_pres := ihL hL h_between_l
            exact BSTNode.node left_pres hR h_between
        | eq =>
            exact BSTNode.node hL hR h_between
        | gt =>
            have h_gt : a' < a := (ValidElemType.compare_gt_iff_gt a a').mp hcmp
            have h_between_r : between (.el a') a upp :=
            ⟨WithBounds.LessThan.el_preserved h_gt, cont.right⟩
            have right_pres := ihR hR h_between_r
            exact BSTNode.node hL right_pres h_between

-- Exercise 2: 1 point
-- Prove the theorem.
-- Note: I am using a different letter here since we don't need any properties we assumed of α.
theorem insert_depth_increase_bounded [Ord β] {t : BinTree β} :
    DepthBound k t → DepthBound (k+1) (t.insert a) := by
        intro h
        induction h with
        | @leaf k' =>
        unfold BinTree.insert
        have h_l : DepthBound k' (BinTree.leaf : BinTree β) := DepthBound.leaf
        have h_r : DepthBound k' (BinTree.leaf : BinTree β) := DepthBound.leaf
        exact DepthBound.node h_l h_r
        | @node a' l r k' hl hr ihL ihR =>
        unfold BinTree.insert
        cases hcmp : compare a a' with
        | lt =>
            have h_r_up : DepthBound (k'+1) r := depth_bound_closed_upwards hr

            exact DepthBound.node ihL h_r_up
        | eq =>
            exact depth_bound_closed_upwards (DepthBound.node hl hr)
        | gt =>
            have h_l_up : DepthBound (k'+1) l := depth_bound_closed_upwards hl
            exact DepthBound.node h_l_up ihR

-- Exercise 3: 1 point
-- Prove the theorem.
theorem depth_bounds_size {t : BinTree β} :
    DepthBound k t → t.size < 2 ^ k := by
    intro h
    induction h with
    | @leaf k' =>
      simp [BinTree.size]
    | @node a l r k' hl hr ihL ihR =>
      simp [BinTree.size]
      have h_pow_sum : 2^(k' + 1) = 2^k' + 2^k' := pow2_iff_add
      omega

-- Exercise 4: 2 points
-- Prove the theorem.
theorem depth_bound_is_strict [Inhabited β] {k : ℕ} : ∃ (t : BinTree β), t.size + 1 = 2^k ∧ DepthBound k t := by
  induction' k with k ih
  · exact ⟨.leaf, by simp, DepthBound.leaf⟩
  · rcases ih with ⟨t, ht, hdb⟩
    let a : β := default
    let u := BinTree.node a t t
    refine ⟨u, ?sz, ?db⟩

    calc
      u.size + 1
          = ((t.size) + (t.size) + 1) + 1 := by
                simp [u, BinTree.size, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      _   = (t.size + 1) + (t.size + 1) := by ac_rfl
      _   = 2 ^ k + 2 ^ k := by simp [ht]
      _   = 2 ^ (k + 1) := by simp [pow2_iff_add]

    exact DepthBound.node hdb hdb

-- Exercise 5: 1 point
-- Prove the theorem.
-- You can give a direct proof if you want, but it will be painful.
theorem linear_contains_finds_if_contains_finds
    {a : α} {t : BinTree α} :
    t.contains a = true → t.linear_contains a = true := by
    intro h
    exact linear_contains_finds_if_present a t (present_if_contains_finds a t h)


-- Exercise 6: 3 points
-- Provide an instance of ValidElemType for ℕ.
-- This ensures that you do not do anything funny in ValidElemType.
instance instVET_for_Nat : ValidElemType ℕ where
  beq_correct := by simp
  compare_eq_correct := by simp
  compare_lt_iff_lt := by
    intro a b
    rw [Nat.compare_eq_lt]
  compare_gt_iff_gt := by
    intro a b
    rw [Nat.compare_eq_gt]
  lt_trans' := by exact Nat.lt_trans
  beq_eq_true_iff_eq := by simp
  compare_eq_iff_eq := by
    intro a b
    rw [Nat.compare_eq_eq]
