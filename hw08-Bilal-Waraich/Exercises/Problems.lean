import Exercises.Given.Direction
import Exercises.Given.RBTreeDefs
import Exercises.Given.RBTreeBST
import Exercises.Given.WithBounds

variable {α : Type} [LinearOrder α]

-- Exercise 1 (2 points)
lemma RBTree_BST.change_bounds {node : RBTree α c k} (hlow : low' ≤ low) (hupp : upp ≤ upp')
    : RBTree_BST low upp node → RBTree_BST low' upp' node := by
    intro h
    revert low' upp' hlow hupp
    induction h with
    | leaf h_le =>
        intro low' upp' hlow hupp
        exact .leaf (hlow.trans (h_le.trans hupp))
    | red_node lst_bst rst_bst h_between ihL ihR =>
        intro low' upp' hlow hupp
        exact .red_node
          (ihL hlow le_rfl)
          (ihR le_rfl hupp)
          (between_weaken_both hlow hupp h_between)
    | black_node lst_bst rst_bst h_between ihL ihR =>
        intro low' upp' hlow hupp
        exact .black_node
          (ihL hlow le_rfl)
          (ihR le_rfl hupp)
          (between_weaken_both hlow hupp h_between)

-- The following two lemmas are given as hints for some techniques that may
-- make the proofs a little less painful.
lemma RBTree_BST.relax_bounds_fully {node : RBTree α c k} :
    RBTree_BST low upp node → RBTree_BST .min .max node := by
  intro h
  apply (RBTree_BST.change_bounds ?_ ?_ (by assumption)) <;> simp

lemma Ancestor.rebuild_respects_BST {anc : Ancestor α pc pk c k} {node : RBTree α c k}
    : Ancestor_BST plow pupp low upp anc
    → RBTree_BST low upp node
    → RBTree_BST plow pupp (anc.rebuild node) := by
  rintro ⟨⟩ node_bst
    <;> simp only [Ancestor.rebuild, Direction.order, id, RBTree.reverse]
    <;> constructor <;> assumption

-- Exercise 2 (2 points)
lemma Ancestry.rebuild_respects_BST {ancs : Ancestry α c k} {node : RBTree α c k}
    : Ancestry_BST low upp ancs
    → RBTree_BST low upp node
    → RBRoot_BST (ancs.rebuild node) := by
    intro ancs_bst node_bst
    induction ancs_bst with
    | root =>
      simp [Ancestry.rebuild, RBTree.to_root, RBRoot_BST]
      assumption
    | parent plow pupp anc ancs anc_bst ancs_bst ih =>
      simp [Ancestry.rebuild]
      apply ih
      exact Ancestor.rebuild_respects_BST anc_bst node_bst

-- Exercise 3 (1 point)
lemma make_black_respects_BST {node : RBTree α .red k}
    : RBTree_BST low upp node → RBTree_BST low upp node.make_black := by
      intro h
      cases h with
      | red_node hL hR hbt =>
          exact RBTree_BST.black_node hL hR hbt

-- Exercise 4 (1 point)
lemma to_root_respects_BST {node : RBTree α c k}
    : RBTree_BST low upp node → RBRoot_BST node.to_root := by
    intro h
    have h' : RBTree_BST (.min) (.max) node :=
      (RBTree_BST.relax_bounds_fully (node:=node)) h
    cases node with
    | leaf =>
        simpa [RBTree.to_root]
          using h'
    | red_node a lst rst =>
        have hb : RBTree_BST .min .max (RBTree.black_node a lst rst) := by
          cases h' with
          | red_node hL hR hbt => exact RBTree_BST.black_node hL hR hbt
        simpa [RBTree.to_root]
          using hb
    | black_node a lst rst =>
        simpa [RBTree.to_root]
          using h'

-- Exercise 5 (1 point)
lemma allow_red_respects_BST {anc : Ancestor α .black pk c k}
    : Ancestor_BST plow pupp low upp anc → Ancestor_BST plow pupp low upp anc.allow_red := by
    intro h
    cases h <;> constructor <;> assumption

-- Exercise 6 (5 points)
lemma rebuild_and_fix_respects_BST {anc : Ancestry α .black k} {node : RBTree α .red k}
    : Ancestry_BST low upp anc
    → RBTree_BST low upp node
    → RBRoot_BST (anc.rebuild_and_fix node) := by
  intro ancs_bst node_bst
  fun_induction Ancestry.rebuild_and_fix node anc generalizing low upp <;> clear k

  · exact to_root_respects_BST node_bst

  · rename_i pk dir pa sib gdir ga ancs' node uncle topmost
    unfold topmost; clear topmost
    cases ancs_bst; rename_i plow pupp pbst ancs_bst_tail
    cases ancs_bst_tail; rename_i glow gupp gbst ancs_bst_rest
    cases gbst with
    | black_parent_left uncle_bst ga_between =>
      cases pbst with
      | red_parent_left sib_bst pa_between =>
        split
        · next heq =>
          simp only [Direction.order]
          apply Ancestry.rebuild_respects_BST ancs_bst_rest
          constructor
          · assumption
          · constructor <;> try assumption
            exact ⟨ pa_between.2, ga_between.2 ⟩
          · exact ⟨ pa_between.1, lt_trans pa_between.2 ga_between.2 ⟩
        · next hne => exfalso; exact hne rfl
      | red_parent_right sib_bst pa_between =>
        split
        · next hne => exfalso; cases hne
        · next heq =>
          simp only [RBTree.pick_child, RBTree.left_child, RBTree.right_child, RBTree.value, Direction.order]
          cases node_bst
          rename_i n_val n_lst n_rst n_bst_lst n_bst_rst n_between
          apply Ancestry.rebuild_respects_BST ancs_bst_rest
          constructor
          · constructor <;> try assumption
            exact ⟨ pa_between.1, n_between.1 ⟩
          · constructor <;> try assumption
            exact ⟨ n_between.2, ga_between.2 ⟩
          · exact ⟨ lt_trans pa_between.1 n_between.1, lt_trans n_between.2 ga_between.2 ⟩
    | black_parent_right uncle_bst ga_between =>
      cases pbst with
      | red_parent_left sib_bst pa_between =>
        split
        · next hne => exfalso; cases hne
        · next heq =>
          simp only [RBTree.pick_child, RBTree.left_child, RBTree.right_child, RBTree.value, Direction.order]
          cases node_bst
          rename_i n_val n_lst n_rst n_bst_lst n_bst_rst n_between
          apply Ancestry.rebuild_respects_BST ancs_bst_rest
          constructor
          · constructor <;> try assumption
            exact ⟨ ga_between.1, n_between.1 ⟩
          · constructor <;> try assumption
            exact ⟨ n_between.2, pa_between.2 ⟩
          · exact ⟨ lt_trans ga_between.1 n_between.1, lt_trans n_between.2 pa_between.2 ⟩
      | red_parent_right sib_bst pa_between =>
        split
        · next heq =>
          simp only [Direction.order]
          apply Ancestry.rebuild_respects_BST ancs_bst_rest
          constructor
          · constructor <;> try assumption
            exact ⟨ ga_between.1, pa_between.1 ⟩
          · assumption
          · exact ⟨ lt_trans ga_between.1 pa_between.1, pa_between.2 ⟩
        · next hne => exfalso; exact hne rfl

  · cases ancs_bst; rename_i plow pupp pbst ancs_bst_tail
    cases ancs_bst_tail; rename_i glow gupp gbst ancs_bst_rest
    rename_i dir pa sib gdir ga ancs' node parent uncle grandpa IH
    cases gbst with
    | black_parent_left uncle_bst ga_between =>
      cases pbst with
      | red_parent_left sib_bst pa_between =>
        apply IH
        · assumption
        · constructor
          · constructor
            · assumption
            · assumption
            · exact pa_between
          · exact make_black_respects_BST uncle_bst
          · exact ga_between
      | red_parent_right sib_bst pa_between =>
        apply IH
        · assumption
        · constructor
          · constructor
            · assumption
            · assumption
            · exact pa_between
          · exact make_black_respects_BST uncle_bst
          · exact ga_between
    | black_parent_right uncle_bst ga_between =>
      cases pbst with
      | red_parent_left sib_bst pa_between =>
        apply IH
        · assumption
        · constructor
          · exact make_black_respects_BST uncle_bst
          · constructor
            · assumption
            · assumption
            · exact pa_between
          · exact ga_between
      | red_parent_right sib_bst pa_between =>
        apply IH
        · assumption
        · constructor
          · exact make_black_respects_BST uncle_bst
          · constructor
            · assumption
            · assumption
            · exact pa_between
          · exact ga_between

  · cases ancs_bst; rename_i plow pupp pbst ancs_bst_tail
    apply Ancestry.rebuild_respects_BST ancs_bst_tail
    exact Ancestor.rebuild_respects_BST (allow_red_respects_BST pbst) node_bst

-- Exercise 7 (4 points)
lemma find_insertion_point_rec_respects_BST {node : RBTree α c k}
    : between low ai upp
    → RBTree_BST low upp node
    → Ancestry_BST low upp ancs
    → InsertionPoint_BST ai (node.find_insertion_point_rec ai ancs) := by
    intro ai_between node_bst ancs_bst
    induction node_bst with
    | leaf _ =>
      simp [RBTree.find_insertion_point_rec]
      constructor <;> assumption
    | red_node lst_bst rst_bst a_between ih_left ih_right =>
      simp [RBTree.find_insertion_point_rec]
      split
      · next H_lt =>
        simp only [compare_lt_iff_lt] at H_lt
        apply ih_left
        · apply between_change_upp
          · rw [WithBounds.el_lt_iff_lt]
            exact H_lt
          · exact ai_between
        · constructor
          · constructor <;> assumption
          · assumption
      · next H_eq =>
        constructor
      · next H_gt =>
        simp only [compare_gt_iff_gt] at H_gt
        apply ih_right
        · apply between_change_low
          · rw [WithBounds.el_lt_iff_lt]
            exact H_gt
          · exact ai_between
        · constructor
          · constructor <;> assumption
          · assumption
    | black_node lst_bst rst_bst a_between ih_left ih_right =>
      simp [RBTree.find_insertion_point_rec]
      split
      · next H_lt =>
        simp only [compare_lt_iff_lt] at H_lt
        apply ih_left
        · apply between_change_upp
          · rw [WithBounds.el_lt_iff_lt]
            exact H_lt
          · exact ai_between
        · constructor
          · constructor <;> assumption
          · assumption
      · next H_eq =>
        constructor
      · next H_gt =>
        simp only [compare_gt_iff_gt] at H_gt
        apply ih_right
        · apply between_change_low
          · rw [WithBounds.el_lt_iff_lt]
            exact H_gt
          · exact ai_between
        · constructor
          · constructor <;> assumption
          · assumption

-- Exercise 8 (2 points)
lemma find_root_insertion_point_respects_BST {node : RBRoot α}
    : RBRoot_BST node
    → InsertionPoint_BST ai (node.find_root_insertion_point ai) := by
    intro h
    simp [RBRoot.find_root_insertion_point]
    apply find_insertion_point_rec_respects_BST
    · unfold between
      constructor
      · exact WithBounds.min_lt_el
      · exact WithBounds.el_lt_max
    · exact h
    · constructor

-- Exercise 9 (2 points)
theorem RBRoot_BST.insert_preserves_BST {node : RBRoot α}
    : RBRoot_BST node → RBRoot_BST (node.insert ai) := by
      intro h
      simp [RBRoot.insert]
      have ip_bst := @find_root_insertion_point_respects_BST _ _ ai _ h
      split
      · rename_i ancs h_insert
        rw [h_insert] at ip_bst
        cases ip_bst with
        | insert_at ai_between ancs_bst =>
          apply rebuild_and_fix_respects_BST
          · exact ancs_bst
          · constructor
            · constructor
              apply le_of_lt
              exact ai_between.1
            · constructor
              apply le_of_lt
              exact ai_between.2
            · exact ai_between
      · exact h
