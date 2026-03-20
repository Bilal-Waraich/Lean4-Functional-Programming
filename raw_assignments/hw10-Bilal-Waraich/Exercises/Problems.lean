import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Lemma
import Std.Data.HashMap
import Exercises.Given

-- An idea that may be useful:
--   Γ ⊢ C[·] : tyIn, tyOut iff whenever Γ ⊢ e : tyIn we have Γ ⊢ C[·] : tyOut
--
-- Note that these types are not used anywhere in the exercises themselves.
-- However, pick the right definitions here (analogous to how TyJdg is defined
-- for other types) and you will have a much better time stating your lemmas.
inductive ExCtx1.TyJdg : TyCtx → ExCtx1 → Ty → Ty → Prop where
  | binOpLeft : BinOp.TyJdg op tyLhs tyRhs tyOut
      → Exp.TyJdg Γ rhs tyRhs
      → ExCtx1.TyJdg Γ (.binOpLeft op rhs) tyLhs tyOut
  | binOpRight : BinOp.TyJdg op tyLhs tyRhs tyOut
      → Value.TyJdg v tyLhs
      → ExCtx1.TyJdg Γ (.binOpRight op v) tyRhs tyOut

inductive ExCtx.TyJdg : TyCtx → ExCtx → Ty → Ty → Prop where
  | nil : ExCtx.TyJdg Γ [] tyIn tyIn
  | cons : ExCtx1.TyJdg Γ head tyMid tyOut
      → ExCtx.TyJdg Γ tail tyIn tyMid
      → ExCtx.TyJdg Γ (head :: tail) tyIn tyOut


-- Don't forget you can look at what `IsValueOrHasDecompositionOfExp` is using `#print`:
#print IsValueOrHasDecompositionOfExp

-- Exercise 1 (3 points)
lemma ex_is_value_or_has_decomposition_of_exp : IsValueOrHasDecompositionOfExp := by
  apply Exp.simple_rec
  · intro v
    left
    exact IsValue.value

  · intro n
    right
    refine HasDecomposition.decomposition [] rfl ?_
    exact IsRedex.const

  · intro x
    right
    refine HasDecomposition.decomposition [] rfl ?_
    exact IsRedex.var

  · intro op lhs rhs lIH rIH
    rcases lIH with h_val_l | ⟨ctx_l, eq_l, redex_l⟩

    · cases h_val_l
      rename_i v_l

      rcases rIH with h_val_r | ⟨ctx_r, eq_r, redex_r⟩

      · right
        cases h_val_r
        refine HasDecomposition.decomposition [] rfl ?_
        exact IsRedex.bin_op

      · right
        refine HasDecomposition.decomposition (ExCtx1.binOpRight op v_l :: ctx_r) ?_ redex_r
        rw [eq_r]
        rfl

    · right
      refine HasDecomposition.decomposition (ExCtx1.binOpLeft op rhs :: ctx_l) ?_ redex_l
      rw [eq_l]
      rfl

  · intro x body _
    right
    refine HasDecomposition.decomposition [] rfl ?_
    exact IsRedex.abs

-- Exercise 2 (1 point)
lemma ex_bin_op_progress : BinOpProgress := by
  intro op tyLhs tyRhs tyOut lhs rhs op_ty lhs_ty rhs_ty
  cases op_ty with
  | add_ty =>
    cases lhs_ty
    cases rhs_ty
    rename_i ln rn
    exact ⟨.value (.nat (ln + rn)), BinOpStep.add_step⟩
  | mul_ty =>
    cases lhs_ty
    cases rhs_ty
    rename_i ln rn
    exact ⟨.value (.nat (ln * rn)), BinOpStep.mul_step⟩
  | app_ty =>
    cases lhs_ty
    rename_i x body jdg_body
    exact ⟨body.subst x rhs, BinOpStep.app_step rfl⟩

-- Exercise 3 (2 points)
lemma ex_redex_progress : BinOpProgress → RedexProgress := by
  intro bin_op_progress e ty jdg redex
  cases redex
  · rename_i n
    exact ⟨.value (.nat n), HeadStep.const_step⟩

  · cases jdg
    simp at *

  · cases jdg with
    | bin_op_ty h_op h_lhs h_rhs =>
      cases h_lhs with | value_ty v_lhs =>
        cases h_rhs with | value_ty v_rhs =>
          obtain ⟨e', step⟩ := bin_op_progress h_op v_lhs v_rhs
          exact ⟨e', HeadStep.bin_op_step step⟩

  · rename_i x body
    exact ⟨.value (.closure x body), HeadStep.abs_step⟩

-- Exercise 4 (3 points)
theorem ex_progress : IsValueOrHasDecompositionOfExp → RedexProgress → Progress := by
  intro is_value_or_has_decomposition_of_exp redex_progress
  intro e ty jdg

  obtain h_val | h_decomp := is_value_or_has_decomposition_of_exp e
  · left
    exact h_val
  · right
    obtain ⟨ctx, eq, h_redex⟩ := h_decomp
    rename_i e_inner

    have ⟨ty_inner, h_inner_ty⟩ : ∃ ty', Exp.TyJdg ∅ e_inner ty' := by
      rw [eq] at jdg
      clear eq h_redex e
      induction ctx generalizing ty with
      | nil =>
        simp [ExCtx.fill] at jdg
        exact ⟨ty, jdg⟩
      | cons c cs ih =>
        simp only [ExCtx.fill] at jdg
        match c with
        | ExCtx1.binOpLeft _ _ =>
          cases jdg with | bin_op_ty _ h_lhs _ => exact ih h_lhs
        | ExCtx1.binOpRight _ _ =>
          cases jdg with | bin_op_ty _ _ h_rhs => exact ih h_rhs

    obtain ⟨e_next, h_head_step⟩ := redex_progress h_inner_ty h_redex
    exact ⟨ExCtx.fill e_next ctx, Step.ctx_step ctx eq rfl h_head_step⟩

-- Exercise 5 (4 points)
lemma ex_subst_preservation : SubstPreservation := by
  intro v ty e ty' Γ x v_jdg
  revert ty' Γ e
  apply Exp.simple_rec
  · intro v' ty' Γ jdg
    simp [Exp.subst]
    cases jdg with | value_ty h_v =>
      exact Exp.TyJdg.value_ty h_v

  · intro n ty' Γ jdg
    simp [Exp.subst]
    cases jdg
    apply Exp.TyJdg.const_ty

  · intro y ty' Γ jdg
    cases jdg with | var_ty h_lookup =>
      simp [Exp.subst]
      split
      · next h_eq =>
          subst h_eq
          simp at h_lookup
          try injection h_lookup with h_lookup
          subst h_lookup
          exact Exp.TyJdg.value_ty v_jdg

      · next h_ne =>
          apply Exp.TyJdg.var_ty
          rw [Std.HashMap.getElem?_insert] at h_lookup
          simp [Ne.symm h_ne] at h_lookup
          exact h_lookup

  · intro op lhs rhs lhs_ih rhs_ih ty' Γ jdg
    cases jdg with | bin_op_ty h_op h_lhs h_rhs =>
      simp [Exp.subst]
      apply Exp.TyJdg.bin_op_ty h_op
      · apply lhs_ih; exact h_lhs
      · apply rhs_ih; exact h_rhs

  · intro y body ih ty' Γ jdg
    cases jdg
    rename_i T_ret T_arg h_body
    simp [Exp.subst]
    split
    · next h_eq =>
        subst h_eq
        apply Exp.TyJdg.abs_ty
        have : (Γ.insert y ty).insert y T_arg = Γ.insert y T_arg := by
          apply map_ext
          intro k
          simp [Std.HashMap.getElem?_insert]
          split <;> rfl
        rw [←this]
        exact h_body

    · next h_ne =>
        apply Exp.TyJdg.abs_ty
        apply ih
        have ctx_swap : (Γ.insert x ty).insert y T_arg = (Γ.insert y T_arg).insert x ty := by
          apply map_ext
          intro k
          simp only [Std.HashMap.getElem?_insert]
          by_cases hy : k = y
          · subst hy
            simp [Ne.symm h_ne]
          · by_cases hx : k = x
            · subst hx
              simp [h_ne]
            · simp [if_neg (Ne.symm hy), if_neg (Ne.symm hx)]
        rw [ctx_swap] at h_body
        exact h_body

-- Exercise 6 (2 points)
lemma ex_bin_op_preservation : SubstPreservation → BinOpPreservation := by
  intros subst_preservation op lhsTy rhsTy outTy lhs rhs e'
  intros op_ty lhs_ty rhs_ty step

  cases step with
  | add_step =>
    cases op_ty
    apply Exp.TyJdg.value_ty
    exact Value.TyJdg.nat_ty

  | mul_step =>
    cases op_ty
    apply Exp.TyJdg.value_ty
    exact Value.TyJdg.nat_ty

  | app_step h_eq =>
    subst h_eq
    cases op_ty

    cases lhs_ty
    rename_i h_body

    apply subst_preservation
    · exact rhs_ty
    · exact h_body

-- Exercise 7 (1 point)
lemma ex_head_preservation : BinOpPreservation → HeadPreservation := by
  intro bin_op_preservation e e' ty jdg head_step
  cases head_step
  case const_step n =>
    cases jdg
    apply Exp.TyJdg.value_ty
    exact Value.TyJdg.nat_ty

  case bin_op_step op lv rv step_proof =>
    cases jdg with | bin_op_ty h_op h_lhs h_rhs =>
      cases h_lhs with | value_ty h_v_lhs =>
      cases h_rhs with | value_ty h_v_rhs =>
        apply bin_op_preservation h_op h_v_lhs h_v_rhs step_proof

  case abs_step x body =>
    cases jdg with | abs_ty h_body =>
      apply Exp.TyJdg.value_ty
      apply Value.TyJdg.closure_ty
      exact h_body

-- Exercise 8 (2 points)
theorem ex_preservation : HeadPreservation → Preservation := by
  intro head_preservation e e' ty jdg step
  cases step with
  | ctx_step ctx eq1 eq2 h_step =>
    subst eq1
    subst eq2
    revert jdg
    induction ctx generalizing ty with
    | nil =>
      intro jdg
      simp [ExCtx.fill] at jdg
      exact head_preservation jdg h_step

    | cons c cs ih =>
      intro jdg
      simp only [ExCtx.fill] at jdg
      cases c
      · cases jdg with | bin_op_ty h_op h_lhs h_rhs =>
        exact Exp.TyJdg.bin_op_ty h_op (ih h_lhs) h_rhs

      · cases jdg with | bin_op_ty h_op h_lhs h_rhs =>
        exact Exp.TyJdg.bin_op_ty h_op h_lhs (ih h_rhs)
