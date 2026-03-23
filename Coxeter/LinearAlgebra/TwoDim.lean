import Mathlib.Analysis.InnerProductSpace.TwoDim

namespace Coxeter

open scoped RealInnerProductSpace
open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]
  (o : Orientation ℝ E (Fin 2))

local notation "ω" => o.areaForm
local notation "J" => o.rightAngleRotation

theorem eq_J_iff (x y : E) : J x = y ↔ ⟪x, y⟫ = 0 ∧ ‖y‖ = ‖x‖ ∧ ω x y ≥ 0 := by
  constructor
  · intro h
    symm at h
    simp_all only [Orientation.inner_rightAngleRotation_right, Orientation.areaForm_apply_self,
      neg_zero, LinearIsometryEquiv.norm_map, Orientation.areaForm_rightAngleRotation_right,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq, ge_iff_le, norm_nonneg,
      pow_succ_nonneg, and_self]
  · intro ⟨h1, h2, h3⟩
    by_cases! hx : x = 0
    · subst hx
      simp only [norm_zero, norm_eq_zero, map_zero] at h2 ⊢
      symm at h2
      exact h2
    · have h4 : finrank ℝ (ℝ ∙ x)ᗮ = 1 := by
        apply Submodule.finrank_orthogonal_span_singleton
        exact hx
      have h5 : y ∈ (ℝ ∙ x)ᗮ := by
        rwa [Submodule.mem_orthogonal_singleton_iff_inner_right]
      have h6 : J x ∈ (ℝ ∙ x)ᗮ := by
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
        simp
      have h7 : J x ≠ 0 := by
        simp_all only [ge_iff_le, ne_eq, EmbeddingLike.map_eq_zero_iff, not_false_eq_true]
      have ⟨c, hc⟩ := @exists_smul_eq_of_finrank_eq_one _ _ _ _ _ h4 ⟨J x, h6⟩ (by simpa) ⟨y, h5⟩
      simp only [SetLike.mk_smul_mk, Subtype.mk.injEq] at hc
      rw [←hc, norm_smul] at h2
      simp only [Real.norm_eq_abs, LinearIsometryEquiv.norm_map] at h2
      rw [mul_eq_right₀ (by positivity), abs_eq (by simp)] at h2
      cases h2 with
      | inl h2 =>
          subst h2
          simp only [one_smul] at hc
          exact hc
      | inr h2 =>
          subst h2
          simp only [neg_smul, one_smul] at hc
          subst hc
          simp at h3
          contradiction

end Coxeter
