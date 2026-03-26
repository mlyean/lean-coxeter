import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Reflection
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

namespace Coxeter

theorem cos_two_nsmul (θ : Real.Angle) :
  (2 • θ).cos = θ.cos * θ.cos - θ.sin * θ.sin := by
  rw [two_nsmul, Real.Angle.cos_add]

open scoped RealInnerProductSpace
open Function Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [hdim2 : Fact (finrank ℝ E = 2)]
variable (o : Orientation ℝ E (Fin 2))

instance : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_two

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

noncomputable def reflect {x : E} (hx : ‖x‖ = 1) : E ≃ₗ[ℝ] E :=
  @Module.reflection ℝ E _ _ _ x (2 • InnerProductSpace.toDual ℝ E x) (by simp [hx])

theorem reflect_apply {x : E} (hx : ‖x‖ = 1) (y : E) : reflect hx y = y - (2 * ⟪x, y⟫) • x := by
  simp [reflect, Module.reflection_apply]

theorem reflect_reflect {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
  reflect hx ≪≫ₗ reflect hy = o.rotation (2 • o.oangle x y) := by
  let b := o.basisRightAngleRotation x ?_
  on_goal 2 =>
    intro h
    subst h
    simp at hx
  apply_fun LinearEquiv.toLinearMap using LinearEquiv.toLinearMap_injective
  apply b.ext
  let θ := o.oangle x y
  have hy2 : y = (θ.cos) • x + (θ.sin) • J x := by
    rw [←Orientation.rotation_apply]
    symm
    rw [Orientation.rotation_oangle_eq_iff_norm_eq, hx, hy]
  intro i
  match i with
  | 0 =>
      simp only [Fin.isValue, Orientation.coe_basisRightAngleRotation, Nat.succ_eq_add_one,
        Nat.reduceAdd, Matrix.cons_val_zero, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
        SemilinearEquivClass.semilinearEquiv_apply, b]
      calc
        reflect hy (reflect hx x) = reflect hy (-x) := by simp [reflect]
        _ = -x - (2 * ⟪y, -x⟫) • y := by rw [reflect_apply]
        _ = -x - (2 * ⟪(θ.cos) • x + (θ.sin) • J x, -x⟫) • ((θ.cos) • x + (θ.sin) • J x) := by
          rw [hy2]
        _ = -x - (-2 * θ.cos) • ((θ.cos) • x + (θ.sin) • J x) := ?_
        _ = (2 • θ).cos • x + (2 • θ).sin • J x  := ?_
        _ = (o.rotation (2 • θ)) x := by rw [Orientation.rotation_apply]
      · congr 2
        simp only [inner_neg_right, mul_neg, neg_mul, neg_inj, mul_eq_mul_left_iff,
          OfNat.ofNat_ne_zero, or_false]
        rw [inner_add_left, inner_smul_left, inner_smul_left]
        simp [hx]
      · match_scalars
        · simp only [neg_mul, mul_one, sub_neg_eq_add]
          rw [cos_two_nsmul, ←Real.Angle.cos_sq_add_sin_sq]
          ring
        · simp only [neg_mul, mul_one, neg_neg]
          rw [Real.Angle.sin_two_nsmul]
          ring
  | 1 =>
      simp only [Fin.isValue, Orientation.coe_basisRightAngleRotation, Nat.succ_eq_add_one,
        Nat.reduceAdd, Matrix.cons_val_one, Matrix.cons_val_fin_one, LinearEquiv.coe_coe,
        LinearEquiv.trans_apply, SemilinearEquivClass.semilinearEquiv_apply, b]
      calc
        reflect hy (reflect hx (J x)) = reflect hy (J x) := ?_
        _ = J x - (2 * ⟪y, J x⟫) • y := by rw [reflect_apply]
        _ = J x - (2 * ⟪(θ.cos) • x + (θ.sin) • J x, J x⟫) • ((θ.cos) • x + (θ.sin) • J x) := by
          rw [hy2]
        _ = J x - (2 * θ.sin) • ((θ.cos) • x + (θ.sin) • J x) := ?_
        _ = (2 • θ).cos • (J x) - (2 • θ).sin • x := ?_
        _ = (2 • θ).cos • (J x) + (2 • θ).sin • (J (J x)) := by simp [sub_eq_add_neg]
        _ = o.rotation (2 • θ) (J x) := by rw [Orientation.rotation_apply]
      · simp only [reflect, EmbeddingLike.apply_eq_iff_eq]
        rw [reflection_apply]
        simp
      · congr
        rw [inner_add_left, inner_smul_left, inner_smul_left]
        simp [hx]
      · match_scalars
        · simp only [mul_one]
          rw [cos_two_nsmul, ←Real.Angle.cos_sq_add_sin_sq]
          ring
        · simp only [mul_one, neg_inj]
          rw [Real.Angle.sin_two_nsmul]
          ring

theorem reflect_reflect_apply {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (v : E) :
  reflect hy ((reflect hx) v) = o.rotation (2 • o.oangle x y) v := by
  change (reflect hx ≪≫ₗ reflect hy) v = o.rotation (2 • o.oangle x y) v
  rw [reflect_reflect o]
  rfl

theorem rotation_inj : Injective o.rotation := by
  intro θ₁ θ₂ h
  have ⟨x, hx⟩ : ∃ (x : E), x ≠ 0 := by
    have b := Module.finBasisOfFinrankEq ℝ E hdim2.out
    exists b 0
    exact Basis.ne_zero b 0
  have h2 : o.rotation (θ₂ - θ₁) (o.rotation θ₁ x) = o.rotation θ₁ x := by
    simp only [Orientation.rotation_rotation, sub_add_cancel]
    rw [h]
  rw [Orientation.rotation_eq_self_iff_angle_eq_zero] at h2
  · rw [sub_eq_zero] at h2
    rw [h2]
  · simpa

theorem iterate_rotation (n : ℕ) (θ : Real.Angle) : (o.rotation θ)^[n] = o.rotation (n • θ) := by
  ext x
  induction n with
  | zero => simp
  | succ n ih =>
      rw [add_comm, iterate_add, comp_apply, ih]
      simp only [iterate_one, Orientation.rotation_rotation]
      congr
      rw [add_smul]
      simp

theorem iterate_eq_id_iff (m : ℤ) (n : ℕ) (hm : m ≠ 0) :
  (o.rotation ((2 * Real.pi / m) : ℝ))^[n] = id ↔ m ∣ n := by
  have h : (o.rotation 0).toFun = id := by simp
  rw [←h, iterate_rotation]
  constructor
  · intro h
    replace h : o.rotation (n • ↑(2 * Real.pi / ↑m)) = o.rotation 0 := by
      exact LinearIsometryEquiv.ext_iff.mpr (congrFun h)
    have h2 := rotation_inj o h
    rw [←Real.Angle.coe_nsmul, Real.Angle.coe_eq_zero_iff] at h2
    have ⟨k, hk⟩ := h2
    simp at hk
    field_simp at hk
    change (k : ℝ) * ((m : ℤ) : ℝ) = ((n : ℤ) : ℝ) at hk
    rw [←Int.cast_mul, Int.cast_inj] at hk
    exact dvd_of_mul_left_eq k hk
  · intro h
    rw [dvd_iff_exists_eq_mul_left] at h
    have ⟨k, hk⟩ := h
    suffices h : n • ((2 * Real.pi / ↑m) : ℝ) = (0 : Real.Angle) by
      simp [h]
    rw [←Real.Angle.coe_nsmul, Real.Angle.coe_eq_zero_iff]
    exists k
    change k • (2 * Real.pi) = (n : ℤ) • (2 * Real.pi / ↑m)
    rw [hk]
    simp
    field

end Coxeter
