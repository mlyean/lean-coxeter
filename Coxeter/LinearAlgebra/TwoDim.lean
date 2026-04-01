module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
public import Mathlib.LinearAlgebra.Reflection

/-!
# Two dimensional Euclidean spaces

This file proves that the composition of two reflections is a rotation.

## Main statements

* `Coxeter.reflect_reflect`
-/

@[expose] public section

namespace Coxeter

theorem cos_two_nsmul (θ : Real.Angle) :
  (2 • θ).cos = θ.cos * θ.cos - θ.sin * θ.sin := by
  rw [two_nsmul, Real.Angle.cos_add]

open scoped RealInnerProductSpace
open Function Module Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [hdim2 : Fact (finrank ℝ E = 2)]
variable (o : Orientation ℝ E (Fin 2))

instance : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_two

local notation "ω" => o.areaForm
local notation "J" => o.rightAngleRotation

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

theorem rotation_pow (n : ℕ) (θ : Real.Angle) : (o.rotation θ) ^ n = o.rotation (n • θ) := by
  induction n with
  | zero =>
      simp
      rfl
  | succ n ih =>
      rw [pow_add, ih, add_smul]
      ext x
      simp

theorem order_rotation_two_pi_div (m : ℕ) (hm : m ≠ 0) :
  orderOf (o.rotation ((2 * π / m) : ℝ)) = m := by
  rw [orderOf_eq_iff (by grind)]
  constructor
  · rw [rotation_pow, ←Real.Angle.coe_nsmul]
    conv in m • (2 * π / ↑m) =>
      simp
      field_simp
    simp
    rfl
  · intro k hk1 hk2
    rw [rotation_pow]
    intro h
    replace h : o.rotation (k • (2 * π / m : ℝ)) = o.rotation 0 := by
      rwa [Orientation.rotation_zero]
    have h2 := rotation_inj o h
    rw [←Real.Angle.coe_nsmul, Real.Angle.coe_eq_zero_iff] at h2
    have ⟨r, hr⟩ := h2
    simp at hr
    field_simp at hr
    change (r : ℝ) * ((m : ℤ) : ℝ) = ((k : ℤ) : ℝ) at hr
    rw [←Int.cast_mul, Int.cast_inj] at hr
    zify at hk1 hk2
    rw [←hr] at hk1 hk2
    qify at hk1 hk2
    have : (m : ℚ) > 0 := by
      grind
    replace hk1 : r < 1 := by
      have hr_lt_one : (r : ℚ) < 1 := by
        simp_all only [mul_lt_iff_lt_one_left]
      exact Rat.intCast_lt_intCast.mp hr_lt_one
    replace hk2 : 0 < r := by
      have : 0 < (r : ℚ) := by
        simp_all only [mul_pos_iff_of_pos_right]
      simp_all only [mul_pos_iff_of_pos_left, gt_iff_lt, Nat.cast_pos, Int.cast_pos]
    lia

end Coxeter
