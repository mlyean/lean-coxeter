import Mathlib.Algebra.CharP.Invertible
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Bilinear forms

This file relates bilinar forms and matrices, and proves properties about real vector spaces with
positive definite symmetric bilinear forms.

-/

namespace Coxeter

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {ι : Type*} (b : Module.Basis ι R M)

/-- Omits the `Fintype` and `DecidableEq` hypotheses from mathlib's version -/
noncomputable def LinearMap.BilinForm.toMatrix :
  LinearMap.BilinForm R M ≃ₗ[R] Matrix ι ι R where
  toFun B i j := B (b i) (b j)
  invFun B := b.constr R ((b.constr R) ∘ B)
  map_add' := by
    intro B₁ B₂
    ext i j
    simp
  map_smul' := by
    intro m B
    ext i j
    simp
  left_inv := by
    intro B
    apply b.ext
    intro i
    apply b.ext
    intro j
    simp
  right_inv := by
    intro B
    ext i j
    simp

/-- Omits the `Fintype` and `DecidableEq` hypotheses from mathlib's version -/
noncomputable def Matrix.toBilin : Matrix ι ι R ≃ₗ[R] LinearMap.BilinForm R M :=
  (LinearMap.BilinForm.toMatrix b).symm

theorem Matrix.toBilin_single (B : Matrix ι ι R) (i j : ι) : toBilin b B (b i) (b j) = B i j := by
  unfold toBilin LinearMap.BilinForm.toMatrix
  simp

section real

/-! ### Positive definite symmetric bilinear forms on real vector spaces -/

open Real

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def Orthonormal {ι : Type*} (B : LinearMap.BilinForm ℝ V) (v : ι → V) :=
  (∀ (i : ι), B (v i) (v i) = 1) ∧ LinearMap.IsOrthoᵢ B v

/-- A positive definite symmetric bilinear form on a finite dimensional real vector space has an
orthonormal basis. -/
theorem exists_orthonormal_basis [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V)
  (hB1 : B.IsSymm) (hB2 : B.IsNonneg) (hB3 : B.Nondegenerate) :
  ∃ (v : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V), Orthonormal B v := by
  rw [LinearMap.BilinForm.isSymm_iff] at hB1
  have ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB1
  have h1 : ∀ (i : Fin (Module.finrank ℝ V)), B (v i) (v i) > 0 := by
    intro i
    unfold LinearMap.BilinForm.Nondegenerate at hB3
    rw [LinearMap.BilinForm.nondegenerate_iff' _ hB2.nonneg hB1] at hB3
    apply hB3
    exact v.ne_zero i
  have h2 : ∀ (i : Fin (Module.finrank ℝ V)), IsUnit (1 / sqrt (B (v i) (v i))) := by
    intro i
    apply Ne.isUnit
    grind
  let w := v.unitsSMul (fun i => (h2 i).choose)
  exists w
  constructor
  · intro i
    unfold w
    rw [Module.Basis.unitsSMul_apply]
    change (B ((h2 i).choose.val • v i)) ((h2 i).choose.val • v i) = 1
    rw [(h2 i).choose_spec]
    simp
    grind
  · intro i j h
    change B (w i) (w j) = 0
    unfold w
    simp only [Module.Basis.unitsSMul_apply, LinearMap.map_smul_of_tower, LinearMap.smul_apply]
    rw [hv h]
    simp

variable {W : Submodule ℝ V} [FiniteDimensional ℝ W]

/-- If $V$ is an arbitrary real vector space equipped with a positive definite symmetric
bilinar form and $W$ is a finite dimensional subspace, then $V$ is a sum of $W$ and its
orthogonal complement. -/
theorem sup_orthogonal_eq_top (B : LinearMap.BilinForm ℝ V)
  (hB1 : B.IsSymm) (hB2 : (B.restrict W).IsNonneg) (hB3 : (B.restrict W).Nondegenerate) :
  W ⊔ W.orthogonalBilin B = ⊤ := by
  have hB1' : (B.restrict W).IsSymm := by
    exact hB1.restrict W
  have ⟨v, hv1, hv2⟩ := exists_orthonormal_basis (B.restrict W) hB1' hB2 hB3
  rw [Submodule.sup_eq_top_iff]
  intro x
  let u : W := ∑ (i : Fin (Module.finrank ℝ W)), B x (v i) • v i
  exists u
  refine ⟨u.prop, x - u, ?_, by simp⟩
  rw [Submodule.mem_orthogonalBilin_iff]
  unfold LinearMap.IsOrtho
  conv =>
    intro
    rw [hB1.eq, ←LinearMap.mem_ker]
  change W ≤ (B (x - ↑u)).ker
  have : Submodule.span ℝ (Set.range (Subtype.val ∘ v)) = W := by
    apply Submodule.span_eq_of_le
    · rw [Set.range_subset_iff]
      intro i
      simp
    · intro w hw
      rw [Submodule.mem_span_set']
      exists Module.finrank ℝ W, v.repr ⟨w, hw⟩, fun i => ⟨(v i).val, by simp⟩
      have h1 : ∑ (i : Fin (Module.finrank ℝ W)), (v.repr ⟨w, hw⟩ i) • (v i) = w := by simp
      conv =>
        lhs
        congr
        · skip
        · intro i
          change ((v.repr ⟨w, hw⟩) i • (v i)).val
      rwa [←Submodule.coe_sum]
  nth_rw 1 [←this]
  rw [Submodule.span_le, Set.range_subset_iff]
  intro i
  simp only [map_sub, Function.comp_apply, SetLike.mem_coe, LinearMap.mem_ker,
    LinearMap.sub_apply]
  rw [sub_eq_zero]
  symm
  unfold u
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, map_sum, map_smul,
    LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  change ∑ j, B x (v j) * B (v j) (v i) = B x (v i)
  have : ∀ (i j : Fin (Module.finrank ℝ W)), (B x (v j)) * B (v j) (v i)
    = Set.indicator {i} (fun j => B x (v j)) j := by
    intro i j
    by_cases h : j = i
    · simp only [h, Set.mem_singleton_iff, Set.indicator_of_mem]
      have : B (v i).val (v i).val = 1 := hv1 i
      rw [this, mul_one]
    · simp only [Set.mem_singleton_iff, h, not_false_eq_true, Set.indicator_of_notMem,
        mul_eq_zero]
      right
      exact hv2 h
  conv =>
    lhs
    congr
    · skip
    · intro j
      rw [this]
  simp

end real

end Coxeter
