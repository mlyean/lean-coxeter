import Coxeter.Basic
import Coxeter.LinearAlgebra.BilinearForm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Geometric representation of Coxeter groups

This file attempts to define the geometric representation of a Coxeter group.

## References

* [bourbaki2007] N. Bourbaki, *Groupes et algèbres de Lie*

-/

namespace Coxeter

open CoxeterGroup Real

noncomputable section

abbrev V (W : Type*) [CoxeterGroup W] := B W →₀ ℝ

variable {W : Type*} [CoxeterGroup W]

def stdBasis : Module.Basis (B W) ℝ (V W) := Finsupp.basisSingleOne

def bilAux (i i' : B W) : ℝ := - cos (π / M i i')

def bil : LinearMap.BilinForm ℝ (V W) := Matrix.toBilin stdBasis bilAux

theorem bil_isSymm : LinearMap.BilinForm.IsSymm (@bil W _) := by
  rw [LinearMap.BilinForm.isSymm_iff_basis stdBasis]
  intro i i'
  unfold bil
  rw [Matrix.toBilin_single, Matrix.toBilin_single]
  unfold bilAux
  rw [M.symmetric i i']

theorem bil_diag (i : B W) : bil (stdBasis i) (stdBasis i) = 1 := by
  unfold bil
  rw [Matrix.toBilin_single]
  unfold bilAux
  simp

theorem bil_off_diag (i i' : B W) (h : i ≠ i') : bil (stdBasis i) (stdBasis i') ≤ 0 := by
  unfold bil
  rw [Matrix.toBilin_single]
  unfold bilAux
  rw [Left.neg_nonpos_iff]
  apply Real.cos_nonneg_of_mem_Icc
  have := M.off_diagonal i i' h
  rw [Set.mem_Icc]
  have := pi_pos
  constructor
  · trans 0
    · grind
    · positivity
  · cases Nat.eq_zero_or_pos (M.M i i') with
    | inl h =>
        rw [h]
        simp only [CharP.cast_eq_zero, div_zero]
        positivity
    | inr h =>
        apply div_le_div_of_nonneg_left
        · grind
        · norm_num
        · norm_num
          grind

def σ (i : B W) (x : V W) : V W := x - (2 * bil (stdBasis i) x) • stdBasis i

def E (i i' : B W) : Submodule ℝ (V W) := Finsupp.supported ℝ _ {i, i'}

theorem mem_E_iff (i i' : B W) (v : V W)
  : v ∈ E i i' ↔ ∃ (x y : ℝ), v = x • stdBasis i + y • stdBasis i' := by
  unfold E stdBasis
  simp only [Finsupp.coe_basisSingleOne, Finsupp.smul_single, smul_eq_mul, mul_one]
  constructor
  · intro h
    by_cases h2 : i = i'
    · subst h2
      exists v i, 0
      simp only [Finsupp.single_zero, add_zero]
      ext j
      by_cases h3 : j = i
      · subst h3
        simp
      · simp only [ne_eq, h3, not_false_eq_true, Finsupp.single_eq_of_ne]
        rw [Finsupp.mem_supported'] at h
        apply h
        simp [h3]
    · exists v i, v i'
      ext j
      by_cases h3 : j = i
      · subst h3
        simp [h2]
      · by_cases h4 : j = i'
        · subst h4
          simp [h2]
        · simp only [Finsupp.coe_add, Pi.add_apply, ne_eq, h3, not_false_eq_true,
          Finsupp.single_eq_of_ne, h4, add_zero]
          rw [Finsupp.mem_supported'] at h
          apply h
          simp [h3, h4]
  · intro ⟨x, y, h⟩
    rw [h]
    apply add_mem
    all_goals
    apply Finsupp.single_mem_supported
    simp

theorem bil_restrict_E (i i' : B W) (x y : ℝ) :
  bil (x • stdBasis i + y • stdBasis i') (x • stdBasis i + y • stdBasis i')
  = (x - y * cos (π / M.M i i')) ^ 2 + (y * sin (π / M.M i i')) ^ 2 := by
  calc
    bil (x • stdBasis i + y • stdBasis i') (x • stdBasis i + y • stdBasis i')
      = x ^ 2 - 2 * x * y * cos (π / M.M i i') + y ^ 2 := ?_
    _ = (x - y * cos (π / M.M i i')) ^ 2 + (y * sin (π / M.M i i')) ^ 2 := ?_
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    unfold bil
    simp only [Matrix.toBilin_single stdBasis]
    unfold bilAux
    rw [M.symmetric i i']
    simp
    ring
  · conv =>
      lhs
      congr
      · skip
      · rw [←one_mul (y ^ 2), ←Real.sin_sq_add_cos_sq (π / M.M i i')]
    ring

theorem bil_restrict_E_isSymm (i i' : B W) : (bil.restrict (E i i')).IsSymm := by
  apply LinearMap.BilinForm.IsSymm.restrict
  exact bil_isSymm

theorem bil_restrict_E_nonneg (i i' : B W) : (bil.restrict (E i i')).IsNonneg := by
  rw [LinearMap.BilinForm.isNonneg_def]
  intro z
  have ⟨x, y, h⟩ := (mem_E_iff i i' z).mp z.prop
  simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
  rw [h, bil_restrict_E]
  positivity

/-- Bourbaki Ch V, §4, Proposition 1 -/
theorem bil_restrict_E_isPosSemidef (i i' : B W) : (bil.restrict (E i i')).IsPosSemidef := by
  rw [LinearMap.BilinForm.isPosSemidef_def]
  constructor
  · apply bil_restrict_E_isSymm
  · apply bil_restrict_E_nonneg

/-- Bourbaki Ch V, §4, Proposition 1 (continued) -/
theorem bil_restrict_E_nondegenerate_iff (i i' : B W) (h : i ≠ i') :
  (bil.restrict (E i i')).Nondegenerate ↔ M.M i i' ≠ 0 := by
  unfold LinearMap.BilinForm.Nondegenerate
  rw [LinearMap.BilinForm.nondegenerate_iff']
  · generalize h2 : M.M i i' = m
    match m with
    | 0 =>
        simp only [ne_eq,  not_true_eq_false, iff_false]
        push_neg
        exists ⟨cos (π / M.M i i') • stdBasis i + 1 • stdBasis i', ?_⟩
        · rw [mem_E_iff]
          exists cos (π / M.M i i'), 1
          simp
        · constructor
          · simp only [one_smul, ne_eq, Submodule.mk_eq_zero]
            rw [←ne_eq, Finsupp.ne_iff]
            exists i'
            simp [stdBasis, h]
          · have := bil_restrict_E i i' (cos (π / M.M i i')) 1
            simp only [ne_eq, one_smul, map_add, map_smul, LinearMap.add_apply,
              LinearMap.smul_apply, smul_eq_mul, one_mul, sub_self, OfNat.ofNat_ne_zero,
              not_false_eq_true, zero_pow, zero_add, LinearMap.BilinForm.restrict_apply,
              LinearMap.domRestrict_apply, ge_iff_le] at *
            rw [this, h2]
            simp
    | 1 =>
        have := M.off_diagonal i i' h
        contradiction
    | k+2 =>
        simp only [ne_eq, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
          Subtype.forall, Submodule.mk_eq_zero, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false,
          not_false_eq_true, iff_true]
        intro z hz1 hz2
        apply lt_of_le_of_ne
        · exact (bil_restrict_E_nonneg i i').nonneg ⟨z, hz1⟩
        · have ⟨x, y, h⟩ := (mem_E_iff i i' z).mp hz1
          rw [h, bil_restrict_E]
          intro h3
          symm at h3
          rw [sq, sq, mul_self_add_mul_self_eq_zero] at h3
          replace ⟨h3, h4⟩ := h3
          have : sin (π / ↑(M.M i i')) ≠ 0 := by
            rw [h2]
            apply ne_of_gt
            apply Real.sin_pos_of_mem_Ioo
            have := pi_pos
            have : ↑(k + 2) ≥ 2 := by simp
            simp only [Nat.cast_add, Nat.cast_ofNat, Set.mem_Ioo]
            constructor
            · positivity
            · field_simp
              linarith
          simp only [mul_eq_zero, this, or_false] at h4
          rw [h4] at h3
          simp only [zero_mul, sub_zero] at h3
          rw [h3, h4] at h
          simp at h
          contradiction
  · exact (bil_restrict_E_nonneg i i').nonneg
  · rw [←LinearMap.BilinForm.isSymm_iff]
    exact bil_restrict_E_isSymm i i'

instance {i i' : B W} : FiniteDimensional ℝ (E i i') := by
  have : E i i' ≃ₗ[ℝ] (({i, i'} : Set (B W)) →₀ ℝ) :=
    Finsupp.supportedEquivFinsupp _
  exact Module.Finite.equiv this.symm

theorem E_sup_orthogonal {i i' : B W} (h : M i i' ≥ 2) :
  E i i' ⊔ (E i i').orthogonalBilin bil = ⊤ := by
  apply sup_orthogonal_eq_top
  · exact bil_isSymm
  · exact bil_restrict_E_nonneg i i'
  · have : i ≠ i' := by
      intro h2
      subst h2
      simp at h
    rw [bil_restrict_E_nondegenerate_iff i i' this]
    grind

end

end Coxeter
