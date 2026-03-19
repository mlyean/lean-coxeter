import Coxeter.Basic
import Coxeter.LinearAlgebra.BilinearForm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The geometric representation

This file attempts to define the geometric representation of a Coxeter group.

## References

* [bourbaki2007] N. Bourbaki, *Groupes et algèbres de Lie*

-/


namespace Coxeter

open CoxeterGroup Real

abbrev V (W : Type*) [CoxeterGroup W] := B W →₀ ℝ

variable {W : Type*} [CoxeterGroup W]

noncomputable def stdBasis : Module.Basis (B W) ℝ (V W) := Finsupp.basisSingleOne

noncomputable def bilAux (i i' : B W) : ℝ := - cos (π / M i i')

noncomputable def bil : LinearMap.BilinForm ℝ (V W) := Matrix.toBilin stdBasis bilAux

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

end Coxeter
