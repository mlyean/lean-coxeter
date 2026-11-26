module

public import Coxeter.BilinearLatticeDynkins
public import Coxeter.SpecialFeatures

/-!
# Exceptional finite Coxeter groups

This file packages mathlib's exceptional finite Coxeter matrices as `CoxeterGroup`s and proves
that they are irreducible and finite (positive definite `bil`), and, for the crystallographic
ones, irreducible finite Weyl groups.

## Implementation notes

Positive definiteness is proved from an explicit `LDLᵀ` decomposition of the Gram matrix of `bil`
as a sum of squares with positive coefficients; irreducibility from
`isIrreducibleMatrix_of_exists_lt` / `isIrreducibleMatrix_of_exists_rank_lt`.
-/

@[expose] public section

namespace Coxeter

@[reducible] noncomputable def typeE6Group : CoxeterGroup CoxeterMatrix.E₆.Group where
  B := Fin 6
  M := CoxeterMatrix.E₆
  cs := CoxeterMatrix.E₆.toCoxeterSystem

@[reducible] noncomputable def typeE7Group : CoxeterGroup CoxeterMatrix.E₇.Group where
  B := Fin 7
  M := CoxeterMatrix.E₇
  cs := CoxeterMatrix.E₇.toCoxeterSystem

@[reducible] noncomputable def typeE8Group : CoxeterGroup CoxeterMatrix.E₈.Group where
  B := Fin 8
  M := CoxeterMatrix.E₈
  cs := CoxeterMatrix.E₈.toCoxeterSystem

@[reducible] noncomputable def typeF4Group : CoxeterGroup CoxeterMatrix.F₄.Group where
  B := Fin 4
  M := CoxeterMatrix.F₄
  cs := CoxeterMatrix.F₄.toCoxeterSystem

@[reducible] noncomputable def typeG2Group : CoxeterGroup CoxeterMatrix.G₂.Group where
  B := Fin 2
  M := CoxeterMatrix.G₂
  cs := CoxeterMatrix.G₂.toCoxeterSystem

@[reducible] noncomputable def typeH3Group : CoxeterGroup CoxeterMatrix.H₃.Group where
  B := Fin 3
  M := CoxeterMatrix.H₃
  cs := CoxeterMatrix.H₃.toCoxeterSystem

@[reducible] noncomputable def typeH4Group : CoxeterGroup CoxeterMatrix.H₄.Group where
  B := Fin 4
  M := CoxeterMatrix.H₄
  cs := CoxeterMatrix.H₄.toCoxeterSystem

theorem typeE6_isCrystallographic : @IsCrystallographic _ typeE6Group := by
  intro i i' hii'
  change Fin 6 at i
  change Fin 6 at i'
  change CoxeterMatrix.E₆ i i' = 0 ∨ CoxeterMatrix.E₆ i i' = 2 ∨
    CoxeterMatrix.E₆ i i' = 3 ∨ CoxeterMatrix.E₆ i i' = 4 ∨
    CoxeterMatrix.E₆ i i' = 6
  fin_cases i <;> fin_cases i' <;> simp at hii' <;> norm_num [CoxeterMatrix.E₆]

theorem typeE7_isCrystallographic : @IsCrystallographic _ typeE7Group := by
  intro i i' hii'
  change Fin 7 at i
  change Fin 7 at i'
  change CoxeterMatrix.E₇ i i' = 0 ∨ CoxeterMatrix.E₇ i i' = 2 ∨
    CoxeterMatrix.E₇ i i' = 3 ∨ CoxeterMatrix.E₇ i i' = 4 ∨
    CoxeterMatrix.E₇ i i' = 6
  fin_cases i <;> fin_cases i' <;> simp at hii' <;> norm_num [CoxeterMatrix.E₇]

theorem typeE8_isCrystallographic : @IsCrystallographic _ typeE8Group := by
  intro i i' hii'
  change Fin 8 at i
  change Fin 8 at i'
  change CoxeterMatrix.E₈ i i' = 0 ∨ CoxeterMatrix.E₈ i i' = 2 ∨
    CoxeterMatrix.E₈ i i' = 3 ∨ CoxeterMatrix.E₈ i i' = 4 ∨
    CoxeterMatrix.E₈ i i' = 6
  fin_cases i <;> fin_cases i' <;> simp at hii' <;> norm_num [CoxeterMatrix.E₈]

theorem typeF4_isCrystallographic : @IsCrystallographic _ typeF4Group := by
  intro i i' hii'
  change Fin 4 at i
  change Fin 4 at i'
  change CoxeterMatrix.F₄ i i' = 0 ∨ CoxeterMatrix.F₄ i i' = 2 ∨
    CoxeterMatrix.F₄ i i' = 3 ∨ CoxeterMatrix.F₄ i i' = 4 ∨
    CoxeterMatrix.F₄ i i' = 6
  fin_cases i <;> fin_cases i' <;> simp at hii' <;> norm_num [CoxeterMatrix.F₄]

theorem typeG2_isCrystallographic : @IsCrystallographic _ typeG2Group := by
  intro i i' hii'
  change Fin 2 at i
  change Fin 2 at i'
  change CoxeterMatrix.G₂ i i' = 0 ∨ CoxeterMatrix.G₂ i i' = 2 ∨
    CoxeterMatrix.G₂ i i' = 3 ∨ CoxeterMatrix.G₂ i i' = 4 ∨
    CoxeterMatrix.G₂ i i' = 6
  fin_cases i <;> fin_cases i' <;> simp at hii' <;> norm_num [CoxeterMatrix.G₂]

/-- `bil` of type `E₆` is positive definite: it is a sum of squares (an `LDLᵀ`
decomposition of its Gram matrix) with positive coefficients. -/
private theorem bil_typeE6_pos (x : Fin 6 →₀ ℝ) (hx : x ≠ 0) :
    0 < (@bil _ typeE6Group) x x := by
  have hsos : (@bil _ typeE6Group) x x =
      (1) * (x 0 - x 2/2) ^ 2 +
      (1) * (x 1 - x 3/2) ^ 2 +
      (3/4) * (x 2 - 2*x 3/3) ^ 2 +
      (5/12) * (x 3 - 6*x 4/5) ^ 2 +
      (2/5) * (x 4 - 5*x 5/4) ^ 2 +
      (3/8) * (x 5) ^ 2 := by
    rw [@bil_self_eq_sum _ typeE6Group (Fin.fintype 6)]
    change ∑ i : Fin 6, ∑ i' : Fin 6,
      x i * x i' * -Real.cos (Real.pi / (CoxeterMatrix.E₆ i i' : ℝ)) = _
    simp only [Fin.sum_univ_six]
    norm_num [CoxeterMatrix.E₆, Real.cos_pi_div_three]
    ring
  rw [hsos]
  by_contra hlt
  have hle := not_lt.mp hlt
  apply hx
  have h0 : x 0 - x 2/2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5)]) (sq_nonneg _)
  have h1 : x 1 - x 3/2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5)]) (sq_nonneg _)
  have h2 : x 2 - 2*x 3/3 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5)]) (sq_nonneg _)
  have h3 : x 3 - 6*x 4/5 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5)]) (sq_nonneg _)
  have h4 : x 4 - 5*x 5/4 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5)]) (sq_nonneg _)
  have h5 : x 5 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5)]) (sq_nonneg _)
  ext i
  fin_cases i <;> simp <;> linarith

theorem typeE6_isFiniteCoxeter : @IsFiniteCoxeter _ typeE6Group :=
  isFiniteCoxeter_of_pos fun x hx ↦ bil_typeE6_pos x hx

/-- `bil` of type `E₇` is positive definite: it is a sum of squares (an `LDLᵀ`
decomposition of its Gram matrix) with positive coefficients. -/
private theorem bil_typeE7_pos (x : Fin 7 →₀ ℝ) (hx : x ≠ 0) :
    0 < (@bil _ typeE7Group) x x := by
  have hsos : (@bil _ typeE7Group) x x =
      (1) * (x 0 - x 2/2) ^ 2 +
      (1) * (x 1 - x 3/2) ^ 2 +
      (3/4) * (x 2 - 2*x 3/3) ^ 2 +
      (5/12) * (x 3 - 6*x 4/5) ^ 2 +
      (2/5) * (x 4 - 5*x 5/4) ^ 2 +
      (3/8) * (x 5 - 4*x 6/3) ^ 2 +
      (1/3) * (x 6) ^ 2 := by
    rw [@bil_self_eq_sum _ typeE7Group (Fin.fintype 7)]
    change ∑ i : Fin 7, ∑ i' : Fin 7,
      x i * x i' * -Real.cos (Real.pi / (CoxeterMatrix.E₇ i i' : ℝ)) = _
    simp only [Fin.sum_univ_seven]
    norm_num [CoxeterMatrix.E₇, Real.cos_pi_div_three]
    ring
  rw [hsos]
  by_contra hlt
  have hle := not_lt.mp hlt
  apply hx
  have h0 : x 0 - x 2/2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6)]) (sq_nonneg _)
  have h1 : x 1 - x 3/2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6)]) (sq_nonneg _)
  have h2 : x 2 - 2*x 3/3 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6)]) (sq_nonneg _)
  have h3 : x 3 - 6*x 4/5 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6)]) (sq_nonneg _)
  have h4 : x 4 - 5*x 5/4 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6)]) (sq_nonneg _)
  have h5 : x 5 - 4*x 6/3 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6)]) (sq_nonneg _)
  have h6 : x 6 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6)]) (sq_nonneg _)
  ext i
  fin_cases i <;> simp <;> linarith

theorem typeE7_isFiniteCoxeter : @IsFiniteCoxeter _ typeE7Group :=
  isFiniteCoxeter_of_pos fun x hx ↦ bil_typeE7_pos x hx

/-- `bil` of type `E₈` is positive definite: it is a sum of squares (an `LDLᵀ`
decomposition of its Gram matrix) with positive coefficients. -/
private theorem bil_typeE8_pos (x : Fin 8 →₀ ℝ) (hx : x ≠ 0) :
    0 < (@bil _ typeE8Group) x x := by
  have hsos : (@bil _ typeE8Group) x x =
      (1) * (x 0 - x 2/2) ^ 2 +
      (1) * (x 1 - x 3/2) ^ 2 +
      (3/4) * (x 2 - 2*x 3/3) ^ 2 +
      (5/12) * (x 3 - 6*x 4/5) ^ 2 +
      (2/5) * (x 4 - 5*x 5/4) ^ 2 +
      (3/8) * (x 5 - 4*x 6/3) ^ 2 +
      (1/3) * (x 6 - 3*x 7/2) ^ 2 +
      (1/4) * (x 7) ^ 2 := by
    rw [@bil_self_eq_sum _ typeE8Group (Fin.fintype 8)]
    change ∑ i : Fin 8, ∑ i' : Fin 8,
      x i * x i' * -Real.cos (Real.pi / (CoxeterMatrix.E₈ i i' : ℝ)) = _
    simp only [Fin.sum_univ_eight]
    norm_num [CoxeterMatrix.E₈, Real.cos_pi_div_three]
    ring
  rw [hsos]
  by_contra hlt
  have hle := not_lt.mp hlt
  apply hx
  have h0 : x 0 - x 2/2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7)]) (sq_nonneg _)
  have h1 : x 1 - x 3/2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7)]) (sq_nonneg _)
  have h2 : x 2 - 2*x 3/3 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7)]) (sq_nonneg _)
  have h3 : x 3 - 6*x 4/5 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7)]) (sq_nonneg _)
  have h4 : x 4 - 5*x 5/4 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7)]) (sq_nonneg _)
  have h5 : x 5 - 4*x 6/3 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7)]) (sq_nonneg _)
  have h6 : x 6 - 3*x 7/2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7)]) (sq_nonneg _)
  have h7 : x 7 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2),
                  sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5),
                  sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
                  sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7)]) (sq_nonneg _)
  ext i
  fin_cases i <;> simp <;> linarith

theorem typeE8_isFiniteCoxeter : @IsFiniteCoxeter _ typeE8Group :=
  isFiniteCoxeter_of_pos fun x hx ↦ bil_typeE8_pos x hx


theorem typeE6_isIrreducible : @IsIrreducible _ typeE6Group := by
  refine isIrreducibleMatrix_of_exists_rank_lt (B1 := Fin 6) CoxeterMatrix.E₆ 3
    ![2, 1, 1, 0, 1, 2] fun i hi ↦ ?_
  fin_cases i
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact absurd rfl hi
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩

theorem typeE6_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeE6Group :=
  ⟨⟨typeE6_isFiniteCoxeter, typeE6_isCrystallographic⟩, typeE6_isIrreducible⟩

theorem typeE7_isIrreducible : @IsIrreducible _ typeE7Group := by
  refine isIrreducibleMatrix_of_exists_rank_lt (B1 := Fin 7) CoxeterMatrix.E₇ 3
    ![2, 1, 1, 0, 1, 2, 3] fun i hi ↦ ?_
  fin_cases i
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact absurd rfl hi
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨5, by decide, by decide⟩

theorem typeE7_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeE7Group :=
  ⟨⟨typeE7_isFiniteCoxeter, typeE7_isCrystallographic⟩, typeE7_isIrreducible⟩

theorem typeE8_isIrreducible : @IsIrreducible _ typeE8Group := by
  refine isIrreducibleMatrix_of_exists_rank_lt (B1 := Fin 8) CoxeterMatrix.E₈ 3
    ![2, 1, 1, 0, 1, 2, 3, 4] fun i hi ↦ ?_
  fin_cases i
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact absurd rfl hi
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨5, by decide, by decide⟩
  · exact ⟨6, by decide, by decide⟩

theorem typeE8_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeE8Group :=
  ⟨⟨typeE8_isFiniteCoxeter, typeE8_isCrystallographic⟩, typeE8_isIrreducible⟩

/-- `bil` of type `F₄` is positive definite: it is a sum of squares (an `LDLᵀ` decomposition of
its Gram matrix) with positive coefficients. -/
private theorem bil_typeF4_pos (x : Fin 4 →₀ ℝ) (hx : x ≠ 0) :
    0 < (@bil _ typeF4Group) x x := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsos : (@bil _ typeF4Group) x x =
      (x 0 - x 1 / 2) ^ 2 + 3 / 4 * (x 1 - 2 * Real.sqrt 2 * x 2 / 3) ^ 2 +
        1 / 3 * (x 2 - 3 * x 3 / 2) ^ 2 + 1 / 4 * x 3 ^ 2 := by
    rw [@bil_self_eq_sum _ typeF4Group (Fin.fintype 4)]
    change ∑ i : Fin 4, ∑ i' : Fin 4,
      x i * x i' * -Real.cos (Real.pi / (CoxeterMatrix.F₄ i i' : ℝ)) = _
    simp only [Fin.sum_univ_four]
    norm_num [CoxeterMatrix.F₄, Real.cos_pi_div_three, Real.cos_pi_div_four]
    linear_combination (-(x 2) ^ 2 / 3) * hs
  rw [hsos]
  by_contra hlt
  have hle := not_lt.mp hlt
  apply hx
  have hsq := fun t : ℝ ↦ sq_nonneg t
  have h3 : x 3 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [hsq (x 0 - x 1 / 2), hsq (x 1 - 2 * Real.sqrt 2 * x 2 / 3),
        hsq (x 2 - 3 * x 3 / 2), hsq (x 3)]) (sq_nonneg _)
  have h2 : x 2 - 3 * x 3 / 2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [hsq (x 0 - x 1 / 2), hsq (x 1 - 2 * Real.sqrt 2 * x 2 / 3),
        hsq (x 2 - 3 * x 3 / 2), hsq (x 3)]) (sq_nonneg _)
  have h1 : x 1 - 2 * Real.sqrt 2 * x 2 / 3 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [hsq (x 0 - x 1 / 2), hsq (x 1 - 2 * Real.sqrt 2 * x 2 / 3),
        hsq (x 2 - 3 * x 3 / 2), hsq (x 3)]) (sq_nonneg _)
  have h0 : x 0 - x 1 / 2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [hsq (x 0 - x 1 / 2), hsq (x 1 - 2 * Real.sqrt 2 * x 2 / 3),
        hsq (x 2 - 3 * x 3 / 2), hsq (x 3)]) (sq_nonneg _)
  have e2 : x 2 = 0 := by linarith
  rw [e2, mul_zero, zero_div, sub_zero] at h1
  have e0 : x 0 = 0 := by linarith
  ext i
  fin_cases i <;> simp [e0, h1, e2, h3]

theorem typeF4_isFiniteCoxeter : @IsFiniteCoxeter _ typeF4Group :=
  isFiniteCoxeter_of_pos fun x hx ↦ bil_typeF4_pos x hx

theorem typeF4_isIrreducible : @IsIrreducible _ typeF4Group := by
  refine isIrreducibleMatrix_of_exists_lt CoxeterMatrix.F₄ fun i hi ↦ ?_
  fin_cases i
  · exact absurd rfl hi
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩

theorem typeF4_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeF4Group :=
  ⟨⟨typeF4_isFiniteCoxeter, typeF4_isCrystallographic⟩, typeF4_isIrreducible⟩

/-- `bil` of type `G₂` is positive definite:
`x₀² + x₁² - √3 x₀ x₁ = (x₀ - √3 x₁ / 2)² + x₁² / 4`. -/
private theorem bil_typeG2_pos (x : Fin 2 →₀ ℝ) (hx : x ≠ 0) :
    0 < (@bil _ typeG2Group) x x := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsos : (@bil _ typeG2Group) x x =
      (x 0 - Real.sqrt 3 * x 1 / 2) ^ 2 + 1 / 4 * x 1 ^ 2 := by
    rw [@bil_self_eq_sum _ typeG2Group (Fin.fintype 2)]
    change ∑ i : Fin 2, ∑ i' : Fin 2,
      x i * x i' * -Real.cos (Real.pi / (CoxeterMatrix.G₂ i i' : ℝ)) = _
    simp only [Fin.sum_univ_two]
    norm_num [CoxeterMatrix.G₂, Real.cos_pi_div_six]
    linear_combination (-(x 1) ^ 2 / 4) * hs
  rw [hsos]
  by_contra hlt
  have hle := not_lt.mp hlt
  apply hx
  have h1 : x 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - Real.sqrt 3 * x 1 / 2), sq_nonneg (x 1)]) (sq_nonneg _)
  have h0 : x 0 - Real.sqrt 3 * x 1 / 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by linarith [sq_nonneg (x 0 - Real.sqrt 3 * x 1 / 2), sq_nonneg (x 1)]) (sq_nonneg _)
  rw [h1, mul_zero, zero_div, sub_zero] at h0
  ext i
  fin_cases i <;> simp [h0, h1]

theorem typeG2_isFiniteCoxeter : @IsFiniteCoxeter _ typeG2Group :=
  isFiniteCoxeter_of_pos fun x hx ↦ bil_typeG2_pos x hx

theorem typeG2_isIrreducible : @IsIrreducible _ typeG2Group := by
  refine isIrreducibleMatrix_of_exists_lt CoxeterMatrix.G₂ fun i hi ↦ ?_
  fin_cases i
  · exact absurd rfl hi
  · exact ⟨0, by decide, by decide⟩

theorem typeG2_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeG2Group :=
  ⟨⟨typeG2_isFiniteCoxeter, typeG2_isCrystallographic⟩, typeG2_isIrreducible⟩

theorem typeH3_isIrreducible : @IsIrreducible _ typeH3Group := by
  refine isIrreducibleMatrix_of_exists_lt CoxeterMatrix.H₃ fun i hi ↦ ?_
  fin_cases i
  · exact absurd rfl hi
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩

theorem typeH4_isIrreducible : @IsIrreducible _ typeH4Group := by
  refine isIrreducibleMatrix_of_exists_lt CoxeterMatrix.H₄ fun i hi ↦ ?_
  fin_cases i
  · exact absurd rfl hi
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩

/-- `bil` of type `H₃` is positive definite: with `cos (π / 5) = (1 + √5) / 4` it is a sum of
squares (an `LDLᵀ` decomposition of its Gram matrix) with positive coefficients, the last one
`1 / 2 - √5 / 6` being positive since `√5 < 3`. -/
private theorem bil_typeH3_pos (x : Fin 3 →₀ ℝ) (hx : x ≠ 0) :
    0 < (@bil _ typeH3Group) x x := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hd : 0 < 1 / 2 - Real.sqrt 5 / 6 := by nlinarith
  have hsos : (@bil _ typeH3Group) x x =
      (x 0 - x 1 / 2) ^ 2 + 3 / 4 * (x 1 - (1 + Real.sqrt 5) / 3 * x 2) ^ 2 +
        (1 / 2 - Real.sqrt 5 / 6) * x 2 ^ 2 := by
    rw [@bil_self_eq_sum _ typeH3Group (Fin.fintype 3)]
    change ∑ i : Fin 3, ∑ i' : Fin 3,
      x i * x i' * -Real.cos (Real.pi / (CoxeterMatrix.H₃ i i' : ℝ)) = _
    simp only [Fin.sum_univ_three]
    norm_num [CoxeterMatrix.H₃, Real.cos_pi_div_three]
    linear_combination (-(x 2) ^ 2 / 12) * hs
  rw [hsos]
  by_contra hlt
  have hle := not_lt.mp hlt
  apply hx
  have hlast := mul_nonneg hd.le (sq_nonneg (x 2))
  have h2 : (1 / 2 - Real.sqrt 5 / 6) * x 2 ^ 2 = 0 := le_antisymm
    (by linarith [sq_nonneg (x 0 - x 1 / 2), sq_nonneg (x 1 - (1 + Real.sqrt 5) / 3 * x 2)])
    hlast
  have e2 : x 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp
    ((mul_eq_zero.mp h2).resolve_left hd.ne')
  rw [e2] at hle
  have h1 : x 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by nlinarith [sq_nonneg (x 0 - x 1 / 2), sq_nonneg (x 1)]) (sq_nonneg _)
  rw [h1] at hle
  have h0 : x 0 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by nlinarith [sq_nonneg (x 0)]) (sq_nonneg _)
  ext i
  fin_cases i <;> simp [h0, h1, e2]

theorem typeH3_isFiniteCoxeter : @IsFiniteCoxeter _ typeH3Group :=
  isFiniteCoxeter_of_pos fun x hx ↦ bil_typeH3_pos x hx

/-- `bil` of type `H₄` is positive definite: with `cos (π / 5) = (1 + √5) / 4` it is a sum of
squares (an `LDLᵀ` decomposition of its Gram matrix) with positive coefficients, the last one
`(7 - 3 √5) / 16` being positive since `√5 < 7 / 3`. -/
private theorem bil_typeH4_pos (x : Fin 4 →₀ ℝ) (hx : x ≠ 0) :
    0 < (@bil _ typeH4Group) x x := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hd : 0 < (7 - 3 * Real.sqrt 5) / 16 := by nlinarith
  have hsos : (@bil _ typeH4Group) x x =
      (x 0 - x 1 / 2) ^ 2 + 3 / 4 * (x 1 - 2 * x 2 / 3) ^ 2 +
        2 / 3 * (x 2 - 3 * (1 + Real.sqrt 5) / 8 * x 3) ^ 2 +
        (7 - 3 * Real.sqrt 5) / 16 * x 3 ^ 2 := by
    rw [@bil_self_eq_sum _ typeH4Group (Fin.fintype 4)]
    change ∑ i : Fin 4, ∑ i' : Fin 4,
      x i * x i' * -Real.cos (Real.pi / (CoxeterMatrix.H₄ i i' : ℝ)) = _
    simp only [Fin.sum_univ_four]
    norm_num [CoxeterMatrix.H₄, Real.cos_pi_div_three]
    linear_combination (-3 * x 3 ^ 2 / 32) * hs
  rw [hsos]
  by_contra hlt
  have hle := not_lt.mp hlt
  apply hx
  have hlast := mul_nonneg hd.le (sq_nonneg (x 3))
  have h3 : (7 - 3 * Real.sqrt 5) / 16 * x 3 ^ 2 = 0 := le_antisymm
    (by linarith [sq_nonneg (x 0 - x 1 / 2), sq_nonneg (x 1 - 2 * x 2 / 3),
      sq_nonneg (x 2 - 3 * (1 + Real.sqrt 5) / 8 * x 3)])
    hlast
  have e3 : x 3 = 0 := pow_eq_zero_iff two_ne_zero |>.mp
    ((mul_eq_zero.mp h3).resolve_left hd.ne')
  rw [e3] at hle
  have h2 : x 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by nlinarith [sq_nonneg (x 0 - x 1 / 2), sq_nonneg (x 1 - 2 * x 2 / 3), sq_nonneg (x 2)])
    (sq_nonneg _)
  rw [h2] at hle
  have h1 : x 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by nlinarith [sq_nonneg (x 0 - x 1 / 2), sq_nonneg (x 1)]) (sq_nonneg _)
  rw [h1] at hle
  have h0 : x 0 = 0 := pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
    (by nlinarith [sq_nonneg (x 0)]) (sq_nonneg _)
  ext i
  fin_cases i <;> simp [h0, h1, h2, e3]

theorem typeH4_isFiniteCoxeter : @IsFiniteCoxeter _ typeH4Group :=
  isFiniteCoxeter_of_pos fun x hx ↦ bil_typeH4_pos x hx


/-! ### Euler lattices of `E₆`, `E₇`, `E₈` -/

section EulerLattice

/-- The Euler lattice of type `E₆` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev typeE6BilinearLattice : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice CoxeterMatrix.E₆

theorem typeE6_isSimplyLaced : BilinearLattice.IsSimplyLaced CoxeterMatrix.E₆ := by
  unfold BilinearLattice.IsSimplyLaced
  intro i j; fin_cases i <;> fin_cases j <;> decide

/-- The Coxeter number of `E₆` is `12`. -/
private def typeE6CoxeterTransformation : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, -1;
     0, 0, 1, 0, 0, -1;
     1, 1, 0, 0, 0, -1;
     0, 1, 1, 0, 0, -1;
     0, 0, 0, 1, 0, -1;
     0, 0, 0, 0, 1, -1]
set_option maxRecDepth 100000 in
theorem typeE6BilinearLattice_S_pow :
    (typeE6BilinearLattice.S : Module.End ℤ typeE6BilinearLattice) ^ 12 = 1 :=
  BilinearLattice.ofUnimodular_S_pow_eq_one _ _ typeE6CoxeterTransformation (by decide)
    (by decide)

/-- The Euler lattice of type `E₇` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev typeE7BilinearLattice : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice CoxeterMatrix.E₇

theorem typeE7_isSimplyLaced : BilinearLattice.IsSimplyLaced CoxeterMatrix.E₇ := by
  unfold BilinearLattice.IsSimplyLaced
  intro i j; fin_cases i <;> fin_cases j <;> decide

/-- The Coxeter number of `E₇` is `18`. -/
private def typeE7CoxeterTransformation : Matrix (Fin 7) (Fin 7) ℤ :=
  !![0, 1, 0, 0, 0, 0, -1;
     0, 0, 1, 0, 0, 0, -1;
     1, 1, 0, 0, 0, 0, -1;
     0, 1, 1, 0, 0, 0, -1;
     0, 0, 0, 1, 0, 0, -1;
     0, 0, 0, 0, 1, 0, -1;
     0, 0, 0, 0, 0, 1, -1]
set_option maxRecDepth 100000 in
theorem typeE7BilinearLattice_S_pow :
    (typeE7BilinearLattice.S : Module.End ℤ typeE7BilinearLattice) ^ 18 = 1 :=
  BilinearLattice.ofUnimodular_S_pow_eq_one _ _ typeE7CoxeterTransformation (by decide)
    (by decide)

/-- The Euler lattice of type `E₈` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev typeE8BilinearLattice : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice CoxeterMatrix.E₈

theorem typeE8_isSimplyLaced : BilinearLattice.IsSimplyLaced CoxeterMatrix.E₈ := by
  unfold BilinearLattice.IsSimplyLaced
  intro i j; fin_cases i <;> fin_cases j <;> decide

/-- The Coxeter number of `E₈` is `30`. -/
private def typeE8CoxeterTransformation : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 1, 0, 0, 0, 0, 0, -1;
     0, 0, 1, 0, 0, 0, 0, -1;
     1, 1, 0, 0, 0, 0, 0, -1;
     0, 1, 1, 0, 0, 0, 0, -1;
     0, 0, 0, 1, 0, 0, 0, -1;
     0, 0, 0, 0, 1, 0, 0, -1;
     0, 0, 0, 0, 0, 1, 0, -1;
     0, 0, 0, 0, 0, 0, 1, -1]
set_option maxRecDepth 100000 in
theorem typeE8BilinearLattice_S_pow :
    (typeE8BilinearLattice.S : Module.End ℤ typeE8BilinearLattice) ^ 30 = 1 :=
  BilinearLattice.ofUnimodular_S_pow_eq_one _ _ typeE8CoxeterTransformation (by decide)
    (by decide)

noncomputable abbrev typeE6BilinearLatticeWithMonoidQuasiUnipotent :
    BilinearLattice.BilinearLatticeWithMonoidQuasiUnipotent.{0} :=
  BilinearLattice.eulerLatticeWithMonoidQuasiUnipotent
    (M := CoxeterMatrix.E₆)
    (hS := Module.End.isQuasiUnipotentOfIndex_of_pow_eq_one (by norm_num)
      typeE6BilinearLattice_S_pow two_pos)

noncomputable abbrev typeE7BilinearLatticeWithMonoidQuasiUnipotent :
    BilinearLattice.BilinearLatticeWithMonoidQuasiUnipotent.{0} :=
  BilinearLattice.eulerLatticeWithMonoidQuasiUnipotent
    (M := CoxeterMatrix.E₇)
    (hS := Module.End.isQuasiUnipotentOfIndex_of_pow_eq_one (by norm_num)
      typeE7BilinearLattice_S_pow two_pos)

noncomputable abbrev typeE8BilinearLatticeWithMonoidQuasiUnipotent :
    BilinearLattice.BilinearLatticeWithMonoidQuasiUnipotent.{0} :=
  BilinearLattice.eulerLatticeWithMonoidQuasiUnipotent
    (M := CoxeterMatrix.E₈)
    (hS := Module.End.isQuasiUnipotentOfIndex_of_pow_eq_one (by norm_num)
      typeE8BilinearLattice_S_pow two_pos)

end EulerLattice

end Coxeter
