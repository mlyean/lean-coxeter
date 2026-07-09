module

public import Coxeter.SpecialFeatures

/-!
# Exceptional finite Coxeter groups

This file packages mathlib's exceptional finite Coxeter matrices as `CoxeterGroup`s.

The classification proofs are intentionally left as `proof_wanted` stubs.
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

proof_wanted typeE6_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeE6Group
proof_wanted typeE7_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeE7Group
proof_wanted typeE8_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeE8Group
proof_wanted typeF4_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeF4Group
proof_wanted typeG2_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeG2Group

proof_wanted typeH3_isIrreducible : @IsIrreducible _ typeH3Group
proof_wanted typeH4_isIrreducible : @IsIrreducible _ typeH4Group
proof_wanted typeH3_isFiniteCoxeter : @IsFiniteCoxeter _ typeH3Group
proof_wanted typeH4_isFiniteCoxeter : @IsFiniteCoxeter _ typeH4Group

end Coxeter
