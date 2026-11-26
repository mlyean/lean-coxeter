module

public import Coxeter.BilinearLatticeDynkins
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
