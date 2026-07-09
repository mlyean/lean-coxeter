module

public import Coxeter.FiniteOrAffine.TypeA
public import Coxeter.SpecialFeatures

/-!
# The Coxeter group of type D

This file packages the finite Coxeter group of type `D`.

The classification proofs are intentionally left as `proof_wanted` stubs.

Mathlib's current uniform `CoxeterMatrix.D` formula has the wrong small-rank behavior at `n = 3`,
where it produces a triangle rather than the classical `D₃ = A₃`. The local `typeDMatrix`
normalizes the small ranks by using type `A` for `n ≤ 3`, and uses mathlib's `CoxeterMatrix.D`
from rank `4` onward.
-/

@[expose] public section

namespace Coxeter

/-- The Coxeter matrix of finite type `D` on `n` generators.

For `n ≤ 3` this is normalized to the classical accidental type `Aₙ`; from rank `4` onward it is
mathlib's `CoxeterMatrix.D n`. -/
noncomputable def typeDMatrix (n : ℕ) : CoxeterMatrix (Fin n) :=
  if n ≤ 3 then CoxeterMatrix.A n else CoxeterMatrix.D n

/-- The Coxeter group of finite type `D` on `n` generators, realized as the abstract group
presented by `typeDMatrix n`. -/
@[reducible] noncomputable def typeDGroup (n : ℕ) [NeZero n] :
    CoxeterGroup (typeDMatrix n).Group where
  B := Fin n
  M := typeDMatrix n
  cs := (typeDMatrix n).toCoxeterSystem

/-- Type `D`'s normalized matrix is crystallographic in every nonempty rank. -/
theorem typeD_isCrystallographic (n : ℕ) [NeZero n] :
    @IsCrystallographic _ (typeDGroup n) := by
  intro i i' hii'
  change (typeDMatrix n) i i' = 0 ∨ (typeDMatrix n) i i' = 2 ∨
    (typeDMatrix n) i i' = 3 ∨ (typeDMatrix n) i i' = 4 ∨
    (typeDMatrix n) i i' = 6
  unfold typeDMatrix
  by_cases h : n ≤ 3
  · simp only [if_pos h]
    unfold CoxeterMatrix.A
    simp only [Matrix.of_apply, if_neg hii']
    split_ifs <;> tauto
  · simp only [if_neg h]
    unfold CoxeterMatrix.D
    simp only [Matrix.of_apply, if_neg hii']
    split_ifs <;> tauto

proof_wanted typeD_isIrreducible (n : ℕ) : @IsIrreducible _ (typeDGroup (n + 4))

axiom typeD_isFiniteCoxeter (n : ℕ) : @IsFiniteCoxeter _ (typeDGroup (n + 4))

theorem typeD_isPolyFiniteWeyl (n : ℕ) : @IsPolyFiniteWeyl _ (typeDGroup (n + 4)) :=
  ⟨typeD_isFiniteCoxeter n, typeD_isCrystallographic (n + 4)⟩

proof_wanted typeD_isIrreducibleFiniteWeyl (n : ℕ) :
    @IsIrreducibleFiniteWeyl _ (typeDGroup (n + 4))

/-! ### Small-rank accidental identifications -/

section Accidentals

private theorem typeDMatrix_one_eq_A_one : typeDMatrix 1 = CoxeterMatrix.A 1 := by
  unfold typeDMatrix
  simp

private theorem typeDMatrix_two_eq_A_two : typeDMatrix 2 = CoxeterMatrix.A 2 := by
  unfold typeDMatrix
  simp

private theorem typeDMatrix_three_eq_A_three : typeDMatrix 3 = CoxeterMatrix.A 3 := by
  unfold typeDMatrix
  simp

/-- The Coxeter-system-level accidental identification `D₁ = A₁`.

The entrywise matrix equality used to prove this is private. -/
theorem typeD_one_identifies_typeA_one :
    HEq (@CoxeterGroup.cs _ (typeDGroup 1)) (@CoxeterGroup.cs _ (typeAGroup 1)) := by
  change HEq (typeDMatrix 1).toCoxeterSystem (CoxeterMatrix.A 1).toCoxeterSystem
  rw [← typeDMatrix_one_eq_A_one]

/-- The Coxeter-system-level accidental identification `D₂ = A₂`.

The entrywise matrix equality used to prove this is private. -/
theorem typeD_two_identifies_typeA_two :
    HEq (@CoxeterGroup.cs _ (typeDGroup 2)) (@CoxeterGroup.cs _ (typeAGroup 2)) := by
  change HEq (typeDMatrix 2).toCoxeterSystem (CoxeterMatrix.A 2).toCoxeterSystem
  rw [← typeDMatrix_two_eq_A_two]

/-- The Coxeter-system-level accidental identification `D₃ = A₃`.

The entrywise matrix equality used to prove this is private. -/
theorem typeD_three_identifies_typeA_three :
    HEq (@CoxeterGroup.cs _ (typeDGroup 3)) (@CoxeterGroup.cs _ (typeAGroup 3)) := by
  change HEq (typeDMatrix 3).toCoxeterSystem (CoxeterMatrix.A 3).toCoxeterSystem
  rw [← typeDMatrix_three_eq_A_three]

end Accidentals

end Coxeter
