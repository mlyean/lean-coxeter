module

public import Coxeter.FiniteOrAffine.AffineTypeC
public import Coxeter.SpecialFeatures

/-!
# Affine Coxeter groups of type B

This file defines the affine type `B` Coxeter matrix and Coxeter group, and proves the accidental
identification `B̃₂ = C̃₂`. The classification statements are left as `proof_wanted`.
-/

@[expose] public section

namespace Coxeter

/-- The Coxeter matrix of affine type `B̃ₙ`, `n ≥ 3`: mathlib's `Bₙ` diagram on `0, …, n - 1` (the
path whose last edge, `n - 2 — n - 1`, is labelled `4`), plus the node `n` attached to `1`.
```
    0
     \               4
      1 --- ⋯ --- o --- o
     /
    n
```
-/
def affineTypeBForkMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
      else if ((i : ℕ) = n - 2 ∧ (j : ℕ) = n - 1) ∨ ((j : ℕ) = n - 2 ∧ (i : ℕ) = n - 1) then 4
      else if ((i : ℕ) + 1 = j ∧ (j : ℕ) ≤ n - 2) ∨ ((j : ℕ) + 1 = i ∧ (i : ℕ) ≤ n - 2) ∨
        ((i : ℕ) = 1 ∧ (j : ℕ) = n) ∨ ((j : ℕ) = 1 ∧ (i : ℕ) = n) then 3 else 2
  isSymm := by grind [Matrix.IsSymm, Matrix.transpose_of]
  diagonal := by simp
  off_diagonal i j h := by
    simp only [Matrix.of_apply, h, ite_false]
    split_ifs <;> omega

/-- The Coxeter matrix of affine type `B̃ₙ` on `n + 1` generators.

From rank `3` onward it is `affineTypeBForkMatrix n`; for `n ≤ 2` it is normalized to `C̃ₙ`, so that
`B̃₂ = C̃₂` holds on the nose. -/
def affineTypeBMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1)) :=
  if n ≤ 2 then affineTypeCMatrix n else affineTypeBForkMatrix n

@[reducible] noncomputable def affineTypeBGroup (n : ℕ) (_ : 2 ≤ n) :
    CoxeterGroup (affineTypeBMatrix n).Group where
  B := Fin (n + 1)
  M := affineTypeBMatrix n
  cs := (affineTypeBMatrix n).toCoxeterSystem

proof_wanted affineTypeB_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducibleAffineCoxeter _ (affineTypeBGroup n hn)

proof_wanted affineTypeB_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducibleAffineWeyl _ (affineTypeBGroup n hn)

/-! ### Accidental low-rank affine identifications -/

section Accidentals

theorem affineTypeBMatrix_two : affineTypeBMatrix 2 = affineTypeCMatrix 2 := ite_eq_left le_rfl

/-- The Coxeter-system-level accidental identification `C̃₂ = B̃₂`. -/
theorem affineTypeC_two_identifies_affineTypeB_two :
    HEq (@CoxeterGroup.cs _ (affineTypeCGroup 2 (by omega)))
      (@CoxeterGroup.cs _ (affineTypeBGroup 2 (by omega))) := by
  change HEq (affineTypeCMatrix 2).toCoxeterSystem (affineTypeBMatrix 2).toCoxeterSystem
  rw [affineTypeBMatrix_two]

end Accidentals

end Coxeter
