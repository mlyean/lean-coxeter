module

public import Coxeter.SpecialFeatures

/-!
# Affine Coxeter groups of type C

This file defines the affine type `C` Coxeter matrix and Coxeter group. The classification
statements are left as `proof_wanted`.
-/

@[expose] public section

namespace Coxeter

/-- The Coxeter matrix of affine type `C̃ₙ`: the path `0 — 1 — ⋯ — n` whose two end edges are
labelled `4`.
```
       4                 4
    o --- o --- ⋯ --- o --- o
```
For `n = 1` the two generators are joined by an edge labelled `∞` (coded as `0`). -/
def affineTypeCMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
      else if n = 1 then 0
      else if ((i : ℕ) + (j : ℕ) = 1) ∨ ((i : ℕ) + (j : ℕ) = 2 * n - 1 ∧ (n ≤ i ∨ n ≤ j)) then 4
      else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 3 else 2
  isSymm := by grind [Matrix.IsSymm, Matrix.transpose_of]
  diagonal := by simp
  off_diagonal i j h := by
    simp only [Matrix.of_apply, h, ite_false]
    split_ifs <;> omega

@[reducible] noncomputable def affineTypeCGroup (n : ℕ) (_ : 2 ≤ n) :
    CoxeterGroup (affineTypeCMatrix n).Group where
  B := Fin (n + 1)
  M := affineTypeCMatrix n
  cs := (affineTypeCMatrix n).toCoxeterSystem

proof_wanted affineTypeC_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducibleAffineCoxeter _ (affineTypeCGroup n hn)

proof_wanted affineTypeC_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducibleAffineWeyl _ (affineTypeCGroup n hn)

end Coxeter
