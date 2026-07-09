module

public import Coxeter.FiniteOrAffine.AffineTypeB
public import Coxeter.SpecialFeatures

/-!
# Affine Coxeter groups of type C

This file reserves names for the affine type `C` Coxeter matrix and Coxeter group. The matrix
definition and classification proof are intentionally left as stubs.
-/

@[expose] public section

namespace Coxeter

axiom affineTypeCMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1))

@[reducible] noncomputable def affineTypeCGroup (n : ℕ) (_ : 2 ≤ n) :
    CoxeterGroup (affineTypeCMatrix n).Group where
  B := Fin (n + 1)
  M := affineTypeCMatrix n
  cs := (affineTypeCMatrix n).toCoxeterSystem

proof_wanted affineTypeC_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducibleAffineCoxeter _ (affineTypeCGroup n hn)

proof_wanted affineTypeC_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducibleAffineWeyl _ (affineTypeCGroup n hn)

/-! ### Accidental low-rank affine identifications -/

section Accidentals

/-- The Coxeter-system-level accidental identification `C₂-hat = B₂-hat`.

The matrix-level identification is not public; the affine matrices are currently stubs. -/
proof_wanted affineTypeC_two_identifies_affineTypeB_two :
    HEq (@CoxeterGroup.cs _ (affineTypeCGroup 2 (by omega)))
      (@CoxeterGroup.cs _ (affineTypeBGroup 2 (by omega)))

end Accidentals

end Coxeter
