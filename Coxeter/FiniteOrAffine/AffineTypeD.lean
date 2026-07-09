module

public import Coxeter.SpecialFeatures

/-!
# Affine Coxeter groups of type D

This file reserves names for the affine type `D` Coxeter matrix and Coxeter group. The matrix
definition and classification proof are intentionally left as stubs.
-/

@[expose] public section

namespace Coxeter

axiom affineTypeDMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1))

@[reducible] noncomputable def affineTypeDGroup (n : ℕ) [NeZero n] :
    CoxeterGroup (affineTypeDMatrix n).Group where
  B := Fin (n + 1)
  M := affineTypeDMatrix n
  cs := (affineTypeDMatrix n).toCoxeterSystem

proof_wanted affineTypeD_isIrreducibleAffineCoxeter (n : ℕ) [NeZero n] :
    @IsIrreducibleAffineCoxeter _ (affineTypeDGroup n)

proof_wanted affineTypeD_isIrreducibleAffineWeyl (n : ℕ) [NeZero n] :
    @IsIrreducibleAffineWeyl _ (affineTypeDGroup n)

end Coxeter
