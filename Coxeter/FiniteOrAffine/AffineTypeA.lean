module

public import Coxeter.SpecialFeatures

/-!
# Affine Coxeter groups of type A

This file reserves names for the affine type `A` Coxeter matrix and Coxeter group. The matrix
definition and classification proof are intentionally left as stubs.
-/

@[expose] public section

namespace Coxeter

axiom affineTypeAMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1))

@[reducible] noncomputable def affineTypeAGroup (n : ℕ) [NeZero n] :
    CoxeterGroup (affineTypeAMatrix n).Group where
  B := Fin (n + 1)
  M := affineTypeAMatrix n
  cs := (affineTypeAMatrix n).toCoxeterSystem

proof_wanted affineTypeA_isIrreducibleAffineCoxeter (n : ℕ) [NeZero n] :
    @IsIrreducibleAffineCoxeter _ (affineTypeAGroup n)

proof_wanted affineTypeA_isIrreducibleAffineWeyl (n : ℕ) [NeZero n] :
    @IsIrreducibleAffineWeyl _ (affineTypeAGroup n)

end Coxeter
