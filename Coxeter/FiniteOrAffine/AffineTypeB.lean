module

public import Coxeter.SpecialFeatures

/-!
# Affine Coxeter groups of type B

This file reserves names for the affine type `B` Coxeter matrix and Coxeter group. The matrix
definition and classification proof are intentionally left as stubs.
-/

@[expose] public section

namespace Coxeter

axiom affineTypeBMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1))

@[reducible] noncomputable def affineTypeBGroup (n : ℕ) (_ : 2 ≤ n) :
    CoxeterGroup (affineTypeBMatrix n).Group where
  B := Fin (n + 1)
  M := affineTypeBMatrix n
  cs := (affineTypeBMatrix n).toCoxeterSystem

proof_wanted affineTypeB_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducibleAffineCoxeter _ (affineTypeBGroup n hn)

proof_wanted affineTypeB_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducibleAffineWeyl _ (affineTypeBGroup n hn)

end Coxeter
