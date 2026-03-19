import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Bilinear forms

This file removes the `Fintype` and `DecidableEq` hypotheses on `BilinForm.toMatrix` and
`Matrix.toBilin` that are present in mathlib's implementation.

-/

namespace Coxeter

variable {R : Type*} {M : Type*} {ι : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (b : Module.Basis ι R M)

noncomputable def LinearMap.BilinForm.toMatrix :
  LinearMap.BilinForm R M ≃ₗ[R] Matrix ι ι R where
  toFun B i j := B (b i) (b j)
  invFun B := b.constr R ((b.constr R) ∘ B)
  map_add' := by
    intro B₁ B₂
    ext i j
    simp
  map_smul' := by
    intro m B
    ext i j
    simp
  left_inv := by
    intro B
    apply b.ext
    intro i
    apply b.ext
    intro j
    simp
  right_inv := by
    intro B
    ext i j
    simp

noncomputable def Matrix.toBilin : Matrix ι ι R ≃ₗ[R] LinearMap.BilinForm R M :=
  (LinearMap.BilinForm.toMatrix b).symm

theorem Matrix.toBilin_single (B : Matrix ι ι R) (i j : ι) : toBilin b B (b i) (b j) = B i j := by
  unfold toBilin LinearMap.BilinForm.toMatrix
  simp

end Coxeter
