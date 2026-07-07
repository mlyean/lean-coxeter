module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Data.Real.Sqrt
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Bilinear forms

This file relates bilinar forms and matrices, and proves properties about real vector spaces with
positive definite symmetric bilinear forms.
-/

@[expose] public section

namespace Coxeter

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {ι : Type*} (b : Module.Basis ι R M)

/-- Omits the `Fintype` and `DecidableEq` hypotheses from mathlib's version -/
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

/-- Omits the `Fintype` and `DecidableEq` hypotheses from mathlib's version -/
noncomputable def Matrix.toBilin : Matrix ι ι R ≃ₗ[R] LinearMap.BilinForm R M :=
  (LinearMap.BilinForm.toMatrix b).symm

theorem Matrix.toBilin_single (B : Matrix ι ι R) (i j : ι) : toBilin b B (b i) (b j) = B i j := by
  unfold toBilin LinearMap.BilinForm.toMatrix
  simp

section BlockDiagonal

variable {κ : Type*} {ιk : κ → Type*}

/-- If the matrix of a bilinear form `B` (w.r.t. a basis indexed by a disjoint union `Σ k, ιk k`)
is block diagonal, with each block itself the matrix of a bilinear form `Bk k` on the free module
`ιk k →₀ R` (w.r.t. its standard basis `Finsupp.basisSingleOne`), and some block `Bk k₀` is
degenerate (not left-separating), then `B` itself is degenerate.

Proof idea (currently unproved — pick up here):
* Unfold `¬ (Bk k₀).SeparatingLeft` (`LinearMap.SeparatingLeft`, `not_forall`) to get `x ≠ 0` in
  `ιk k₀ →₀ R` with `∀ y, Bk k₀ x y = 0`.
* The witness for `¬ B.SeparatingLeft` is `x' := x.sum (fun j r => r • b ⟨k₀, j⟩)` — `x` padded
  with zeros outside block `k₀`.
* `x' ≠ 0`: `b` is a basis (so `b ⟨k₀, ·⟩` is injective / linearly independent) and `x ≠ 0`.
* `∀ z, B x' z = 0`: reduce to `z = b l` for `l : Σ k, ιk k` via `Module.Basis.ext` (a linear map
  vanishing on a basis is the zero map). Then
  `B x' (b l) = x.sum (fun j r => r * (toMatrix b B) ⟨k₀, j⟩ l)`
  (unfold via `B.flip (b l) : M →ₗ[R] R`, `map_sum` after `unfold Finsupp.sum` — `map_finsupp_sum`
  does not exist under that name in this mathlib version, use `map_sum f (fun a => g a (l a))
  l.support` instead — plus `map_smul`/`smul_eq_mul` and the definitional
  `(toMatrix b B) i j = B (b i) (b j)`).
  Rewrite the matrix entry via `hB` and `Matrix.blockDiagonal'_apply'`:
  - if `k₀ ≠ l.1`: every term is `r * 0`, so the sum is `0` (`Finsupp.sum` of the zero function).
  - if `k₀ = l.1` (with `m := cast _ l.2 : ιk k₀`): the sum becomes
    `x.sum (fun j r => r * (toMatrix Finsupp.basisSingleOne (Bk k₀)) j m)`, which is exactly
    `Bk k₀ x (Finsupp.basisSingleOne m)` run through the *same* unfolding (using
    `x = x.sum (fun j r => r • Finsupp.basisSingleOne j)`, from `Finsupp.sum_single` +
    `Finsupp.coe_basisSingleOne`) — so it equals `0` by `hx`. -/
theorem LinearMap.BilinForm.not_separatingLeft_of_toMatrix_eq_blockDiagonal' [DecidableEq κ]
    (b : Module.Basis (Σ k, ιk k) R M) (B : LinearMap.BilinForm R M)
    (Bk : ∀ k, LinearMap.BilinForm R (ιk k →₀ R))
    (hB : LinearMap.BilinForm.toMatrix b B =
      Matrix.blockDiagonal' (fun k => LinearMap.BilinForm.toMatrix Finsupp.basisSingleOne (Bk k)))
    {k₀ : κ} (hdeg : ¬ (Bk k₀).SeparatingLeft) :
    ¬ B.SeparatingLeft := by
  sorry

end BlockDiagonal

section real

/-! ### Positive definite symmetric bilinear forms on real vector spaces -/

open Real

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

section BlockDiagonalPosSemidef

variable {κ : Type*} {ιk : κ → Type*}

/-- The positive-semidefinite analogue of
`LinearMap.BilinForm.not_separatingLeft_of_toMatrix_eq_blockDiagonal'`: if the matrix of `B` is
block diagonal with blocks the matrices of `Bk k` (w.r.t. `Finsupp.basisSingleOne`), and every
block `Bk k` is positive semidefinite, then `B` is positive semidefinite.

Proof idea (currently unproved — pick up here):
* `IsSymm`: `B (b l) (b l') = (toMatrix b B) l l' = blockDiagonal' ... l l'`; this is symmetric in
  `l, l'` termwise (`0` off the diagonal blocks, and `(Bk k).IsSymm` on the diagonal block), so
  `B.IsSymm` follows from `LinearMap.BilinForm.isSymm_iff_basis b` (already used for `bil_isSymm`
  in `Coxeter/GeometricRepresentation.lean`) plus a case split on whether `l, l'` share a block.
* `IsNonneg`, i.e. `∀ x, 0 ≤ B x x`: write `x = b.repr.symm (b.repr x)`; group `b.repr x : (Σ k, ιk
  k) →₀ ℝ` by its first (block) coordinate to get, for each block `k` in the *finite* set
  `(b.repr x).support.image Sigma.fst`, a vector `xk : ιk k →₀ ℝ` (the restriction of `b.repr x` to
  block `k`, via `Finsupp.comapDomain`/`Finsupp.subtypeDomain` composed with `Equiv.sigmaFiberEquiv`
  as in `Coxeter/Component.lean`'s `blockEquiv`). Off-diagonal-block terms of `B x x` vanish (same
  `blockDiagonal'_apply'` case split as the degenerate-case lemma), so `B x x` reduces to a *finite*
  sum `∑ k ∈ s, Bk k xk xk`, and each summand is `≥ 0` by `hpsd k`, hence so is the sum. -/
theorem LinearMap.BilinForm.isPosSemidef_of_toMatrix_eq_blockDiagonal' [DecidableEq κ]
    (b : Module.Basis (Σ k, ιk k) ℝ V) (B : LinearMap.BilinForm ℝ V)
    (Bk : ∀ k, LinearMap.BilinForm ℝ (ιk k →₀ ℝ))
    (hB : LinearMap.BilinForm.toMatrix b B =
      Matrix.blockDiagonal' (fun k =>
        LinearMap.BilinForm.toMatrix Finsupp.basisSingleOne (Bk k)))
    (hpsd : ∀ k, (Bk k).IsPosSemidef) :
    B.IsPosSemidef := by
  sorry

end BlockDiagonalPosSemidef

def Orthonormal {ι : Type*} (B : LinearMap.BilinForm ℝ V) (v : ι → V) :=
  (∀ (i : ι), B (v i) (v i) = 1) ∧ LinearMap.IsOrthoᵢ B v

/-- A positive definite symmetric bilinear form on a finite dimensional real vector space has an
orthonormal basis. -/
theorem exists_orthonormal_basis [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V)
  (hB1 : B.IsSymm) (hB2 : B.IsNonneg) (hB3 : B.Nondegenerate) :
  ∃ (v : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V), Orthonormal B v := by
  rw [LinearMap.BilinForm.isSymm_iff] at hB1
  have ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB1
  have h1 : ∀ (i : Fin (Module.finrank ℝ V)), B (v i) (v i) > 0 := by
    intro i
    unfold LinearMap.BilinForm.Nondegenerate at hB3
    rw [LinearMap.BilinForm.nondegenerate_iff' _ hB2.nonneg hB1] at hB3
    apply hB3
    exact v.ne_zero i
  have h2 : ∀ (i : Fin (Module.finrank ℝ V)), IsUnit (1 / sqrt (B (v i) (v i))) := by
    intro i
    apply Ne.isUnit
    grind
  let w := v.unitsSMul (fun i => (h2 i).choose)
  exists w
  constructor
  · intro i
    unfold w
    rw [Module.Basis.unitsSMul_apply]
    change (B ((h2 i).choose.val • v i)) ((h2 i).choose.val • v i) = 1
    rw [(h2 i).choose_spec]
    simp
    grind
  · intro i j h
    change B (w i) (w j) = 0
    unfold w
    simp only [Module.Basis.unitsSMul_apply, LinearMap.map_smul_of_tower, LinearMap.smul_apply]
    rw [hv h]
    simp

variable {W : Submodule ℝ V} [FiniteDimensional ℝ W]

/-- If $V$ is an arbitrary real vector space equipped with a positive definite symmetric
bilinar form and $W$ is a finite dimensional subspace, then $V$ is a sum of $W$ and its
orthogonal complement. -/
theorem sup_orthogonal_eq_top (B : LinearMap.BilinForm ℝ V)
  (hB1 : B.IsSymm) (hB2 : (B.restrict W).IsNonneg) (hB3 : (B.restrict W).Nondegenerate) :
  W ⊔ W.orthogonalBilin B = ⊤ := by
  have hB1' : (B.restrict W).IsSymm := by
    exact hB1.restrict W
  have ⟨v, hv1, hv2⟩ := exists_orthonormal_basis (B.restrict W) hB1' hB2 hB3
  rw [Submodule.sup_eq_top_iff]
  intro x
  let u : W := ∑ (i : Fin (Module.finrank ℝ W)), B x (v i) • v i
  exists u
  refine ⟨u.prop, x - u, ?_, by simp⟩
  rw [Submodule.mem_orthogonalBilin_iff]
  unfold LinearMap.IsOrtho
  conv =>
    intro
    rw [hB1.eq, ←LinearMap.mem_ker]
  change W ≤ (B (x - ↑u)).ker
  have : Submodule.span ℝ (Set.range (Subtype.val ∘ v)) = W := by
    apply Submodule.span_eq_of_le
    · rw [Set.range_subset_iff]
      intro i
      simp
    · intro w hw
      rw [Submodule.mem_span_set']
      exists Module.finrank ℝ W, v.repr ⟨w, hw⟩, fun i => ⟨(v i).val, by simp⟩
      have h1 : ∑ (i : Fin (Module.finrank ℝ W)), (v.repr ⟨w, hw⟩ i) • (v i) = w := by simp
      conv =>
        lhs
        congr
        · skip
        · intro i
          change ((v.repr ⟨w, hw⟩) i • (v i)).val
      rwa [←Submodule.coe_sum]
  nth_rw 1 [←this]
  rw [Submodule.span_le, Set.range_subset_iff]
  intro i
  simp only [map_sub, Function.comp_apply, SetLike.mem_coe, LinearMap.mem_ker,
    LinearMap.sub_apply]
  rw [sub_eq_zero]
  symm
  unfold u
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, map_sum, map_smul,
    LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  change ∑ j, B x (v j) * B (v j) (v i) = B x (v i)
  have : ∀ (i j : Fin (Module.finrank ℝ W)), (B x (v j)) * B (v j) (v i)
    = Set.indicator {i} (fun j => B x (v j)) j := by
    intro i j
    by_cases h : j = i
    · simp only [h, Set.mem_singleton_iff, Set.indicator_of_mem]
      have : B (v i).val (v i).val = 1 := hv1 i
      rw [this, mul_one]
    · simp only [Set.mem_singleton_iff, h, not_false_eq_true, Set.indicator_of_notMem,
        mul_eq_zero]
      right
      exact hv2 h
  conv =>
    lhs
    congr
    · skip
    · intro j
      rw [this]
  simp

end real

end Coxeter
