module

public import Coxeter.BilinearLattice
public import Coxeter.SpecialFeatures
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Bilinear lattices of Dynkin and extended Dynkin type

This file connects `Coxeter.BilinearLattice` and
`Coxeter.BilinearLattice.WithMonoidQuasiUnipotent` to Coxeter systems.

## The dictionary

Let `M` be a *simply-laced* Coxeter matrix on
`Fin n` (`M i j ∈ {2, 3}` off the diagonal), and
orient each edge `i — j` of its diagram from the smaller to the larger index.
This orientation gives a quiver without oriented cycles.
Its **Euler form** has Gram matrix `C = eulerMatrix M`,
which is upper unitriangular: `C i i = 1`, and
`C i j = -1` for `i < j` joined by an edge.

* `χ x y = xᵀ C y` is unimodular,
since `det C = 1` (`det_eulerMatrix`).
* `S = -C⁻¹ Cᵀ` is the **Coxeter transformation**
  (`ofUnimodular`).
* The symmetrization `C + Cᵀ`
  is the Cartan matrix, which is twice the Gram matrix of the
  Coxeter form `bil` (`eulerMatrix_add_transpose`).
  So the quadratic form `x ↦ χ x x` is the
  restriction of `bil` to the root lattice `ℤⁿ` (`eulerLattice_χ_self`).
* The distinguished submonoid is the cone of dimension vectors `positiveCone n`.
* Disjoint unions of diagrams
  correspond to the orthogonal direct sum `BilinearLattice.prod`.

Under this dictionary,
the classification of the diagram is reflected by `S`:

* **Dynkin** (`bil` positive definite): `S` has finite order (the Coxeter number), so it is
  quasi-unipotent of index `1`. This is for case of disjoint union of Dynkin diagrams
  which is the only case of positive definite `bil` within this realm.
* **Extended Dynkin** (`bil` positive semidefinite with nonzero radical):
  `S` fixes the radical and has finite order modulo it,
  so it is quasi-unipotent of index `2` but not `1`.
  This is for the case of disjoint union of extended Dynkin diagrams,
  (at least one of which is extended)
  which is the only case of positive semidefinite `bil` within this realm.
* Otherwise (`bil` indefinite) the spectral radius of `S` exceeds `1` (A'Campo), so `S` is not
  quasi-unipotent of any index.

So among Euler lattices of simply-laced diagrams,
the objects of `WithMonoidQuasiUnipotent` are
exactly the disjoint unions of Dynkin and extended Dynkin diagrams.
The forward direction goes
through the deferred `IsPsdQuasiUnipotent`
The converse is A'Campo's theorem (`proof_wanted`
below).

Each type's Euler lattice is named in its own file under `Coxeter.FiniteOrAffine`
(e.g. `typeABilinearLattice`, `affineTypeDBilinearLattice`).

## Main definitions

* `Coxeter.BilinearLattice.IsSimplyLaced`
* `Coxeter.BilinearLattice.eulerMatrix`, `Coxeter.BilinearLattice.eulerLattice`
* `Coxeter.BilinearLattice.eulerLatticeWithMonoid`

## Main statements

* `Coxeter.BilinearLattice.eulerMatrix_add_transpose`
* `Coxeter.BilinearLattice.eulerLattice_χ_self`
-/

@[expose] public section

namespace Coxeter

namespace BilinearLattice

open _root_.Matrix

variable {n : ℕ}

/-- A Coxeter matrix is *simply laced*
if every off-diagonal entry is `2` or `3`. -/
def IsSimplyLaced (M : CoxeterMatrix (Fin n)) : Prop :=
  ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3

/-- The Gram matrix of the
Euler form of the quiver
obtained by orienting each edge of `M`'s
diagram from the smaller to the larger index. -/
def eulerMatrix (M : CoxeterMatrix (Fin n)) :
  Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j ↦ if i = j then 1 else if i < j ∧ M i j = 3 then -1 else 0

theorem det_eulerMatrix (M : CoxeterMatrix (Fin n)) : (eulerMatrix M).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [eulerMatrix]
  · intro i j hji
    simp only [id] at hji
    simp [eulerMatrix, (ne_of_lt hji).symm, not_lt_of_gt hji]

/-- The Euler lattice of a Coxeter matrix:
`ℤⁿ` with the Euler form and the Coxeter transformation. -/
@[implicit_reducible]
noncomputable def eulerLattice (M : CoxeterMatrix (Fin n)) : BilinearLattice.{0} :=
  ofUnimodular (eulerMatrix M) (by rw [det_eulerMatrix]; exact isUnit_one)

/-- The Euler lattice of `M` with the cone of dimension vectors `positiveCone n`, given that its
Coxeter transformation is quasi-unipotent of index at most `2`. -/
noncomputable def eulerLatticeWithMonoidQuasiUnipotent
  (M : CoxeterMatrix (Fin n))
  (hS : Module.End.IsQuasiUnipotentOfIndex
    ((eulerLattice M).S : Module.End ℤ (eulerLattice M)) 2)
  : BilinearLatticeWithMonoidQuasiUnipotent where
  toBilinearLattice := eulerLattice M
  P := positiveCone n
  isQuasiUnipotent := hS


/-- `M` as a Coxeter group, so that its Coxeter form `bil` is available. -/
@[reducible] noncomputable def coxeterGroupOf (M : CoxeterMatrix (Fin n)) :
    CoxeterGroup M.Group where
  B := Fin n
  M := M
  cs := M.toCoxeterSystem

open Real in
/-- The symmetrization of the Euler form is twice the Coxeter form: `C + Cᵀ` is the Cartan
matrix `2 * (-cos (π / M i j))`. -/
theorem eulerMatrix_add_transpose (M : CoxeterMatrix (Fin n)) (hM : IsSimplyLaced M)
    (i j : Fin n) :
    ((eulerMatrix M i j + eulerMatrix M j i : ℤ) : ℝ) = 2 * -cos (π / M i j) := by
  rcases eq_or_ne i j with rfl | hij
  · simp [eulerMatrix]
  have hji : j ≠ i := hij.symm
  rcases hM i j hij with h | h
  · have h' : M j i = 2 := by rw [M.symmetric]; exact h
    simp [eulerMatrix, hij, hji, h, h']
  · have h' : M j i = 3 := by rw [M.symmetric]; exact h
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · simp [eulerMatrix, hij, hji, h, h', hlt, not_lt_of_gt hlt]
    · simp [eulerMatrix, hij, hji, h, h', hlt, not_lt_of_gt hlt]

/-- The embedding of the root lattice `ℤⁿ` into `bil`'s space `Fin n →₀ ℝ`. -/
noncomputable def toV (x : Fin n → ℤ) : Fin n →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ (x i : ℝ)

/-- The quadratic form of the Euler lattice is the restriction of the Coxeter form `bil` to the
root lattice. -/
theorem eulerLattice_χ_self (M : CoxeterMatrix (Fin n)) (hM : IsSimplyLaced M)
    (x : Fin n → ℤ) :
    ((eulerLattice M).χ x x : ℝ) = @bil M.Group (coxeterGroupOf M) (toV x) (toV x) := by
  set C := eulerMatrix M
  have hχ : ((eulerLattice M).χ x x : ℝ) = ∑ i, ∑ j, (x i : ℝ) * C i j * x j := by
    change ((ofUnimodular C _).χ x x : ℝ) = _
    rw [ofUnimodular_χ_apply]
    simp [dotProduct, _root_.Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hbil : @bil M.Group (coxeterGroupOf M) (toV x) (toV x) =
      ∑ i, ∑ j, (x i : ℝ) * -Real.cos (Real.pi / M i j) * x j := by
    let := coxeterGroupOf M
    have hv : toV x = ∑ i, (x i : ℝ) • (stdBasis (W := M.Group)) i := by
      ext k
      simp [toV, stdBasis, Finsupp.single_apply]
    rw [hv]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, bil_eq,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      rw [M.symmetric i j]
      ring_nf
      rfl
  have hsym : ∑ i, ∑ j, (x i : ℝ) * C i j * x j = ∑ i, ∑ j, (x i : ℝ) * C j i * x j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  have h2 : 2 * ∑ i, ∑ j, (x i : ℝ) * C i j * x j =
      2 * ∑ i, ∑ j, (x i : ℝ) * -Real.cos (Real.pi / M i j) * x j := by
    calc 2 * ∑ i, ∑ j, (x i : ℝ) * C i j * x j
        = ∑ i, ∑ j, (x i : ℝ) * ((C i j + C j i : ℤ) : ℝ) * x j := by
          rw [two_mul]
          nth_rw 2 [hsym]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ ↦ by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun j _ ↦ by push_cast; ring
      _ = 2 * ∑ i, ∑ j, (x i : ℝ) * -Real.cos (Real.pi / M i j) * x j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ ↦ by
              rw [eulerMatrix_add_transpose M hM]; ring
  rw [hχ, hbil]
  linarith

/-- A positive semidefinite Coxeter form makes the Euler form nonnegative on `ℤⁿ`. -/
theorem eulerLattice_χ_self_nonneg (M : CoxeterMatrix (Fin n)) (hM : IsSimplyLaced M)
    (hpsd : (@bil M.Group (coxeterGroupOf M)).IsPosSemidef) (x : Fin n → ℤ) :
    0 ≤ (eulerLattice M).χ x x := by
  have : (0 : ℝ) ≤ (eulerLattice M).χ x x := by
    rw [eulerLattice_χ_self M hM]
    exact hpsd.isNonneg.nonneg _
  exact_mod_cast this

/-- **A'Campo**:
for the Euler lattice of a simply-laced diagram
quasi-unipotence of `S` (of any index)
forces the Coxeter form to be positive semidefinite. -/
proof_wanted isPosSemidef_of_isQuasiUnipotentOfIndex (M : CoxeterMatrix (Fin n))
    (hM : IsSimplyLaced M) {k : ℕ}
    (h : Module.End.IsQuasiUnipotentOfIndex
      ((eulerLattice M).S : Module.End ℤ (eulerLattice M)) k) :
    (@bil M.Group (coxeterGroupOf M)).IsPosSemidef

end BilinearLattice

end Coxeter
