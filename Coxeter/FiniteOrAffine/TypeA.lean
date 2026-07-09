module

public import Coxeter.FiniteOrAffine.TridiagonalForm
public import Coxeter.SpecialFeatures
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# The Coxeter group of type A

This file packages mathlib's `CoxeterMatrix.A n` (the Coxeter matrix whose Coxeter-Dynkin diagram
is a path on `n` vertices, corresponding to the symmetric group `S_(n+1)`) into a `CoxeterGroup`
instance, and verifies all of the `SpecialFeatures.lean` properties that apply to it:
`IsCrystallographic`, `IsIrreducible`, and (on `m + 1` generators) `IsFiniteCoxeter`,
`IsPolyFiniteWeyl`, `IsIrreducibleFiniteWeyl`.

We use the abstract presented group `(CoxeterMatrix.A n).Group` (mathlib gives us a
`CoxeterSystem` on it for free via `CoxeterMatrix.toCoxeterSystem`), exactly as
`Coxeter.componentCoxeterGroup` does for the components of a general Coxeter diagram. We do *not*
identify this group with `Equiv.Perm (Fin (n + 1))` here.

Finiteness is established via the bilinear form, not via `Finite W`: the (doubled) Gram matrix of
`bil` on type A's standard basis — `1` on the diagonal, `-1/2` on adjacent off-diagonal entries,
`0` elsewhere — is a sum of squares (`sos_identity`/`sum_range_double`):
`2 * (∑ y_i^2 - ∑ y_i y_{i+1}) = y_0^2 + y_m^2 + ∑ (y_i - y_{i+1})^2`. Reading off `≥ 0` gives
`bil.IsPosSemidef`; forcing every square to vanish when the form is `0` gives `bil.Nondegenerate`.

## Main definitions

* `Coxeter.typeAGroup`

## Main statements

* `Coxeter.typeA_isCrystallographic`
* `Coxeter.typeA_isIrreducible`
* `Coxeter.typeA_isFiniteCoxeter`
* `Coxeter.typeA_isPolyFiniteWeyl`
* `Coxeter.typeA_isIrreducibleFiniteWeyl`
-/

@[expose] public section

namespace Coxeter

/-- The Coxeter group of type `A` on `n` generators, realized as the abstract group presented by
`CoxeterMatrix.A n` (whose Coxeter-Dynkin diagram is a path on `n` vertices). -/
@[reducible] noncomputable def typeAGroup (n : ℕ) [NeZero n] :
    CoxeterGroup (CoxeterMatrix.A n).Group where
  B := Fin n
  M := CoxeterMatrix.A n
  cs := (CoxeterMatrix.A n).toCoxeterSystem

/-- Type `A`'s off-diagonal entries are always `2` or `3`, both in the crystallographic set
`{0, 2, 3, 4, 6}`. -/
theorem typeA_isCrystallographic (n : ℕ) [NeZero n] :
    @IsCrystallographic _ (typeAGroup n) := by
  intro i i' hii'
  change (CoxeterMatrix.A n) i i' = 0 ∨ (CoxeterMatrix.A n) i i' = 2 ∨
    (CoxeterMatrix.A n) i i' = 3 ∨ (CoxeterMatrix.A n) i i' = 4 ∨ (CoxeterMatrix.A n) i i' = 6
  unfold CoxeterMatrix.A
  simp only [Matrix.of_apply, if_neg hii']
  split_ifs <;> tauto

/-- Type `A`'s Coxeter-Dynkin diagram is literally the path graph on `n` vertices: two distinct
generators `i ≠ j` are joined exactly when `CoxeterMatrix.A n i j ≠ 2`, which (by the matrix's
definition) happens exactly when `i` and `j` are consecutive. -/
private theorem coxeterGraphMatrix_typeA_eq_pathGraph (n : ℕ) :
    coxeterGraphMatrix (CoxeterMatrix.A n) = SimpleGraph.pathGraph n := by
  ext i j
  rw [coxeterGraphMatrix, SimpleGraph.fromRel_adj, SimpleGraph.pathGraph_adj]
  unfold CoxeterMatrix.A
  simp only [Matrix.of_apply, ne_eq]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h)]
    have hiff1 : ¬(if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then (3 : ℕ) else 2) = 2 ↔
        ((j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j) := by
      split_ifs with hp
      · simp [hp]
      · simp [hp]
    have hiff2 : ¬(if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then (3 : ℕ) else 2) = 2 ↔
        ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) := by
      split_ifs with hp
      · simp [hp]
      · simp [hp]
    rw [hiff1, hiff2]
    tauto

/-- Type `A` on `n + 1` generators (`n ≥ 0`, i.e. the Coxeter-Dynkin diagram is nonempty) is
irreducible: its diagram is the path graph on `n + 1` vertices, which is connected. -/
theorem typeA_isIrreducible (n : ℕ) : @IsIrreducible _ (typeAGroup (n + 1)) := by
  unfold IsIrreducible IsIrreducibleMatrix
  change (coxeterGraphMatrix (CoxeterMatrix.A (n + 1))).Connected
  rw [coxeterGraphMatrix_typeA_eq_pathGraph]
  exact SimpleGraph.pathGraph_connected n

/-! ### Positive definiteness of `bil` for type A

Type A's Coxeter matrix is exactly the tridiagonal ("path graph") form handled generically by
`Coxeter.FiniteOrAffine.TridiagonalForm`: diagonal `1`s and off-diagonal `-1/2`s. `sos_identity`
there gives `2 * Q(y) = y_0^2 + y_m^2 + ∑_{i<m} (y_i - y_{i+1})^2`, letting us read off both
non-negativity and (via forcing every square to vanish) positive definiteness directly, with no
eigenvalue computation needed. -/

/-- The Gram matrix entries of `bil` on standard basis vectors of type A match `pathEntry`. -/
private theorem bil_typeA_entries (m : ℕ) (i j : Fin (m + 1)) :
    (@bil _ (typeAGroup (m + 1))) (@stdBasis _ (typeAGroup (m + 1)) i)
      (@stdBasis _ (typeAGroup (m + 1)) j) = pathEntry (i : ℕ) (j : ℕ) := by
  unfold bil
  rw [Matrix.toBilin_single]
  change -Real.cos (Real.pi / ((CoxeterMatrix.A (m + 1)) i j : ℝ)) = pathEntry (i : ℕ) (j : ℕ)
  unfold CoxeterMatrix.A pathEntry
  simp only [Matrix.of_apply]
  by_cases hij : i = j
  · have hij' : (i : ℕ) = (j : ℕ) := by rw [hij]
    rw [if_pos hij, if_pos hij']
    norm_num
  · have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rw [if_neg hij, if_neg hij']
    split_ifs with hadj
    · rw [show ((3 : ℕ) : ℝ) = 3 by norm_num, Real.cos_pi_div_three]; norm_num
    · rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, Real.cos_pi_div_two]
      norm_num

/-- Extends `x : Fin (m + 1) →₀ ℝ` to a function on all of `ℕ`, vanishing past `m`. -/
private noncomputable def typeAExtend (m : ℕ) (x : Fin (m + 1) →₀ ℝ) : ℕ → ℝ :=
  fun k => if h : k < m + 1 then x ⟨k, h⟩ else 0

private theorem typeAExtend_apply_fin (m : ℕ) (x : Fin (m + 1) →₀ ℝ) (i : Fin (m + 1)) :
    typeAExtend m x (i : ℕ) = x i := by
  unfold typeAExtend
  rw [dif_pos i.isLt]

/-- `bil x x` for type A, spelled out as the tridiagonal quadratic form on the `ℕ`-extension of
`x`'s coordinates. -/
private theorem bil_typeA_apply (m : ℕ) (x : Fin (m + 1) →₀ ℝ) :
    (@bil _ (typeAGroup (m + 1))) x x
      = ∑ i ∈ Finset.range (m + 1), (typeAExtend m x i) ^ 2
        - ∑ i ∈ Finset.range m, typeAExtend m x i * typeAExtend m x (i + 1) := by
  rw [← pathEntry_sum_range_double (typeAExtend m x) m]
  have hrepr : (@stdBasis _ (typeAGroup (m + 1))).repr x = x := rfl
  have key : (@bil _ (typeAGroup (m + 1))) x x
      = ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          x i * x j * (@bil _ (typeAGroup (m + 1)))
            (@stdBasis _ (typeAGroup (m + 1)) i) (@stdBasis _ (typeAGroup (m + 1)) j) := by
    rw [← LinearMap.BilinForm.sum_repr_mul_repr_mul
      (B := @bil _ (typeAGroup (m + 1))) (@stdBasis _ (typeAGroup (m + 1))) x x, hrepr,
      Finsupp.sum_fintype x _ (fun i => by simp)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finsupp.sum_fintype x _ (fun j => by simp)]
    simp only [smul_eq_mul, ← mul_assoc]
  rw [key]
  have hentry : ∀ i j : Fin (m + 1),
      x i * x j * (@bil _ (typeAGroup (m + 1)))
        (@stdBasis _ (typeAGroup (m + 1)) i) (@stdBasis _ (typeAGroup (m + 1)) j)
      = typeAExtend m x (i : ℕ) * typeAExtend m x (j : ℕ) * pathEntry (i : ℕ) (j : ℕ) := by
    intro i j
    rw [bil_typeA_entries, typeAExtend_apply_fin, typeAExtend_apply_fin]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin (m + 1)))) =>
    Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin (m + 1)))) => hentry i j))]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin (m + 1),
    typeAExtend m x i * typeAExtend m x j * pathEntry i j) (m + 1)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Fin.sum_univ_eq_sum_range (fun j => typeAExtend m x i * typeAExtend m x j * pathEntry i j)
    (m + 1)

/-- Type A's `bil` is positive semidefinite: `bil x x ≥ 0` for every `x`, since (doubled) it's a
sum of squares by `sos_identity`. -/
private theorem bil_typeA_isNonneg (m : ℕ) : (@bil _ (typeAGroup (m + 1))).IsNonneg := by
  rw [LinearMap.BilinForm.isNonneg_def]
  intro x
  rw [bil_typeA_apply]
  have h := sos_identity (typeAExtend m x) m
  have hC : 0 ≤ ∑ i ∈ Finset.range m, (typeAExtend m x i - typeAExtend m x (i + 1)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith [h, sq_nonneg (typeAExtend m x 0), sq_nonneg (typeAExtend m x m), hC]

/-- Type A's `bil` is nondegenerate: if `bil x x = 0`, the sum-of-squares identity forces every
`typeAExtend m x i` (`i ≤ m`) to vanish, i.e. `x = 0`. -/
private theorem bil_typeA_nondegenerate (m : ℕ) : (@bil _ (typeAGroup (m + 1))).Nondegenerate := by
  unfold LinearMap.BilinForm.Nondegenerate
  rw [LinearMap.BilinForm.nondegenerate_iff'
    (hs := (bil_typeA_isNonneg m).nonneg)
    (hB := LinearMap.BilinForm.isSymm_iff.mp (@bil_isSymm _ (typeAGroup (m + 1))))]
  intro x hx
  rcases ((bil_typeA_isNonneg m).nonneg x).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have hzero : (@bil _ (typeAGroup (m + 1))) x x = 0 := h.symm
    rw [bil_typeA_apply] at hzero
    set y := typeAExtend m x with hy_def
    have hsos := sos_identity y m
    have hC : 0 ≤ ∑ i ∈ Finset.range m, (y i - y (i + 1)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h0sq : y 0 ^ 2 = 0 := by nlinarith [hsos, hzero, sq_nonneg (y m), hC]
    have hCsum : ∑ i ∈ Finset.range m, (y i - y (i + 1)) ^ 2 = 0 := by
      nlinarith [hsos, hzero, sq_nonneg (y 0), sq_nonneg (y m)]
    have h0 : y 0 = 0 := sq_eq_zero_iff.mp h0sq
    have hstep : ∀ i ∈ Finset.range m, y i = y (i + 1) := by
      intro i hi
      have hzero_term : (y i - y (i + 1)) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hCsum i hi
      have := sq_eq_zero_iff.mp hzero_term
      linarith
    have hall : ∀ i ≤ m, y i = 0 := by
      intro i hi
      induction i with
      | zero => exact h0
      | succ k ih =>
          have hk : k < m := by omega
          rw [← hstep k (Finset.mem_range.mpr hk)]
          exact ih (by omega)
    apply Finsupp.ext
    intro i
    have hi : (i : Fin (m + 1)).val ≤ m := by omega
    have hi0 : y (i : Fin (m + 1)).val = 0 := hall _ hi
    rw [hy_def, typeAExtend_apply_fin] at hi0
    simpa using hi0

/-- Type A on `m + 1` generators is of finite type: `bil` is positive semidefinite and
nondegenerate (i.e. positive definite). -/
theorem typeA_isFiniteCoxeter (m : ℕ) : @IsFiniteCoxeter _ (typeAGroup (m + 1)) :=
  Or.inr ⟨⟨@bil_isSymm _ (typeAGroup (m + 1)), bil_typeA_isNonneg m⟩, bil_typeA_nondegenerate m⟩

/-- Type A on `m + 1` generators is a (product of) finite Weyl group(s). -/
theorem typeA_isPolyFiniteWeyl (m : ℕ) : @IsPolyFiniteWeyl _ (typeAGroup (m + 1)) :=
  ⟨typeA_isFiniteCoxeter m, typeA_isCrystallographic (m + 1)⟩

/-- Type A on `m + 1` generators is an *irreducible* finite Weyl group. -/
theorem typeA_isIrreducibleFiniteWeyl (m : ℕ) : @IsIrreducibleFiniteWeyl _ (typeAGroup (m + 1)) :=
  ⟨typeA_isPolyFiniteWeyl m, typeA_isIrreducible m⟩

end Coxeter
