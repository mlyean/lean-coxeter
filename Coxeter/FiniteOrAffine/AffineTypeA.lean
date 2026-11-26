module

public import Coxeter.BilinearLatticeDynkins
public import Coxeter.SpecialFeatures

/-!
# Affine Coxeter groups of type A

This file defines the affine type `A` Coxeter matrix and Coxeter group, proves that `Ãₙ` is an
irreducible affine Coxeter group and an irreducible affine Weyl group for `n ≥ 1`, and defines the
Euler lattice of `Ãₙ` for `n ≥ 2`, whose Coxeter transformation is quasi-unipotent of index exactly
`2`.

## Main definitions

* `Coxeter.affineTypeAMatrix`: the Coxeter matrix of `Ãₙ`, a cycle on `n + 1` generators.
* `Coxeter.affineTypeABilinearLattice`: its Euler lattice.

## Main statements

* `Coxeter.affineTypeA_isIrreducibleAffineCoxeter`, `Coxeter.affineTypeA_isIrreducibleAffineWeyl`
* `Coxeter.affineTypeABilinearLattice_isQuasiUnipotent`

## Implementation notes

With the edges oriented from smaller to larger index, the quiver of `Ãₙ` has the two paths
`0 → 1 → ⋯ → n` and `0 → n`. Extending `x : Fin (n + 1) → ℤ` to `ℤ` by
`X (j) = x (j mod n) - ⌊j / n⌋ φ(x)`, where `φ(x) = x₀ - xₙ`, the Coxeter transformation becomes a
shift plus a constant: `(S x)ᵢ = φ(x) + X (i - 1)`. Hence `(S ^ k x)ᵢ = k φ(x) + X (i - k)`, and in
particular `S ^ n x = x + (n + 1) φ(x) • (1, …, 1)`.
-/

@[expose] public section

namespace Coxeter

/-- The Coxeter matrix of affine type `Ãₙ`: the generators `0, …, n` form a cycle. For `n = 1` the
two generators are joined by an edge labelled `∞` (coded as `0`). -/
def affineTypeAMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
      else if n = 1 then 0
      else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i ∨ ((i : ℕ) = 0 ∧ (j : ℕ) = n) ∨
        ((j : ℕ) = 0 ∧ (i : ℕ) = n) then 3 else 2
  isSymm := by grind [Matrix.IsSymm, Matrix.transpose_of]
  diagonal := by simp
  off_diagonal i j h := by
    simp only [Matrix.of_apply, h, ite_false]
    split_ifs <;> omega

@[reducible] noncomputable def affineTypeAGroup (n : ℕ) [NeZero n] :
    CoxeterGroup (affineTypeAMatrix n).Group where
  B := Fin (n + 1)
  M := affineTypeAMatrix n
  cs := (affineTypeAMatrix n).toCoxeterSystem

/-! ### `Ãₙ` is an irreducible affine Weyl group

Indexing the cycle by `Fin (n + 1)`, whose addition wraps around, the neighbours of `i` are
`i + 1` and `i - 1`, and `bil x x = ½ ∑ᵢ (xᵢ - xᵢ₊₁)²`. -/

section Classification

variable {n : ℕ} [NeZero n]

/-- The Gram entries of `bil` for `Ãₙ`, `n ≥ 1`: `1` on the diagonal and `-½` for each of the two
cyclic neighbours. For `n = 1` the two neighbours coincide, giving `-1` (the edge labelled `∞`). -/
private theorem affineTypeA_gram (i j : Fin (n + 1)) :
    -Real.cos (Real.pi / (affineTypeAMatrix n i j : ℝ)) =
      (if j = i then 1 else 0) - (if j = i + 1 then 1 / 2 else 0) -
        (if j = i - 1 then 1 / 2 else 0) := by
  have hn := NeZero.ne n
  have hi := i.isLt
  have hj := j.isLt
  have h0 : j = i ↔ (j : ℕ) = i := Fin.ext_iff
  have h1 : j = i + 1 ↔ ((i : ℕ) + 1 = j ∨ ((i : ℕ) = n ∧ (j : ℕ) = 0)) := by
    rw [Fin.ext_iff, Fin.val_add_one]
    split_ifs with h <;> simp only [Fin.ext_iff, Fin.val_last] at h <;> omega
  have h2 : j = i - 1 ↔ ((j : ℕ) + 1 = i ∨ ((i : ℕ) = 0 ∧ (j : ℕ) = n)) := by
    rw [Fin.ext_iff, Fin.coe_sub_one]
    split_ifs with h <;> simp only [Fin.ext_iff, Fin.val_zero] at h <;> omega
  simp only [h0, h1, h2]
  unfold affineTypeAMatrix
  simp only [Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first
    | omega
    | norm_num [Real.cos_pi_div_three]

/-- `bil x x = ½ ∑ᵢ (xᵢ - xᵢ₊₁)²` around the cycle. -/
private theorem affineTypeA_bil_eq (x : Fin (n + 1) →₀ ℝ) :
    (@bil _ (affineTypeAGroup n)) x x = (∑ i, (x i - x (i + 1)) ^ 2) / 2 := by
  rw [@bil_self_eq_sum _ (affineTypeAGroup n) (Fin.fintype (n + 1))]
  change ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
    x i * x j * -Real.cos (Real.pi / (affineTypeAMatrix n i j : ℝ)) = _
  simp only [affineTypeA_gram, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hshift : ∑ i : Fin (n + 1), x i * x (i - 1) * (1 / 2) =
      ∑ i : Fin (n + 1), x i * x (i + 1) * (1 / 2) := by
    rw [← Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1)))]
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hsq : ∑ i : Fin (n + 1), x (i + 1) ^ 2 = ∑ i : Fin (n + 1), x i ^ 2 :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1))) fun i ↦ x i ^ 2
  have hexp : ∑ i : Fin (n + 1), (x i - x (i + 1)) ^ 2 =
      2 * ∑ i : Fin (n + 1), x i ^ 2 - 2 * ∑ i : Fin (n + 1), x i * x (i + 1) := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsq, mul_assoc,
      ← Finset.mul_sum]
    ring
  rw [hshift, hexp, ← Finset.sum_mul]
  simp only [sq]
  ring

private theorem affineTypeA_bil_nonneg (x : Fin (n + 1) →₀ ℝ) :
    0 ≤ (@bil _ (affineTypeAGroup n)) x x := by
  rw [affineTypeA_bil_eq]
  positivity

/-- The null root of `Ãₙ`: `(1, …, 1)`. -/
private noncomputable def affineTypeANull : Fin (n + 1) →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm fun _ ↦ 1

omit [NeZero n] in
private theorem affineTypeANull_apply (i : Fin (n + 1)) : affineTypeANull (n := n) i = 1 := by
  simp [affineTypeANull]

private theorem affineTypeA_bil_null (j : Fin (n + 1)) :
    (@bil _ (affineTypeAGroup n)) affineTypeANull (@stdBasis _ (affineTypeAGroup n) j) = 0 := by
  rw [@bil_stdBasis_right_eq_sum _ (affineTypeAGroup n) (Fin.fintype (n + 1))]
  change ∑ i : Fin (n + 1),
    affineTypeANull i * -Real.cos (Real.pi / (affineTypeAMatrix n i j : ℝ)) = 0
  have h1 : ∀ i : Fin (n + 1), j = i + 1 ↔ i = j - 1 := fun i ↦ by
    rw [eq_sub_iff_add_eq, eq_comm]
  have h2 : ∀ i : Fin (n + 1), j = i - 1 ↔ i = j + 1 := fun i ↦ by
    rw [eq_sub_iff_add_eq, eq_comm]
  simp only [affineTypeA_gram, affineTypeANull_apply, one_mul, h1, h2, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  norm_num

/-- A vector isotropic for `bil` of type `Ãₙ` is constant, hence a multiple of the null root. -/
private theorem affineTypeA_bil_isotropic (x : Fin (n + 1) →₀ ℝ)
    (hx : (@bil _ (affineTypeAGroup n)) x x = 0) : ∃ a : ℝ, x = a • affineTypeANull := by
  rw [affineTypeA_bil_eq, div_eq_zero_iff, or_iff_left two_ne_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ sq_nonneg _] at hx
  have hstep : ∀ i, x (i + 1) = x i := fun i ↦
    (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (hx i (Finset.mem_univ _)))).symm
  have hconst : ∀ k (hk : k < n + 1), x ⟨k, hk⟩ = x 0 := by
    intro k
    induction k with
    | zero => exact fun _ ↦ rfl
    | succ k ih =>
        intro hk
        have hk' : (⟨k + 1, hk⟩ : Fin (n + 1)) = ⟨k, by omega⟩ + 1 := by
          rw [Fin.ext_iff, Fin.val_add_one, ite_eq_right fun h ↦ by
            simp only [Fin.ext_iff, Fin.val_last] at h; omega]
        rw [hk', hstep, ih]
  refine ⟨x 0, ?_⟩
  ext i
  rw [Finsupp.smul_apply, affineTypeANull_apply, smul_eq_mul, mul_one]
  exact hconst i i.isLt

private theorem affineTypeA_isIrreducible' : @IsIrreducible _ (affineTypeAGroup n) := by
  refine isIrreducibleMatrix_of_exists_lt (affineTypeAMatrix n) fun i hi ↦ ?_
  have hi0 : (i : ℕ) ≠ 0 := fun h ↦ hi (Fin.ext h)
  refine ⟨⟨i - 1, by omega⟩, Fin.lt_def.mpr (by simp only; omega), ?_⟩
  unfold affineTypeAMatrix
  simp only [Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem affineTypeA_isCrystallographic' : @IsCrystallographic _ (affineTypeAGroup n) := by
  intro i i' hii'
  change affineTypeAMatrix n i i' = 0 ∨ affineTypeAMatrix n i i' = 2 ∨
    affineTypeAMatrix n i i' = 3 ∨ affineTypeAMatrix n i i' = 4 ∨ affineTypeAMatrix n i i' = 6
  unfold affineTypeAMatrix
  simp only [Matrix.of_apply]
  split_ifs <;> simp_all

private theorem affineTypeA_isAffineCoxeter' : @IsAffineCoxeter _ (affineTypeAGroup n) :=
  isAffineCoxeter_of_nonneg_of_radical (fun x ↦ affineTypeA_bil_nonneg x) affineTypeANull
    (fun h ↦ by simpa [affineTypeANull_apply] using congrArg (fun f : Fin (n + 1) →₀ ℝ ↦ f 0) h)
    affineTypeA_bil_null

end Classification

theorem affineTypeA_isIrreducible (n : ℕ) [NeZero n] : @IsIrreducible _ (affineTypeAGroup n) :=
  affineTypeA_isIrreducible'

theorem affineTypeA_isCrystallographic (n : ℕ) [NeZero n] :
    @IsCrystallographic _ (affineTypeAGroup n) :=
  affineTypeA_isCrystallographic'

theorem affineTypeA_isIrreducibleAffineCoxeter (n : ℕ) [NeZero n] :
    @IsIrreducibleAffineCoxeter _ (affineTypeAGroup n) :=
  ⟨affineTypeA_isAffineCoxeter', affineTypeA_isIrreducible'⟩

theorem affineTypeA_isIrreducibleAffineWeyl (n : ℕ) [NeZero n] :
    @IsIrreducibleAffineWeyl _ (affineTypeAGroup n) :=
  ⟨isPolyAffineWeyl_of_isotropic affineTypeA_isAffineCoxeter'.1 affineTypeA_isCrystallographic'
    (0 : Fin (n + 1)) affineTypeANull (affineTypeANull_apply 0) affineTypeA_bil_null
    fun x hx ↦ affineTypeA_bil_isotropic x hx, affineTypeA_isIrreducible'⟩


/-! ### Euler lattice -/

section EulerLattice

/-- The Euler lattice of type `Ãₙ` (see `Coxeter.BilinearLatticeDynkins`). It needs `n ≥ 2`:
`Ã₁` is the Kronecker quiver, with a double edge, so it is not simply laced. -/
noncomputable abbrev affineTypeABilinearLattice (n : ℕ) (_ : 2 ≤ n) : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice (affineTypeAMatrix n)

theorem affineTypeA_isSimplyLaced (n : ℕ) (hn : 2 ≤ n) :
    BilinearLattice.IsSimplyLaced (affineTypeAMatrix n) := by
  intro i j hij
  unfold affineTypeAMatrix
  simp only [Matrix.of_apply, hij, ite_false, show n ≠ 1 by omega]
  split_ifs <;> simp

variable {n : ℕ}

open _root_.Matrix

/-- The Euler matrix of `Ãₙ`, `n ≥ 2`: `1` on the diagonal, `-1` at `(i, i + 1)` and at `(0, n)`. -/
private theorem eulerMatrix_affineTypeA_apply (hn : 2 ≤ n) (i j : Fin (n + 1)) :
    BilinearLattice.eulerMatrix (affineTypeAMatrix n) i j =
      (if (j : ℕ) = i then 1 else 0) - (if (j : ℕ) = i + 1 then 1 else 0) -
        (if (i : ℕ) = 0 ∧ (j : ℕ) = n then 1 else 0) := by
  unfold BilinearLattice.eulerMatrix affineTypeAMatrix
  simp only [Matrix.of_apply, Fin.lt_def, Fin.ext_iff]
  split_ifs <;> omega

/-- The transpose of the Euler matrix of `Ãₙ`, `n ≥ 2`. -/
private theorem eulerMatrix_affineTypeA_transpose_apply (hn : 2 ≤ n) (i j : Fin (n + 1)) :
    (BilinearLattice.eulerMatrix (affineTypeAMatrix n))ᵀ i j =
      (if (j : ℕ) = i then 1 else 0) - (if 0 < (i : ℕ) ∧ (j : ℕ) = i - 1 then 1 else 0) -
        (if (i : ℕ) = n ∧ (j : ℕ) = 0 then 1 else 0) := by
  rw [Matrix.transpose_apply, eulerMatrix_affineTypeA_apply hn]
  split_ifs <;> omega

/-- Summing against the indicator of a single index, given by its value in `ℕ`. -/
private theorem sum_ite_val_eq (k : ℕ) (f : Fin (n + 1) → ℤ) :
    (∑ j : Fin (n + 1), if (j : ℕ) = k then f j else 0) =
      if h : k < n + 1 then f ⟨k, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k, h⟩ (fun j _ hj ↦ ite_eq_right fun hjk ↦ hj (Fin.ext hjk))
      (fun h' ↦ absurd (Finset.mem_univ _) h'), ite_eq_left rfl]
  · exact Finset.sum_eq_zero fun j _ ↦ ite_eq_right (by omega)

private theorem eulerMatrix_affineTypeA_mulVec (hn : 2 ≤ n) (z : Fin (n + 1) → ℤ)
    (i : Fin (n + 1)) :
    (BilinearLattice.eulerMatrix (affineTypeAMatrix n) *ᵥ z) i =
      z i - (if h : (i : ℕ) + 1 < n + 1 then z ⟨i + 1, h⟩ else 0) -
        (if (i : ℕ) = 0 then z (Fin.last n) else 0) := by
  simp only [Matrix.mulVec, dotProduct, eulerMatrix_affineTypeA_apply hn, sub_mul, ite_mul,
    one_mul, zero_mul, Finset.sum_sub_distrib, sum_ite_val_eq, i.isLt, dite_true]
  by_cases hi : (i : ℕ) = 0
  · simp only [hi, true_and, sum_ite_val_eq, lt_add_one, dite_true, ite_true]
    obtain rfl : i = 0 := Fin.ext hi
    rfl
  · simp only [hi, false_and, ite_false, Finset.sum_const_zero]

private theorem eulerMatrix_affineTypeA_transpose_mulVec (hn : 2 ≤ n) (x : Fin (n + 1) → ℤ)
    (i : Fin (n + 1)) :
    ((BilinearLattice.eulerMatrix (affineTypeAMatrix n))ᵀ *ᵥ x) i =
      x i - (if h : 0 < (i : ℕ) then x ⟨i - 1, by omega⟩ else 0) -
        (if (i : ℕ) = n then x 0 else 0) := by
  simp only [Matrix.mulVec, dotProduct, eulerMatrix_affineTypeA_transpose_apply hn, sub_mul,
    ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, sum_ite_val_eq, i.isLt, dite_true]
  congr 1
  · by_cases hi : 0 < (i : ℕ)
    · simp only [hi, true_and, sum_ite_val_eq, show (i : ℕ) - 1 < n + 1 by omega, dite_true]
    · simp only [hi, false_and, ite_false, Finset.sum_const_zero, dite_false]
  · by_cases hi : (i : ℕ) = n
    · simp only [hi, true_and, sum_ite_val_eq, show 0 < n + 1 by omega, dite_true, ite_true]
      rfl
    · simp only [hi, false_and, ite_false, Finset.sum_const_zero]

/-- `φ(x) = x₀ - xₙ`, which the Coxeter transformation of `Ãₙ` preserves. -/
private def affA_φ (x : Fin (n + 1) → ℤ) : ℤ := x 0 - x (Fin.last n)

/-- `x` read at a natural-number index, `0` out of range. -/
private def affA_get (x : Fin (n + 1) → ℤ) (k : ℕ) : ℤ := if h : k < n + 1 then x ⟨k, h⟩ else 0

/-- The quasi-periodic extension `X (j) = x (j mod n) - ⌊j / n⌋ φ(x)` of `x` to `ℤ`. -/
private def affA_ext (n : ℕ) (x : Fin (n + 1) → ℤ) (j : ℤ) : ℤ :=
  affA_get x (j % n).toNat - (j / n) * affA_φ x

private theorem affA_ext_add_mul (hn : 2 ≤ n) (x : Fin (n + 1) → ℤ) (j q : ℤ) :
    affA_ext n x (j + n * q) = affA_ext n x j - q * affA_φ x := by
  have hn0 : (n : ℤ) ≠ 0 := by omega
  unfold affA_ext
  rw [Int.add_mul_emod_self_left, Int.add_mul_ediv_left _ _ hn0]
  ring

private theorem affA_ext_natCast_of_lt (x : Fin (n + 1) → ℤ) (k : ℕ) (hk : k < n) :
    affA_ext n x k = x ⟨k, by omega⟩ := by
  unfold affA_ext affA_get
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.ediv_eq_zero_of_lt (by omega) (by omega),
    Int.toNat_natCast, dite_eq_left (by omega)]
  ring

private theorem affA_ext_val (hn : 2 ≤ n) (x : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    affA_ext n x (i : ℕ) = x i := by
  by_cases hi : (i : ℕ) < n
  · exact affA_ext_natCast_of_lt x i hi
  · obtain rfl : i = Fin.last n := Fin.ext (by rw [Fin.val_last]; omega)
    have h := affA_ext_add_mul hn x 0 1
    have h0 := affA_ext_natCast_of_lt x 0 (by omega)
    rw [Nat.cast_zero] at h0
    rw [zero_add, mul_one, h0] at h
    rw [Fin.val_last, h]
    simp only [affA_φ, one_mul, Fin.zero_eta]
    ring

private theorem affA_ext_zero (x : Fin (n + 1) → ℤ) (hn : 2 ≤ n) : affA_ext n x 0 = x 0 := by
  have h := affA_ext_natCast_of_lt x 0 (by omega)
  rwa [Nat.cast_zero] at h

private theorem affA_ext_last (hn : 2 ≤ n) (x : Fin (n + 1) → ℤ) :
    affA_ext n x n = x (Fin.last n) := by
  have h := affA_ext_val hn x (Fin.last n)
  rwa [Fin.val_last] at h

private theorem affA_ext_neg_one (hn : 2 ≤ n) (x : Fin (n + 1) → ℤ) :
    affA_ext n x (-1) = x ⟨n - 1, by omega⟩ + affA_φ x := by
  have h := affA_ext_add_mul hn x ((n - 1 : ℕ) : ℤ) (-1)
  rw [show ((n - 1 : ℕ) : ℤ) + n * (-1) = -1 by omega, affA_ext_natCast_of_lt x _ (by omega)] at h
  rw [h]
  ring

/-- The Coxeter transformation of `Ãₙ` is a shift plus a constant on the quasi-periodic
extension: `(S x)ᵢ = φ(x) + X (i - 1)`. -/
private theorem affineTypeA_S_eq (hn : 2 ≤ n) (x : Fin (n + 1) → ℤ) :
    (affineTypeABilinearLattice n hn).S x =
      fun i : Fin (n + 1) ↦ affA_φ x + affA_ext n x ((i : ℕ) - 1) := by
  unfold affineTypeABilinearLattice BilinearLattice.eulerLattice
  rw [BilinearLattice.ofUnimodular_S_eq_iff]
  ext ⟨i, hi⟩
  rw [eulerMatrix_affineTypeA_mulVec hn, Pi.neg_apply, eulerMatrix_affineTypeA_transpose_mulVec hn]
  simp only [Fin.val_last]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · -- `i = 0`: the row of `C` meets `z₀`, `z₁`, `zₙ`.
    rw [dite_eq_left (show 0 + 1 < n + 1 by omega), ite_eq_left rfl,
      dite_eq_right (show ¬ 0 < 0 from lt_irrefl 0), ite_eq_right (show (0 : ℕ) ≠ n by omega)]
    simp only [Nat.cast_zero, zero_sub, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      affA_ext_neg_one hn, affA_ext_zero x hn, show ((n : ℤ) - 1) = ((n - 1 : ℕ) : ℤ) by omega,
      affA_ext_natCast_of_lt x (n - 1) (by omega)]
    simp only [affA_φ, Fin.zero_eta, Fin.last]
    ring
  · have hcast : ((i : ℕ) : ℤ) - 1 = ((i - 1 : ℕ) : ℤ) := by omega
    rw [ite_eq_right (show i ≠ 0 by omega), dite_eq_left hi0, hcast,
      affA_ext_natCast_of_lt x (i - 1) (by omega)]
    rcases Nat.lt_or_ge i n with hin | hin
    · -- `0 < i < n`: the row of `C` meets `zᵢ`, `zᵢ₊₁`.
      rw [dite_eq_left (show i + 1 < n + 1 by omega), ite_eq_right (show i ≠ n by omega)]
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
        affA_ext_natCast_of_lt x i hin]
      ring
    · -- `i = n`: the row of `C` meets only `zₙ`.
      obtain rfl : i = n := by omega
      rw [dite_eq_right (show ¬ i + 1 < i + 1 from lt_irrefl _), ite_eq_left rfl]
      simp only [affA_φ, Fin.last]
      ring

/-- `(S ^ k x)ᵢ = k φ(x) + X (i - k)`. -/
private theorem affineTypeA_S_pow_apply (hn : 2 ≤ n) (k : ℕ) (x : Fin (n + 1) → ℤ)
    (i : Fin (n + 1)) :
    (((affineTypeABilinearLattice n hn).S : Module.End ℤ (affineTypeABilinearLattice n hn)) ^ k)
      x i = k * affA_φ x + affA_ext n x ((i : ℕ) - k) := by
  induction k generalizing i with
  | zero =>
      rw [pow_zero, one_apply_eq_self, Nat.cast_zero, zero_mul, zero_add, sub_zero,
        affA_ext_val hn]
  | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp]
      set y := (((affineTypeABilinearLattice n hn).S :
        Module.End ℤ (affineTypeABilinearLattice n hn)) ^ k) x
      have hφ : affA_φ y = affA_φ x := by
        change y 0 - y (Fin.last n) = affA_φ x
        rw [ih, ih]
        simp only [Fin.val_zero, Fin.val_last, Nat.cast_zero, zero_sub]
        have h := affA_ext_add_mul hn x ((n : ℤ) - k) (-1)
        rw [show (n : ℤ) - k + n * (-1) = -k by ring] at h
        rw [h]
        ring
      change (affineTypeABilinearLattice n hn).S y i = _
      rw [affineTypeA_S_eq hn y]
      simp only [hφ]
      have hn0 : (0 : ℤ) < n := by omega
      set j : ℤ := ((i : ℕ) : ℤ) - 1
      have hj : (j % n).toNat < n + 1 := by
        have := Int.emod_lt_of_pos j hn0
        have := Int.emod_nonneg j hn0.ne'
        omega
      have hy : affA_ext n y j = k * affA_φ x + affA_ext n x (j - k) := by
        change affA_get y (j % n).toNat - (j / n) * affA_φ y = _
        rw [hφ, affA_get, dite_eq_left hj, ih, Int.toNat_of_nonneg (Int.emod_nonneg j hn0.ne')]
        have h := affA_ext_add_mul hn x (j % n - k) (j / n)
        rw [show j % n - k + n * (j / n) = j - k by
          linear_combination Int.emod_add_mul_ediv j n] at h
        rw [h]
        ring
      rw [hy]
      push_cast
      rw [show ((i : ℕ) : ℤ) - 1 - k = ((i : ℕ) : ℤ) - (k + 1) by ring]
      ring

/-- `S ^ n x = x + (n + 1) φ(x) • (1, …, 1)`. -/
private theorem affineTypeA_S_pow_n_apply (hn : 2 ≤ n) (x : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    (((affineTypeABilinearLattice n hn).S : Module.End ℤ (affineTypeABilinearLattice n hn)) ^ n)
      x i = x i + (n + 1) * affA_φ x := by
  rw [affineTypeA_S_pow_apply hn]
  have h := affA_ext_add_mul hn x ((i : ℕ) : ℤ) (-1)
  rw [show ((i : ℕ) : ℤ) + n * (-1) = (i : ℕ) - n by ring, affA_ext_val hn] at h
  rw [h]
  ring

private theorem affA_φ_const (c : ℤ) : affA_φ (n := n) (fun _ ↦ c) = 0 := sub_self c

/-- `S` is quasi-unipotent of index exactly `2`: the null root gives a Jordan block of size `2`
at eigenvalue `1`. -/
theorem affineTypeABilinearLattice_isQuasiUnipotent (n : ℕ) (hn : 2 ≤ n) :
    Module.End.IsQuasiUnipotentOfIndex
      ((affineTypeABilinearLattice n hn).S : Module.End ℤ (affineTypeABilinearLattice n hn)) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      ((affineTypeABilinearLattice n hn).S : Module.End ℤ (affineTypeABilinearLattice n hn)) 1 := by
  set S := ((affineTypeABilinearLattice n hn).S : Module.End ℤ (affineTypeABilinearLattice n hn))
  have hsub : ∀ x : Fin (n + 1) → ℤ, (S ^ n - 1) x = fun _ ↦ (n + 1) * affA_φ x := by
    intro x
    funext i
    change (S ^ n) x i - x i = _
    rw [affineTypeA_S_pow_n_apply hn]
    ring
  refine ⟨⟨n, by omega, LinearMap.ext fun x ↦ ?_⟩, ?_⟩
  · rw [sq, mul_apply_eq_comp, hsub, hsub, affA_φ_const, mul_zero]
    rfl
  · let δ : Fin (n + 1) → ℤ := fun _ ↦ (n + 1 : ℤ)
    let v : Fin (n + 1) → ℤ := Pi.single 0 1
    have hφv : affA_φ v = 1 := by
      simp only [affA_φ, v, Pi.single_eq_same,
        Pi.single_eq_of_ne (show Fin.last n ≠ 0 from fun h ↦ by simp [Fin.ext_iff] at h; omega)]
      ring
    refine Module.End.not_isQuasiUnipotentOfIndex_one_of_pow_apply (M := Fin (n + 1) → ℤ) S
      (h := n) v δ ?_ ?_ ?_
    · funext i
      rw [affineTypeA_S_pow_n_apply hn, affA_φ_const, mul_zero, add_zero]
    · funext i
      rw [affineTypeA_S_pow_n_apply hn, hφv, mul_one]
      rfl
    · intro h
      have := congrFun h 0
      simp only [δ, Pi.zero_apply] at this
      omega

noncomputable abbrev affineTypeABilinearLatticeWithMonoidQuasiUnipotent (n : ℕ) (hn : 2 ≤ n) :
    BilinearLattice.BilinearLatticeWithMonoidQuasiUnipotent.{0} :=
  BilinearLattice.eulerLatticeWithMonoidQuasiUnipotent
    (M := affineTypeAMatrix n)
    (hS := (affineTypeABilinearLattice_isQuasiUnipotent n hn).1)

end EulerLattice

end Coxeter
