module

public import Coxeter.BilinearLatticeDynkins
public import Coxeter.SpecialFeatures

/-!
# Affine Coxeter groups of type D

This file defines the affine type `D` Coxeter matrix and Coxeter group, proves that `D̃ₙ` is an
irreducible affine Coxeter group and an irreducible affine Weyl group for `n ≥ 4`, and defines the
Euler lattice of `D̃ₙ`, whose Coxeter transformation is quasi-unipotent of index exactly `2`.

## Main definitions

* `Coxeter.affineTypeDMatrix`: the Coxeter matrix of `D̃ₙ` on `n + 1` generators.
* `Coxeter.affineTypeDBilinearLattice`: its Euler lattice.

## Main statements

* `Coxeter.affineTypeD_isIrreducibleAffineCoxeter`, `Coxeter.affineTypeD_isIrreducibleAffineWeyl`
* `Coxeter.affineTypeDBilinearLattice_isQuasiUnipotent`

## Implementation notes

`D̃₄` is a fixed matrix, handled by `decide`. For `D̃ₙ`, `n = m + 5`, the root lattice embeds in
`ℤⁿ ⊕ ℤ δ` (node `j ≤ n - 2` ↦ `e_{j+1} - e_{j+2}`, node `n - 1` ↦ `e_{n-1} + e_n`, node `n` ↦
`δ - e₁ - e₂`). In these coordinates the Coxeter transformation is a signed permutation of `ℤⁿ`
plus a shift of the `δ`-coordinate. We record it as a model `x ↦ (g, a, b, k)`, where
`g : Fin (n - 2) → ℤ` collects the coordinates on which the signed permutation is (up to one
sign) a cyclic rotation, `a`, `b` are the two coordinates it negates, and `k = xₙ`; then `S` acts by
`(g, a, b, k) ↦ (g (· - 1), -a, -b, k - g 0 + a)`. Hence `S ^ (2 (n - 2))` fixes `g`, `a`, `b`
and shifts `k`, so it is `x ↦ x + c(x) • δ` for the null root `δ`.
-/

@[expose] public section

namespace Coxeter

/-- The Coxeter matrix of affine type `D̃ₙ` (meaningful for `n ≥ 4`): mathlib's `Dₙ` diagram on
`0, …, n - 1` (the path `0 — ⋯ — n - 2` with `n - 1` attached to `n - 3`), plus the node `n`
attached to `1`.
```
    0               n - 2
     \             /
      1 — ⋯ — n - 3
     /             \
    n               n - 1
```
-/
def affineTypeDMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
      else if ((i : ℕ) + 1 = j ∧ (j : ℕ) ≤ n - 2) ∨ ((j : ℕ) + 1 = i ∧ (i : ℕ) ≤ n - 2) ∨
        ((i : ℕ) = n - 3 ∧ (j : ℕ) = n - 1) ∨ ((j : ℕ) = n - 3 ∧ (i : ℕ) = n - 1) ∨
        ((i : ℕ) = 1 ∧ (j : ℕ) = n) ∨ ((j : ℕ) = 1 ∧ (i : ℕ) = n) then 3 else 2
  isSymm := by grind [Matrix.IsSymm, Matrix.transpose_of]
  diagonal := by simp
  off_diagonal i j h := by
    simp only [Matrix.of_apply, h, ite_false]
    split_ifs <;> omega

@[reducible] noncomputable def affineTypeDGroup (n : ℕ) [NeZero n] :
    CoxeterGroup (affineTypeDMatrix n).Group where
  B := Fin (n + 1)
  M := affineTypeDMatrix n
  cs := (affineTypeDMatrix n).toCoxeterSystem

/-! ### `D̃ₙ` is an irreducible affine Weyl group

By `isIrreducibleAffineWeyl_of_null` it suffices that the diagram is connected, the entries are
crystallographic, and the null root `δ = (1, 2, …, 2, 1, 1, 1)` (`1` at the four leaves `0`,
`n - 2`, `n - 1`, `n`) is orthogonal to every `stdBasis j`. We write `n = m + 4`. -/

section Classification

variable {m : ℕ}

/-- `y` read at a natural-number index, `0` out of range. -/
private def affDN_get (y : Fin (m + 4 + 1) → ℝ) (k : ℕ) : ℝ :=
  if h : k < m + 4 + 1 then y ⟨k, h⟩ else 0

/-- Summing against the indicator of a single index, given by its value in `ℕ`. -/
private theorem affDN_sum_ite (P : Prop) [Decidable P] (k : ℕ) (f : Fin (m + 4 + 1) → ℝ) :
    (∑ i : Fin (m + 4 + 1), if P ∧ (i : ℕ) = k then f i else 0) =
      if P then affDN_get f k else 0 := by
  by_cases hP : P
  · simp only [hP, true_and, ↓reduceIte, affDN_get]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨k, h⟩ (fun j _ hj ↦ ite_eq_right fun hjk ↦ hj (Fin.ext hjk))
        (fun h' ↦ absurd (Finset.mem_univ _) h'), ite_eq_left rfl]
    · exact Finset.sum_eq_zero fun j _ ↦ ite_eq_right (by omega)
  · simp only [hP, false_and, ↓reduceIte, Finset.sum_const_zero]

private theorem affDN_sum_val (k : ℕ) (f : Fin (m + 4 + 1) → ℝ) :
    (∑ i : Fin (m + 4 + 1), if (i : ℕ) = k then f i else 0) = affDN_get f k := by
  simpa using affDN_sum_ite True k f

/-- Column `j` of the Gram matrix of `bil` for `D̃_(m+4)`: one indicator per possible neighbour. -/
private theorem affineTypeD_gram (i j : Fin (m + 4 + 1)) :
    -Real.cos (Real.pi / (affineTypeDMatrix (m + 4) i j : ℝ)) =
      (if (i : ℕ) = j then 1 else 0) -
        (if (j : ℕ) + 1 ≤ m + 2 ∧ (i : ℕ) = j + 1 then 1 / 2 else 0) -
        (if (1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ m + 2) ∧ (i : ℕ) = j - 1 then 1 / 2 else 0) -
        (if (j : ℕ) = m + 1 ∧ (i : ℕ) = m + 3 then 1 / 2 else 0) -
        (if (j : ℕ) = m + 3 ∧ (i : ℕ) = m + 1 then 1 / 2 else 0) -
        (if (j : ℕ) = 1 ∧ (i : ℕ) = m + 4 then 1 / 2 else 0) -
        (if (j : ℕ) = m + 4 ∧ (i : ℕ) = 1 then 1 / 2 else 0) := by
  have hi := i.isLt
  have hj := j.isLt
  unfold affineTypeDMatrix
  simp only [Matrix.of_apply, Fin.ext_iff]
  split
  · simp (disch := omega) only [ite_eq_right]
    norm_num
  · split
    · rename_i hadj
      rcases hadj with h | h | h | h | h | h
      all_goals
        simp (disch := omega) only [ite_eq_left, ite_eq_right]
        norm_num [Real.cos_pi_div_three]
    · simp (disch := omega) only [ite_eq_right]
      norm_num

/-- The null root of `D̃_(m+4)`. -/
private noncomputable def affineTypeDNull : Fin (m + 4 + 1) →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ if (i : ℕ) = 0 ∨ m + 2 ≤ (i : ℕ) then 1 else 2

private theorem affineTypeDNull_pos (i : Fin (m + 4 + 1)) : 0 < affineTypeDNull (m := m) i := by
  simp only [affineTypeDNull, Finsupp.coe_equivFunOnFinite_symm]
  split_ifs <;> norm_num

private theorem affDN_get_null (k : ℕ) :
    affDN_get (affineTypeDNull (m := m)) k =
      if k < m + 4 + 1 then (if k = 0 ∨ m + 2 ≤ k then 1 else 2) else 0 := by
  unfold affDN_get
  split_ifs <;> simp_all [affineTypeDNull]

private theorem affineTypeD_bil_null (j : Fin (m + 4 + 1)) :
    (@bil _ (affineTypeDGroup (m + 4))) affineTypeDNull
      (@stdBasis _ (affineTypeDGroup (m + 4)) j) = 0 := by
  rw [@bil_stdBasis_right_eq_sum _ (affineTypeDGroup (m + 4)) (Fin.fintype (m + 4 + 1))]
  change ∑ i : Fin (m + 4 + 1),
    affineTypeDNull i * -Real.cos (Real.pi / (affineTypeDMatrix (m + 4) i j : ℝ)) = 0
  simp only [affineTypeD_gram, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    affDN_sum_ite, affDN_sum_val]
  have hmul : ∀ k, affDN_get (m := m) (fun i ↦ affineTypeDNull (m := m) i * (1 / 2)) k =
      affDN_get (m := m) affineTypeDNull k * (1 / 2) := fun k ↦ by
    unfold affDN_get
    split_ifs <;> simp
  simp only [hmul, affDN_get_null]
  obtain ⟨j, hj⟩ := j
  simp only
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    all_goals
      rcases Nat.eq_zero_or_pos m with rfl | hm
      all_goals
        simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte, true_or]
        norm_num
  · rcases Nat.lt_or_ge j (m + 1) with hjm | hjm
    · simp (disch := omega) only [ite_eq_left, ite_eq_right]
      norm_num
    · obtain rfl | rfl | rfl | rfl : j = m + 1 ∨ j = m + 2 ∨ j = m + 3 ∨ j = m + 4 := by omega
      all_goals
        simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte]
        norm_num

private theorem affineTypeD_isIrreducible' :
    @IsIrreducible _ (affineTypeDGroup (m + 4)) := by
  refine isIrreducibleMatrix_of_exists_lt (affineTypeDMatrix (m + 4)) fun i hi ↦ ?_
  obtain ⟨i, hi'⟩ := i
  have hi0 : i ≠ 0 := fun h ↦ hi (Fin.ext h)
  have key : ∀ j : Fin (m + 4 + 1), (j : ℕ) < i →
      (((j : ℕ) + 1 = i ∧ i ≤ m + 2) ∨ ((j : ℕ) = m + 1 ∧ i = m + 3) ∨
        ((j : ℕ) = 1 ∧ i = m + 4)) → affineTypeDMatrix (m + 4) j ⟨i, hi'⟩ ≠ 2 := by
    intro j _ hj
    unfold affineTypeDMatrix
    simp only [Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  by_cases h1 : i ≤ m + 2
  · exact ⟨⟨i - 1, by omega⟩, Fin.lt_def.mpr (by simp only; omega),
      key _ (by simp only; omega) (Or.inl ⟨by simp only; omega, h1⟩)⟩
  · obtain rfl | rfl : i = m + 3 ∨ i = m + 4 := by omega
    · exact ⟨⟨m + 1, by omega⟩, Fin.lt_def.mpr (by simp only; omega),
        key _ (by simp only; omega) (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨⟨1, by omega⟩, Fin.lt_def.mpr (by simp only; omega),
        key _ (by simp only; omega) (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

private theorem affineTypeD_isCrystallographic' :
    @IsCrystallographic _ (affineTypeDGroup (m + 4)) := by
  intro i i' hii'
  change affineTypeDMatrix (m + 4) i i' = 0 ∨ affineTypeDMatrix (m + 4) i i' = 2 ∨
    affineTypeDMatrix (m + 4) i i' = 3 ∨ affineTypeDMatrix (m + 4) i i' = 4 ∨
    affineTypeDMatrix (m + 4) i i' = 6
  unfold affineTypeDMatrix
  simp only [Matrix.of_apply]
  split_ifs <;> simp_all

end Classification

theorem affineTypeD_isIrreducible (n : ℕ) (hn : 4 ≤ n) :
    @IsIrreducible _ (@affineTypeDGroup n ⟨by omega⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  exact affineTypeD_isIrreducible'

theorem affineTypeD_isCrystallographic (n : ℕ) (hn : 4 ≤ n) :
    @IsCrystallographic _ (@affineTypeDGroup n ⟨by omega⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  exact affineTypeD_isCrystallographic'

/-- `D̃ₙ` is an irreducible affine Coxeter group (`n ≥ 4`; for smaller `n`, `affineTypeDMatrix n`
is not `D̃ₙ`). -/
theorem affineTypeD_isIrreducibleAffineCoxeter (n : ℕ) (hn : 4 ≤ n) :
    @IsIrreducibleAffineCoxeter _ (@affineTypeDGroup n ⟨by omega⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  exact @isIrreducibleAffineCoxeter_of_null _ (affineTypeDGroup (m + 4))
    (Finite.of_fintype (Fin (m + 4 + 1))) affineTypeD_isIrreducible' affineTypeDNull
    (fun i ↦ affineTypeDNull_pos i) affineTypeD_bil_null

/-- `D̃ₙ` is an irreducible affine Weyl group (`n ≥ 4`). -/
theorem affineTypeD_isIrreducibleAffineWeyl (n : ℕ) (hn : 4 ≤ n) :
    @IsIrreducibleAffineWeyl _ (@affineTypeDGroup n ⟨by omega⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  exact @isIrreducibleAffineWeyl_of_null _ (affineTypeDGroup (m + 4))
    (Finite.of_fintype (Fin (m + 4 + 1))) affineTypeD_isIrreducible' affineTypeD_isCrystallographic'
    affineTypeDNull (fun i ↦ affineTypeDNull_pos i) affineTypeD_bil_null


/-! ### Euler lattice -/

section EulerLattice

/-- The Euler lattice of type `D̃ₙ`, `n ≥ 4` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev affineTypeDBilinearLattice (n : ℕ) (_ : 4 ≤ n) : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice (affineTypeDMatrix n)

theorem affineTypeD_isSimplyLaced (n : ℕ) (_ : 4 ≤ n) :
    BilinearLattice.IsSimplyLaced (affineTypeDMatrix n) := by
  intro i j hij
  unfold affineTypeDMatrix
  simp only [Matrix.of_apply, hij, ite_false]
  split_ifs <;> simp

open _root_.Matrix

/-! #### `D̃₄` -/

/-- The Coxeter transformation of `affineTypeDBilinearLattice 4` as an integer matrix. `Q ^ 2 - 1`
is square-zero but nonzero. -/
private def affineTypeD4CoxeterTransformation : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 2, -1, -1, -1;
     1, 2, -1, -1, -1;
     0, 1, -1, 0, 0;
     0, 1, 0, -1, 0;
     0, 1, 0, 0, -1]

private theorem affineTypeD4_isQuasiUnipotent (hn : 4 ≤ 4) :
    Module.End.IsQuasiUnipotentOfIndex
      ((affineTypeDBilinearLattice 4 hn).S : Module.End ℤ (affineTypeDBilinearLattice 4 hn)) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      ((affineTypeDBilinearLattice 4 hn).S : Module.End ℤ (affineTypeDBilinearLattice 4 hn)) 1 :=
  ⟨BilinearLattice.ofUnimodular_isQuasiUnipotentOfIndex_two _ _
      affineTypeD4CoxeterTransformation (by decide) (m := 2) (by norm_num) (by decide),
    BilinearLattice.ofUnimodular_not_isQuasiUnipotentOfIndex_one _ _
      affineTypeD4CoxeterTransformation (by decide) (h := 2)
      ![1, 0, 0, 0, 0] ![1, 2, 1, 1, 1] (by decide) (by decide) (by decide)⟩

/-! #### `D̃ₙ`, `n = m + 5` -/

variable {m : ℕ}

/-- `x` read at a natural-number index, `0` out of range. -/
private def affD_get (x : Fin (m + 5 + 1) → ℤ) (k : ℕ) : ℤ :=
  if h : k < m + 5 + 1 then x ⟨k, h⟩ else 0

private theorem affD_get_val (x : Fin (m + 5 + 1) → ℤ) (i : Fin (m + 5 + 1)) :
    affD_get x i = x i := dite_eq_left i.isLt

private theorem affD_get_add_smul (x y : Fin (m + 5 + 1) → ℤ) (t : ℤ) (k : ℕ) :
    affD_get (x + t • y) k = affD_get x k + t * affD_get y k := by
  unfold affD_get
  split_ifs <;> simp

/-- The Euler matrix of `D̃_(m+5)`. -/
private theorem eulerMatrix_affD_apply (i j : Fin (m + 5 + 1)) :
    BilinearLattice.eulerMatrix (affineTypeDMatrix (m + 5)) i j =
      (if (j : ℕ) = i then 1 else 0) - (if (i : ℕ) + 1 ≤ m + 3 ∧ (j : ℕ) = i + 1 then 1 else 0) -
        (if (i : ℕ) = m + 2 ∧ (j : ℕ) = m + 4 then 1 else 0) -
        (if (i : ℕ) = 1 ∧ (j : ℕ) = m + 5 then 1 else 0) := by
  unfold BilinearLattice.eulerMatrix affineTypeDMatrix
  simp only [Matrix.of_apply, Fin.lt_def, Fin.ext_iff]
  split_ifs <;> omega

private theorem eulerMatrix_affD_transpose_apply (i j : Fin (m + 5 + 1)) :
    (BilinearLattice.eulerMatrix (affineTypeDMatrix (m + 5)))ᵀ i j =
      (if (j : ℕ) = i then 1 else 0) -
        (if (1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ m + 3) ∧ (j : ℕ) = i - 1 then 1 else 0) -
        (if (i : ℕ) = m + 4 ∧ (j : ℕ) = m + 2 then 1 else 0) -
        (if (i : ℕ) = m + 5 ∧ (j : ℕ) = 1 then 1 else 0) := by
  rw [transpose_apply, eulerMatrix_affD_apply]
  split_ifs <;> omega

/-- Summing against the indicator of a single index, given by its value in `ℕ`. -/
private theorem affD_sum_ite (P : Prop) [Decidable P] (k : ℕ) (f : Fin (m + 5 + 1) → ℤ) :
    (∑ j : Fin (m + 5 + 1), if P ∧ (j : ℕ) = k then f j else 0) =
      if P then affD_get f k else 0 := by
  by_cases hP : P
  · simp only [hP, true_and, ↓reduceIte, affD_get]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨k, h⟩ (fun j _ hj ↦ ite_eq_right fun hjk ↦ hj (Fin.ext hjk))
        (fun h' ↦ absurd (Finset.mem_univ _) h'), ite_eq_left rfl]
    · exact Finset.sum_eq_zero fun j _ ↦ ite_eq_right (by omega)
  · simp only [hP, false_and, ↓reduceIte, Finset.sum_const_zero]

private theorem affD_sum_val (k : ℕ) (f : Fin (m + 5 + 1) → ℤ) :
    (∑ j : Fin (m + 5 + 1), if (j : ℕ) = k then f j else 0) = affD_get f k := by
  simpa using affD_sum_ite True k f

private theorem affD_mulVec (z : Fin (m + 5 + 1) → ℤ) (i : Fin (m + 5 + 1)) :
    (BilinearLattice.eulerMatrix (affineTypeDMatrix (m + 5)) *ᵥ z) i =
      affD_get z i - (if (i : ℕ) + 1 ≤ m + 3 then affD_get z (i + 1) else 0) -
        (if (i : ℕ) = m + 2 then affD_get z (m + 4) else 0) -
        (if (i : ℕ) = 1 then affD_get z (m + 5) else 0) := by
  simp only [mulVec, dotProduct, eulerMatrix_affD_apply, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, affD_sum_ite, affD_sum_val]

private theorem affD_transpose_mulVec (x : Fin (m + 5 + 1) → ℤ) (i : Fin (m + 5 + 1)) :
    ((BilinearLattice.eulerMatrix (affineTypeDMatrix (m + 5)))ᵀ *ᵥ x) i =
      affD_get x i - (if 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ m + 3 then affD_get x (i - 1) else 0) -
        (if (i : ℕ) = m + 4 then affD_get x (m + 2) else 0) -
        (if (i : ℕ) = m + 5 then affD_get x 1 else 0) := by
  simp only [mulVec, dotProduct, eulerMatrix_affD_transpose_apply, sub_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_sub_distrib, affD_sum_ite, affD_sum_val]

/-- The Coxeter transformation of `D̃_(m+5)`, coordinatewise; `α = x_{m+2} - x_{m+3} - x_{m+4}`. -/
private def affD_q (x : Fin (m + 5 + 1) → ℤ) (i : ℕ) : ℤ :=
  if i = 0 then
    affD_get x 1 + (affD_get x (m + 2) - affD_get x (m + 3) - affD_get x (m + 4)) -
      affD_get x (m + 5)
  else if i = 1 then
    affD_get x 0 + affD_get x 1 +
      (affD_get x (m + 2) - affD_get x (m + 3) - affD_get x (m + 4)) - affD_get x (m + 5)
  else if i ≤ m + 2 then
    affD_get x (i - 1) + (affD_get x (m + 2) - affD_get x (m + 3) - affD_get x (m + 4))
  else if i = m + 3 then affD_get x (m + 2) - affD_get x (m + 3)
  else if i = m + 4 then affD_get x (m + 2) - affD_get x (m + 4)
  else affD_get x 1 - affD_get x (m + 5)

private theorem affD_get_q (x : Fin (m + 5 + 1) → ℤ) (k : ℕ) :
    affD_get (fun i : Fin (m + 5 + 1) ↦ affD_q x i) k =
      if k < m + 5 + 1 then affD_q x k else 0 := by
  unfold affD_get
  split_ifs <;> rfl

private theorem affineTypeD_S_eq (hn : 4 ≤ m + 5) (x : Fin (m + 5 + 1) → ℤ) :
    (affineTypeDBilinearLattice (m + 5) hn).S x = fun i : Fin (m + 5 + 1) ↦ affD_q x i := by
  unfold affineTypeDBilinearLattice BilinearLattice.eulerLattice
  rw [BilinearLattice.ofUnimodular_S_eq_iff]
  ext ⟨i, hi⟩
  rw [affD_mulVec, Pi.neg_apply, affD_transpose_mulVec]
  simp only [affD_get_q]
  unfold affD_q
  rcases i with _ | _ | j
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte]
    ring
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte]
    simp only [Nat.reduceAdd, Nat.add_one_sub_one]
    ring
  · rcases Nat.lt_or_ge j m with hj | hj
    · simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte]
      simp only [Nat.add_one_sub_one]
      ring
    · obtain rfl | rfl | rfl | rfl : j = m ∨ j = m + 1 ∨ j = m + 2 ∨ j = m + 3 := by omega
      all_goals
        simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte]
        simp only [Nat.add_one_sub_one, Nat.add_assoc, Nat.reduceAdd]
        ring

/-! The model `x ↦ (g, a, b, k)`. -/

open Fin.NatCast

/-- The rotating coordinates, indexed by `ℕ`. -/
private def affD_gN (x : Fin (m + 5 + 1) → ℤ) (j : ℕ) : ℤ :=
  if j = 0 then affD_get x (m + 5) - affD_get x 0
  else if j ≤ m + 1 then affD_get x (j + 1) - affD_get x j
  else affD_get x (m + 3) - affD_get x (m + 2) + affD_get x (m + 4)

/-- The rotating coordinates. -/
private def affD_g (x : Fin (m + 5 + 1) → ℤ) (a : Fin (m + 3)) : ℤ := affD_gN x a

/-- A negated coordinate. -/
private def affD_a (x : Fin (m + 5 + 1) → ℤ) : ℤ := affD_get x 1 - affD_get x 0 - affD_get x (m + 5)

/-- The other negated coordinate. -/
private def affD_b (x : Fin (m + 5 + 1) → ℤ) : ℤ := affD_get x (m + 4) - affD_get x (m + 3)

/-- The `δ`-coordinate. -/
private def affD_k (x : Fin (m + 5 + 1) → ℤ) : ℤ := affD_get x (m + 5)

private theorem affD_gN_q (x : Fin (m + 5 + 1) → ℤ) (j : ℕ) (hj : j ≤ m + 2) :
    affD_gN (fun i : Fin (m + 5 + 1) ↦ affD_q x i) j =
      affD_gN x (if j = 0 then m + 2 else j - 1) := by
  unfold affD_gN
  simp only [affD_get_q]
  unfold affD_q
  rcases j with _ | _ | j
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte]
    ring
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte]
    simp only [Nat.reduceAdd, Nat.add_one_sub_one]
    ring
  · rcases Nat.lt_or_ge j m with hj' | hj'
    · simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte]
      simp only [Nat.add_one_sub_one]
      ring
    · obtain rfl : j = m := by omega
      simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte]
      simp only [Nat.add_one_sub_one, Nat.add_assoc, Nat.reduceAdd]
      ring

private theorem affD_g_q (x : Fin (m + 5 + 1) → ℤ) (a : Fin (m + 3)) :
    affD_g (fun i : Fin (m + 5 + 1) ↦ affD_q x i) a = affD_g x (a - 1) := by
  unfold affD_g
  rw [affD_gN_q x a (by omega), Fin.coe_sub_one]
  congr 1
  by_cases ha : a = 0
  · simp [ha]
  · rw [ite_eq_right ha]
    exact ite_eq_right fun h ↦ ha (Fin.ext h)

private theorem affD_a_q (x : Fin (m + 5 + 1) → ℤ) :
    affD_a (fun i : Fin (m + 5 + 1) ↦ affD_q x i) = -affD_a x := by
  unfold affD_a
  simp only [affD_get_q]
  unfold affD_q
  simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte]
  ring

private theorem affD_b_q (x : Fin (m + 5 + 1) → ℤ) :
    affD_b (fun i : Fin (m + 5 + 1) ↦ affD_q x i) = -affD_b x := by
  unfold affD_b
  simp only [affD_get_q]
  unfold affD_q
  simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte]
  ring

private theorem affD_k_q (x : Fin (m + 5 + 1) → ℤ) :
    affD_k (fun i : Fin (m + 5 + 1) ↦ affD_q x i) = affD_k x - affD_g x 0 + affD_a x := by
  unfold affD_k affD_g affD_gN affD_a
  simp only [affD_get_q, Fin.val_zero]
  unfold affD_q
  simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte]
  ring

/-- The model determines `x`. -/
private theorem affD_ext {x y : Fin (m + 5 + 1) → ℤ} (hg : ∀ a, affD_g x a = affD_g y a)
    (ha : affD_a x = affD_a y) (hb : affD_b x = affD_b y) (hk : affD_k x = affD_k y) : x = y := by
  have hgN : ∀ j ≤ m + 2, affD_gN x j = affD_gN y j := fun j hj ↦ hg ⟨j, by omega⟩
  unfold affD_a at ha
  unfold affD_b at hb
  unfold affD_k at hk
  have h0 : affD_get x 0 = affD_get y 0 := by
    have := hgN 0 (by omega)
    simp only [affD_gN, ↓reduceIte] at this
    omega
  have hmid : ∀ j ≤ m + 2, affD_get x j = affD_get y j := by
    intro j hj
    induction j with
    | zero => exact h0
    | succ j ih =>
        rcases j with _ | j
        · change affD_get x 1 = affD_get y 1
          omega
        · have := hgN (j + 1) (by omega)
          simp only [affD_gN, Nat.add_one_ne_zero, ↓reduceIte,
            show j + 1 ≤ m + 1 by omega] at this
          have := ih (by omega)
          omega
  have hlast := hgN (m + 2) le_rfl
  simp only [affD_gN, show m + 2 ≠ 0 by omega, show ¬ m + 2 ≤ m + 1 by omega,
    ↓reduceIte] at hlast
  have h2 := hmid (m + 2) le_rfl
  funext ⟨k, hk'⟩
  rw [← affD_get_val x, ← affD_get_val y]
  simp only
  rcases Nat.lt_or_ge k (m + 3) with hk3 | hk3
  · exact hmid k (by omega)
  · obtain rfl | rfl | rfl : k = m + 3 ∨ k = m + 4 ∨ k = m + 5 := by omega
    all_goals omega

private theorem affD_gN_add_smul (x y : Fin (m + 5 + 1) → ℤ) (t : ℤ) (j : ℕ) :
    affD_gN (x + t • y) j = affD_gN x j + t * affD_gN y j := by
  unfold affD_gN
  simp only [affD_get_add_smul]
  split_ifs <;> ring

/-- The null root `δ = (1, 2, …, 2, 1, 1, 1)`. -/
private def affD_δ : Fin (m + 5 + 1) → ℤ := fun i ↦ if (i : ℕ) = 0 ∨ m + 3 ≤ (i : ℕ) then 1 else 2

private theorem affD_get_δ (k : ℕ) (hk : k < m + 5 + 1) :
    affD_get (affD_δ (m := m)) k = if k = 0 ∨ m + 3 ≤ k then 1 else 2 := by
  simp only [affD_get, hk, ↓reduceDIte, affD_δ]

private theorem affD_gN_δ (j : ℕ) (hj : j ≤ m + 2) : affD_gN (affD_δ (m := m)) j = 0 := by
  unfold affD_gN
  split_ifs
  all_goals
    simp (disch := omega) only [affD_get_δ, ite_eq_left, ite_eq_right, ↓reduceIte, true_or]
    norm_num

private theorem affD_gN_zero (j : ℕ) : affD_gN (0 : Fin (m + 5 + 1) → ℤ) j = 0 := by
  unfold affD_gN affD_get
  split_ifs <;> simp

private theorem affD_gN_smul_δ (t : ℤ) (j : ℕ) (hj : j ≤ m + 2) :
    affD_gN (t • affD_δ (m := m)) j = 0 := by
  have h := affD_gN_add_smul (m := m) 0 affD_δ t j
  rw [zero_add] at h
  rw [h, affD_gN_zero, affD_gN_δ j hj, mul_zero, add_zero]

/-- The total `δ`-shift of `S ^ (2 (m + 3))`. -/
private def affD_c (x : Fin (m + 5 + 1) → ℤ) : ℤ :=
  -∑ i ∈ Finset.range (2 * (m + 3)), affD_g x (-(i : Fin (m + 3)))

private theorem affD_c_smul_δ (t : ℤ) : affD_c (t • affD_δ (m := m)) = 0 := by
  unfold affD_c affD_g
  rw [Finset.sum_eq_zero fun i _ ↦ affD_gN_smul_δ t _ (Nat.le_of_lt_succ (Fin.isLt _)), neg_zero]

private theorem affineTypeD_S_pow_model (hn : 4 ≤ m + 5) (j : ℕ) (x : Fin (m + 5 + 1) → ℤ) :
    let y := (((affineTypeDBilinearLattice (m + 5) hn).S :
      Module.End ℤ (affineTypeDBilinearLattice (m + 5) hn)) ^ j) x
    (∀ a, affD_g y a = affD_g x (a - (j : Fin (m + 3)))) ∧ affD_a y = (-1) ^ j * affD_a x ∧
      affD_b y = (-1) ^ j * affD_b x ∧
      affD_k y = affD_k x +
        ∑ i ∈ Finset.range j, (-affD_g x (-(i : Fin (m + 3))) + (-1) ^ i * affD_a x) := by
  induction j with
  | zero =>
      refine ⟨fun a ↦ ?_, ?_, ?_, ?_⟩ <;> simp [one_apply_eq_self]
  | succ j ih =>
      obtain ⟨hg, ha, hb, hk⟩ := ih
      simp only at hg ha hb hk ⊢
      rw [pow_succ', mul_apply_eq_comp]
      set y := (((affineTypeDBilinearLattice (m + 5) hn).S :
        Module.End ℤ (affineTypeDBilinearLattice (m + 5) hn)) ^ j) x
      rw [show ((affineTypeDBilinearLattice (m + 5) hn).S :
          Module.End ℤ (affineTypeDBilinearLattice (m + 5) hn)) y =
          fun i : Fin (m + 5 + 1) ↦ affD_q y i from affineTypeD_S_eq hn y]
      refine ⟨fun a ↦ ?_, ?_, ?_, ?_⟩
      · rw [affD_g_q, hg]
        congr 1
        push_cast
        abel
      · rw [affD_a_q, ha, pow_succ]
        ring
      · rw [affD_b_q, hb, pow_succ]
        ring
      · rw [affD_k_q, hk, hg, ha, Finset.sum_range_succ, zero_sub]
        ring

/-- `S ^ (2 (m + 3)) x = x + c(x) • δ`. -/
private theorem affineTypeD_S_pow_eq (hn : 4 ≤ m + 5) (x : Fin (m + 5 + 1) → ℤ) :
    (((affineTypeDBilinearLattice (m + 5) hn).S :
      Module.End ℤ (affineTypeDBilinearLattice (m + 5) hn)) ^ (2 * (m + 3))) x =
      x + affD_c x • affD_δ := by
  obtain ⟨hg, ha, hb, hk⟩ := affineTypeD_S_pow_model hn (2 * (m + 3)) x
  have hcast : ((2 * (m + 3) : ℕ) : Fin (m + 3)) = 0 := by
    ext
    simp [Fin.val_natCast, Nat.mul_mod_left]
  have heven : Even (2 * (m + 3)) := even_two_mul _
  apply affD_ext
  · intro a
    have := a.isLt
    rw [hg, hcast, sub_zero]
    unfold affD_g
    rw [affD_gN_add_smul, affD_gN_δ _ (by omega), mul_zero, add_zero]
  · rw [ha, heven.neg_one_pow, one_mul]
    unfold affD_a
    repeat rw [affD_get_add_smul]
    simp (disch := omega) only [affD_get_δ, ite_eq_left, ite_eq_right, ↓reduceIte, true_or]
    ring
  · rw [hb, heven.neg_one_pow, one_mul]
    unfold affD_b
    repeat rw [affD_get_add_smul]
    simp (disch := omega) only [affD_get_δ, ite_eq_left]
    ring
  · rw [hk, Finset.sum_add_distrib, ← Finset.sum_mul, neg_one_geom_sum, ite_eq_left heven,
      zero_mul, add_zero]
    unfold affD_k
    rw [affD_get_add_smul]
    simp (disch := omega) only [affD_get_δ, ite_eq_left]
    unfold affD_c
    simp only [Finset.sum_neg_distrib]
    ring

private theorem affD_get_single (k : ℕ) :
    affD_get (Pi.single 0 1 : Fin (m + 5 + 1) → ℤ) k = if k = 0 then 1 else 0 := by
  unfold affD_get
  split_ifs with h1 h2 <;> simp_all [Pi.single_apply, Fin.ext_iff]

private theorem affD_c_single_pos : 0 < affD_c (Pi.single 0 1 : Fin (m + 5 + 1) → ℤ) := by
  have hgN : ∀ j ≤ m + 2, affD_gN (Pi.single 0 1 : Fin (m + 5 + 1) → ℤ) j =
      if j = 0 then -1 else 0 := by
    intro j hj
    unfold affD_gN
    simp only [affD_get_single]
    split_ifs <;> first | contradiction | omega
  unfold affD_c affD_g
  rw [Finset.sum_congr rfl fun i _ ↦ hgN _ (Nat.le_of_lt_succ (Fin.isLt _))]
  have key : (1 : ℤ) ≤ ∑ i ∈ Finset.range (2 * (m + 3)),
      (if ((-(i : Fin (m + 3)) : Fin (m + 3)) : ℕ) = 0 then 1 else 0) := by
    calc (1 : ℤ) = if ((-((0 : ℕ) : Fin (m + 3)) : Fin (m + 3)) : ℕ) = 0 then 1 else 0 := by simp
      _ ≤ _ := Finset.single_le_sum
          (f := fun i : ℕ ↦ if ((-(i : Fin (m + 3)) : Fin (m + 3)) : ℕ) = 0 then (1 : ℤ) else 0)
          (fun i _ ↦ by split_ifs <;> norm_num)
          (Finset.mem_range.mpr (by omega : 0 < 2 * (m + 3)))
  have hneg : ∀ i ∈ Finset.range (2 * (m + 3)),
      (if ((-(i : Fin (m + 3)) : Fin (m + 3)) : ℕ) = 0 then (-1 : ℤ) else 0) =
        -(if ((-(i : Fin (m + 3)) : Fin (m + 3)) : ℕ) = 0 then 1 else 0) := fun i _ ↦ by
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib, neg_neg]
  omega

private theorem affineTypeD_isQuasiUnipotent_of_five (hn : 4 ≤ m + 5) :
    Module.End.IsQuasiUnipotentOfIndex
      ((affineTypeDBilinearLattice (m + 5) hn).S :
        Module.End ℤ (affineTypeDBilinearLattice (m + 5) hn)) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      ((affineTypeDBilinearLattice (m + 5) hn).S :
        Module.End ℤ (affineTypeDBilinearLattice (m + 5) hn)) 1 := by
  set S := ((affineTypeDBilinearLattice (m + 5) hn).S :
    Module.End ℤ (affineTypeDBilinearLattice (m + 5) hn))
  have hpow := affineTypeD_S_pow_eq hn
  have hsub : ∀ y : Fin (m + 5 + 1) → ℤ, (S ^ (2 * (m + 3)) - 1) y = affD_c y • affD_δ := by
    intro y
    funext i
    change (S ^ (2 * (m + 3))) y i - y i = _
    rw [hpow, Pi.add_apply, add_sub_cancel_left]
  have hfix : ∀ t : ℤ, (S ^ (2 * (m + 3))) (t • affD_δ) = t • affD_δ := by
    intro t
    rw [hpow, affD_c_smul_δ, zero_smul, add_zero]
  refine ⟨⟨2 * (m + 3), by omega, LinearMap.ext fun x ↦ ?_⟩, ?_⟩
  · rw [sq, mul_apply_eq_comp, hsub, hsub, affD_c_smul_δ, zero_smul]
    rfl
  · have hcv := affD_c_single_pos (m := m)
    refine Module.End.not_isQuasiUnipotentOfIndex_one_of_pow_apply (M := Fin (m + 5 + 1) → ℤ) S
      (h := 2 * (m + 3)) (Pi.single 0 1) (affD_c (Pi.single 0 1) • affD_δ) (hfix _)
      (hpow _) ?_
    intro h
    have := congrFun h 0
    simp only [Pi.smul_apply, affD_δ, Fin.val_zero, true_or, ↓reduceIte, smul_eq_mul, mul_one,
      Pi.zero_apply] at this
    omega

/-- `S` is quasi-unipotent of index exactly `2`: the null root gives a Jordan block of size `2`
at eigenvalue `1`. -/
theorem affineTypeDBilinearLattice_isQuasiUnipotent (n : ℕ) (hn : 4 ≤ n) :
    Module.End.IsQuasiUnipotentOfIndex
      ((affineTypeDBilinearLattice n hn).S : Module.End ℤ (affineTypeDBilinearLattice n hn)) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      ((affineTypeDBilinearLattice n hn).S : Module.End ℤ (affineTypeDBilinearLattice n hn)) 1 := by
  rcases Nat.lt_or_ge n 5 with h | h
  · obtain rfl : n = 4 := by omega
    exact affineTypeD4_isQuasiUnipotent hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    exact affineTypeD_isQuasiUnipotent_of_five hn

noncomputable abbrev affineTypeDBilinearLatticeWithMonoidQuasiUnipotent (n : ℕ) (hn : 4 ≤ n) :
    BilinearLattice.BilinearLatticeWithMonoidQuasiUnipotent.{0} :=
  BilinearLattice.eulerLatticeWithMonoidQuasiUnipotent
    (M := affineTypeDMatrix n)
    (hS := (affineTypeDBilinearLattice_isQuasiUnipotent n hn).1)

end EulerLattice

/-! ### Special features -/

theorem affineTypeD_isAffineCoxeter (n : ℕ) (hn : 4 ≤ n) :
    @IsAffineCoxeter _ (@affineTypeDGroup n ⟨by omega⟩) :=
  (affineTypeD_isIrreducibleAffineCoxeter n hn).1

theorem affineTypeD_isAffineCoxeterOrEmpty (n : ℕ) (hn : 4 ≤ n) :
    @IsAffineCoxeterOrEmpty _ (@affineTypeDGroup n ⟨by omega⟩) :=
  Or.inr (affineTypeD_isAffineCoxeter n hn)

theorem affineTypeD_isPolyAffineWeyl (n : ℕ) (hn : 4 ≤ n) :
    @IsPolyAffineWeyl _ (@affineTypeDGroup n ⟨by omega⟩) :=
  (affineTypeD_isIrreducibleAffineWeyl n hn).1

theorem affineTypeD_hasGeneralizedCartanMatrix (n : ℕ) (hn : 4 ≤ n) :
    @HasGeneralizedCartanMatrix _ (@affineTypeDGroup n ⟨by omega⟩) :=
  hasGeneralizedCartanMatrix_of_entries fun i i' hne ↦
    Or.inr (affineTypeD_isSimplyLaced n hn i i' hne)

end Coxeter
