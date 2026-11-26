module

public import Coxeter.BilinearLatticeDynkins
public import Coxeter.SpecialFeatures

/-!
# Exceptional affine Coxeter groups

This file defines the affine Coxeter matrices of types `Ẽ₆`, `Ẽ₇`, `Ẽ₈`, `F̃₄`, `G̃₂`, proves
that they are irreducible affine Coxeter groups and irreducible affine Weyl groups, and defines the
Euler lattices of the simply laced ones.

## Implementation notes

Positive semidefiniteness of `bil` is proved from an explicit `LDLᵀ` decomposition of its Gram
matrix as a sum of squares (the last pivot is `0`), and degeneracy by exhibiting the null root.
-/

@[expose] public section

namespace Coxeter

set_option backward.isDefEq.respectTransparency false in
/-- The Coxeter matrix of affine type `Ẽ₆`: mathlib's `CoxeterMatrix.E₆` with one extra node.
```
                o
                |
                o
                |
    o --- o --- o --- o --- o
```
(the extra node `6` is attached to node `1`). -/
def affineTypeE6Matrix : CoxeterMatrix (Fin 7) where
  M := !![1, 2, 3, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 3;
          3, 2, 1, 3, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2;
          2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 3, 1, 2;
          2, 3, 2, 2, 2, 2, 1]

set_option backward.isDefEq.respectTransparency false in
/-- The Coxeter matrix of affine type `Ẽ₇`: mathlib's `CoxeterMatrix.E₇` with one extra node.
```
                      o
                      |
    o --- o --- o --- o --- o --- o --- o
```
(the extra node `7` is attached to node `0`). -/
def affineTypeE7Matrix : CoxeterMatrix (Fin 8) where
  M := !![1, 2, 3, 2, 2, 2, 2, 3;
          2, 1, 2, 3, 2, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2, 2;
          2, 2, 2, 3, 1, 3, 2, 2;
          2, 2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 2, 3, 1, 2;
          3, 2, 2, 2, 2, 2, 2, 1]

set_option backward.isDefEq.respectTransparency false in
/-- The Coxeter matrix of affine type `Ẽ₈`: mathlib's `CoxeterMatrix.E₈` with one extra node.
```
                o
                |
    o --- o --- o --- o --- o --- o --- o --- o
```
(the extra node `8` is attached to node `7`). -/
def affineTypeE8Matrix : CoxeterMatrix (Fin 9) where
  M := !![1, 2, 3, 2, 2, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2, 2, 2;
          2, 2, 2, 3, 1, 3, 2, 2, 2;
          2, 2, 2, 2, 3, 1, 3, 2, 2;
          2, 2, 2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 2, 2, 2, 3, 1]

set_option backward.isDefEq.respectTransparency false in
/-- The Coxeter matrix of affine type `F̃₄`: mathlib's `CoxeterMatrix.F₄` with one extra node.
```
                    4
    o --- o --- o --- o --- o
```
(the extra node `4` is attached to node `0`, at the left end). -/
def affineTypeF4Matrix : CoxeterMatrix (Fin 5) where
  M := !![1, 3, 2, 2, 3;
          3, 1, 4, 2, 2;
          2, 4, 1, 3, 2;
          2, 2, 3, 1, 2;
          3, 2, 2, 2, 1]

set_option backward.isDefEq.respectTransparency false in
/-- The Coxeter matrix of affine type `G̃₂`: mathlib's `CoxeterMatrix.G₂` with one extra node.
```
             6
    o --- o --- o
```
(the extra node `2` is attached to node `0`, at the left end). -/
def affineTypeG2Matrix : CoxeterMatrix (Fin 3) where
  M := !![1, 6, 3;
          6, 1, 2;
          3, 2, 1]

@[reducible] noncomputable def affineTypeE6Group : CoxeterGroup affineTypeE6Matrix.Group where
  B := Fin 7
  M := affineTypeE6Matrix
  cs := affineTypeE6Matrix.toCoxeterSystem

@[reducible] noncomputable def affineTypeE7Group : CoxeterGroup affineTypeE7Matrix.Group where
  B := Fin 8
  M := affineTypeE7Matrix
  cs := affineTypeE7Matrix.toCoxeterSystem

@[reducible] noncomputable def affineTypeE8Group : CoxeterGroup affineTypeE8Matrix.Group where
  B := Fin 9
  M := affineTypeE8Matrix
  cs := affineTypeE8Matrix.toCoxeterSystem

@[reducible] noncomputable def affineTypeF4Group : CoxeterGroup affineTypeF4Matrix.Group where
  B := Fin 5
  M := affineTypeF4Matrix
  cs := affineTypeF4Matrix.toCoxeterSystem

@[reducible] noncomputable def affineTypeG2Group : CoxeterGroup affineTypeG2Matrix.Group where
  B := Fin 3
  M := affineTypeG2Matrix
  cs := affineTypeG2Matrix.toCoxeterSystem

/-- `bil` of type `Ẽ₆` as a sum of squares: an `LDLᵀ` decomposition of its Gram matrix,
whose last pivot is `0`. -/
private theorem bil_affineTypeE6_eq (x : Fin 7 →₀ ℝ) :
    (@bil _ affineTypeE6Group) x x =
      (1) * (x 0 - x 2/2) ^ 2 +
        (1) * (x 1 - x 3/2 - x 6/2) ^ 2 +
        (3/4) * (x 2 - 2*x 3/3) ^ 2 +
        (5/12) * (x 3 - 6*x 4/5 - 3*x 6/5) ^ 2 +
        (2/5) * (x 4 - 5*x 5/4 - 3*x 6/4) ^ 2 +
        (3/8) * (x 5 - x 6) ^ 2 := by
  rw [@bil_self_eq_sum _ affineTypeE6Group (Fin.fintype 7)]
  change ∑ i : Fin 7, ∑ i' : Fin 7,
    x i * x i' * -Real.cos (Real.pi / (affineTypeE6Matrix i i' : ℝ)) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.reduceSucc]
  norm_num [affineTypeE6Matrix, Real.cos_pi_div_three, Real.cos_pi_div_four, Real.cos_pi_div_six]
  ring

private theorem bil_affineTypeE6_nonneg (x : Fin 7 →₀ ℝ) :
    0 ≤ (@bil _ affineTypeE6Group) x x := by
  rw [bil_affineTypeE6_eq]
  positivity

/-- The null root of `Ẽ₆`, in the coordinates of `V`. -/
private noncomputable def affineTypeE6Null : Fin 7 →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm ![1, 2, 2, 3, 2, 1, 1]

private theorem bil_affineTypeE6Null (i : Fin 7) :
    (@bil _ affineTypeE6Group) affineTypeE6Null (@stdBasis _ affineTypeE6Group i) = 0 := by
  rw [@bil_stdBasis_right_eq_sum _ affineTypeE6Group (Fin.fintype 7)]
  change ∑ j : Fin 7, affineTypeE6Null j * -Real.cos (Real.pi / (affineTypeE6Matrix j i : ℝ)) = 0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.reduceSucc]
  fin_cases i <;>
    norm_num [affineTypeE6Null, affineTypeE6Matrix, Real.cos_pi_div_three, Real.cos_pi_div_four,
      Real.cos_pi_div_six]

theorem affineTypeE6_isAffineCoxeter : @IsAffineCoxeter _ affineTypeE6Group :=
  isAffineCoxeter_of_nonneg_of_radical (fun x ↦ bil_affineTypeE6_nonneg x) affineTypeE6Null
    (fun h ↦ by simpa [affineTypeE6Null] using congrArg (fun f : Fin 7 →₀ ℝ ↦ f 0) h)
    bil_affineTypeE6Null

theorem affineTypeE6_isIrreducible : @IsIrreducible _ affineTypeE6Group := by
  refine isIrreducibleMatrix_of_exists_rank_lt (B1 := Fin 7) affineTypeE6Matrix 3
    ![2, 1, 1, 0, 1, 2, 2] fun i hi ↦ ?_
  fin_cases i
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact absurd rfl hi
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩

theorem affineTypeE6_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeE6Group :=
  ⟨affineTypeE6_isAffineCoxeter, affineTypeE6_isIrreducible⟩

theorem affineTypeE6_isCrystallographic : @IsCrystallographic _ affineTypeE6Group := by
  intro i i' hii'
  change Fin 7 at i
  change Fin 7 at i'
  change affineTypeE6Matrix i i' = 0 ∨ affineTypeE6Matrix i i' = 2 ∨
    affineTypeE6Matrix i i' = 3 ∨ affineTypeE6Matrix i i' = 4 ∨ affineTypeE6Matrix i i' = 6
  fin_cases i <;> fin_cases i' <;> simp at hii' <;> norm_num [affineTypeE6Matrix]

/-- A vector isotropic for `bil` of type `Ẽ₆` is a multiple of the null root: every square
of `bil_affineTypeE6_eq` vanishes, and back-substitution expresses each coordinate through the
last one. -/
private theorem bil_affineTypeE6_isotropic (x : Fin 7 →₀ ℝ)
    (hx : (@bil _ affineTypeE6Group) x x = 0) : ∃ a : ℝ, x = a • affineTypeE6Null := by
  rw [bil_affineTypeE6_eq] at hx
  have h0 : x 0 - x 2/2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2 - x 6/2),
        sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5 - 3*x 6/5),
        sq_nonneg (x 4 - 5*x 5/4 - 3*x 6/4), sq_nonneg (x 5 - x 6)])
      (sq_nonneg _)
  have h1 : x 1 - x 3/2 - x 6/2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2 - x 6/2),
        sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5 - 3*x 6/5),
        sq_nonneg (x 4 - 5*x 5/4 - 3*x 6/4), sq_nonneg (x 5 - x 6)])
      (sq_nonneg _)
  have h2 : x 2 - 2*x 3/3 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2 - x 6/2),
        sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5 - 3*x 6/5),
        sq_nonneg (x 4 - 5*x 5/4 - 3*x 6/4), sq_nonneg (x 5 - x 6)])
      (sq_nonneg _)
  have h3 : x 3 - 6*x 4/5 - 3*x 6/5 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2 - x 6/2),
        sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5 - 3*x 6/5),
        sq_nonneg (x 4 - 5*x 5/4 - 3*x 6/4), sq_nonneg (x 5 - x 6)])
      (sq_nonneg _)
  have h4 : x 4 - 5*x 5/4 - 3*x 6/4 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2 - x 6/2),
        sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5 - 3*x 6/5),
        sq_nonneg (x 4 - 5*x 5/4 - 3*x 6/4), sq_nonneg (x 5 - x 6)])
      (sq_nonneg _)
  have h5 : x 5 - x 6 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2 - x 6/2),
        sq_nonneg (x 2 - 2*x 3/3), sq_nonneg (x 3 - 6*x 4/5 - 3*x 6/5),
        sq_nonneg (x 4 - 5*x 5/4 - 3*x 6/4), sq_nonneg (x 5 - x 6)])
      (sq_nonneg _)
  have e0 : x 0 = 1 * x 6 := by
    linear_combination (1) * h0 + (1/2) * h2 + (1/3) * h3 + (2/5) * h4 + (1/2) * h5
  have e1 : x 1 = 2 * x 6 := by
    linear_combination (1) * h1 + (1/2) * h3 + (3/5) * h4 + (3/4) * h5
  have e2 : x 2 = 2 * x 6 := by
    linear_combination (1) * h2 + (2/3) * h3 + (4/5) * h4 + (1) * h5
  have e3 : x 3 = 3 * x 6 := by
    linear_combination (1) * h3 + (6/5) * h4 + (3/2) * h5
  have e4 : x 4 = 2 * x 6 := by
    linear_combination (1) * h4 + (5/4) * h5
  have e5 : x 5 = 1 * x 6 := by
    linear_combination (1) * h5
  refine ⟨x 6, ?_⟩
  ext i
  fin_cases i <;> simp [affineTypeE6Null] <;> linarith

theorem affineTypeE6_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeE6Group :=
  ⟨isPolyAffineWeyl_of_isotropic affineTypeE6_isAffineCoxeter.1 affineTypeE6_isCrystallographic
    (6 : Fin 7) affineTypeE6Null (by simp [affineTypeE6Null]) bil_affineTypeE6Null
    fun x hx ↦ bil_affineTypeE6_isotropic x hx, affineTypeE6_isIrreducible⟩

/-- `bil` of type `Ẽ₇` as a sum of squares: an `LDLᵀ` decomposition of its Gram matrix,
whose last pivot is `0`. -/
private theorem bil_affineTypeE7_eq (x : Fin 8 →₀ ℝ) :
    (@bil _ affineTypeE7Group) x x =
      (1) * (x 0 - x 2/2 - x 7/2) ^ 2 +
        (1) * (x 1 - x 3/2) ^ 2 +
        (3/4) * (x 2 - 2*x 3/3 - x 7/3) ^ 2 +
        (5/12) * (x 3 - 6*x 4/5 - 2*x 7/5) ^ 2 +
        (2/5) * (x 4 - 5*x 5/4 - x 7/2) ^ 2 +
        (3/8) * (x 5 - 4*x 6/3 - 2*x 7/3) ^ 2 +
        (1/3) * (x 6 - x 7) ^ 2 := by
  rw [@bil_self_eq_sum _ affineTypeE7Group (Fin.fintype 8)]
  change ∑ i : Fin 8, ∑ i' : Fin 8,
    x i * x i' * -Real.cos (Real.pi / (affineTypeE7Matrix i i' : ℝ)) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.reduceSucc]
  norm_num [affineTypeE7Matrix, Real.cos_pi_div_three, Real.cos_pi_div_four, Real.cos_pi_div_six]
  ring

private theorem bil_affineTypeE7_nonneg (x : Fin 8 →₀ ℝ) :
    0 ≤ (@bil _ affineTypeE7Group) x x := by
  rw [bil_affineTypeE7_eq]
  positivity

/-- The null root of `Ẽ₇`, in the coordinates of `V`. -/
private noncomputable def affineTypeE7Null : Fin 8 →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm ![2, 2, 3, 4, 3, 2, 1, 1]

private theorem bil_affineTypeE7Null (i : Fin 8) :
    (@bil _ affineTypeE7Group) affineTypeE7Null (@stdBasis _ affineTypeE7Group i) = 0 := by
  rw [@bil_stdBasis_right_eq_sum _ affineTypeE7Group (Fin.fintype 8)]
  change ∑ j : Fin 8, affineTypeE7Null j * -Real.cos (Real.pi / (affineTypeE7Matrix j i : ℝ)) = 0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.reduceSucc]
  fin_cases i <;>
    norm_num [affineTypeE7Null, affineTypeE7Matrix, Real.cos_pi_div_three, Real.cos_pi_div_four,
      Real.cos_pi_div_six]

theorem affineTypeE7_isAffineCoxeter : @IsAffineCoxeter _ affineTypeE7Group :=
  isAffineCoxeter_of_nonneg_of_radical (fun x ↦ bil_affineTypeE7_nonneg x) affineTypeE7Null
    (fun h ↦ by simpa [affineTypeE7Null] using congrArg (fun f : Fin 8 →₀ ℝ ↦ f 0) h)
    bil_affineTypeE7Null

theorem affineTypeE7_isIrreducible : @IsIrreducible _ affineTypeE7Group := by
  refine isIrreducibleMatrix_of_exists_rank_lt (B1 := Fin 8) affineTypeE7Matrix 3
    ![2, 1, 1, 0, 1, 2, 3, 3] fun i hi ↦ ?_
  fin_cases i
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact absurd rfl hi
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨5, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩

theorem affineTypeE7_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeE7Group :=
  ⟨affineTypeE7_isAffineCoxeter, affineTypeE7_isIrreducible⟩

theorem affineTypeE7_isCrystallographic : @IsCrystallographic _ affineTypeE7Group := by
  intro i i' hii'
  change Fin 8 at i
  change Fin 8 at i'
  change affineTypeE7Matrix i i' = 0 ∨ affineTypeE7Matrix i i' = 2 ∨
    affineTypeE7Matrix i i' = 3 ∨ affineTypeE7Matrix i i' = 4 ∨ affineTypeE7Matrix i i' = 6
  fin_cases i <;> fin_cases i' <;> simp at hii' <;> norm_num [affineTypeE7Matrix]

/-- A vector isotropic for `bil` of type `Ẽ₇` is a multiple of the null root: every square
of `bil_affineTypeE7_eq` vanishes, and back-substitution expresses each coordinate through the
last one. -/
private theorem bil_affineTypeE7_isotropic (x : Fin 8 →₀ ℝ)
    (hx : (@bil _ affineTypeE7Group) x x = 0) : ∃ a : ℝ, x = a • affineTypeE7Null := by
  rw [bil_affineTypeE7_eq] at hx
  have h0 : x 0 - x 2/2 - x 7/2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2 - x 7/2), sq_nonneg (x 1 - x 3/2),
        sq_nonneg (x 2 - 2*x 3/3 - x 7/3), sq_nonneg (x 3 - 6*x 4/5 - 2*x 7/5),
        sq_nonneg (x 4 - 5*x 5/4 - x 7/2), sq_nonneg (x 5 - 4*x 6/3 - 2*x 7/3),
        sq_nonneg (x 6 - x 7)])
      (sq_nonneg _)
  have h1 : x 1 - x 3/2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2 - x 7/2), sq_nonneg (x 1 - x 3/2),
        sq_nonneg (x 2 - 2*x 3/3 - x 7/3), sq_nonneg (x 3 - 6*x 4/5 - 2*x 7/5),
        sq_nonneg (x 4 - 5*x 5/4 - x 7/2), sq_nonneg (x 5 - 4*x 6/3 - 2*x 7/3),
        sq_nonneg (x 6 - x 7)])
      (sq_nonneg _)
  have h2 : x 2 - 2*x 3/3 - x 7/3 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2 - x 7/2), sq_nonneg (x 1 - x 3/2),
        sq_nonneg (x 2 - 2*x 3/3 - x 7/3), sq_nonneg (x 3 - 6*x 4/5 - 2*x 7/5),
        sq_nonneg (x 4 - 5*x 5/4 - x 7/2), sq_nonneg (x 5 - 4*x 6/3 - 2*x 7/3),
        sq_nonneg (x 6 - x 7)])
      (sq_nonneg _)
  have h3 : x 3 - 6*x 4/5 - 2*x 7/5 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2 - x 7/2), sq_nonneg (x 1 - x 3/2),
        sq_nonneg (x 2 - 2*x 3/3 - x 7/3), sq_nonneg (x 3 - 6*x 4/5 - 2*x 7/5),
        sq_nonneg (x 4 - 5*x 5/4 - x 7/2), sq_nonneg (x 5 - 4*x 6/3 - 2*x 7/3),
        sq_nonneg (x 6 - x 7)])
      (sq_nonneg _)
  have h4 : x 4 - 5*x 5/4 - x 7/2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2 - x 7/2), sq_nonneg (x 1 - x 3/2),
        sq_nonneg (x 2 - 2*x 3/3 - x 7/3), sq_nonneg (x 3 - 6*x 4/5 - 2*x 7/5),
        sq_nonneg (x 4 - 5*x 5/4 - x 7/2), sq_nonneg (x 5 - 4*x 6/3 - 2*x 7/3),
        sq_nonneg (x 6 - x 7)])
      (sq_nonneg _)
  have h5 : x 5 - 4*x 6/3 - 2*x 7/3 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2 - x 7/2), sq_nonneg (x 1 - x 3/2),
        sq_nonneg (x 2 - 2*x 3/3 - x 7/3), sq_nonneg (x 3 - 6*x 4/5 - 2*x 7/5),
        sq_nonneg (x 4 - 5*x 5/4 - x 7/2), sq_nonneg (x 5 - 4*x 6/3 - 2*x 7/3),
        sq_nonneg (x 6 - x 7)])
      (sq_nonneg _)
  have h6 : x 6 - x 7 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2 - x 7/2), sq_nonneg (x 1 - x 3/2),
        sq_nonneg (x 2 - 2*x 3/3 - x 7/3), sq_nonneg (x 3 - 6*x 4/5 - 2*x 7/5),
        sq_nonneg (x 4 - 5*x 5/4 - x 7/2), sq_nonneg (x 5 - 4*x 6/3 - 2*x 7/3),
        sq_nonneg (x 6 - x 7)])
      (sq_nonneg _)
  have e0 : x 0 = 2 * x 7 := by
    linear_combination (1) * h0 + (1/2) * h2 + (1/3) * h3 + (2/5) * h4 + (1/2) * h5 + (2/3) * h6
  have e1 : x 1 = 2 * x 7 := by
    linear_combination (1) * h1 + (1/2) * h3 + (3/5) * h4 + (3/4) * h5 + (1) * h6
  have e2 : x 2 = 3 * x 7 := by
    linear_combination (1) * h2 + (2/3) * h3 + (4/5) * h4 + (1) * h5 + (4/3) * h6
  have e3 : x 3 = 4 * x 7 := by
    linear_combination (1) * h3 + (6/5) * h4 + (3/2) * h5 + (2) * h6
  have e4 : x 4 = 3 * x 7 := by
    linear_combination (1) * h4 + (5/4) * h5 + (5/3) * h6
  have e5 : x 5 = 2 * x 7 := by
    linear_combination (1) * h5 + (4/3) * h6
  have e6 : x 6 = 1 * x 7 := by
    linear_combination (1) * h6
  refine ⟨x 7, ?_⟩
  ext i
  fin_cases i <;> simp [affineTypeE7Null] <;> linarith

theorem affineTypeE7_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeE7Group :=
  ⟨isPolyAffineWeyl_of_isotropic affineTypeE7_isAffineCoxeter.1 affineTypeE7_isCrystallographic
    (7 : Fin 8) affineTypeE7Null (by simp [affineTypeE7Null]) bil_affineTypeE7Null
    fun x hx ↦ bil_affineTypeE7_isotropic x hx, affineTypeE7_isIrreducible⟩

/-- `bil` of type `Ẽ₈` as a sum of squares: an `LDLᵀ` decomposition of its Gram matrix,
whose last pivot is `0`. -/
private theorem bil_affineTypeE8_eq (x : Fin 9 →₀ ℝ) :
    (@bil _ affineTypeE8Group) x x =
      (1) * (x 0 - x 2/2) ^ 2 +
        (1) * (x 1 - x 3/2) ^ 2 +
        (3/4) * (x 2 - 2*x 3/3) ^ 2 +
        (5/12) * (x 3 - 6*x 4/5) ^ 2 +
        (2/5) * (x 4 - 5*x 5/4) ^ 2 +
        (3/8) * (x 5 - 4*x 6/3) ^ 2 +
        (1/3) * (x 6 - 3*x 7/2) ^ 2 +
        (1/4) * (x 7 - 2*x 8) ^ 2 := by
  rw [@bil_self_eq_sum _ affineTypeE8Group (Fin.fintype 9)]
  change ∑ i : Fin 9, ∑ i' : Fin 9,
    x i * x i' * -Real.cos (Real.pi / (affineTypeE8Matrix i i' : ℝ)) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.reduceSucc]
  norm_num [affineTypeE8Matrix, Real.cos_pi_div_three, Real.cos_pi_div_four, Real.cos_pi_div_six]
  ring

private theorem bil_affineTypeE8_nonneg (x : Fin 9 →₀ ℝ) :
    0 ≤ (@bil _ affineTypeE8Group) x x := by
  rw [bil_affineTypeE8_eq]
  positivity

/-- The null root of `Ẽ₈`, in the coordinates of `V`. -/
private noncomputable def affineTypeE8Null : Fin 9 →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm ![2, 3, 4, 6, 5, 4, 3, 2, 1]

private theorem bil_affineTypeE8Null (i : Fin 9) :
    (@bil _ affineTypeE8Group) affineTypeE8Null (@stdBasis _ affineTypeE8Group i) = 0 := by
  rw [@bil_stdBasis_right_eq_sum _ affineTypeE8Group (Fin.fintype 9)]
  change ∑ j : Fin 9, affineTypeE8Null j * -Real.cos (Real.pi / (affineTypeE8Matrix j i : ℝ)) = 0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.reduceSucc]
  fin_cases i <;>
    norm_num [affineTypeE8Null, affineTypeE8Matrix, Real.cos_pi_div_three, Real.cos_pi_div_four,
      Real.cos_pi_div_six]

theorem affineTypeE8_isAffineCoxeter : @IsAffineCoxeter _ affineTypeE8Group :=
  isAffineCoxeter_of_nonneg_of_radical (fun x ↦ bil_affineTypeE8_nonneg x) affineTypeE8Null
    (fun h ↦ by simpa [affineTypeE8Null] using congrArg (fun f : Fin 9 →₀ ℝ ↦ f 0) h)
    bil_affineTypeE8Null

theorem affineTypeE8_isIrreducible : @IsIrreducible _ affineTypeE8Group := by
  refine isIrreducibleMatrix_of_exists_rank_lt (B1 := Fin 9) affineTypeE8Matrix 3
    ![2, 1, 1, 0, 1, 2, 3, 4, 5] fun i hi ↦ ?_
  fin_cases i
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact absurd rfl hi
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨5, by decide, by decide⟩
  · exact ⟨6, by decide, by decide⟩
  · exact ⟨7, by decide, by decide⟩

theorem affineTypeE8_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeE8Group :=
  ⟨affineTypeE8_isAffineCoxeter, affineTypeE8_isIrreducible⟩

theorem affineTypeE8_isCrystallographic : @IsCrystallographic _ affineTypeE8Group := by
  intro i i' hii'
  change Fin 9 at i
  change Fin 9 at i'
  change affineTypeE8Matrix i i' = 0 ∨ affineTypeE8Matrix i i' = 2 ∨
    affineTypeE8Matrix i i' = 3 ∨ affineTypeE8Matrix i i' = 4 ∨ affineTypeE8Matrix i i' = 6
  fin_cases i <;> fin_cases i' <;> simp at hii' <;> norm_num [affineTypeE8Matrix]

/-- A vector isotropic for `bil` of type `Ẽ₈` is a multiple of the null root: every square
of `bil_affineTypeE8_eq` vanishes, and back-substitution expresses each coordinate through the
last one. -/
private theorem bil_affineTypeE8_isotropic (x : Fin 9 →₀ ℝ)
    (hx : (@bil _ affineTypeE8Group) x x = 0) : ∃ a : ℝ, x = a • affineTypeE8Null := by
  rw [bil_affineTypeE8_eq] at hx
  have h0 : x 0 - x 2/2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2), sq_nonneg (x 2 - 2*x 3/3),
        sq_nonneg (x 3 - 6*x 4/5), sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
        sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7 - 2*x 8)])
      (sq_nonneg _)
  have h1 : x 1 - x 3/2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2), sq_nonneg (x 2 - 2*x 3/3),
        sq_nonneg (x 3 - 6*x 4/5), sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
        sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7 - 2*x 8)])
      (sq_nonneg _)
  have h2 : x 2 - 2*x 3/3 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2), sq_nonneg (x 2 - 2*x 3/3),
        sq_nonneg (x 3 - 6*x 4/5), sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
        sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7 - 2*x 8)])
      (sq_nonneg _)
  have h3 : x 3 - 6*x 4/5 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2), sq_nonneg (x 2 - 2*x 3/3),
        sq_nonneg (x 3 - 6*x 4/5), sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
        sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7 - 2*x 8)])
      (sq_nonneg _)
  have h4 : x 4 - 5*x 5/4 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2), sq_nonneg (x 2 - 2*x 3/3),
        sq_nonneg (x 3 - 6*x 4/5), sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
        sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7 - 2*x 8)])
      (sq_nonneg _)
  have h5 : x 5 - 4*x 6/3 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2), sq_nonneg (x 2 - 2*x 3/3),
        sq_nonneg (x 3 - 6*x 4/5), sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
        sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7 - 2*x 8)])
      (sq_nonneg _)
  have h6 : x 6 - 3*x 7/2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2), sq_nonneg (x 2 - 2*x 3/3),
        sq_nonneg (x 3 - 6*x 4/5), sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
        sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7 - 2*x 8)])
      (sq_nonneg _)
  have h7 : x 7 - 2*x 8 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 2/2), sq_nonneg (x 1 - x 3/2), sq_nonneg (x 2 - 2*x 3/3),
        sq_nonneg (x 3 - 6*x 4/5), sq_nonneg (x 4 - 5*x 5/4), sq_nonneg (x 5 - 4*x 6/3),
        sq_nonneg (x 6 - 3*x 7/2), sq_nonneg (x 7 - 2*x 8)])
      (sq_nonneg _)
  have e0 : x 0 = 2 * x 8 := by
    linear_combination (1) * h0 + (1/2) * h2 + (1/3) * h3 + (2/5) * h4 + (1/2) * h5 + (2/3) * h6 +
      (1) * h7
  have e1 : x 1 = 3 * x 8 := by
    linear_combination (1) * h1 + (1/2) * h3 + (3/5) * h4 + (3/4) * h5 + (1) * h6 + (3/2) * h7
  have e2 : x 2 = 4 * x 8 := by
    linear_combination (1) * h2 + (2/3) * h3 + (4/5) * h4 + (1) * h5 + (4/3) * h6 + (2) * h7
  have e3 : x 3 = 6 * x 8 := by
    linear_combination (1) * h3 + (6/5) * h4 + (3/2) * h5 + (2) * h6 + (3) * h7
  have e4 : x 4 = 5 * x 8 := by
    linear_combination (1) * h4 + (5/4) * h5 + (5/3) * h6 + (5/2) * h7
  have e5 : x 5 = 4 * x 8 := by
    linear_combination (1) * h5 + (4/3) * h6 + (2) * h7
  have e6 : x 6 = 3 * x 8 := by
    linear_combination (1) * h6 + (3/2) * h7
  have e7 : x 7 = 2 * x 8 := by
    linear_combination (1) * h7
  refine ⟨x 8, ?_⟩
  ext i
  fin_cases i <;> simp [affineTypeE8Null] <;> linarith

theorem affineTypeE8_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeE8Group :=
  ⟨isPolyAffineWeyl_of_isotropic affineTypeE8_isAffineCoxeter.1 affineTypeE8_isCrystallographic
    (8 : Fin 9) affineTypeE8Null (by simp [affineTypeE8Null]) bil_affineTypeE8Null
    fun x hx ↦ bil_affineTypeE8_isotropic x hx, affineTypeE8_isIrreducible⟩

/-- `bil` of type `F̃₄` as a sum of squares: an `LDLᵀ` decomposition of its Gram matrix,
whose last pivot is `0`. -/
private theorem bil_affineTypeF4_eq (x : Fin 5 →₀ ℝ) :
    (@bil _ affineTypeF4Group) x x =
      (1) * (x 0 - x 1/2 - x 4/2) ^ 2 +
        (3/4) * (-2*Real.sqrt 2*x 2/3 + x 1 - x 4/3) ^ 2 +
        (1/3) * (-Real.sqrt 2*x 4/2 + x 2 - 3*x 3/2) ^ 2 +
        (1/4) * (-Real.sqrt 2*x 4 + x 3) ^ 2 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [@bil_self_eq_sum _ affineTypeF4Group (Fin.fintype 5)]
  change ∑ i : Fin 5, ∑ i' : Fin 5,
    x i * x i' * -Real.cos (Real.pi / (affineTypeF4Matrix i i' : ℝ)) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.reduceSucc]
  norm_num [affineTypeF4Matrix, Real.cos_pi_div_three, Real.cos_pi_div_four, Real.cos_pi_div_six]
  linear_combination (-x 2^2/3 - x 4^2/3) * hs2

private theorem bil_affineTypeF4_nonneg (x : Fin 5 →₀ ℝ) :
    0 ≤ (@bil _ affineTypeF4Group) x x := by
  rw [bil_affineTypeF4_eq]
  positivity

/-- The null root of `F̃₄`, in the coordinates of `V`. -/
private noncomputable def affineTypeF4Null : Fin 5 →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm ![2, 3, 2*Real.sqrt 2, Real.sqrt 2, 1]

private theorem bil_affineTypeF4Null (i : Fin 5) :
    (@bil _ affineTypeF4Group) affineTypeF4Null (@stdBasis _ affineTypeF4Group i) = 0 := by
  rw [@bil_stdBasis_right_eq_sum _ affineTypeF4Group (Fin.fintype 5)]
  change ∑ j : Fin 5, affineTypeF4Null j * -Real.cos (Real.pi / (affineTypeF4Matrix j i : ℝ)) = 0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.reduceSucc]
  fin_cases i <;>
    norm_num [affineTypeF4Null, affineTypeF4Matrix, Real.cos_pi_div_three, Real.cos_pi_div_four,
      Real.cos_pi_div_six]
  all_goals ring_nf
  norm_num

theorem affineTypeF4_isAffineCoxeter : @IsAffineCoxeter _ affineTypeF4Group :=
  isAffineCoxeter_of_nonneg_of_radical (fun x ↦ bil_affineTypeF4_nonneg x) affineTypeF4Null
    (fun h ↦ by simpa [affineTypeF4Null] using congrArg (fun f : Fin 5 →₀ ℝ ↦ f 0) h)
    bil_affineTypeF4Null

theorem affineTypeF4_isIrreducible : @IsIrreducible _ affineTypeF4Group := by
  refine isIrreducibleMatrix_of_exists_rank_lt (B1 := Fin 5) affineTypeF4Matrix 0
    ![0, 1, 2, 3, 1] fun i hi ↦ ?_
  fin_cases i
  · exact absurd rfl hi
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩

theorem affineTypeF4_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeF4Group :=
  ⟨affineTypeF4_isAffineCoxeter, affineTypeF4_isIrreducible⟩

theorem affineTypeF4_isCrystallographic : @IsCrystallographic _ affineTypeF4Group := by
  intro i i' hii'
  change Fin 5 at i
  change Fin 5 at i'
  change affineTypeF4Matrix i i' = 0 ∨ affineTypeF4Matrix i i' = 2 ∨
    affineTypeF4Matrix i i' = 3 ∨ affineTypeF4Matrix i i' = 4 ∨ affineTypeF4Matrix i i' = 6
  fin_cases i <;> fin_cases i' <;> simp at hii' <;> norm_num [affineTypeF4Matrix]

/-- A vector isotropic for `bil` of type `F̃₄` is a multiple of the null root: every square
of `bil_affineTypeF4_eq` vanishes, and back-substitution expresses each coordinate through the
last one. -/
private theorem bil_affineTypeF4_isotropic (x : Fin 5 →₀ ℝ)
    (hx : (@bil _ affineTypeF4Group) x x = 0) : ∃ a : ℝ, x = a • affineTypeF4Null := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [bil_affineTypeF4_eq] at hx
  have h0 : x 0 - x 1/2 - x 4/2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 1/2 - x 4/2),
        sq_nonneg (-2*Real.sqrt 2*x 2/3 + x 1 - x 4/3),
        sq_nonneg (-Real.sqrt 2*x 4/2 + x 2 - 3*x 3/2), sq_nonneg (-Real.sqrt 2*x 4 + x 3)])
      (sq_nonneg _)
  have h1 : -2*Real.sqrt 2*x 2/3 + x 1 - x 4/3 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 1/2 - x 4/2),
        sq_nonneg (-2*Real.sqrt 2*x 2/3 + x 1 - x 4/3),
        sq_nonneg (-Real.sqrt 2*x 4/2 + x 2 - 3*x 3/2), sq_nonneg (-Real.sqrt 2*x 4 + x 3)])
      (sq_nonneg _)
  have h2 : -Real.sqrt 2*x 4/2 + x 2 - 3*x 3/2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 1/2 - x 4/2),
        sq_nonneg (-2*Real.sqrt 2*x 2/3 + x 1 - x 4/3),
        sq_nonneg (-Real.sqrt 2*x 4/2 + x 2 - 3*x 3/2), sq_nonneg (-Real.sqrt 2*x 4 + x 3)])
      (sq_nonneg _)
  have h3 : -Real.sqrt 2*x 4 + x 3 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (x 0 - x 1/2 - x 4/2),
        sq_nonneg (-2*Real.sqrt 2*x 2/3 + x 1 - x 4/3),
        sq_nonneg (-Real.sqrt 2*x 4/2 + x 2 - 3*x 3/2), sq_nonneg (-Real.sqrt 2*x 4 + x 3)])
      (sq_nonneg _)
  have e0 : x 0 = 2 * x 4 := by
    linear_combination (1) * h0 + (1/2) * h1 + (Real.sqrt 2/3) * h2 + (Real.sqrt 2/2) * h3 +
      (2*x 4/3) * hs2
  have e1 : x 1 = 3 * x 4 := by
    linear_combination (1) * h1 + (2*Real.sqrt 2/3) * h2 + (Real.sqrt 2) * h3 + (4*x 4/3) * hs2
  have e2 : x 2 = 2*Real.sqrt 2 * x 4 := by
    linear_combination (1) * h2 + (3/2) * h3
  have e3 : x 3 = Real.sqrt 2 * x 4 := by
    linear_combination (1) * h3
  refine ⟨x 4, ?_⟩
  ext i
  fin_cases i <;> simp [affineTypeF4Null] <;> linarith

theorem affineTypeF4_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeF4Group :=
  ⟨isPolyAffineWeyl_of_isotropic affineTypeF4_isAffineCoxeter.1 affineTypeF4_isCrystallographic
    (4 : Fin 5) affineTypeF4Null (by simp [affineTypeF4Null]) bil_affineTypeF4Null
    fun x hx ↦ bil_affineTypeF4_isotropic x hx, affineTypeF4_isIrreducible⟩

/-- `bil` of type `G̃₂` as a sum of squares: an `LDLᵀ` decomposition of its Gram matrix,
whose last pivot is `0`. -/
private theorem bil_affineTypeG2_eq (x : Fin 3 →₀ ℝ) :
    (@bil _ affineTypeG2Group) x x =
      (1) * (-Real.sqrt 3*x 1/2 + x 0 - x 2/2) ^ 2 +
        (1/4) * (-Real.sqrt 3*x 2 + x 1) ^ 2 := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [@bil_self_eq_sum _ affineTypeG2Group (Fin.fintype 3)]
  change ∑ i : Fin 3, ∑ i' : Fin 3,
    x i * x i' * -Real.cos (Real.pi / (affineTypeG2Matrix i i' : ℝ)) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  norm_num [affineTypeG2Matrix, Real.cos_pi_div_three, Real.cos_pi_div_four, Real.cos_pi_div_six]
  linear_combination (-x 1^2/4 - x 2^2/4) * hs3

private theorem bil_affineTypeG2_nonneg (x : Fin 3 →₀ ℝ) :
    0 ≤ (@bil _ affineTypeG2Group) x x := by
  rw [bil_affineTypeG2_eq]
  positivity

/-- The null root of `G̃₂`, in the coordinates of `V`. -/
private noncomputable def affineTypeG2Null : Fin 3 →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm ![2, Real.sqrt 3, 1]

private theorem bil_affineTypeG2Null (i : Fin 3) :
    (@bil _ affineTypeG2Group) affineTypeG2Null (@stdBasis _ affineTypeG2Group i) = 0 := by
  rw [@bil_stdBasis_right_eq_sum _ affineTypeG2Group (Fin.fintype 3)]
  change ∑ j : Fin 3, affineTypeG2Null j * -Real.cos (Real.pi / (affineTypeG2Matrix j i : ℝ)) = 0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  fin_cases i <;>
    norm_num [affineTypeG2Null, affineTypeG2Matrix, Real.cos_pi_div_three, Real.cos_pi_div_four,
      Real.cos_pi_div_six]
  all_goals ring_nf
  norm_num

theorem affineTypeG2_isAffineCoxeter : @IsAffineCoxeter _ affineTypeG2Group :=
  isAffineCoxeter_of_nonneg_of_radical (fun x ↦ bil_affineTypeG2_nonneg x) affineTypeG2Null
    (fun h ↦ by simpa [affineTypeG2Null] using congrArg (fun f : Fin 3 →₀ ℝ ↦ f 0) h)
    bil_affineTypeG2Null

theorem affineTypeG2_isIrreducible : @IsIrreducible _ affineTypeG2Group := by
  refine isIrreducibleMatrix_of_exists_rank_lt (B1 := Fin 3) affineTypeG2Matrix 0
    ![0, 1, 1] fun i hi ↦ ?_
  fin_cases i
  · exact absurd rfl hi
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩

theorem affineTypeG2_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeG2Group :=
  ⟨affineTypeG2_isAffineCoxeter, affineTypeG2_isIrreducible⟩

theorem affineTypeG2_isCrystallographic : @IsCrystallographic _ affineTypeG2Group := by
  intro i i' hii'
  change Fin 3 at i
  change Fin 3 at i'
  change affineTypeG2Matrix i i' = 0 ∨ affineTypeG2Matrix i i' = 2 ∨
    affineTypeG2Matrix i i' = 3 ∨ affineTypeG2Matrix i i' = 4 ∨ affineTypeG2Matrix i i' = 6
  fin_cases i <;> fin_cases i' <;> simp at hii' <;> norm_num [affineTypeG2Matrix]

/-- A vector isotropic for `bil` of type `G̃₂` is a multiple of the null root: every square
of `bil_affineTypeG2_eq` vanishes, and back-substitution expresses each coordinate through the
last one. -/
private theorem bil_affineTypeG2_isotropic (x : Fin 3 →₀ ℝ)
    (hx : (@bil _ affineTypeG2Group) x x = 0) : ∃ a : ℝ, x = a • affineTypeG2Null := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [bil_affineTypeG2_eq] at hx
  have h0 : -Real.sqrt 3*x 1/2 + x 0 - x 2/2 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (-Real.sqrt 3*x 1/2 + x 0 - x 2/2),
        sq_nonneg (-Real.sqrt 3*x 2 + x 1)])
      (sq_nonneg _)
  have h1 : -Real.sqrt 3*x 2 + x 1 = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm
      (by linarith [sq_nonneg (-Real.sqrt 3*x 1/2 + x 0 - x 2/2),
        sq_nonneg (-Real.sqrt 3*x 2 + x 1)])
      (sq_nonneg _)
  have e0 : x 0 = 2 * x 2 := by
    linear_combination (1) * h0 + (Real.sqrt 3/2) * h1 + (x 2/2) * hs3
  have e1 : x 1 = Real.sqrt 3 * x 2 := by
    linear_combination (1) * h1
  refine ⟨x 2, ?_⟩
  ext i
  fin_cases i <;> simp [affineTypeG2Null] <;> linarith

theorem affineTypeG2_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeG2Group :=
  ⟨isPolyAffineWeyl_of_isotropic affineTypeG2_isAffineCoxeter.1 affineTypeG2_isCrystallographic
    (2 : Fin 3) affineTypeG2Null (by simp [affineTypeG2Null]) bil_affineTypeG2Null
    fun x hx ↦ bil_affineTypeG2_isotropic x hx, affineTypeG2_isIrreducible⟩


/-! ### Euler lattices of `Ẽ₆`, `Ẽ₇`, `Ẽ₈` -/

section EulerLattice

/-- The Euler lattice of type `Ẽ₆` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev affineTypeE6BilinearLattice : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice affineTypeE6Matrix

theorem affineTypeE6_isSimplyLaced : BilinearLattice.IsSimplyLaced affineTypeE6Matrix := by
  unfold BilinearLattice.IsSimplyLaced
  intro i j; fin_cases i <;> fin_cases j <;> decide

/-- The Coxeter transformation of `affineTypeE6BilinearLattice` as an integer matrix. `Q ^ 6 - 1`
is square-zero but nonzero. -/
private def affineTypeE6CoxeterTransformation : Matrix (Fin 7) (Fin 7) ℤ :=
  !![0, 1, 0, 0, 0, -1, 0;
     0, 1, 1, 0, 0, -1, -1;
     1, 1, 0, 0, 0, -1, 0;
     0, 1, 1, 0, 0, -1, 0;
     0, 0, 0, 1, 0, -1, 0;
     0, 0, 0, 0, 1, -1, 0;
     0, 1, 0, 0, 0, 0, -1]

/-- `S` is quasi-unipotent of index exactly `2`. -/
theorem affineTypeE6BilinearLattice_isQuasiUnipotent :
    Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE6BilinearLattice.S : Module.End ℤ affineTypeE6BilinearLattice) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE6BilinearLattice.S : Module.End ℤ affineTypeE6BilinearLattice) 1 :=
  ⟨BilinearLattice.ofUnimodular_isQuasiUnipotentOfIndex_two _ _
      affineTypeE6CoxeterTransformation (by decide) (m := 6) (by norm_num) (by decide),
    BilinearLattice.ofUnimodular_not_isQuasiUnipotentOfIndex_one _ _
      affineTypeE6CoxeterTransformation (by decide) (h := 6)
      ![1, 0, 0, 0, 0, 0, 0] ![1, 2, 2, 3, 2, 1, 1] (by decide) (by decide) (by decide)⟩

/-- The Euler lattice of type `Ẽ₇` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev affineTypeE7BilinearLattice : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice affineTypeE7Matrix

theorem affineTypeE7_isSimplyLaced : BilinearLattice.IsSimplyLaced affineTypeE7Matrix := by
  unfold BilinearLattice.IsSimplyLaced
  intro i j; fin_cases i <;> fin_cases j <;> decide

/-- The Coxeter transformation of `affineTypeE7BilinearLattice` as an integer matrix. `Q ^ 12 - 1`
is square-zero but nonzero. -/
private def affineTypeE7CoxeterTransformation : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 1, 0, 0, 0, 0, -1, -1;
     0, 0, 1, 0, 0, 0, -1, 0;
     1, 1, 0, 0, 0, 0, -1, 0;
     0, 1, 1, 0, 0, 0, -1, 0;
     0, 0, 0, 1, 0, 0, -1, 0;
     0, 0, 0, 0, 1, 0, -1, 0;
     0, 0, 0, 0, 0, 1, -1, 0;
     1, 0, 0, 0, 0, 0, 0, -1]

/-- `S` is quasi-unipotent of index exactly `2`. -/
theorem affineTypeE7BilinearLattice_isQuasiUnipotent :
    Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE7BilinearLattice.S : Module.End ℤ affineTypeE7BilinearLattice) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE7BilinearLattice.S : Module.End ℤ affineTypeE7BilinearLattice) 1 :=
  ⟨BilinearLattice.ofUnimodular_isQuasiUnipotentOfIndex_two _ _
      affineTypeE7CoxeterTransformation (by decide) (m := 12) (by norm_num) (by decide),
    BilinearLattice.ofUnimodular_not_isQuasiUnipotentOfIndex_one _ _
      affineTypeE7CoxeterTransformation (by decide) (h := 12)
      ![1, 0, 0, 0, 0, 0, 0, 0] ![4, 4, 6, 8, 6, 4, 2, 2] (by decide) (by decide) (by decide)⟩

/-- The Euler lattice of type `Ẽ₈` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev affineTypeE8BilinearLattice : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice affineTypeE8Matrix

theorem affineTypeE8_isSimplyLaced : BilinearLattice.IsSimplyLaced affineTypeE8Matrix := by
  unfold BilinearLattice.IsSimplyLaced
  intro i j; fin_cases i <;> fin_cases j <;> decide

/-- The Coxeter transformation of `affineTypeE8BilinearLattice` as an integer matrix. `Q ^ 30 - 1`
is square-zero but nonzero. -/
private def affineTypeE8CoxeterTransformation : Matrix (Fin 9) (Fin 9) ℤ :=
  !![0, 1, 0, 0, 0, 0, 0, 0, -1;
     0, 0, 1, 0, 0, 0, 0, 0, -1;
     1, 1, 0, 0, 0, 0, 0, 0, -1;
     0, 1, 1, 0, 0, 0, 0, 0, -1;
     0, 0, 0, 1, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 1, 0, 0, 0, -1;
     0, 0, 0, 0, 0, 1, 0, 0, -1;
     0, 0, 0, 0, 0, 0, 1, 0, -1;
     0, 0, 0, 0, 0, 0, 0, 1, -1]

set_option maxRecDepth 100000 in
/-- `S` is quasi-unipotent of index exactly `2`. -/
theorem affineTypeE8BilinearLattice_isQuasiUnipotent :
    Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE8BilinearLattice.S : Module.End ℤ affineTypeE8BilinearLattice) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE8BilinearLattice.S : Module.End ℤ affineTypeE8BilinearLattice) 1 :=
  ⟨BilinearLattice.ofUnimodular_isQuasiUnipotentOfIndex_two _ _
      affineTypeE8CoxeterTransformation (by decide) (m := 30) (by norm_num) (by decide),
    BilinearLattice.ofUnimodular_not_isQuasiUnipotentOfIndex_one _ _
      affineTypeE8CoxeterTransformation (by decide) (h := 30)
      ![1, 0, 0, 0, 0, 0, 0, 0, 0] ![4, 6, 8, 12, 10, 8, 6, 4, 2]
      (by decide) (by decide) (by decide)⟩

noncomputable abbrev affineTypeE6BilinearLatticeWithMonoidQuasiUnipotent :
    BilinearLattice.BilinearLatticeWithMonoidQuasiUnipotent.{0} :=
  BilinearLattice.eulerLatticeWithMonoidQuasiUnipotent
    (M := affineTypeE6Matrix)
    (hS := affineTypeE6BilinearLattice_isQuasiUnipotent.1)

noncomputable abbrev affineTypeE7BilinearLatticeWithMonoidQuasiUnipotent :
    BilinearLattice.BilinearLatticeWithMonoidQuasiUnipotent.{0} :=
  BilinearLattice.eulerLatticeWithMonoidQuasiUnipotent
    (M := affineTypeE7Matrix)
    (hS := affineTypeE7BilinearLattice_isQuasiUnipotent.1)

noncomputable abbrev affineTypeE8BilinearLatticeWithMonoidQuasiUnipotent :
    BilinearLattice.BilinearLatticeWithMonoidQuasiUnipotent.{0} :=
  BilinearLattice.eulerLatticeWithMonoidQuasiUnipotent
    (M := affineTypeE8Matrix)
    (hS := affineTypeE8BilinearLattice_isQuasiUnipotent.1)

end EulerLattice

/-! ### Special features -/

theorem affineTypeE6_hasGeneralizedCartanMatrix : @HasGeneralizedCartanMatrix _ affineTypeE6Group :=
  hasGeneralizedCartanMatrix_of_entries fun i i' hne ↦ Or.inr (affineTypeE6_isSimplyLaced i i' hne)

theorem affineTypeE6_isAffineCoxeterOrEmpty : @IsAffineCoxeterOrEmpty _ affineTypeE6Group :=
  Or.inr affineTypeE6_isAffineCoxeter

theorem affineTypeE6_isPolyAffineWeyl : @IsPolyAffineWeyl _ affineTypeE6Group :=
  affineTypeE6_isIrreducibleAffineWeyl.1

theorem affineTypeE7_hasGeneralizedCartanMatrix : @HasGeneralizedCartanMatrix _ affineTypeE7Group :=
  hasGeneralizedCartanMatrix_of_entries fun i i' hne ↦ Or.inr (affineTypeE7_isSimplyLaced i i' hne)

theorem affineTypeE7_isAffineCoxeterOrEmpty : @IsAffineCoxeterOrEmpty _ affineTypeE7Group :=
  Or.inr affineTypeE7_isAffineCoxeter

theorem affineTypeE7_isPolyAffineWeyl : @IsPolyAffineWeyl _ affineTypeE7Group :=
  affineTypeE7_isIrreducibleAffineWeyl.1

theorem affineTypeE8_hasGeneralizedCartanMatrix : @HasGeneralizedCartanMatrix _ affineTypeE8Group :=
  hasGeneralizedCartanMatrix_of_entries fun i i' hne ↦ Or.inr (affineTypeE8_isSimplyLaced i i' hne)

theorem affineTypeE8_isAffineCoxeterOrEmpty : @IsAffineCoxeterOrEmpty _ affineTypeE8Group :=
  Or.inr affineTypeE8_isAffineCoxeter

theorem affineTypeE8_isPolyAffineWeyl : @IsPolyAffineWeyl _ affineTypeE8Group :=
  affineTypeE8_isIrreducibleAffineWeyl.1

theorem affineTypeF4_hasGeneralizedCartanMatrix :
    @HasGeneralizedCartanMatrix _ affineTypeF4Group := by
  refine hasGeneralizedCartanMatrix_of_scale (cg := affineTypeF4Group)
    (fun i : Fin 5 ↦ ![1, 1, Real.sqrt 2, Real.sqrt 2, 1] i)
    (fun i : Fin 5 ↦ by fin_cases i <;> norm_num)
    fun i i' hne ↦ ?_
  change Fin 5 at i i'
  change affineTypeF4Matrix i i' = 2 ∨
    ((affineTypeF4Matrix i i' = 0 ∨ affineTypeF4Matrix i i' = 3) ∧ _) ∨
    (affineTypeF4Matrix i i' = 4 ∧ _) ∨ (affineTypeF4Matrix i i' = 6 ∧ _)
  fin_cases i <;> fin_cases i' <;> simp at hne <;> norm_num [affineTypeF4Matrix]

theorem affineTypeF4_isAffineCoxeterOrEmpty : @IsAffineCoxeterOrEmpty _ affineTypeF4Group :=
  Or.inr affineTypeF4_isAffineCoxeter

theorem affineTypeF4_isPolyAffineWeyl : @IsPolyAffineWeyl _ affineTypeF4Group :=
  affineTypeF4_isIrreducibleAffineWeyl.1

theorem affineTypeG2_hasGeneralizedCartanMatrix :
    @HasGeneralizedCartanMatrix _ affineTypeG2Group := by
  refine hasGeneralizedCartanMatrix_of_scale (cg := affineTypeG2Group)
    (fun i : Fin 3 ↦ ![1, Real.sqrt 3, 1] i)
    (fun i : Fin 3 ↦ by fin_cases i <;> norm_num)
    fun i i' hne ↦ ?_
  change Fin 3 at i i'
  change affineTypeG2Matrix i i' = 2 ∨
    ((affineTypeG2Matrix i i' = 0 ∨ affineTypeG2Matrix i i' = 3) ∧ _) ∨
    (affineTypeG2Matrix i i' = 4 ∧ _) ∨ (affineTypeG2Matrix i i' = 6 ∧ _)
  fin_cases i <;> fin_cases i' <;> simp at hne <;> norm_num [affineTypeG2Matrix]

theorem affineTypeG2_isAffineCoxeterOrEmpty : @IsAffineCoxeterOrEmpty _ affineTypeG2Group :=
  Or.inr affineTypeG2_isAffineCoxeter

theorem affineTypeG2_isPolyAffineWeyl : @IsPolyAffineWeyl _ affineTypeG2Group :=
  affineTypeG2_isIrreducibleAffineWeyl.1


end Coxeter
