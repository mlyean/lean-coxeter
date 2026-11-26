module

public import Coxeter.Data.Fin
public import Coxeter.SpecialFeatures

/-!
# Affine Coxeter groups of type C

This file defines the affine type `C` Coxeter matrix and Coxeter group, and proves that `C̃ₙ`
(`n ≥ 2`) is an irreducible affine Coxeter group and an irreducible affine Weyl group.
-/

@[expose] public section

namespace Coxeter

/-- The Coxeter matrix of affine type `C̃ₙ`: the path `0 — 1 — ⋯ — n` whose two end edges are
labelled `4`.
```
       4                 4
    o --- o --- ⋯ --- o --- o
```
For `n = 1` the two generators are joined by an edge labelled `∞` (coded as `0`). -/
def affineTypeCMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
      else if n = 1 then 0
      else if ((i : ℕ) + (j : ℕ) = 1) ∨ ((i : ℕ) + (j : ℕ) = 2 * n - 1 ∧ (n ≤ i ∨ n ≤ j)) then 4
      else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 3 else 2
  isSymm := by grind [Matrix.IsSymm, Matrix.transpose_of]
  diagonal := by simp
  off_diagonal i j h := by
    simp only [Matrix.of_apply, h, ite_false]
    split_ifs <;> omega

@[reducible] noncomputable def affineTypeCGroup (n : ℕ) (_ : 2 ≤ n) :
    CoxeterGroup (affineTypeCMatrix n).Group where
  B := Fin (n + 1)
  M := affineTypeCMatrix n
  cs := (affineTypeCMatrix n).toCoxeterSystem

/-! ### `C̃ₙ` is an irreducible affine Weyl group

By `isIrreducibleAffineWeyl_of_null` it suffices that the diagram is connected, the entries are
crystallographic, and the null root `δ = (1, √2, …, √2, 1)` is orthogonal to every `stdBasis j`.
We write `n = m + 2`. -/

section Classification

variable {m : ℕ}

/-- Column `j` of the Gram matrix of `bil` for `C̃_(m+2)`: the neighbours `j ± 1` along the path,
with coefficient `√2 / 2` across an end edge (labelled `4`) and `1 / 2` otherwise. -/
private theorem affineTypeC_gram (i j : Fin (m + 2 + 1)) :
    -Real.cos (Real.pi / (affineTypeCMatrix (m + 2) i j : ℝ)) =
      (if (i : ℕ) = j then 1 else 0) -
        (if (j : ℕ) + 1 ≤ m + 2 ∧ (i : ℕ) = j + 1 then
          (if (j : ℕ) = 0 ∨ (j : ℕ) = m + 1 then Real.sqrt 2 / 2 else 1 / 2) else 0) -
        (if 1 ≤ (j : ℕ) ∧ (i : ℕ) = j - 1 then
          (if (j : ℕ) = 1 ∨ (j : ℕ) = m + 2 then Real.sqrt 2 / 2 else 1 / 2) else 0) := by
  have hi := i.isLt
  have hj := j.isLt
  unfold affineTypeCMatrix
  simp only [Matrix.of_apply, Fin.ext_iff]
  split
  · simp (disch := omega) only [ite_eq_right]
    norm_num
  · split
    · exfalso
      omega
    · split
      · rename_i h4
        rcases h4 with h | ⟨h, h' | h'⟩
        · obtain h0 | h0 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
          all_goals
            simp (disch := omega) only [ite_eq_left, ite_eq_right]
            norm_num [Real.cos_pi_div_four]
        all_goals
          simp (disch := omega) only [ite_eq_left, ite_eq_right]
          norm_num [Real.cos_pi_div_four]
      · split
        · rename_i h3
          rcases h3 with h | h
          all_goals
            simp (disch := omega) only [ite_eq_left, ite_eq_right]
            norm_num [Real.cos_pi_div_three]
        · simp (disch := omega) only [ite_eq_right]
          norm_num

/-- The null root of `C̃_(m+2)`. -/
private noncomputable def affineTypeCNull : Fin (m + 2 + 1) →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ if (i : ℕ) = 0 ∨ (i : ℕ) = m + 2 then 1 else Real.sqrt 2

private theorem affineTypeCNull_pos (i : Fin (m + 2 + 1)) : 0 < affineTypeCNull (m := m) i := by
  simp only [affineTypeCNull, Finsupp.coe_equivFunOnFinite_symm]
  split_ifs <;> positivity

private theorem finNatGet_affineTypeCNull (k : ℕ) :
    finNatGet (affineTypeCNull (m := m)) k =
      if k < m + 2 + 1 then (if k = 0 ∨ k = m + 2 then 1 else Real.sqrt 2) else 0 := by
  unfold finNatGet
  split_ifs <;> simp_all [affineTypeCNull]

private theorem affineTypeC_bil_null (j : Fin (m + 2 + 1)) :
    (@bil _ (affineTypeCGroup (m + 2) (by omega))) affineTypeCNull
      (@stdBasis _ (affineTypeCGroup (m + 2) (by omega)) j) = 0 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [@bil_stdBasis_right_eq_sum _ (affineTypeCGroup (m + 2) (by omega)) (Fin.fintype _)]
  change ∑ i : Fin (m + 2 + 1),
    affineTypeCNull i * -Real.cos (Real.pi / (affineTypeCMatrix (m + 2) i j : ℝ)) = 0
  simp only [affineTypeC_gram, mul_sub, Finset.sum_sub_distrib, sum_mul_ite_and_val_eq,
    sum_mul_ite_val_eq, finNatGet_affineTypeCNull]
  obtain ⟨j, hj⟩ := j
  simp only
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte, true_or]
    nlinarith
  · rcases Nat.lt_or_ge j (m + 2) with hjm | hjm
    · by_cases h1 : j = 1 <;> by_cases h2 : j = m + 1
      all_goals
        simp (disch := omega) only [ite_eq_left, ite_eq_right]
        ring
    · obtain rfl : j = m + 2 := by omega
      simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte, or_true]
      nlinarith

private theorem affineTypeC_isIrreducible' :
    @IsIrreducible _ (affineTypeCGroup (m + 2) (by omega)) := by
  refine isIrreducibleMatrix_of_exists_lt (affineTypeCMatrix (m + 2)) fun i hi ↦ ?_
  have hi0 : (i : ℕ) ≠ 0 := fun h ↦ hi (Fin.ext h)
  refine ⟨⟨i - 1, by omega⟩, Fin.lt_def.mpr (by simp only; omega), ?_⟩
  unfold affineTypeCMatrix
  simp only [Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem affineTypeC_isCrystallographic' :
    @IsCrystallographic _ (affineTypeCGroup (m + 2) (by omega)) := by
  intro i i' hii'
  change affineTypeCMatrix (m + 2) i i' = 0 ∨ affineTypeCMatrix (m + 2) i i' = 2 ∨
    affineTypeCMatrix (m + 2) i i' = 3 ∨ affineTypeCMatrix (m + 2) i i' = 4 ∨
    affineTypeCMatrix (m + 2) i i' = 6
  unfold affineTypeCMatrix
  simp only [Matrix.of_apply]
  split_ifs <;> simp_all

end Classification

theorem affineTypeC_isIrreducible (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducible _ (affineTypeCGroup n hn) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact affineTypeC_isIrreducible'

theorem affineTypeC_isCrystallographic (n : ℕ) (hn : 2 ≤ n) :
    @IsCrystallographic _ (affineTypeCGroup n hn) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact affineTypeC_isCrystallographic'

theorem affineTypeC_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducibleAffineCoxeter _ (affineTypeCGroup n hn) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact @isIrreducibleAffineCoxeter_of_null _ (affineTypeCGroup (m + 2) hn)
    (Finite.of_fintype (Fin (m + 2 + 1))) affineTypeC_isIrreducible' affineTypeCNull
    (fun i ↦ affineTypeCNull_pos i) affineTypeC_bil_null

theorem affineTypeC_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducibleAffineWeyl _ (affineTypeCGroup n hn) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact @isIrreducibleAffineWeyl_of_null _ (affineTypeCGroup (m + 2) hn)
    (Finite.of_fintype (Fin (m + 2 + 1))) affineTypeC_isIrreducible' affineTypeC_isCrystallographic'
    affineTypeCNull (fun i ↦ affineTypeCNull_pos i) affineTypeC_bil_null

/-! ### Special features -/

theorem affineTypeC_isAffineCoxeter (n : ℕ) (hn : 2 ≤ n) :
    @IsAffineCoxeter _ (affineTypeCGroup n hn) :=
  (affineTypeC_isIrreducibleAffineCoxeter n hn).1

theorem affineTypeC_isAffineCoxeterOrEmpty (n : ℕ) (hn : 2 ≤ n) :
    @IsAffineCoxeterOrEmpty _ (affineTypeCGroup n hn) :=
  Or.inr (affineTypeC_isAffineCoxeter n hn)

theorem affineTypeC_isPolyAffineWeyl (n : ℕ) (hn : 2 ≤ n) :
    @IsPolyAffineWeyl _ (affineTypeCGroup n hn) :=
  (affineTypeC_isIrreducibleAffineWeyl n hn).1

/-- Scaling the two end roots by `√2` (across the end edges labelled `4`) gives a generalized
Cartan matrix. -/
theorem affineTypeC_hasGeneralizedCartanMatrix (n : ℕ) (hn : 2 ≤ n) :
    @HasGeneralizedCartanMatrix _ (affineTypeCGroup n hn) := by
  refine hasGeneralizedCartanMatrix_of_scale (cg := affineTypeCGroup n hn)
    (fun i : Fin (n + 1) ↦ if (i : ℕ) = 0 ∨ (i : ℕ) = n then Real.sqrt 2 else 1)
    (fun i : Fin (n + 1) ↦ by split_ifs <;> positivity) fun i i' hne ↦ ?_
  change Fin (n + 1) at i i'
  have hi := i.isLt
  have hi' := i'.isLt
  have hne' : (i : ℕ) ≠ i' := fun h ↦ hne (Fin.ext h)
  change affineTypeCMatrix n i i' = 2 ∨
    ((affineTypeCMatrix n i i' = 0 ∨ affineTypeCMatrix n i i' = 3) ∧ _) ∨
    (affineTypeCMatrix n i i' = 4 ∧ _) ∨ (affineTypeCMatrix n i i' = 6 ∧ _)
  have hC : affineTypeCMatrix n i i' =
      if (i : ℕ) + i' = 1 ∨ ((i : ℕ) + i' = 2 * n - 1 ∧ (n ≤ i ∨ n ≤ i')) then 4
      else if (i : ℕ) + 1 = i' ∨ (i' : ℕ) + 1 = i then 3 else 2 := by
    unfold affineTypeCMatrix
    simp only [Matrix.of_apply, ite_eq_right hne, ite_eq_right (show n ≠ 1 by omega)]
  rw [hC]
  by_cases h4 : (i : ℕ) + i' = 1 ∨ ((i : ℕ) + i' = 2 * n - 1 ∧ (n ≤ i ∨ n ≤ i'))
  · rw [ite_eq_left h4]
    refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
    obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ : (((i : ℕ) = 0 ∨ (i : ℕ) = n) ∧ ¬ ((i' : ℕ) = 0 ∨ (i' : ℕ) = n)) ∨
        (((i' : ℕ) = 0 ∨ (i' : ℕ) = n) ∧ ¬ ((i : ℕ) = 0 ∨ (i : ℕ) = n)) := by omega
    · exact Or.inr (by rw [ite_eq_left ha, ite_eq_right hb, mul_one])
    · exact Or.inl (by rw [ite_eq_left ha, ite_eq_right hb, mul_one])
  · rw [ite_eq_right h4]
    by_cases h3 : (i : ℕ) + 1 = i' ∨ (i' : ℕ) + 1 = i
    · rw [ite_eq_left h3]
      refine Or.inr (Or.inl ⟨Or.inr rfl, ?_⟩)
      rw [ite_eq_right (show ¬ ((i : ℕ) = 0 ∨ (i : ℕ) = n) by omega),
        ite_eq_right (show ¬ ((i' : ℕ) = 0 ∨ (i' : ℕ) = n) by omega)]
    · rw [ite_eq_right h3]
      exact Or.inl rfl

end Coxeter
