module

public import Coxeter.Data.Fin
public import Coxeter.FiniteOrAffine.AffineTypeC
public import Coxeter.SpecialFeatures

/-!
# Affine Coxeter groups of type B

This file defines the affine type `B` Coxeter matrix and Coxeter group, proves that `B̃ₙ`
(`n ≥ 2`) is an irreducible affine Coxeter group and an irreducible affine Weyl group, and proves
the accidental identification `B̃₂ = C̃₂`.
-/

@[expose] public section

namespace Coxeter

/-- The Coxeter matrix of affine type `B̃ₙ`, `n ≥ 3`: mathlib's `Bₙ` diagram on `0, …, n - 1` (the
path whose last edge, `n - 2 — n - 1`, is labelled `4`), plus the node `n` attached to `1`.
```
    0
     \               4
      1 --- ⋯ --- o --- o
     /
    n
```
-/
def affineTypeBForkMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 1
      else if ((i : ℕ) = n - 2 ∧ (j : ℕ) = n - 1) ∨ ((j : ℕ) = n - 2 ∧ (i : ℕ) = n - 1) then 4
      else if ((i : ℕ) + 1 = j ∧ (j : ℕ) ≤ n - 2) ∨ ((j : ℕ) + 1 = i ∧ (i : ℕ) ≤ n - 2) ∨
        ((i : ℕ) = 1 ∧ (j : ℕ) = n) ∨ ((j : ℕ) = 1 ∧ (i : ℕ) = n) then 3 else 2
  isSymm := by grind [Matrix.IsSymm, Matrix.transpose_of]
  diagonal := by simp
  off_diagonal i j h := by
    simp only [Matrix.of_apply, h, ite_false]
    split_ifs <;> omega

/-- The Coxeter matrix of affine type `B̃ₙ` on `n + 1` generators.

From rank `3` onward it is `affineTypeBForkMatrix n`; for `n ≤ 2` it is normalized to `C̃ₙ`, so that
`B̃₂ = C̃₂` holds on the nose. -/
def affineTypeBMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1)) :=
  if n ≤ 2 then affineTypeCMatrix n else affineTypeBForkMatrix n

@[reducible] noncomputable def affineTypeBGroup (n : ℕ) (_ : 2 ≤ n) :
    CoxeterGroup (affineTypeBMatrix n).Group where
  B := Fin (n + 1)
  M := affineTypeBMatrix n
  cs := (affineTypeBMatrix n).toCoxeterSystem

/-! ### `B̃ₙ` is an irreducible affine Weyl group

For `n ≥ 3`, by `isIrreducibleAffineWeyl_of_null` it suffices that the fork diagram is connected,
the entries are crystallographic, and the null root `δ = (1, 2, …, 2, √2, 1)` (`1` at the leaves
`0`, `n` of the fork, `√2` at the far end `n - 1`) is orthogonal to every `stdBasis j`. We write
`n = m + 3`. For `n = 2`, `B̃₂ = C̃₂`. -/

section Classification

variable {m : ℕ}

/-- The Coxeter group of `affineTypeBForkMatrix n`. -/
@[reducible] private noncomputable def affineTypeBForkGroup (n : ℕ) :
    CoxeterGroup (affineTypeBForkMatrix n).Group where
  B := Fin (n + 1)
  M := affineTypeBForkMatrix n
  cs := (affineTypeBForkMatrix n).toCoxeterSystem

/-- Column `j` of the Gram matrix of `bil` for the fork `B̃_(m+3)`: one indicator per possible
neighbour, with coefficient `√2 / 2` across the edge `m + 1 — m + 2` (labelled `4`). -/
private theorem affineTypeBFork_gram (i j : Fin (m + 3 + 1)) :
    -Real.cos (Real.pi / (affineTypeBForkMatrix (m + 3) i j : ℝ)) =
      (if (i : ℕ) = j then 1 else 0) -
        (if (j : ℕ) + 1 ≤ m + 1 ∧ (i : ℕ) = j + 1 then 1 / 2 else 0) -
        (if (1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ m + 1) ∧ (i : ℕ) = j - 1 then 1 / 2 else 0) -
        (if (j : ℕ) = m + 1 ∧ (i : ℕ) = m + 2 then Real.sqrt 2 / 2 else 0) -
        (if (j : ℕ) = m + 2 ∧ (i : ℕ) = m + 1 then Real.sqrt 2 / 2 else 0) -
        (if (j : ℕ) = 1 ∧ (i : ℕ) = m + 3 then 1 / 2 else 0) -
        (if (j : ℕ) = m + 3 ∧ (i : ℕ) = 1 then 1 / 2 else 0) := by
  have hi := i.isLt
  have hj := j.isLt
  unfold affineTypeBForkMatrix
  simp only [Matrix.of_apply, Fin.ext_iff]
  split
  · simp (disch := omega) only [ite_eq_right]
    norm_num
  · split
    · rename_i h4
      rcases h4 with h | h
      all_goals
        simp (disch := omega) only [ite_eq_left, ite_eq_right]
        norm_num [Real.cos_pi_div_four]
    · split
      · rename_i h3
        rcases h3 with h | h | h | h
        all_goals
          simp (disch := omega) only [ite_eq_left, ite_eq_right]
          norm_num [Real.cos_pi_div_three]
      · simp (disch := omega) only [ite_eq_right]
        norm_num

/-- The null root of `B̃_(m+3)`. -/
private noncomputable def affineTypeBNull : Fin (m + 3 + 1) →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm fun i ↦
    if (i : ℕ) = 0 ∨ (i : ℕ) = m + 3 then 1 else if (i : ℕ) = m + 2 then Real.sqrt 2 else 2

private theorem affineTypeBNull_pos (i : Fin (m + 3 + 1)) : 0 < affineTypeBNull (m := m) i := by
  simp only [affineTypeBNull, Finsupp.coe_equivFunOnFinite_symm]
  split_ifs <;> positivity

private theorem finNatGet_affineTypeBNull (k : ℕ) :
    finNatGet (affineTypeBNull (m := m)) k =
      if k < m + 3 + 1 then
        (if k = 0 ∨ k = m + 3 then 1 else if k = m + 2 then Real.sqrt 2 else 2) else 0 := by
  unfold finNatGet
  split_ifs <;> simp_all [affineTypeBNull]

private theorem affineTypeBFork_bil_null (j : Fin (m + 3 + 1)) :
    (@bil _ (affineTypeBForkGroup (m + 3))) affineTypeBNull
      (@stdBasis _ (affineTypeBForkGroup (m + 3)) j) = 0 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [@bil_stdBasis_right_eq_sum _ (affineTypeBForkGroup (m + 3)) (Fin.fintype _)]
  change ∑ i : Fin (m + 3 + 1),
    affineTypeBNull i * -Real.cos (Real.pi / (affineTypeBForkMatrix (m + 3) i j : ℝ)) = 0
  simp only [affineTypeBFork_gram, mul_sub, Finset.sum_sub_distrib, sum_mul_ite_and_val_eq,
    sum_mul_ite_val_eq, finNatGet_affineTypeBNull]
  obtain ⟨j, hj⟩ := j
  simp only
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    all_goals
      rcases Nat.eq_zero_or_pos m with rfl | hm
      all_goals
        simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte, true_or, or_true]
        nlinarith
  · rcases Nat.lt_or_ge j (m + 1) with hjm | hjm
    · simp (disch := omega) only [ite_eq_left, ite_eq_right]
      nlinarith
    · obtain rfl | rfl | rfl : j = m + 1 ∨ j = m + 2 ∨ j = m + 3 := by omega
      all_goals
        simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte, or_true]
        nlinarith

private theorem affineTypeBFork_isIrreducible :
    @IsIrreducible _ (affineTypeBForkGroup (m + 3)) := by
  refine isIrreducibleMatrix_of_exists_lt (affineTypeBForkMatrix (m + 3)) fun i hi ↦ ?_
  obtain ⟨i, hi'⟩ := i
  have hi0 : i ≠ 0 := fun h ↦ hi (Fin.ext h)
  have key : ∀ j : Fin (m + 3 + 1), (j : ℕ) < i →
      (((j : ℕ) + 1 = i ∧ i ≤ m + 2) ∨ ((j : ℕ) = 1 ∧ i = m + 3)) →
        affineTypeBForkMatrix (m + 3) j ⟨i, hi'⟩ ≠ 2 := by
    intro j _ hj
    unfold affineTypeBForkMatrix
    simp only [Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  by_cases h1 : i ≤ m + 2
  · exact ⟨⟨i - 1, by omega⟩, Fin.lt_def.mpr (by simp only; omega),
      key _ (by simp only; omega) (Or.inl ⟨by simp only; omega, h1⟩)⟩
  · obtain rfl : i = m + 3 := by omega
    exact ⟨⟨1, by omega⟩, Fin.lt_def.mpr (by simp only; omega),
      key _ (by simp only; omega) (Or.inr ⟨rfl, rfl⟩)⟩

private theorem affineTypeBFork_isCrystallographic :
    @IsCrystallographic _ (affineTypeBForkGroup (m + 3)) := by
  intro i i' hii'
  change affineTypeBForkMatrix (m + 3) i i' = 0 ∨ affineTypeBForkMatrix (m + 3) i i' = 2 ∨
    affineTypeBForkMatrix (m + 3) i i' = 3 ∨ affineTypeBForkMatrix (m + 3) i i' = 4 ∨
    affineTypeBForkMatrix (m + 3) i i' = 6
  unfold affineTypeBForkMatrix
  simp only [Matrix.of_apply]
  split_ifs <;> simp_all

private theorem affineTypeBFork_isIrreducibleAffineWeyl :
    @IsIrreducibleAffineWeyl _ (affineTypeBForkGroup (m + 3)) :=
  @isIrreducibleAffineWeyl_of_null _ (affineTypeBForkGroup (m + 3))
    (Finite.of_fintype (Fin (m + 3 + 1))) affineTypeBFork_isIrreducible
    affineTypeBFork_isCrystallographic affineTypeBNull (fun i ↦ affineTypeBNull_pos i)
    affineTypeBFork_bil_null

private theorem affineTypeBFork_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ (affineTypeBForkGroup (m + 3)) :=
  @isIrreducibleAffineCoxeter_of_null _ (affineTypeBForkGroup (m + 3))
    (Finite.of_fintype (Fin (m + 3 + 1))) affineTypeBFork_isIrreducible affineTypeBNull
    (fun i ↦ affineTypeBNull_pos i) affineTypeBFork_bil_null

/-- Scaling the root `m + 2` at the far end of the edge labelled `4` by `√2` gives a generalized
Cartan matrix for the fork. -/
private theorem affineTypeBFork_hasGeneralizedCartanMatrix :
    @HasGeneralizedCartanMatrix _ (affineTypeBForkGroup (m + 3)) := by
  refine hasGeneralizedCartanMatrix_of_scale (cg := affineTypeBForkGroup (m + 3))
    (fun i : Fin (m + 3 + 1) ↦ if (i : ℕ) = m + 2 then Real.sqrt 2 else 1)
    (fun i : Fin (m + 3 + 1) ↦ by split_ifs <;> positivity) fun i i' hne ↦ ?_
  change Fin (m + 3 + 1) at i i'
  have hi := i.isLt
  have hi' := i'.isLt
  have hne' : (i : ℕ) ≠ i' := fun h ↦ hne (Fin.ext h)
  change affineTypeBForkMatrix (m + 3) i i' = 2 ∨
    ((affineTypeBForkMatrix (m + 3) i i' = 0 ∨ affineTypeBForkMatrix (m + 3) i i' = 3) ∧ _) ∨
    (affineTypeBForkMatrix (m + 3) i i' = 4 ∧ _) ∨ (affineTypeBForkMatrix (m + 3) i i' = 6 ∧ _)
  have hB : affineTypeBForkMatrix (m + 3) i i' =
      if ((i : ℕ) = m + 3 - 2 ∧ (i' : ℕ) = m + 3 - 1) ∨ ((i' : ℕ) = m + 3 - 2 ∧ (i : ℕ) = m + 3 - 1)
        then 4
      else if ((i : ℕ) + 1 = i' ∧ (i' : ℕ) ≤ m + 3 - 2) ∨ ((i' : ℕ) + 1 = i ∧ (i : ℕ) ≤ m + 3 - 2) ∨
        ((i : ℕ) = 1 ∧ (i' : ℕ) = m + 3) ∨ ((i' : ℕ) = 1 ∧ (i : ℕ) = m + 3) then 3 else 2 := by
    unfold affineTypeBForkMatrix
    simp only [Matrix.of_apply, ite_eq_right hne]
  rw [hB]
  by_cases h4 : ((i : ℕ) = m + 3 - 2 ∧ (i' : ℕ) = m + 3 - 1) ∨
      ((i' : ℕ) = m + 3 - 2 ∧ (i : ℕ) = m + 3 - 1)
  · rw [ite_eq_left h4]
    refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
    rcases h4 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl (by
        rw [ite_eq_left (show (i' : ℕ) = m + 2 by omega),
          ite_eq_right (show ¬ (i : ℕ) = m + 2 by omega), mul_one])
    · exact Or.inr (by
        rw [ite_eq_left (show (i : ℕ) = m + 2 by omega),
          ite_eq_right (show ¬ (i' : ℕ) = m + 2 by omega), mul_one])
  · rw [ite_eq_right h4]
    by_cases h3 : ((i : ℕ) + 1 = i' ∧ (i' : ℕ) ≤ m + 3 - 2) ∨
        ((i' : ℕ) + 1 = i ∧ (i : ℕ) ≤ m + 3 - 2) ∨ ((i : ℕ) = 1 ∧ (i' : ℕ) = m + 3) ∨
        ((i' : ℕ) = 1 ∧ (i : ℕ) = m + 3)
    · rw [ite_eq_left h3]
      refine Or.inr (Or.inl ⟨Or.inr rfl, ?_⟩)
      rw [ite_eq_right (show ¬ (i : ℕ) = m + 2 by omega),
        ite_eq_right (show ¬ (i' : ℕ) = m + 2 by omega)]
    · rw [ite_eq_right h3]
      exact Or.inl rfl

end Classification

/-- `B̃ₙ` (`n ≥ 2`) is an irreducible affine Weyl group: for `n ≥ 3` it is the fork, and
`B̃₂ = C̃₂`. -/
theorem affineTypeB_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducibleAffineWeyl _ (affineTypeBGroup n hn) := by
  have key : ∀ M : CoxeterMatrix (Fin (n + 1)),
      (n = 2 ∧ M = affineTypeCMatrix n) ∨ (3 ≤ n ∧ M = affineTypeBForkMatrix n) →
      @IsIrreducibleAffineWeyl M.Group ⟨Fin (n + 1), M, M.toCoxeterSystem⟩ := by
    rintro M (⟨rfl, rfl⟩ | ⟨h3, rfl⟩)
    · exact affineTypeC_isIrreducibleAffineWeyl 2 le_rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      exact affineTypeBFork_isIrreducibleAffineWeyl
  refine key _ ?_
  unfold affineTypeBMatrix
  split_ifs with h
  · exact Or.inl ⟨by omega, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

/-- `B̃ₙ` (`n ≥ 2`) is an irreducible affine Coxeter group: for `n ≥ 3` it is the fork, and
`B̃₂ = C̃₂`. -/
theorem affineTypeB_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducibleAffineCoxeter _ (affineTypeBGroup n hn) := by
  have key : ∀ M : CoxeterMatrix (Fin (n + 1)),
      (n = 2 ∧ M = affineTypeCMatrix n) ∨ (3 ≤ n ∧ M = affineTypeBForkMatrix n) →
      @IsIrreducibleAffineCoxeter M.Group ⟨Fin (n + 1), M, M.toCoxeterSystem⟩ := by
    rintro M (⟨rfl, rfl⟩ | ⟨h3, rfl⟩)
    · exact affineTypeC_isIrreducibleAffineCoxeter 2 le_rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      exact affineTypeBFork_isIrreducibleAffineCoxeter
  refine key _ ?_
  unfold affineTypeBMatrix
  split_ifs with h
  · exact Or.inl ⟨by omega, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

/-! ### Accidental low-rank affine identifications -/

section Accidentals

theorem affineTypeBMatrix_two : affineTypeBMatrix 2 = affineTypeCMatrix 2 := ite_eq_left le_rfl

/-- The Coxeter-system-level accidental identification `C̃₂ = B̃₂`. -/
theorem affineTypeC_two_identifies_affineTypeB_two :
    HEq (@CoxeterGroup.cs _ (affineTypeCGroup 2 (by omega)))
      (@CoxeterGroup.cs _ (affineTypeBGroup 2 (by omega))) := by
  change HEq (affineTypeCMatrix 2).toCoxeterSystem (affineTypeBMatrix 2).toCoxeterSystem
  rw [affineTypeBMatrix_two]

end Accidentals

/-! ### Special features -/

theorem affineTypeB_isIrreducible (n : ℕ) (hn : 2 ≤ n) :
    @IsIrreducible _ (affineTypeBGroup n hn) :=
  (affineTypeB_isIrreducibleAffineWeyl n hn).2

theorem affineTypeB_isCrystallographic (n : ℕ) (hn : 2 ≤ n) :
    @IsCrystallographic _ (affineTypeBGroup n hn) :=
  (affineTypeB_isIrreducibleAffineWeyl n hn).1.2.1

theorem affineTypeB_isAffineCoxeter (n : ℕ) (hn : 2 ≤ n) :
    @IsAffineCoxeter _ (affineTypeBGroup n hn) :=
  (affineTypeB_isIrreducibleAffineCoxeter n hn).1

theorem affineTypeB_isAffineCoxeterOrEmpty (n : ℕ) (hn : 2 ≤ n) :
    @IsAffineCoxeterOrEmpty _ (affineTypeBGroup n hn) :=
  Or.inr (affineTypeB_isAffineCoxeter n hn)

theorem affineTypeB_isPolyAffineWeyl (n : ℕ) (hn : 2 ≤ n) :
    @IsPolyAffineWeyl _ (affineTypeBGroup n hn) :=
  (affineTypeB_isIrreducibleAffineWeyl n hn).1

/-- `B̃ₙ` (`n ≥ 2`) has a generalized Cartan matrix: for `n ≥ 3` it is the fork, and `B̃₂ = C̃₂`. -/
theorem affineTypeB_hasGeneralizedCartanMatrix (n : ℕ) (hn : 2 ≤ n) :
    @HasGeneralizedCartanMatrix _ (affineTypeBGroup n hn) := by
  have key : ∀ M : CoxeterMatrix (Fin (n + 1)),
      (n = 2 ∧ M = affineTypeCMatrix n) ∨ (3 ≤ n ∧ M = affineTypeBForkMatrix n) →
      @HasGeneralizedCartanMatrix M.Group ⟨Fin (n + 1), M, M.toCoxeterSystem⟩ := by
    rintro M (⟨rfl, rfl⟩ | ⟨h3, rfl⟩)
    · exact affineTypeC_hasGeneralizedCartanMatrix 2 le_rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      exact affineTypeBFork_hasGeneralizedCartanMatrix
  refine key _ ?_
  unfold affineTypeBMatrix
  split_ifs with h
  · exact Or.inl ⟨by omega, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

end Coxeter
