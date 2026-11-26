module

public import Coxeter.FiniteOrAffine.TypeA
public import Coxeter.BilinearLatticeDynkins
public import Coxeter.SpecialFeatures

/-!
# The Coxeter group of type D

This file packages the finite Coxeter group of type `D`.

The local `typeDMatrix` normalizes the small ranks by using type `A` for `n ≤ 3`, and uses type `D`
from rank `4` onward.
-/

@[expose] public section

namespace Coxeter

/-- The Coxeter matrix of finite type `D` on `n` generators.

For `n ≤ 3` this is normalized to the classical accidental type `Aₙ`; from rank `4` onward it is
mathlib's `CoxeterMatrix.D n`. -/
noncomputable def typeDMatrix (n : ℕ) : CoxeterMatrix (Fin n) :=
  if n ≤ 3 then CoxeterMatrix.A n else CoxeterMatrix.D n

/-- Adjacency in the `D_(n+4)` diagram: the path `0 — ⋯ — n+2`, plus the fork edge `n+1 — n+3`. -/
def typeDAdj (n i j : ℕ) : Prop :=
  ((i + 1 = j ∨ j + 1 = i) ∧ i ≠ n + 3 ∧ j ≠ n + 3) ∨
    (i = n + 3 ∧ j = n + 1) ∨ (j = n + 3 ∧ i = n + 1)

instance (n i j : ℕ) : Decidable (typeDAdj n i j) := by unfold typeDAdj; infer_instance

/-- The entries of `typeDMatrix (n + 4)`. -/
theorem typeDMatrix_apply (n : ℕ) (i j : Fin (n + 4)) :
    typeDMatrix (n + 4) i j = if i = j then 1 else if typeDAdj n i j then 3 else 2 := by
  rw [typeDMatrix, ite_eq_right (by omega)]
  simp only [CoxeterMatrix.D, Matrix.of_apply, Fin.ext_iff, typeDAdj]
  split_ifs <;> omega

/-- The Coxeter group of finite type `D` on `n` generators, realized as the abstract group
presented by `typeDMatrix n`. -/
@[reducible] noncomputable def typeDGroup (n : ℕ) [NeZero n] :
    CoxeterGroup (typeDMatrix n).Group where
  B := Fin n
  M := typeDMatrix n
  cs := (typeDMatrix n).toCoxeterSystem

/-- Type `D`'s normalized matrix is crystallographic in every nonempty rank. -/
theorem typeD_isCrystallographic (n : ℕ) [NeZero n] :
    @IsCrystallographic _ (typeDGroup n) := by
  intro i i' hii'
  change (typeDMatrix n) i i' = 0 ∨ (typeDMatrix n) i i' = 2 ∨
    (typeDMatrix n) i i' = 3 ∨ (typeDMatrix n) i i' = 4 ∨
    (typeDMatrix n) i i' = 6
  by_cases h : n ≤ 3
  · unfold typeDMatrix
    simp only [ite_eq_left h]
    unfold CoxeterMatrix.A
    simp only [Matrix.of_apply, ite_eq_right hii']
    split_ifs <;> tauto
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [typeDMatrix_apply, ite_eq_right hii']
    split_ifs <;> tauto

/-- Two generators of `D_(n+4)` are joined in the Coxeter diagram exactly when `typeDAdj`. -/
private theorem coxeterGraphMatrix_typeD_adj (n : ℕ) (i j : Fin (n + 4)) :
    (coxeterGraphMatrix (typeDMatrix (n + 4))).Adj i j ↔ typeDAdj n i j := by
  rw [coxeterGraphMatrix, SimpleGraph.fromRel_adj, typeDMatrix_apply, typeDMatrix_apply]
  by_cases hij : i = j
  · subst hij
    simp only [ne_eq, not_true_eq_false, false_and, false_iff, typeDAdj]
    omega
  · simp only [ne_eq, hij, not_false_eq_true, true_and]
    have hsymm : typeDAdj n j i ↔ typeDAdj n i j := by unfold typeDAdj; omega
    split_ifs <;> simp_all

/-- `D_(n+4)` is irreducible: its diagram, a path with a fork at one end, is connected. -/
theorem typeD_isIrreducible (n : ℕ) : @IsIrreducible _ (typeDGroup (n + 4)) := by
  unfold IsIrreducible IsIrreducibleMatrix
  change (coxeterGraphMatrix (typeDMatrix (n + 4))).Connected
  set G := coxeterGraphMatrix (typeDMatrix (n + 4))
  have hpath : ∀ k (hk : k ≤ n + 2), G.Reachable 0 ⟨k, by omega⟩ := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
        refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ?_)
        rw [coxeterGraphMatrix_typeD_adj]
        change typeDAdj n k (k + 1)
        unfold typeDAdj
        omega
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun w ↦ ?_⟩
  by_cases hw : (w : ℕ) ≤ n + 2
  · exact hpath w hw
  · have hw' : w = ⟨n + 3, by omega⟩ := Fin.ext (by have := w.isLt; simp only; omega)
    rw [hw']
    refine (hpath (n + 1) (by omega)).trans (SimpleGraph.Adj.reachable ?_)
    rw [coxeterGraphMatrix_typeD_adj]
    change typeDAdj n (n + 1) (n + 3)
    unfold typeDAdj
    omega

/-! ### Positive definiteness of `bil` for type D

`sos_identity_fork` writes the (doubled) quadratic form of the fork as a sum of squares. -/

/-- The entries of `bil`'s Gram matrix for `D_(n+4)`, on `ℕ` indices. -/
private noncomputable def typeDEntry (n i j : ℕ) : ℝ :=
  if i = j then 1 else if typeDAdj n i j then -(1 / 2) else 0

/-- On the path part `0 — ⋯ — n + 2`, the type `D` entries are the tridiagonal ones. -/
private theorem typeDEntry_eq_pathEntry (n i j : ℕ) (hi : i < n + 3) (hj : j < n + 3) :
    typeDEntry n i j = pathEntry i j := by
  unfold typeDEntry pathEntry typeDAdj
  split_ifs <;> norm_num <;> omega

private theorem bil_typeD_entries (n : ℕ) (i j : Fin (n + 4)) :
    (@bil _ (typeDGroup (n + 4))) (@stdBasis _ (typeDGroup (n + 4)) i)
      (@stdBasis _ (typeDGroup (n + 4)) j) = typeDEntry n i j := by
  rw [@bil_eq _ (typeDGroup (n + 4))]
  change -Real.cos (Real.pi / ((typeDMatrix (n + 4)) i j : ℝ)) = typeDEntry n i j
  rw [typeDMatrix_apply]
  unfold typeDEntry
  by_cases hij : i = j
  · have hij' : (i : ℕ) = (j : ℕ) := by rw [hij]
    rw [ite_eq_left hij, ite_eq_left hij']
    norm_num
  · have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rw [ite_eq_right hij, ite_eq_right hij']
    split_ifs
    · rw [show ((3 : ℕ) : ℝ) = 3 by norm_num, Real.cos_pi_div_three]
    · rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, Real.cos_pi_div_two]
      norm_num

/-- Extends `x : Fin (n + 4) →₀ ℝ` to a function on all of `ℕ`, vanishing past `n + 3`. -/
private noncomputable def typeDExtend (n : ℕ) (x : Fin (n + 4) →₀ ℝ) : ℕ → ℝ :=
  fun k => if h : k < n + 4 then x ⟨k, h⟩ else 0

private theorem typeDExtend_apply_fin (n : ℕ) (x : Fin (n + 4) →₀ ℝ) (i : Fin (n + 4)) :
    typeDExtend n x (i : ℕ) = x i := by
  unfold typeDExtend
  rw [dite_eq_left i.isLt]

/-- The double sum against `typeDEntry` is the fork's quadratic form. -/
private theorem typeDEntry_sum_range_double (n : ℕ) (y : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 4), ∑ j ∈ Finset.range (n + 4), y i * y j * typeDEntry n i j)
      = ∑ i ∈ Finset.range (n + 3), (y i) ^ 2 - ∑ i ∈ Finset.range (n + 2), y i * y (i + 1)
        + y (n + 3) ^ 2 - y (n + 1) * y (n + 3) := by
  have hpath : (∑ i ∈ Finset.range (n + 3), ∑ j ∈ Finset.range (n + 3),
      y i * y j * typeDEntry n i j)
      = ∑ i ∈ Finset.range (n + 3), (y i) ^ 2 - ∑ i ∈ Finset.range (n + 2), y i * y (i + 1) := by
    rw [← pathEntry_sum_range_double y (n + 2)]
    refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
    rw [typeDEntry_eq_pathEntry n i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)]
  have hcol : ∑ i ∈ Finset.range (n + 3), y i * y (n + 3) * typeDEntry n i (n + 3)
      = -(1 / 2) * y (n + 1) * y (n + 3) := by
    rw [Finset.sum_eq_single (n + 1)]
    · unfold typeDEntry typeDAdj
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      ring
    · intro i hi hne
      unfold typeDEntry typeDAdj
      have := Finset.mem_range.1 hi
      rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have hrow : ∑ j ∈ Finset.range (n + 3), y (n + 3) * y j * typeDEntry n (n + 3) j
      = -(1 / 2) * y (n + 1) * y (n + 3) := by
    rw [Finset.sum_eq_single (n + 1)]
    · unfold typeDEntry typeDAdj
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      ring
    · intro j hj hne
      unfold typeDEntry typeDAdj
      have := Finset.mem_range.1 hj
      rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have hdiag : typeDEntry n (n + 3) (n + 3) = 1 := by unfold typeDEntry; rw [ite_eq_left rfl]
  change ∑ i ∈ Finset.range (n + 3 + 1), ∑ j ∈ Finset.range (n + 3 + 1),
    y i * y j * typeDEntry n i j = _
  simp only [Finset.sum_range_succ (n := n + 3), Finset.sum_add_distrib]
  rw [hpath, hcol, hrow, hdiag]
  ring

/-- `bil x x` for `D_(n+4)`, as the fork's quadratic form on the `ℕ`-extension of `x`. -/
private theorem bil_typeD_apply (n : ℕ) (x : Fin (n + 4) →₀ ℝ) :
    (@bil _ (typeDGroup (n + 4))) x x
      = ∑ i ∈ Finset.range (n + 3), (typeDExtend n x i) ^ 2
        - ∑ i ∈ Finset.range (n + 2), typeDExtend n x i * typeDExtend n x (i + 1)
        + typeDExtend n x (n + 3) ^ 2 - typeDExtend n x (n + 1) * typeDExtend n x (n + 3) := by
  rw [← typeDEntry_sum_range_double]
  have hrepr : (@stdBasis _ (typeDGroup (n + 4))).repr x = x := rfl
  have key : (@bil _ (typeDGroup (n + 4))) x x
      = ∑ i : Fin (n + 4), ∑ j : Fin (n + 4),
          x i * x j * (@bil _ (typeDGroup (n + 4)))
            (@stdBasis _ (typeDGroup (n + 4)) i) (@stdBasis _ (typeDGroup (n + 4)) j) := by
    rw [← LinearMap.BilinForm.sum_repr_mul_repr_mul
      (B := @bil _ (typeDGroup (n + 4))) (@stdBasis _ (typeDGroup (n + 4))) x x, hrepr,
      Finsupp.sum_fintype x _ (fun i => by simp)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finsupp.sum_fintype x _ (fun j => by simp)]
    simp only [smul_eq_mul, ← mul_assoc]
  rw [key]
  have hentry : ∀ i j : Fin (n + 4),
      x i * x j * (@bil _ (typeDGroup (n + 4)))
        (@stdBasis _ (typeDGroup (n + 4)) i) (@stdBasis _ (typeDGroup (n + 4)) j)
      = typeDExtend n x (i : ℕ) * typeDExtend n x (j : ℕ) * typeDEntry n (i : ℕ) (j : ℕ) := by
    intro i j
    rw [bil_typeD_entries, typeDExtend_apply_fin, typeDExtend_apply_fin]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 4)))) =>
    Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 4)))) => hentry i j))]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin (n + 4),
    typeDExtend n x i * typeDExtend n x j * typeDEntry n i j) (n + 4)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Fin.sum_univ_eq_sum_range (fun j => typeDExtend n x i * typeDExtend n x j *
    typeDEntry n i j) (n + 4)

/-- Type `D`'s `bil` is positive semidefinite, since (doubled) it is a sum of squares by
`sos_identity_fork`. -/
private theorem bil_typeD_isNonneg (n : ℕ) : (@bil _ (typeDGroup (n + 4))).IsNonneg := by
  rw [LinearMap.BilinForm.isNonneg_def]
  intro x
  rw [bil_typeD_apply]
  set y := typeDExtend n x
  have h := sos_identity_fork n y
  have hC : 0 ≤ ∑ i ∈ Finset.range (n + 1), (y i - y (i + 1)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith [h, sq_nonneg (y 0), sq_nonneg (y (n + 1) - y (n + 2) - y (n + 3)),
    sq_nonneg (y (n + 2) - y (n + 3)), hC]

/-- Type `D`'s `bil` is nondegenerate: if `bil x x = 0`, every square in `sos_identity_fork`
vanishes, forcing each coordinate of `x` to be `0`. -/
private theorem bil_typeD_nondegenerate (n : ℕ) :
    (@bil _ (typeDGroup (n + 4))).Nondegenerate := by
  unfold LinearMap.BilinForm.Nondegenerate
  rw [LinearMap.BilinForm.nondegenerate_iff'
    (hs := (bil_typeD_isNonneg n).nonneg)
    (hB := LinearMap.BilinForm.isSymm_iff.mp (@bil_isSymm _ (typeDGroup (n + 4))))]
  intro x hx
  rcases ((bil_typeD_isNonneg n).nonneg x).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have hzero : (@bil _ (typeDGroup (n + 4))) x x = 0 := h.symm
    rw [bil_typeD_apply] at hzero
    set y := typeDExtend n x with hy_def
    have hsos := sos_identity_fork n y
    have hC : 0 ≤ ∑ i ∈ Finset.range (n + 1), (y i - y (i + 1)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hP := sq_nonneg (y (n + 1) - y (n + 2) - y (n + 3))
    have hQ := sq_nonneg (y (n + 2) - y (n + 3))
    have h0 : y 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (by nlinarith [sq_nonneg (y 0)])
    have hCsum : ∑ i ∈ Finset.range (n + 1), (y i - y (i + 1)) ^ 2 = 0 := by
      nlinarith [sq_nonneg (y 0)]
    have hP0 : y (n + 1) - y (n + 2) - y (n + 3) = 0 := pow_eq_zero_iff (n := 2) (by norm_num)
      |>.mp (by nlinarith [sq_nonneg (y 0)])
    have hQ0 : y (n + 2) - y (n + 3) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (by nlinarith [sq_nonneg (y 0)])
    have hstep : ∀ i ∈ Finset.range (n + 1), y i = y (i + 1) := by
      intro i hi
      have hzero_term : (y i - y (i + 1)) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hCsum i hi
      have := sq_eq_zero_iff.mp hzero_term
      linarith
    have hpath : ∀ i ≤ n + 1, y i = 0 := by
      intro i hi
      induction i with
      | zero => exact h0
      | succ k ih =>
          rw [← hstep k (Finset.mem_range.mpr (by omega))]
          exact ih (by omega)
    have hall : ∀ i ≤ n + 3, y i = 0 := by
      intro i hi
      have hn1 := hpath (n + 1) le_rfl
      rcases (show i ≤ n + 1 ∨ i = n + 2 ∨ i = n + 3 by omega) with h | h | h
      · exact hpath i h
      · subst h; linarith
      · subst h; linarith
    apply Finsupp.ext
    intro i
    have hi0 : y (i : Fin (n + 4)).val = 0 := hall _ (by omega)
    rw [hy_def, typeDExtend_apply_fin] at hi0
    simpa using hi0

/-- `D_(n+4)` is of finite type: `bil` is positive semidefinite and nondegenerate. -/
theorem typeD_isFiniteCoxeter (n : ℕ) : @IsFiniteCoxeter _ (typeDGroup (n + 4)) :=
  Or.inr ⟨⟨@bil_isSymm _ (typeDGroup (n + 4)), bil_typeD_isNonneg n⟩,
    bil_typeD_nondegenerate n⟩

theorem typeD_isPolyFiniteWeyl (n : ℕ) : @IsPolyFiniteWeyl _ (typeDGroup (n + 4)) :=
  ⟨typeD_isFiniteCoxeter n, typeD_isCrystallographic (n + 4)⟩

theorem typeD_isIrreducibleFiniteWeyl (n : ℕ) :
    @IsIrreducibleFiniteWeyl _ (typeDGroup (n + 4)) :=
  ⟨typeD_isPolyFiniteWeyl n, typeD_isIrreducible n⟩

/-! ### Small-rank accidental identifications -/

section Accidentals

private theorem typeDMatrix_one_eq_A_one : typeDMatrix 1 = CoxeterMatrix.A 1 := by
  unfold typeDMatrix
  simp

private theorem typeDMatrix_two_eq_A_two : typeDMatrix 2 = CoxeterMatrix.A 2 := by
  unfold typeDMatrix
  simp

private theorem typeDMatrix_three_eq_A_three : typeDMatrix 3 = CoxeterMatrix.A 3 := by
  unfold typeDMatrix
  simp

/-- The Coxeter-system-level accidental identification `D₁ = A₁`.

The entrywise matrix equality used to prove this is private. -/
theorem typeD_one_identifies_typeA_one :
    HEq (@CoxeterGroup.cs _ (typeDGroup 1)) (@CoxeterGroup.cs _ (typeAGroup 1)) := by
  change HEq (typeDMatrix 1).toCoxeterSystem (CoxeterMatrix.A 1).toCoxeterSystem
  rw [← typeDMatrix_one_eq_A_one]

/-- The Coxeter-system-level accidental identification `D₂ = A₂`.

The entrywise matrix equality used to prove this is private. -/
theorem typeD_two_identifies_typeA_two :
    HEq (@CoxeterGroup.cs _ (typeDGroup 2)) (@CoxeterGroup.cs _ (typeAGroup 2)) := by
  change HEq (typeDMatrix 2).toCoxeterSystem (CoxeterMatrix.A 2).toCoxeterSystem
  rw [← typeDMatrix_two_eq_A_two]

/-- The Coxeter-system-level accidental identification `D₃ = A₃`.

The entrywise matrix equality used to prove this is private. -/
theorem typeD_three_identifies_typeA_three :
    HEq (@CoxeterGroup.cs _ (typeDGroup 3)) (@CoxeterGroup.cs _ (typeAGroup 3)) := by
  change HEq (typeDMatrix 3).toCoxeterSystem (CoxeterMatrix.A 3).toCoxeterSystem
  rw [← typeDMatrix_three_eq_A_three]

/-! Special features of `D1`, transported from `A1`. -/

theorem typeD_one_isIrreducible : @IsIrreducible _ (typeDGroup 1) :=
  coxeterGroup_transport typeDMatrix_one_eq_A_one.symm (fun cg ↦ @IsIrreducible _ cg)
    (typeA_isIrreducible 0)

theorem typeD_one_isFiniteCoxeter : @IsFiniteCoxeter _ (typeDGroup 1) :=
  coxeterGroup_transport typeDMatrix_one_eq_A_one.symm (fun cg ↦ @IsFiniteCoxeter _ cg)
    (typeA_isFiniteCoxeter 0)

theorem typeD_one_isPolyFiniteWeyl : @IsPolyFiniteWeyl _ (typeDGroup 1) :=
  coxeterGroup_transport typeDMatrix_one_eq_A_one.symm (fun cg ↦ @IsPolyFiniteWeyl _ cg)
    (typeA_isPolyFiniteWeyl 0)

theorem typeD_one_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ (typeDGroup 1) :=
  coxeterGroup_transport typeDMatrix_one_eq_A_one.symm (fun cg ↦ @IsIrreducibleFiniteWeyl _ cg)
    (typeA_isIrreducibleFiniteWeyl 0)

/-! Special features of `D2`, transported from `A2`. -/

theorem typeD_two_isIrreducible : @IsIrreducible _ (typeDGroup 2) :=
  coxeterGroup_transport typeDMatrix_two_eq_A_two.symm (fun cg ↦ @IsIrreducible _ cg)
    (typeA_isIrreducible 1)

theorem typeD_two_isFiniteCoxeter : @IsFiniteCoxeter _ (typeDGroup 2) :=
  coxeterGroup_transport typeDMatrix_two_eq_A_two.symm (fun cg ↦ @IsFiniteCoxeter _ cg)
    (typeA_isFiniteCoxeter 1)

theorem typeD_two_isPolyFiniteWeyl : @IsPolyFiniteWeyl _ (typeDGroup 2) :=
  coxeterGroup_transport typeDMatrix_two_eq_A_two.symm (fun cg ↦ @IsPolyFiniteWeyl _ cg)
    (typeA_isPolyFiniteWeyl 1)

theorem typeD_two_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ (typeDGroup 2) :=
  coxeterGroup_transport typeDMatrix_two_eq_A_two.symm (fun cg ↦ @IsIrreducibleFiniteWeyl _ cg)
    (typeA_isIrreducibleFiniteWeyl 1)

/-! Special features of `D3`, transported from `A3`. -/

theorem typeD_three_isIrreducible : @IsIrreducible _ (typeDGroup 3) :=
  coxeterGroup_transport typeDMatrix_three_eq_A_three.symm (fun cg ↦ @IsIrreducible _ cg)
    (typeA_isIrreducible 2)

theorem typeD_three_isFiniteCoxeter : @IsFiniteCoxeter _ (typeDGroup 3) :=
  coxeterGroup_transport typeDMatrix_three_eq_A_three.symm (fun cg ↦ @IsFiniteCoxeter _ cg)
    (typeA_isFiniteCoxeter 2)

theorem typeD_three_isPolyFiniteWeyl : @IsPolyFiniteWeyl _ (typeDGroup 3) :=
  coxeterGroup_transport typeDMatrix_three_eq_A_three.symm (fun cg ↦ @IsPolyFiniteWeyl _ cg)
    (typeA_isPolyFiniteWeyl 2)

theorem typeD_three_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ (typeDGroup 3) :=
  coxeterGroup_transport typeDMatrix_three_eq_A_three.symm (fun cg ↦ @IsIrreducibleFiniteWeyl _ cg)
    (typeA_isIrreducibleFiniteWeyl 2)

end Accidentals


/-! ### Euler lattice -/

section EulerLattice

/-- The Euler lattice of type `D_(n+4)` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev typeDBilinearLattice (n : ℕ) : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice (typeDMatrix (n + 4))

theorem typeD_isSimplyLaced (n : ℕ) : BilinearLattice.IsSimplyLaced (typeDMatrix (n + 4)) := by
  intro i j hij
  rw [typeDMatrix_apply, ite_eq_right hij]
  split_ifs <;> simp

/-- The Euler matrix of `D_(n+4)` on `ℕ` indices: `1` on the diagonal and `-1` on each edge
`i — j` with `i < j` (the path edges `i — i + 1` and the fork edge `n + 1 — n + 3`). -/
private def typeDEuler (n i j : ℕ) : ℤ :=
  (if j = i then 1 else 0) - (if j = i + 1 ∧ j ≠ n + 3 then 1 else 0) -
    (if j = n + 3 ∧ i = n + 1 then 1 else 0)

private theorem eulerMatrix_typeD_apply (n : ℕ) (i j : Fin (n + 4)) :
    BilinearLattice.eulerMatrix (typeDMatrix (n + 4)) i j = typeDEuler n i j := by
  unfold BilinearLattice.eulerMatrix
  simp only [Matrix.of_apply, typeDMatrix_apply, Fin.lt_def, Fin.ext_iff, typeDEuler, typeDAdj]
  split_ifs <;> omega

/-- A sum over `range N` of a function supported at the single point `k`. -/
private theorem sum_range_eq_single (N k : ℕ) (f : ℕ → ℤ) (hf : ∀ j, j ≠ k → f j = 0) :
    ∑ j ∈ Finset.range N, f j = if k < N then f k else 0 := by
  split_ifs with hk
  · exact Finset.sum_eq_single k (fun j _ hj ↦ hf j hj)
      (fun h ↦ absurd (Finset.mem_range.2 hk) h)
  · exact Finset.sum_eq_zero fun j hj ↦ hf j (by have := Finset.mem_range.1 hj; omega)

/-- Row sums of the Euler matrix of `D_(n+4)`. -/
private theorem typeDEuler_row_sum (n i : ℕ) :
    ∑ j ∈ Finset.range (n + 4), typeDEuler n i j =
      (if i < n + 4 then 1 else 0) - (if i + 1 < n + 4 ∧ i + 1 ≠ n + 3 then 1 else 0) -
        (if n + 3 < n + 4 ∧ i = n + 1 then 1 else 0) := by
  simp only [typeDEuler, Finset.sum_sub_distrib]
  rw [sum_range_eq_single (n + 4) i (fun j ↦ if j = i then 1 else 0)
      (fun j hj ↦ ite_eq_right hj),
    sum_range_eq_single (n + 4) (i + 1) (fun j ↦ if j = i + 1 ∧ j ≠ n + 3 then 1 else 0)
      (fun j hj ↦ ite_eq_right (by omega)),
    sum_range_eq_single (n + 4) (n + 3) (fun j ↦ if j = n + 3 ∧ i = n + 1 then 1 else 0)
      (fun j hj ↦ ite_eq_right (by omega))]
  split_ifs <;> omega

/-- Column sums of the Euler matrix of `D_(n+4)`. -/
private theorem typeDEuler_col_sum (n i : ℕ) (hi : i < n + 4) :
    ∑ j ∈ Finset.range (n + 4), typeDEuler n j i = if i = 0 then 1 else 0 := by
  simp only [typeDEuler, Finset.sum_sub_distrib]
  rw [sum_range_eq_single (n + 4) i (fun j ↦ if i = j then 1 else 0)
      (fun j hj ↦ ite_eq_right (Ne.symm hj)),
    sum_range_eq_single (n + 4) (i - 1) (fun j ↦ if i = j + 1 ∧ i ≠ n + 3 then 1 else 0)
      (fun j hj ↦ ite_eq_right (by omega)),
    sum_range_eq_single (n + 4) (n + 1) (fun j ↦ if i = n + 3 ∧ j = n + 1 then 1 else 0)
      (fun j hj ↦ ite_eq_right (by omega))]
  split_ifs <;> omega

/-- `S e_k = e_(k+1)` along the path, for `k ≤ n`. -/
private theorem typeD_S_single_succ (n k : ℕ) (hk : k ≤ n) :
    (typeDBilinearLattice n).S (Pi.single ⟨k, by omega⟩ 1) = Pi.single ⟨k + 1, by omega⟩ 1 := by
  unfold typeDBilinearLattice BilinearLattice.eulerLattice
  rw [BilinearLattice.ofUnimodular_S_eq_iff]
  ext i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply, Pi.neg_apply,
    eulerMatrix_typeD_apply, typeDEuler]
  split_ifs <;> omega

/-- `S` sends the branch vertex `e_(n+1)` to the all-ones vector. -/
private theorem typeD_S_single_branch (n : ℕ) :
    (typeDBilinearLattice n).S (Pi.single ⟨n + 1, by omega⟩ 1) = fun _ ↦ 1 := by
  unfold typeDBilinearLattice BilinearLattice.eulerLattice
  rw [BilinearLattice.ofUnimodular_S_eq_iff, Matrix.mulVec_single_one]
  ext i
  simp only [Matrix.mulVec, dotProduct, mul_one, Pi.neg_apply, Matrix.col_apply,
    Matrix.transpose_apply, eulerMatrix_typeD_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ typeDEuler n i j), typeDEuler_row_sum]
  have := i.isLt
  unfold typeDEuler
  split_ifs <;> omega

/-- `S` sends the leaf `e_(n+2)` to `e_(n+3) - (1, …, 1)`. -/
private theorem typeD_S_single_leaf₁ (n : ℕ) :
    (typeDBilinearLattice n).S (Pi.single ⟨n + 2, by omega⟩ 1) =
      Pi.single ⟨n + 3, by omega⟩ 1 - fun _ ↦ 1 := by
  unfold typeDBilinearLattice BilinearLattice.eulerLattice
  rw [BilinearLattice.ofUnimodular_S_eq_iff, Matrix.mulVec_single_one]
  erw [Matrix.mulVec_sub, Matrix.mulVec_single_one]
  ext i
  simp only [Matrix.mulVec, dotProduct, mul_one, Pi.neg_apply, Pi.sub_apply, Matrix.col_apply,
    Matrix.transpose_apply, eulerMatrix_typeD_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ typeDEuler n i j), typeDEuler_row_sum]
  have := i.isLt
  unfold typeDEuler
  split_ifs <;> omega

/-- `S` sends the leaf `e_(n+3)` to `e_(n+2) - (1, …, 1)`. -/
private theorem typeD_S_single_leaf₂ (n : ℕ) :
    (typeDBilinearLattice n).S (Pi.single ⟨n + 3, by omega⟩ 1) =
      Pi.single ⟨n + 2, by omega⟩ 1 - fun _ ↦ 1 := by
  unfold typeDBilinearLattice BilinearLattice.eulerLattice
  rw [BilinearLattice.ofUnimodular_S_eq_iff, Matrix.mulVec_single_one]
  erw [Matrix.mulVec_sub, Matrix.mulVec_single_one]
  ext i
  simp only [Matrix.mulVec, dotProduct, mul_one, Pi.neg_apply, Pi.sub_apply, Matrix.col_apply,
    Matrix.transpose_apply, eulerMatrix_typeD_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ typeDEuler n i j), typeDEuler_row_sum]
  have := i.isLt
  unfold typeDEuler
  split_ifs <;> omega

/-- `S` sends the all-ones vector to `-e_0`. -/
private theorem typeD_S_ones (n : ℕ) :
    (typeDBilinearLattice n).S (fun _ ↦ 1) = -Pi.single 0 1 := by
  unfold typeDBilinearLattice BilinearLattice.eulerLattice
  rw [BilinearLattice.ofUnimodular_S_eq_iff, Matrix.mulVec_neg, Matrix.mulVec_single_one]
  ext i
  simp only [Matrix.mulVec, dotProduct, mul_one, Pi.neg_apply, Matrix.col_apply,
    Matrix.transpose_apply, eulerMatrix_typeD_apply, neg_inj]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ typeDEuler n j i), typeDEuler_col_sum n i i.isLt]
  have h0 : ((0 : Fin (n + 4)) : ℕ) = 0 := rfl
  unfold typeDEuler
  simp only [h0]
  split_ifs <;> tauto

/-- The Coxeter number of `D_(n+4)` is `2 (n + 4) - 2 = 2 n + 6`. -/
theorem typeDBilinearLattice_S_pow (n : ℕ) :
    ((typeDBilinearLattice n).S : Module.End ℤ (typeDBilinearLattice n)) ^ (2 * n + 6) = 1 := by
  set S := ((typeDBilinearLattice n).S : Module.End ℤ (typeDBilinearLattice n))
  -- Basis vectors and the all-ones vector, as elements of the lattice.
  let e : Fin (n + 4) → typeDBilinearLattice n := fun j ↦ (Pi.single j 1 : Fin (n + 4) → ℤ)
  let ones : typeDBilinearLattice n := (fun _ ↦ 1 : Fin (n + 4) → ℤ)
  have hsucc : ∀ k (hk : k ≤ n), S (e ⟨k, by omega⟩) = e ⟨k + 1, by omega⟩ :=
    fun k hk ↦ typeD_S_single_succ n k hk
  have hbranch : S (e ⟨n + 1, by omega⟩) = ones := typeD_S_single_branch n
  have hleaf₁ : S (e ⟨n + 2, by omega⟩) = e ⟨n + 3, by omega⟩ - ones := typeD_S_single_leaf₁ n
  have hleaf₂ : S (e ⟨n + 3, by omega⟩) = e ⟨n + 2, by omega⟩ - ones := typeD_S_single_leaf₂ n
  have hones : S ones = -e 0 := typeD_S_ones n
  -- `e_0` generates the path and `𝟙`: `S ^ k e_0 = e_k` and `S ^ (n + 2) e_0 = 𝟙`.
  have hcyc : ∀ k (hk : k ≤ n + 1), (S ^ k) (e 0) = e ⟨k, by omega⟩ := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [pow_succ', mul_apply_eq_comp, ih (by omega)]
        exact hsucc k (by omega)
  have hone : (S ^ (n + 2)) (e 0) = ones := by
    rw [pow_succ', mul_apply_eq_comp, hcyc (n + 1) le_rfl]
    exact hbranch
  -- `T = S ^ (n + 3)` negates `e_0`, hence every `S ^ k e_0`; so `U = T ^ 2` fixes them.
  have hT0 : (S ^ (n + 3)) (e 0) = -e 0 := by
    rw [pow_succ', mul_apply_eq_comp, hone]
    exact hones
  have hTpow : ∀ k, (S ^ (n + 3)) ((S ^ k) (e 0)) = -(S ^ k) (e 0) := by
    intro k
    rw [← mul_apply_eq_comp, ← pow_add, add_comm, pow_add, mul_apply_eq_comp, hT0, map_neg]
  have hTT : ∀ v, (S ^ (n + 3)) v = -v → (S ^ (2 * n + 6)) v = v := by
    intro v h
    rw [show 2 * n + 6 = (n + 3) + (n + 3) by ring, pow_add, mul_apply_eq_comp, h, map_neg, h,
      neg_neg]
  have hUk : ∀ k (hk : k ≤ n + 1), (S ^ (2 * n + 6)) (e ⟨k, by omega⟩) = e ⟨k, by omega⟩ := by
    intro k hk
    rw [← hcyc k hk]
    exact hTT _ (hTpow k)
  have hU1 : (S ^ (2 * n + 6)) ones = ones := by
    rw [← hone]
    exact hTT _ (hTpow (n + 2))
  -- `S` negates the difference of the two leaves, so `U` fixes it.
  set ea := e ⟨n + 2, by omega⟩
  set eb := e ⟨n + 3, by omega⟩
  have hd : S (ea - eb) = -(ea - eb) := by
    rw [map_sub, hleaf₁, hleaf₂]
    abel
  have hd2 : ∀ m, (S ^ (2 * m)) (ea - eb) = ea - eb := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, mul_apply_eq_comp, hd,
          map_neg, pow_succ, mul_apply_eq_comp, hd, map_neg, neg_neg, ih]
  have hdU : (S ^ (2 * n + 6)) (ea - eb) = ea - eb := by
    rw [show 2 * n + 6 = 2 * (n + 3) by ring]
    exact hd2 _
  set U := S ^ (2 * n + 6)
  -- `U` fixes `𝟙 = ∑ e_j` and every `e_j` off the leaves, hence `ea + eb`; with `ea - eb` this
  -- gives `2 • (U ea - ea) = 0`.
  have hsum : (U ea - ea) + (U eb - eb) = 0 := by
    have hs : ∑ j : Fin (n + 4), (U (e j) - e j) = 0 := by
      have h1 : ∑ j : Fin (n + 4), e j = ones := Finset.univ_sum_single (fun _ ↦ (1 : ℤ))
      rw [Finset.sum_sub_distrib, ← map_sum, h1, hU1, sub_self]
    rw [← hs, Finset.sum_eq_add ⟨n + 2, by omega⟩ ⟨n + 3, by omega⟩
      (by simp [Fin.ext_iff]) (fun c _ hc ↦ ?_) (by simp) (by simp)]
    have hc' : (c : ℕ) ≤ n + 1 := by
      have := c.isLt
      simp only [ne_eq, Fin.ext_iff] at hc
      omega
    rw [hUk c hc', sub_self]
  have hdiff : (U ea - ea) - (U eb - eb) = 0 := by
    rw [sub_sub_sub_comm, ← map_sub, hdU, sub_self]
  have hhalf : ∀ x y : typeDBilinearLattice n, x + y = 0 → x - y = 0 → x = 0 := by
    intro x y h1 h2
    funext i
    have h1i : x i + y i = 0 := congrFun h1 i
    have h2i : x i - y i = 0 := congrFun h2 i
    change x i = 0
    omega
  have hA : U ea = ea := sub_eq_zero.1 (hhalf _ _ hsum hdiff)
  have hB : U eb = eb := sub_eq_zero.1 (hhalf _ _ (by rw [add_comm]; exact hsum)
    (by rw [← neg_sub, hdiff, neg_zero]))
  refine (Pi.basisFun ℤ (Fin (n + 4))).ext fun j ↦ ?_
  rw [Pi.basisFun_apply]
  change U (e j) = e j
  by_cases hj : (j : ℕ) ≤ n + 1
  · exact hUk j hj
  · rcases (show (j : ℕ) = n + 2 ∨ (j : ℕ) = n + 3 by omega) with h | h
    · rw [show j = ⟨n + 2, by omega⟩ from Fin.ext h]
      exact hA
    · rw [show j = ⟨n + 3, by omega⟩ from Fin.ext h]
      exact hB

noncomputable abbrev typeDBilinearLatticeWithMonoidQuasiUnipotent (n : ℕ) :
    BilinearLattice.BilinearLatticeWithMonoidQuasiUnipotent.{0} :=
  BilinearLattice.eulerLatticeWithMonoidQuasiUnipotent
    (M := typeDMatrix (n + 4))
    (hS := Module.End.isQuasiUnipotentOfIndex_of_pow_eq_one (by omega)
      (typeDBilinearLattice_S_pow n) two_pos)

end EulerLattice

/-! ### Special features -/

theorem typeD_hasGeneralizedCartanMatrix (n : ℕ) [NeZero n] :
    @HasGeneralizedCartanMatrix _ (typeDGroup n) :=
  hasGeneralizedCartanMatrix_of_entries fun i i' hne ↦ Or.inr (by
    change Fin n at i i'
    change typeDMatrix n i i' = 2 ∨ typeDMatrix n i i' = 3
    by_cases h : n ≤ 3
    · rw [typeDMatrix, ite_eq_left h]
      exact typeA_isSimplyLaced n i i' hne
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      exact typeD_isSimplyLaced m i i' hne)

/-- `D₁ = A₁` has a single generator, so it is vacuously right-angled. -/
theorem typeD_one_isRightAngled : @IsRightAngled _ (typeDGroup 1) :=
  fun i i' hne ↦ absurd (Subsingleton.elim (α := Fin 1) i i') hne

end Coxeter
