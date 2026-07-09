module

public import Coxeter.FiniteOrAffine.TridiagonalForm
public import Coxeter.FiniteOrAffine.TypeA
public import Coxeter.SpecialFeatures

/-!
# The Coxeter groups of finite type B/C

Finite types `Bₙ` and `Cₙ` have the same Coxeter system. This file packages that shared Coxeter
system as `typeBCGroup`.

The classification proofs are intentionally left as `proof_wanted` stubs.

For mathlib's current uniform matrix definition, the first nonempty rank satisfies `BC₁ = A₁`.
-/

@[expose] public section

namespace Coxeter

/-- The shared finite Coxeter group of types `B` and `C` on `n` generators, realized as the
abstract group presented by `CoxeterMatrix.B n`. -/
@[reducible] noncomputable def typeBCGroup (n : ℕ) [NeZero n] :
    CoxeterGroup (CoxeterMatrix.B n).Group where
  B := Fin n
  M := CoxeterMatrix.B n
  cs := (CoxeterMatrix.B n).toCoxeterSystem

/-- Type `BC`'s off-diagonal entries are always `2`, `3`, or `4`, hence crystallographic. -/
theorem typeBC_isCrystallographic (n : ℕ) [NeZero n] :
    @IsCrystallographic _ (typeBCGroup n) := by
  intro i i' hii'
  change (CoxeterMatrix.B n) i i' = 0 ∨ (CoxeterMatrix.B n) i i' = 2 ∨
    (CoxeterMatrix.B n) i i' = 3 ∨ (CoxeterMatrix.B n) i i' = 4 ∨
    (CoxeterMatrix.B n) i i' = 6
  unfold CoxeterMatrix.B
  simp only [Matrix.of_apply, if_neg hii']
  split_ifs <;> tauto

private theorem coxeterGraphMatrix_typeBC_eq_pathGraph (n : ℕ) :
    coxeterGraphMatrix (CoxeterMatrix.B n) = SimpleGraph.pathGraph n := by
  ext i j
  rw [coxeterGraphMatrix, SimpleGraph.fromRel_adj, SimpleGraph.pathGraph_adj]
  unfold CoxeterMatrix.B
  simp only [Matrix.of_apply, ne_eq]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h)]
    have key : ∀ p q : Fin n, p ≠ q →
        (¬(if (p : ℕ) = n - 1 ∧ (q : ℕ) = n - 2 ∨ (q : ℕ) = n - 1 ∧ (p : ℕ) = n - 2 then (4 : ℕ)
            else if (q : ℕ) + 1 = p ∨ (p : ℕ) + 1 = q then 3 else 2) = 2 ↔
          ((q : ℕ) + 1 = p ∨ (p : ℕ) + 1 = q)) := by
      intro p q hpq
      have hp := p.isLt
      have hq := q.isLt
      have hpq' : (p : ℕ) ≠ (q : ℕ) := fun he => hpq (Fin.val_injective he)
      have hspec : ((p : ℕ) = n - 1 ∧ (q : ℕ) = n - 2 ∨ (q : ℕ) = n - 1 ∧ (p : ℕ) = n - 2) →
          ((q : ℕ) + 1 = p ∨ (p : ℕ) + 1 = q) := by
        rintro (⟨hp1, hq1⟩ | ⟨hq1, hp1⟩) <;> omega
      split_ifs with hA hB
      · simp [hspec hA]
      · simp [hB]
      · simp [hB]
    have hiff1 := key i j h
    have hiff2 := key j i (Ne.symm h)
    rw [hiff1, hiff2]
    tauto

/-- Type `BC` on `n + 2` generators (so the Coxeter-Dynkin diagram has at least two vertices, hence
the special `4`-edge is present) is irreducible: its diagram is the path graph on `n + 2` vertices,
which is connected. -/
theorem typeBC_isIrreducible (n : ℕ) : @IsIrreducible _ (typeBCGroup (n + 2)) := by
  unfold IsIrreducible IsIrreducibleMatrix
  change (coxeterGraphMatrix (CoxeterMatrix.B (n + 2))).Connected
  rw [coxeterGraphMatrix_typeBC_eq_pathGraph]
  exact SimpleGraph.pathGraph_connected (n + 1)

/-! ### Positive definiteness of `bil` for type B/C

Type `B`/`C`'s Coxeter matrix is the tridiagonal ("path graph") form from
`Coxeter.FiniteOrAffine.TridiagonalForm` with its last edge (between generators `n` and `n + 1`,
out of `n + 2` total) reweighted from `-1/2` to `-√2/2` (it comes from `M = 4`, i.e.
`-cos (π/4) = -√2/2`, rather than `M = 3`). Since `(√2)^2 = 2`, `sos_identity_lastEdge`'s leftover
correction term vanishes, giving a clean sum-of-squares identity for the whole form. -/

/-- `CoxeterMatrix.B (n + 2)` at two distinct generators, with the "size minus 1/2" arithmetic
already resolved to `n + 1`/`n`. -/
private theorem coxeterMatrix_B_apply (n : ℕ) {i j : Fin (n + 2)} (hij : i ≠ j) :
    (CoxeterMatrix.B (n + 2)) i j =
      if (i : ℕ) = n ∧ (j : ℕ) = n + 1 ∨ (j : ℕ) = n ∧ (i : ℕ) = n + 1 then (4 : ℕ)
      else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 := by
  unfold CoxeterMatrix.B
  simp only [Matrix.of_apply, if_neg hij]
  have h1 : n + 2 - 1 = n + 1 := by omega
  have h2 : n + 2 - 2 = n := by omega
  rw [h1, h2]
  have hiff : ((i : ℕ) = n + 1 ∧ (j : ℕ) = n ∨ (j : ℕ) = n + 1 ∧ (i : ℕ) = n) ↔
      ((i : ℕ) = n ∧ (j : ℕ) = n + 1 ∨ (j : ℕ) = n ∧ (i : ℕ) = n + 1) := by tauto
  simp only [hiff]

/-- The Gram matrix entries of `bil` on standard basis vectors of type `B`/`C` match
`lastEdgeEntry n √2`. -/
private theorem bil_typeBC_entries (n : ℕ) (i j : Fin (n + 2)) :
    (@bil _ (typeBCGroup (n + 2))) (@stdBasis _ (typeBCGroup (n + 2)) i)
      (@stdBasis _ (typeBCGroup (n + 2)) j) = lastEdgeEntry n (Real.sqrt 2) (i : ℕ) (j : ℕ) := by
  unfold bil
  rw [Matrix.toBilin_single]
  change -Real.cos (Real.pi / ((CoxeterMatrix.B (n + 2)) i j : ℝ))
    = lastEdgeEntry n (Real.sqrt 2) (i : ℕ) (j : ℕ)
  by_cases hij : i = j
  · have hij' : (i : ℕ) = (j : ℕ) := by rw [hij]
    unfold CoxeterMatrix.B lastEdgeEntry
    simp only [Matrix.of_apply, if_pos hij, if_pos hij']
    norm_num
  · have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rw [coxeterMatrix_B_apply n hij]
    unfold lastEdgeEntry
    rw [if_neg hij']
    split_ifs with hspec hadj
    · rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, Real.cos_pi_div_four]
    · rw [show ((3 : ℕ) : ℝ) = 3 by norm_num, Real.cos_pi_div_three]
    · rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, Real.cos_pi_div_two]
      norm_num

/-- Extends `x : Fin (n + 2) →₀ ℝ` to a function on all of `ℕ`, vanishing past `n + 1`. -/
private noncomputable def typeBCExtend (n : ℕ) (x : Fin (n + 2) →₀ ℝ) : ℕ → ℝ :=
  fun k => if h : k < n + 2 then x ⟨k, h⟩ else 0

private theorem typeBCExtend_apply_fin (n : ℕ) (x : Fin (n + 2) →₀ ℝ) (i : Fin (n + 2)) :
    typeBCExtend n x (i : ℕ) = x i := by
  unfold typeBCExtend
  rw [dif_pos i.isLt]

/-- Sum-of-squares identity for the type-`B`/`C` (doubled) quadratic form on `n + 2` generators:
`sos_identity_lastEdge` at `k = √2`, whose leftover `(2 - k ^ 2) * y (n + 1) ^ 2` term vanishes
since `(√2) ^ 2 = 2`. -/
private theorem sos_identity_BC (n : ℕ) (y : ℕ → ℝ) :
    2 * (∑ i ∈ Finset.range (n + 2), (y i) ^ 2 - ∑ i ∈ Finset.range n, y i * y (i + 1)
        - Real.sqrt 2 * y n * y (n + 1))
      = y 0 ^ 2 + ∑ i ∈ Finset.range n, (y i - y (i + 1)) ^ 2
        + (y n - Real.sqrt 2 * y (n + 1)) ^ 2 := by
  have h := sos_identity_lastEdge n y (Real.sqrt 2)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [hsq, sub_self, zero_mul, add_zero] at h
  exact h

/-- `bil x x` for type `B`/`C`, spelled out as the tridiagonal quadratic form on the
`ℕ`-extension of `x`'s coordinates. -/
private theorem bil_typeBC_apply (n : ℕ) (x : Fin (n + 2) →₀ ℝ) :
    (@bil _ (typeBCGroup (n + 2))) x x
      = ∑ i ∈ Finset.range (n + 2), (typeBCExtend n x i) ^ 2
        - ∑ i ∈ Finset.range n, typeBCExtend n x i * typeBCExtend n x (i + 1)
        - Real.sqrt 2 * typeBCExtend n x n * typeBCExtend n x (n + 1) := by
  rw [← lastEdgeEntry_sum_range_double n (Real.sqrt 2) (typeBCExtend n x)]
  have hrepr : (@stdBasis _ (typeBCGroup (n + 2))).repr x = x := rfl
  have key : (@bil _ (typeBCGroup (n + 2))) x x
      = ∑ i : Fin (n + 2), ∑ j : Fin (n + 2),
          x i * x j * (@bil _ (typeBCGroup (n + 2)))
            (@stdBasis _ (typeBCGroup (n + 2)) i) (@stdBasis _ (typeBCGroup (n + 2)) j) := by
    rw [← LinearMap.BilinForm.sum_repr_mul_repr_mul
      (B := @bil _ (typeBCGroup (n + 2))) (@stdBasis _ (typeBCGroup (n + 2))) x x, hrepr,
      Finsupp.sum_fintype x _ (fun i => by simp)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finsupp.sum_fintype x _ (fun j => by simp)]
    simp only [smul_eq_mul, ← mul_assoc]
  rw [key]
  have hentry : ∀ i j : Fin (n + 2),
      x i * x j * (@bil _ (typeBCGroup (n + 2)))
        (@stdBasis _ (typeBCGroup (n + 2)) i) (@stdBasis _ (typeBCGroup (n + 2)) j)
      = typeBCExtend n x (i : ℕ) * typeBCExtend n x (j : ℕ)
        * lastEdgeEntry n (Real.sqrt 2) (i : ℕ) (j : ℕ) := by
    intro i j
    rw [bil_typeBC_entries, typeBCExtend_apply_fin, typeBCExtend_apply_fin]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 2)))) =>
    Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 2)))) => hentry i j))]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin (n + 2),
    typeBCExtend n x i * typeBCExtend n x j * lastEdgeEntry n (Real.sqrt 2) i j) (n + 2)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Fin.sum_univ_eq_sum_range
    (fun j => typeBCExtend n x i * typeBCExtend n x j * lastEdgeEntry n (Real.sqrt 2) i j) (n + 2)

/-- Type `B`/`C`'s `bil` is positive semidefinite: `bil x x ≥ 0` for every `x`, since (doubled)
it's a sum of squares by `sos_identity_BC`. -/
private theorem bil_typeBC_isNonneg (n : ℕ) : (@bil _ (typeBCGroup (n + 2))).IsNonneg := by
  rw [LinearMap.BilinForm.isNonneg_def]
  intro x
  rw [bil_typeBC_apply]
  have h := sos_identity_BC n (typeBCExtend n x)
  have hC : 0 ≤ ∑ i ∈ Finset.range n, (typeBCExtend n x i - typeBCExtend n x (i + 1)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith [h, sq_nonneg (typeBCExtend n x 0),
    sq_nonneg (typeBCExtend n x n - Real.sqrt 2 * typeBCExtend n x (n + 1)), hC]

/-- Type `B`/`C`'s `bil` is nondegenerate: if `bil x x = 0`, the sum-of-squares identity forces
every `typeBCExtend n x i` (`i ≤ n + 1`) to vanish, i.e. `x = 0`. -/
private theorem bil_typeBC_nondegenerate (n : ℕ) :
    (@bil _ (typeBCGroup (n + 2))).Nondegenerate := by
  unfold LinearMap.BilinForm.Nondegenerate
  rw [LinearMap.BilinForm.nondegenerate_iff'
    (hs := (bil_typeBC_isNonneg n).nonneg)
    (hB := LinearMap.BilinForm.isSymm_iff.mp (@bil_isSymm _ (typeBCGroup (n + 2))))]
  intro x hx
  rcases ((bil_typeBC_isNonneg n).nonneg x).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have hzero : (@bil _ (typeBCGroup (n + 2))) x x = 0 := h.symm
    rw [bil_typeBC_apply] at hzero
    set y := typeBCExtend n x with hy_def
    have hsos := sos_identity_BC n y
    have hC : 0 ≤ ∑ i ∈ Finset.range n, (y i - y (i + 1)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hlastsq : (y n - Real.sqrt 2 * y (n + 1)) ^ 2 = 0 := by
      nlinarith [hsos, hzero, sq_nonneg (y 0), hC]
    have h0sq : y 0 ^ 2 = 0 := by nlinarith [hsos, hzero, hlastsq, hC]
    have hCsum : ∑ i ∈ Finset.range n, (y i - y (i + 1)) ^ 2 = 0 := by
      nlinarith [hsos, hzero, hlastsq, sq_nonneg (y 0)]
    have h0 : y 0 = 0 := sq_eq_zero_iff.mp h0sq
    have hstep : ∀ i ∈ Finset.range n, y i = y (i + 1) := by
      intro i hi
      have hzero_term : (y i - y (i + 1)) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hCsum i hi
      have := sq_eq_zero_iff.mp hzero_term
      linarith
    have hall : ∀ i ≤ n, y i = 0 := by
      intro i hi
      induction i with
      | zero => exact h0
      | succ k ih =>
          have hk : k < n := by omega
          rw [← hstep k (Finset.mem_range.mpr hk)]
          exact ih (by omega)
    have hn0 : y n = 0 := hall n le_rfl
    have hlast : y n - Real.sqrt 2 * y (n + 1) = 0 := sq_eq_zero_iff.mp hlastsq
    have hn1 : y (n + 1) = 0 := by
      rw [hn0] at hlast
      have hmul : Real.sqrt 2 * y (n + 1) = 0 := by linarith
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd h (by positivity)
      · exact h
    apply Finsupp.ext
    intro i
    have hi0 : y (i : Fin (n + 2)).val = 0 := by
      rcases lt_or_ge (i : Fin (n + 2)).val (n + 1) with h | h
      · exact hall _ (by omega)
      · have heq : (i : Fin (n + 2)).val = n + 1 := by omega
        rw [heq]; exact hn1
    rw [hy_def, typeBCExtend_apply_fin] at hi0
    simpa using hi0

theorem typeBC_isFiniteCoxeter (n : ℕ) : @IsFiniteCoxeter _ (typeBCGroup (n + 2)) :=
  Or.inr ⟨⟨@bil_isSymm _ (typeBCGroup (n + 2)), bil_typeBC_isNonneg n⟩, bil_typeBC_nondegenerate n⟩

theorem typeBC_isPolyFiniteWeyl (n : ℕ) : @IsPolyFiniteWeyl _ (typeBCGroup (n + 2)) :=
  ⟨typeBC_isFiniteCoxeter n, typeBC_isCrystallographic (n + 2)⟩

/-- Type `B`/`C` on `n + 2` generators is an *irreducible* finite Weyl group. -/
theorem typeBC_isIrreducibleFiniteWeyl (n : ℕ) : @IsIrreducibleFiniteWeyl _ (typeBCGroup (n + 2)) :=
  ⟨typeBC_isPolyFiniteWeyl n, typeBC_isIrreducible n⟩

/-! ### Small-rank accidental identifications -/

section Accidentals

private theorem coxeterMatrix_B_one_eq_A_one : CoxeterMatrix.B 1 = CoxeterMatrix.A 1 := by
  ext i j
  fin_cases i
  fin_cases j
  rfl

/-- The Coxeter-system-level accidental identification `BC₁ = A₁`.

The entrywise matrix equality used to prove this is private. -/
theorem typeBC_one_identifies_typeA_one :
    HEq (@CoxeterGroup.cs _ (typeBCGroup 1)) (@CoxeterGroup.cs _ (typeAGroup 1)) := by
  change HEq (CoxeterMatrix.B 1).toCoxeterSystem (CoxeterMatrix.A 1).toCoxeterSystem
  rw [← coxeterMatrix_B_one_eq_A_one]

end Accidentals

end Coxeter
