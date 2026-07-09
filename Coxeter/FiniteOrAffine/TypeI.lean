module

public import Coxeter.FiniteOrAffine.Exceptional
public import Coxeter.FiniteOrAffine.TypeA
public import Coxeter.FiniteOrAffine.TypeBC
public import Coxeter.SpecialFeatures

/-!
# The rank-two Coxeter groups of type I

This file packages mathlib's `CoxeterMatrix.I m` as a `CoxeterGroup`.

The rank-two crystallographic cases include the standard accidental identifications
`I₂(3) = A₂`, `I₂(4) = BC₂`, and `I₂(6) = G₂`.
-/

@[expose] public section

namespace Coxeter

/-- The rank-two Coxeter group `I₂(m + 2)`, realized as the abstract group presented by
`CoxeterMatrix.I m`. -/
@[reducible] noncomputable def typeIGroup (m : ℕ) : CoxeterGroup (CoxeterMatrix.I m).Group where
  B := Fin 2
  M := CoxeterMatrix.I m
  cs := (CoxeterMatrix.I m).toCoxeterSystem

/-- Type `I₂(m + 2)`'s Coxeter-Dynkin diagram is the complete graph on `Fin 2`: its only
off-diagonal entry is `m + 2 ≠ 2` because `m ≠ 0`, so the two generators are always joined. -/
private theorem coxeterGraphMatrix_typeI_eq_top (m : ℕ) [m_nz : NeZero m] :
    coxeterGraphMatrix (CoxeterMatrix.I m) = ⊤ := by
  ext i j
  rw [coxeterGraphMatrix, SimpleGraph.fromRel_adj, SimpleGraph.top_adj]
  unfold CoxeterMatrix.I
  simp only [Matrix.of_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h]
    have m_nz' := m_nz.ne
    simp only [Or.inl m_nz']

/-- Type `I₂(m + 2)` is irreducible: its diagram is the complete graph on two vertices, which is
connected. -/
theorem typeI_isIrreducible (m : ℕ) [NeZero m] : @IsIrreducible _ (typeIGroup m) := by
  unfold IsIrreducible IsIrreducibleMatrix
  change (coxeterGraphMatrix (CoxeterMatrix.I m)).Connected
  rw [coxeterGraphMatrix_typeI_eq_top]
  exact SimpleGraph.connected_top

/-- Every `Fin 2 →₀ ℝ` vector decomposes into its two coordinates against `Finsupp.single`. This is
stated concretely over `Fin 2` (rather than `B (typeIGroup m)`) to avoid needing typeclass search
to see through the reducible `typeIGroup` definition; `typeI_stdBasis_decomp` bridges it back. -/
private theorem finsupp_fin_two_decomp (x : Fin 2 →₀ ℝ) :
    x = x 0 • Finsupp.single (0 : Fin 2) (1 : ℝ) + x 1 • Finsupp.single (1 : Fin 2) (1 : ℝ) := by
  apply Finsupp.ext
  intro a
  fin_cases a <;> simp

/-- Every vector of `typeIGroup m`'s two-dimensional representation decomposes into its two
standard-basis coordinates. -/
private theorem typeI_stdBasis_decomp (m : ℕ) (x : @V _ (typeIGroup m)) :
    x = x (0 : Fin 2) • (@stdBasis _ (typeIGroup m)) (0 : Fin 2)
      + x (1 : Fin 2) • (@stdBasis _ (typeIGroup m)) (1 : Fin 2) := by
  have hs0 : (@stdBasis _ (typeIGroup m)) (0 : Fin 2) = Finsupp.single (0 : Fin 2) (1 : ℝ) :=
    congrFun Finsupp.coe_basisSingleOne (0 : Fin 2)
  have hs1 : (@stdBasis _ (typeIGroup m)) (1 : Fin 2) = Finsupp.single (1 : Fin 2) (1 : ℝ) :=
    congrFun Finsupp.coe_basisSingleOne (1 : Fin 2)
  rw [hs0, hs1]
  exact finsupp_fin_two_decomp x

/-- Type `I₂(m + 2)` is of finite type: `bil` is positive semidefinite and nondegenerate (i.e.
positive definite). By `bil_restrict_E_diag` (Bourbaki Ch V, §4, Proposition 1), the Gram form on
the two generators is `(x - y cos θ)^2 + (y sin θ)^2` with `θ = π/(m + 2) ∈ (0, π/2]`, so
`sin θ > 0` and the form is positive definite. -/
theorem typeI_isFiniteCoxeter (m : ℕ) : @IsFiniteCoxeter _ (typeIGroup m) := by
  right
  have hM : (typeIGroup m).M (0 : Fin 2) (1 : Fin 2) = m + 2 := rfl
  have hsin : 0 < Real.sin (Real.pi / ((typeIGroup m).M (0 : Fin 2) (1 : Fin 2) : ℝ)) := by
    rw [hM]
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · apply div_lt_self Real.pi_pos
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) m]
  have hnonneg : ∀ x : @V _ (typeIGroup m), 0 ≤ (@bil _ (typeIGroup m)) x x := by
    intro x
    rw [typeI_stdBasis_decomp m x, @bil_restrict_E_diag _ (typeIGroup m)]
    positivity
  refine ⟨⟨@bil_isSymm _ (typeIGroup m), ?_⟩, ?_⟩
  · rw [LinearMap.BilinForm.isNonneg_def]
    exact hnonneg
  · unfold LinearMap.BilinForm.Nondegenerate
    rw [LinearMap.BilinForm.nondegenerate_iff'
      (hs := hnonneg)
      (hB := LinearMap.BilinForm.isSymm_iff.mp (@bil_isSymm _ (typeIGroup m)))]
    intro x hx
    rcases (hnonneg x).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hx
      have hzero : (@bil _ (typeIGroup m)) x x = 0 := h.symm
      rw [typeI_stdBasis_decomp m x, @bil_restrict_E_diag _ (typeIGroup m)] at hzero
      have h1 : x (1 : Fin 2) * Real.sin (Real.pi / (typeIGroup m).M (0 : Fin 2) (1 : Fin 2))
          = 0 := by
        nlinarith [sq_nonneg (x (0 : Fin 2)
          - x (1 : Fin 2) * Real.cos (Real.pi / (typeIGroup m).M (0 : Fin 2) (1 : Fin 2))),
          hzero]
      have hx1 : x (1 : Fin 2) = 0 := by
        rcases mul_eq_zero.mp h1 with h' | h'
        · exact h'
        · exact absurd h' (ne_of_gt hsin)
      have h0sq : (x (0 : Fin 2)
          - x (1 : Fin 2) * Real.cos (Real.pi / (typeIGroup m).M (0 : Fin 2) (1 : Fin 2))) ^ 2
          = 0 := by
        nlinarith [sq_nonneg (x (1 : Fin 2)
          * Real.sin (Real.pi / (typeIGroup m).M (0 : Fin 2) (1 : Fin 2))), hzero]
      have h0 : x (0 : Fin 2) = 0 := by
        have := sq_eq_zero_iff.mp h0sq
        rw [hx1] at this
        simpa using this
      rw [typeI_stdBasis_decomp m x, h0, hx1]
      simp

/-! ### Accidental rank-two identifications -/

section Accidentals

private theorem coxeterMatrix_I_one_eq_A_two : CoxeterMatrix.I 1 = CoxeterMatrix.A 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem coxeterMatrix_I_two_eq_B_two : CoxeterMatrix.I 2 = CoxeterMatrix.B 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem coxeterMatrix_I_four_eq_G_two : CoxeterMatrix.I 4 = CoxeterMatrix.G₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The Coxeter-system-level accidental identification `I₂(3) = A₂`.

Mathlib's `CoxeterMatrix.I m` represents `I₂(m + 2)`, so `m = 1` is the `I₂(3)` case.
The entrywise matrix equality used to prove this is private. -/
theorem typeI_three_identifies_typeA_two :
    HEq (@CoxeterGroup.cs _ (typeIGroup 1)) (@CoxeterGroup.cs _ (typeAGroup 2)) := by
  change HEq (CoxeterMatrix.I 1).toCoxeterSystem (CoxeterMatrix.A 2).toCoxeterSystem
  rw [← coxeterMatrix_I_one_eq_A_two]

/-- The Coxeter-system-level accidental identification `I₂(4) = BC₂`.

Mathlib's `CoxeterMatrix.I m` represents `I₂(m + 2)`, so `m = 2` is the `I₂(4)` case.
The entrywise matrix equality used to prove this is private. -/
theorem typeI_four_identifies_typeBC_two :
    HEq (@CoxeterGroup.cs _ (typeIGroup 2)) (@CoxeterGroup.cs _ (typeBCGroup 2)) := by
  change HEq (CoxeterMatrix.I 2).toCoxeterSystem (CoxeterMatrix.B 2).toCoxeterSystem
  rw [← coxeterMatrix_I_two_eq_B_two]

/-- The Coxeter-system-level accidental identification `I₂(6) = G₂`.

Mathlib's `CoxeterMatrix.I m` represents `I₂(m + 2)`, so `m = 4` is the `I₂(6)` case.
The entrywise matrix equality used to prove this is private. -/
theorem typeI_six_identifies_typeG_two :
    HEq (@CoxeterGroup.cs _ (typeIGroup 4)) (@CoxeterGroup.cs _ typeG2Group) := by
  change HEq (CoxeterMatrix.I 4).toCoxeterSystem CoxeterMatrix.G₂.toCoxeterSystem
  rw [← coxeterMatrix_I_four_eq_G_two]

end Accidentals

end Coxeter
