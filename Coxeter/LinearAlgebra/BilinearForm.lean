module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Data.Real.Sqrt
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Bilinear forms

This file relates bilinar forms and matrices, and proves properties about real vector spaces with
positive definite symmetric bilinear forms.
-/

@[expose] public section

namespace Coxeter

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {ι : Type*} (b : Module.Basis ι R M)

/-- Omits the `Fintype` and `DecidableEq` hypotheses from mathlib's version -/
noncomputable def LinearMap.BilinForm.toMatrix :
  LinearMap.BilinForm R M ≃ₗ[R] Matrix ι ι R where
  toFun B i j := B (b i) (b j)
  invFun B := b.constr R ((b.constr R) ∘ B)
  map_add' := by
    intro B₁ B₂
    ext i j
    simp
  map_smul' := by
    intro m B
    ext i j
    simp
  left_inv := by
    intro B
    apply b.ext
    intro i
    apply b.ext
    intro j
    simp
  right_inv := by
    intro B
    ext i j
    simp

/-- Omits the `Fintype` and `DecidableEq` hypotheses from mathlib's version -/
noncomputable def Matrix.toBilin : Matrix ι ι R ≃ₗ[R] LinearMap.BilinForm R M :=
  (LinearMap.BilinForm.toMatrix b).symm

theorem Matrix.toBilin_single (B : Matrix ι ι R) (i j : ι) : toBilin b B (b i) (b j) = B i j := by
  unfold toBilin LinearMap.BilinForm.toMatrix
  simp

section BlockDiagonal

variable {κ : Type*} {ιk : κ → Type*}

/-- If the matrix of a bilinear form `B` (w.r.t. a basis indexed by a disjoint union `Σ k, ιk k`)
is block diagonal, with each block itself the matrix of a bilinear form `Bk k` on the free module
`ιk k →₀ R` (w.r.t. its standard basis `Finsupp.basisSingleOne`), and some block `Bk k₀` is
degenerate (not left-separating), then `B` itself is degenerate.

The witness for `¬ B.SeparatingLeft` is the padded vector `Finsupp.linearCombination R
(fun j => b ⟨k₀, j⟩) x`, where `x` witnesses the degeneracy of `Bk k₀`: it is nonzero since
`b ⟨k₀, ·⟩` is linearly independent, and it is left-orthogonal to all of `B` since `B`'s matrix
vanishes off the `k₀`-block. -/
theorem LinearMap.BilinForm.not_separatingLeft_of_toMatrix_eq_blockDiagonal' [DecidableEq κ]
    (b : Module.Basis (Σ k, ιk k) R M) (B : LinearMap.BilinForm R M)
    (Bk : ∀ k, LinearMap.BilinForm R (ιk k →₀ R))
    (hB : LinearMap.BilinForm.toMatrix b B =
      Matrix.blockDiagonal' (fun k => LinearMap.BilinForm.toMatrix Finsupp.basisSingleOne (Bk k)))
    {k₀ : κ} (hdeg : ¬ (Bk k₀).SeparatingLeft) :
    ¬ B.SeparatingLeft := by
  unfold LinearMap.SeparatingLeft at hdeg ⊢
  push Not at hdeg ⊢
  obtain ⟨x, hx1, hx2⟩ := hdeg
  set v : ιk k₀ → M := fun j => b ⟨k₀, j⟩ with hv_def
  have hli : LinearIndependent R v := b.linearIndependent.comp _ sigma_mk_injective
  refine ⟨Finsupp.linearCombination R v x, fun y => ?_, ?_⟩
  · have hzero : B (Finsupp.linearCombination R v x) = 0 := by
      apply b.ext
      rintro ⟨lk, lm⟩
      simp only [LinearMap.zero_apply]
      have key : B (Finsupp.linearCombination R v x) (b ⟨lk, lm⟩)
          = Finsupp.linearCombination R (fun j => B (v j) (b ⟨lk, lm⟩)) x := by
        rw [← LinearMap.BilinForm.flip_apply, Finsupp.apply_linearCombination]
        rfl
      rw [key]
      by_cases h : k₀ = lk
      · subst h
        have hentry : ∀ j, B (v j) (b ⟨k₀, lm⟩) =
            Bk k₀ (Finsupp.basisSingleOne j) (Finsupp.basisSingleOne lm) := by
          intro j
          have h1 : (LinearMap.BilinForm.toMatrix b B) ⟨k₀, j⟩ ⟨k₀, lm⟩
              = B (v j) (b ⟨k₀, lm⟩) := rfl
          have h2 : (LinearMap.BilinForm.toMatrix Finsupp.basisSingleOne (Bk k₀)) j lm
              = Bk k₀ (Finsupp.basisSingleOne j) (Finsupp.basisSingleOne lm) := rfl
          rw [← h1, ← h2, ← Matrix.blockDiagonal'_apply_eq
            (fun k => LinearMap.BilinForm.toMatrix Finsupp.basisSingleOne (Bk k)) k₀ j lm]
          exact congrFun (congrFun hB ⟨k₀, j⟩) ⟨k₀, lm⟩
        simp_rw [hentry]
        have hcomb : Finsupp.linearCombination R (⇑(Finsupp.basisSingleOne (R := R))) x = x := by
          rw [Finsupp.linearCombination_apply]
          simp [Finsupp.coe_basisSingleOne, Finsupp.sum_single]
        have hstep : Bk k₀ x (Finsupp.basisSingleOne lm)
            = Finsupp.linearCombination R
                (fun j => Bk k₀ (Finsupp.basisSingleOne j) (Finsupp.basisSingleOne lm)) x := by
          conv_lhs => rw [← hcomb]
          rw [← LinearMap.BilinForm.flip_apply, Finsupp.apply_linearCombination]
          rfl
        rw [← hstep]
        exact hx1 (Finsupp.basisSingleOne lm)
      · have hentry : ∀ j, B (v j) (b ⟨lk, lm⟩) = 0 := by
          intro j
          have h1 : (LinearMap.BilinForm.toMatrix b B) ⟨k₀, j⟩ ⟨lk, lm⟩
              = B (v j) (b ⟨lk, lm⟩) := rfl
          rw [← h1, congrFun (congrFun hB ⟨k₀, j⟩) ⟨lk, lm⟩, Matrix.blockDiagonal'_apply_ne _ _ _ h]
        rw [show (fun j => B (v j) (b ⟨lk, lm⟩)) = (0 : ιk k₀ → R) from funext hentry,
          Finsupp.linearCombination_zero]
        rfl
    rw [hzero]
    rfl
  · intro heq
    apply hx2
    have : Finsupp.linearCombination R v (0 : ιk k₀ →₀ R) = Finsupp.linearCombination R v x :=
      by rw [map_zero, heq]
    exact (hli this).symm

end BlockDiagonal

section real

/-! ### Positive definite symmetric bilinear forms on real vector spaces -/

open Real

section BlockDiagonalPosSemidef

/-! `IsPosSemidef` only needs an ordered commutative semiring of scalars (not specifically `ℝ`)
so this block-diagonal criterion is stated for a general `R` with a compatible order. -/

variable {R : Type*} [CommSemiring R] [Preorder R] [AddLeftMono R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {κ : Type*} {ιk : κ → Type*}

/-- Suppose the matrix of a bilinear form `B`
(w.r.t. a basis indexed by a disjoint union `Σ k, ιk k`)
is block diagonal, with each block itself the matrix of a bilinear form `Bk k` on the free module
`ιk k →₀ R` (w.r.t. its standard basis `Finsupp.basisSingleOne`) and that R is
a general ordered commutative semiring.

Positive-semidefiniteness carries over from the blocks.

- `IsSymm` follows termwise from `hB`, since off-diagonal-block entries vanish on both sides and
diagonal-block entries agree by each `(Bk k).IsSymm`.
- For `IsNonneg`, `x` is split via
`Finsupp.split`/`splitSupport` (applied to `b.repr x`) into finitely many block components `y k`
with `x = ∑ k, y k`; cross terms `B (y k) (y k')` for `k ≠ k'` vanish by the same block-diagonal
entries, so `B x x` collapses to the finite sum `∑ k, Bk k (l.split k) (l.split k)`, which is
nonnegative termwise by `hpsd`. -/
theorem LinearMap.BilinForm.isPosSemidef_of_toMatrix_eq_blockDiagonal' [DecidableEq κ]
    (b : Module.Basis (Σ k, ιk k) R V) (B : LinearMap.BilinForm R V)
    (Bk : ∀ k, LinearMap.BilinForm R (ιk k →₀ R))
    (hB : LinearMap.BilinForm.toMatrix b B =
      Matrix.blockDiagonal' (fun k =>
        LinearMap.BilinForm.toMatrix Finsupp.basisSingleOne (Bk k)))
    (hpsd : ∀ k, (Bk k).IsPosSemidef) :
    B.IsPosSemidef := by
  have hentry_diag : ∀ k (i j : ιk k), B (b ⟨k, i⟩) (b ⟨k, j⟩) =
      Bk k (Finsupp.basisSingleOne i) (Finsupp.basisSingleOne j) := by
    intro k i j
    have h1 : (LinearMap.BilinForm.toMatrix b B) ⟨k, i⟩ ⟨k, j⟩ = B (b ⟨k, i⟩) (b ⟨k, j⟩) := rfl
    have h2 : (LinearMap.BilinForm.toMatrix Finsupp.basisSingleOne (Bk k)) i j
        = Bk k (Finsupp.basisSingleOne i) (Finsupp.basisSingleOne j) := rfl
    rw [← h1, ← h2, ← Matrix.blockDiagonal'_apply_eq
      (fun k => LinearMap.BilinForm.toMatrix Finsupp.basisSingleOne (Bk k)) k i j]
    exact congrFun (congrFun hB ⟨k, i⟩) ⟨k, j⟩
  have hentry_off : ∀ {k k' : κ} (i : ιk k) (j : ιk k'), k ≠ k' → B (b ⟨k, i⟩) (b ⟨k', j⟩) = 0 := by
    intro k k' i j h
    have h1 : (LinearMap.BilinForm.toMatrix b B) ⟨k, i⟩ ⟨k', j⟩ = B (b ⟨k, i⟩) (b ⟨k', j⟩) := rfl
    rw [← h1, congrFun (congrFun hB ⟨k, i⟩) ⟨k', j⟩, Matrix.blockDiagonal'_apply_ne _ _ _ h]
  constructor
  · rw [LinearMap.BilinForm.isSymm_iff_basis b]
    rintro ⟨k, i⟩ ⟨k', j⟩
    by_cases h : k = k'
    · subst h
      rw [hentry_diag k i j, hentry_diag k j i, (hpsd k).isSymm.eq]
    · rw [hentry_off i j h, hentry_off j i (Ne.symm h)]
  · rw [LinearMap.BilinForm.isNonneg_def]
    intro x
    set l : (Σ k, ιk k) →₀ R := b.repr x with hl_def
    set y : κ → V := fun k => Finsupp.linearCombination R (fun i => b ⟨k, i⟩) (l.split k)
      with hy_def
    have hl_split : l = ∑ k ∈ l.splitSupport, Finsupp.mapDomain (Sigma.mk k) (l.split k) := by
      conv_lhs => rw [← Finsupp.sum_single l]
      rw [Finsupp.sigma_sum]
      exact Finset.sum_congr rfl (fun k _ => rfl)
    have hxA : x = ∑ k ∈ l.splitSupport, y k := by
      have hx0 : x = Finsupp.linearCombination R b l := (b.linearCombination_repr x).symm
      rw [hx0]
      conv_lhs => rw [hl_split]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hy_def]
      exact Finsupp.linearCombination_mapDomain R (Sigma.mk k) (l.split k)
    have hcross : ∀ k k' : κ, k ≠ k' → B (y k) (y k') = 0 := by
      intro k k' hne
      have key1 : B (y k) (y k')
          = Finsupp.linearCombination R (fun i => B (b ⟨k, i⟩) (y k')) (l.split k) := by
        rw [hy_def, ← LinearMap.BilinForm.flip_apply, Finsupp.apply_linearCombination]
        rfl
      have key2 : ∀ i, B (b ⟨k, i⟩) (y k')
          = Finsupp.linearCombination R (fun j => B (b ⟨k, i⟩) (b ⟨k', j⟩)) (l.split k') := by
        intro i
        rw [hy_def, Finsupp.apply_linearCombination]
        rfl
      rw [key1]
      have hz : (fun i => B (b ⟨k, i⟩) (y k')) = (0 : ιk k → R) := by
        funext i
        rw [key2 i]
        have hz2 : (fun j => B (b ⟨k, i⟩) (b ⟨k', j⟩)) = (0 : ιk k' → R) := by
          funext j
          exact hentry_off i j hne
        rw [hz2, Finsupp.linearCombination_zero]
        rfl
      rw [hz, Finsupp.linearCombination_zero]
      rfl
    have hdiag : ∀ k, B (y k) (y k) = Bk k (l.split k) (l.split k) := by
      intro k
      have hcombk : Finsupp.linearCombination R (⇑(Finsupp.basisSingleOne (R := R))) (l.split k)
          = l.split k := by
        rw [Finsupp.linearCombination_apply]
        simp [Finsupp.coe_basisSingleOne, Finsupp.sum_single]
      have lhs_eq : B (y k) (y k)
          = Finsupp.linearCombination R (fun i =>
              Finsupp.linearCombination R
                (fun j => Bk k (Finsupp.basisSingleOne i) (Finsupp.basisSingleOne j))
                (l.split k)) (l.split k) := by
        rw [hy_def, ← LinearMap.BilinForm.flip_apply, Finsupp.apply_linearCombination]
        congr 1
        congr 1
        funext i
        simp only [Function.comp_apply]
        rw [LinearMap.BilinForm.flip_apply, Finsupp.apply_linearCombination]
        congr 1
        congr 1
        funext j
        exact hentry_diag k i j
      have rhs_eq : Bk k (l.split k) (l.split k)
          = Finsupp.linearCombination R (fun i =>
              Finsupp.linearCombination R
                (fun j => Bk k (Finsupp.basisSingleOne i) (Finsupp.basisSingleOne j))
                (l.split k)) (l.split k) := by
        conv_lhs => rw [← hcombk]
        rw [← LinearMap.BilinForm.flip_apply, Finsupp.apply_linearCombination]
        congr 1
        congr 1
        funext i
        simp only [Function.comp_apply]
        rw [LinearMap.BilinForm.flip_apply, Finsupp.apply_linearCombination]
        rfl
      rw [lhs_eq, rhs_eq]
    rw [hxA]
    simp_rw [map_sum]
    conv_rhs => simp [Finset.sum_apply']
    have hcollapse : ∑ k' ∈ l.splitSupport, ∑ k ∈ l.splitSupport, B (y k) (y k')
        = ∑ k ∈ l.splitSupport, Bk k (l.split k) (l.split k) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [Finset.sum_eq_single k (fun k' _ hne => hcross k k' (Ne.symm hne))
        (fun hk' => absurd hk hk')]
      exact hdiag k
    conv_rhs => rw [hcollapse]
    exact Finset.sum_nonneg (fun k _ => (hpsd k).nonneg (l.split k))

end BlockDiagonalPosSemidef

/-! ### Orthonormal bases and orthogonal complements over `ℝ` -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def Orthonormal {ι : Type*} (B : LinearMap.BilinForm ℝ V) (v : ι → V) :=
  (∀ (i : ι), B (v i) (v i) = 1) ∧ LinearMap.IsOrthoᵢ B v

/-- A positive definite symmetric bilinear form on a finite dimensional real vector space has an
orthonormal basis. -/
theorem exists_orthonormal_basis [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V)
  (hB1 : B.IsSymm) (hB2 : B.IsNonneg) (hB3 : B.Nondegenerate) :
  ∃ (v : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V), Orthonormal B v := by
  rw [LinearMap.BilinForm.isSymm_iff] at hB1
  have ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB1
  have h1 : ∀ (i : Fin (Module.finrank ℝ V)), B (v i) (v i) > 0 := by
    intro i
    unfold LinearMap.BilinForm.Nondegenerate at hB3
    rw [LinearMap.BilinForm.nondegenerate_iff' _ hB2.nonneg hB1] at hB3
    apply hB3
    exact v.ne_zero i
  have h2 : ∀ (i : Fin (Module.finrank ℝ V)), IsUnit (1 / sqrt (B (v i) (v i))) := by
    intro i
    apply Ne.isUnit
    grind
  let w := v.unitsSMul (fun i => (h2 i).choose)
  exists w
  constructor
  · intro i
    unfold w
    rw [Module.Basis.unitsSMul_apply]
    change (B ((h2 i).choose.val • v i)) ((h2 i).choose.val • v i) = 1
    rw [(h2 i).choose_spec]
    simp
    grind
  · intro i j h
    change B (w i) (w j) = 0
    unfold w
    simp only [Module.Basis.unitsSMul_apply, LinearMap.map_smul_of_tower, LinearMap.smul_apply]
    rw [hv h]
    simp

variable {W : Submodule ℝ V} [FiniteDimensional ℝ W]

/-- If $V$ is an arbitrary real vector space equipped with a positive definite symmetric
bilinar form and $W$ is a finite dimensional subspace, then $V$ is a sum of $W$ and its
orthogonal complement. -/
theorem sup_orthogonal_eq_top (B : LinearMap.BilinForm ℝ V)
  (hB1 : B.IsSymm) (hB2 : (B.restrict W).IsNonneg) (hB3 : (B.restrict W).Nondegenerate) :
  W ⊔ W.orthogonalBilin B = ⊤ := by
  have hB1' : (B.restrict W).IsSymm := by
    exact hB1.restrict W
  have ⟨v, hv1, hv2⟩ := exists_orthonormal_basis (B.restrict W) hB1' hB2 hB3
  rw [Submodule.sup_eq_top_iff]
  intro x
  let u : W := ∑ (i : Fin (Module.finrank ℝ W)), B x (v i) • v i
  exists u
  refine ⟨u.prop, x - u, ?_, by simp⟩
  rw [Submodule.mem_orthogonalBilin_iff]
  unfold LinearMap.IsOrtho
  conv =>
    intro
    rw [hB1.eq, ←LinearMap.mem_ker]
  change W ≤ (B (x - ↑u)).ker
  have : Submodule.span ℝ (Set.range (Subtype.val ∘ v)) = W := by
    apply Submodule.span_eq_of_le
    · rw [Set.range_subset_iff]
      intro i
      simp
    · intro w hw
      rw [Submodule.mem_span_set']
      exists Module.finrank ℝ W, v.repr ⟨w, hw⟩, fun i => ⟨(v i).val, by simp⟩
      have h1 : ∑ (i : Fin (Module.finrank ℝ W)), (v.repr ⟨w, hw⟩ i) • (v i) = w := by simp
      conv =>
        lhs
        congr
        · skip
        · intro i
          change ((v.repr ⟨w, hw⟩) i • (v i)).val
      rwa [←Submodule.coe_sum]
  nth_rw 1 [←this]
  rw [Submodule.span_le, Set.range_subset_iff]
  intro i
  simp only [map_sub, Function.comp_apply, SetLike.mem_coe, LinearMap.mem_ker,
    LinearMap.sub_apply]
  rw [sub_eq_zero]
  symm
  unfold u
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, map_sum, map_smul,
    LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  change ∑ j, B x (v j) * B (v j) (v i) = B x (v i)
  have : ∀ (i j : Fin (Module.finrank ℝ W)), (B x (v j)) * B (v j) (v i)
    = Set.indicator {i} (fun j => B x (v j)) j := by
    intro i j
    by_cases h : j = i
    · simp only [h, Set.mem_singleton_iff, Set.indicator_of_mem]
      have : B (v i).val (v i).val = 1 := hv1 i
      rw [this, mul_one]
    · simp only [Set.mem_singleton_iff, h, not_false_eq_true, Set.indicator_of_notMem,
        mul_eq_zero]
      right
      exact hv2 h
  conv =>
    lhs
    congr
    · skip
    · intro j
      rw [this]
  simp

end real

end Coxeter
