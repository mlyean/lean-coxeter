module

public import Coxeter.SpecialFeatures
public import Mathlib.NumberTheory.Niven
public import Mathlib.LinearAlgebra.Ray

/-!
# Generalized Cartan matrices

This file packages the classical Kac–Moody **generalized Cartan matrix** realizing a Coxeter
system's `HasGeneralizedCartanMatrix` witness (see `Coxeter.SpecialFeatures`) as an actual matrix,
and connects it to the standard Cartan-integer formula in terms of `bil`.

## Main definitions

* `Coxeter.SymmetrizableGeneralizedCartanMatrix`
* `Coxeter.HasGeneralizedCartanMatrix.cartanMatrix`

## Main statements

* `Coxeter.HasGeneralizedCartanMatrix.isCrystallographic`
* `Coxeter.HasGeneralizedCartanMatrix.cartanMatrix_apply_eq`
* `Coxeter.HasGeneralizedCartanMatrix.geomRep_mapsTo_lattice`
-/

@[expose] public section

namespace Coxeter

variable {W : Type*} {cg : CoxeterGroup W}

/-- The individual condition `2 * scale i' * cos (π / M i i') = n * scale i` looks asymmetric in
`i`/`i'`, but requiring it for *both* orderings (as the `∀ i i'` in `HasGeneralizedCartanMatrix`
already does) pins the two integer witnesses `n`, `m` — the generalized Cartan matrix entries
`a_{i i'}`, `a_{i' i}` — together via their product, which depends only on the unordered pair:
`n * m = 4 * cos (π / M i i') ^ 2`, using `M i i' = M i' i`. This is the familiar Kac–Moody
"Cartan integer product" identity (e.g. `4 cos² (π/M) ∈ {0, 1, 2, 3, 4}` for
`M ∈ {2, 3, 4, 6, 0}` respectively), and confirms the two ordered instances of the condition are not
independent data but two faces of one order-independent constraint. -/
private theorem generalizedCartanMatrix_mul_eq
    (scale : cg.B → ℝ) (hscale : ∀ i, 0 < scale i) (i i' : cg.B)
    (n : ℕ) (hn : 2 * scale i' * Real.cos (Real.pi / cg.M i i') = n * scale i)
    (m : ℕ) (hm : 2 * scale i * Real.cos (Real.pi / cg.M i i') = m * scale i') :
    (n : ℝ) * m = 4 * Real.cos (Real.pi / cg.M i i') ^ 2 := by
  have hi := (hscale i).ne'
  have hi' := (hscale i').ne'
  have key : (n : ℝ) * scale i * (m * scale i')
      = (2 * scale i' * Real.cos (Real.pi / cg.M i i'))
        * (2 * scale i * Real.cos (Real.pi / cg.M i i')) := by
    rw [hn, hm]
  have hne : scale i * scale i' ≠ 0 := mul_ne_zero hi hi'
  apply mul_right_cancel₀ hne
  linarith [key]

/-- If `4 * cos (π / M) ^ 2` is a natural number for `M : ℕ` (with `M ≠ 1`), then
`M ∈ {0, 2, 3, 4, 6}`. This is the classical crystallographic restriction theorem, reduced to
**Niven's theorem** (`niven_angle_div_pi_eq`, already in Mathlib): the double-angle identity
turns `4 cos² (π / M) = k` into `cos ((2 / M) * π) = (k - 2) / 2`, a *rational* value at a
*rational* multiple of `π`, so Niven's theorem pins `2 / M ∈ {0, 1/3, 1/2, 2/3, 1}` (using
`0 ≤ 2/M ≤ 1`, which needs `M ≠ 1`), matching `M ∈ {0, 6, 4, 3, 2}` respectively. -/
theorem crystallographic_of_four_cos_sq_pi_div_nat {M : ℕ} (hM1 : M ≠ 1) (k : ℕ)
    (hk : (k : ℝ) = 4 * Real.cos (Real.pi / M) ^ 2) :
    M = 0 ∨ M = 2 ∨ M = 3 ∨ M = 4 ∨ M = 6 := by
  by_cases hM0 : M = 0
  · exact Or.inl hM0
  · have hM2 : 2 ≤ M := by omega
    have hMQ : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM0
    set r : ℚ := 2 / (M : ℚ) with hr_def
    have hrpi : (r : ℝ) * Real.pi = 2 * (Real.pi / M) := by
      rw [hr_def]; push_cast; ring
    have hcos2mul : Real.cos (2 * (Real.pi / M)) = ((k : ℝ) - 2) / 2 := by
      rw [Real.cos_two_mul]; linarith [hk]
    have hcos_rat : ∃ q : ℚ, Real.cos ((r : ℝ) * Real.pi) = (q : ℝ) :=
      ⟨((k : ℚ) - 2) / 2, by rw [hrpi, hcos2mul]; push_cast; ring⟩
    have hr_bound : r ∈ Set.Icc (0 : ℚ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [hr_def, div_le_one (by positivity)]
      exact_mod_cast hM2
    have hniven := niven_angle_div_pi_eq hcos_rat hr_bound
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hr_def] at hniven
    rcases hniven with h | h | h | h | h
    · exact absurd ((div_eq_zero_iff).mp h) (by simp [hMQ])
    · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      have hMeq : (M : ℚ) = 6 := by field_simp [hMQ] at h; linarith
      exact_mod_cast hMeq
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      have hMeq : (M : ℚ) = 4 := by field_simp [hMQ] at h; linarith
      exact_mod_cast hMeq
    · refine Or.inr (Or.inr (Or.inl ?_))
      have hMeq : (M : ℚ) = 3 := by field_simp [hMQ] at h; linarith
      exact_mod_cast hMeq
    · refine Or.inr (Or.inl ?_)
      have hMeq : (M : ℚ) = 2 := by field_simp [hMQ] at h; linarith
      exact_mod_cast hMeq

/-- Every pair of distinct generators has `M i i' ∈ {0, 2, 3, 4, 6}`: the two witnesses for
`(i, i')` and `(i', i)` multiply, via `generalizedCartanMatrix_mul_eq`, to
`4 * cos (π / M i i') ^ 2`, a natural number, and `crystallographic_of_four_cos_sq_pi_div_nat`
turns that into the crystallographic restriction on `M i i'`. -/
theorem HasGeneralizedCartanMatrix.isCrystallographic (h : @HasGeneralizedCartanMatrix W cg) :
    @IsCrystallographic W cg := by
  intro i i' hii'
  obtain ⟨scale, hpos, hcond⟩ := h
  obtain ⟨n, hn⟩ := hcond i i' hii'
  obtain ⟨m, hm⟩ := hcond i' i hii'.symm
  rw [cg.M.symmetric i' i] at hm
  have hprod : (n : ℝ) * m = 4 * Real.cos (Real.pi / cg.M i i') ^ 2 :=
    generalizedCartanMatrix_mul_eq scale hpos i i' n hn m hm
  exact crystallographic_of_four_cos_sq_pi_div_nat (cg.M.off_diagonal i i' hii') (n * m)
    (by exact_mod_cast hprod)

/-- Whether *this specific* proof's extracted scale (`h.choose` — whatever `Classical.choice`
happens to have produced) satisfies the standard Kac–Moody symmetrization convention: integer
squared root lengths (`h.choose i ^ 2 = sqLen i` for some `sqLen : cg.B → ℕ`), taken in lowest
terms on each connected component of the Coxeter diagram (no integer `d > 1` divides every `sqLen
i` for `i` in that component).

This is a property of one particular witness, not an existence claim: it does not assert that a
scale satisfying it exists, nor is it automatically true of every `HasGeneralizedCartanMatrix`
proof — `h.choose` may just as well be some non-minimal or irrational-valued scale. Even when it
does hold, it does not pin `h.choose` down to a canonical choice: at a multi-bond (e.g. `M i i' =
4`, where `n * m = 2` forces `(n, m) = (1, 2)` or `(2, 1)`), the discrete long/short assignment is
untouched by minimality — two scales can both be integer-squared and primitive on a component while
disagreeing by a long/short swap there. -/
def HasGeneralizedCartanMatrix.IsMinimal (h : @HasGeneralizedCartanMatrix W cg) : Prop :=
  ∃ sqLen : cg.B → ℕ,
    (∀ i, 0 < sqLen i) ∧
    (∀ i, h.choose i ^ 2 = sqLen i) ∧
    ∀ c : (coxeterGraphMatrix cg.M).ConnectedComponent,
      ¬ ∃ d : ℕ, 1 < d ∧ ∀ i, (coxeterGraphMatrix cg.M).connectedComponentMk i = c → d ∣ sqLen i

/-- `cos (π / M) = 0` exactly at `M = 2`, for *every* `M : ℕ` — no crystallographic restriction on
`M` is needed: `π / M` and `π / 2` both lie in `[0, π]`, where `cos` is injective, so matching
`cos (π / M) = 0 = cos (π / 2)` already forces `π / M = π / 2`, i.e. `M = 2`. -/
private theorem cos_pi_div_M_eq_zero_iff (M : ℕ) : Real.cos (Real.pi / M) = 0 ↔ M = 2 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · simp [hM0] at h
    · have hmem1 : Real.pi / M ∈ Set.Icc (0 : ℝ) Real.pi :=
        ⟨by positivity, div_le_self Real.pi_pos.le (by exact_mod_cast hMpos)⟩
      have hmem2 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi :=
        ⟨by positivity, div_le_self Real.pi_pos.le one_le_two⟩
      have heq : Real.pi / (M : ℝ) = Real.pi / 2 :=
        Real.injOn_cos hmem1 hmem2 (by rw [h, Real.cos_pi_div_two])
      rw [div_eq_div_iff (by exact_mod_cast hMpos.ne') two_ne_zero] at heq
      have h2 : (2 : ℝ) = M := mul_left_cancel₀ Real.pi_ne_zero heq
      exact_mod_cast h2.symm
  · rintro rfl
    norm_num [Real.cos_pi_div_two]

/-- The integer witness in `HasGeneralizedCartanMatrix`'s defining condition vanishes exactly when
`M i i' = 2` (i.e. the two generators commute), and is otherwise nonzero — since
`cos (π / M i i') = 0` exactly at `M i i' = 2`, and `scale` is everywhere positive. -/
private theorem generalizedCartanMatrix_witness_eq_zero_iff (i i' : cg.B)
    (scale : cg.B → ℝ) (hscale : ∀ i, 0 < scale i) (n : ℕ)
    (hn : 2 * scale i' * Real.cos (Real.pi / cg.M i i') = n * scale i) :
    n = 0 ↔ cg.M i i' = 2 := by
  rw [← cos_pi_div_M_eq_zero_iff (cg.M i i')]
  constructor
  · intro h0
    subst h0
    have hn' : 2 * scale i' * Real.cos (Real.pi / cg.M i i') = 0 := by rw [hn]; norm_num
    have h2 : (2 : ℝ) * scale i' ≠ 0 := mul_ne_zero two_ne_zero (hscale i').ne'
    exact (mul_eq_zero.mp hn').resolve_left h2
  · intro hcos
    rw [hcos, mul_zero] at hn
    have := (mul_eq_zero.mp hn.symm).resolve_right (hscale i).ne'
    exact_mod_cast this

/-- Excluding `M i i' = 0` (the infinite-dihedral case) pins the ordered pair of witnesses `(n, m)`
for `(i, i')` and `(i', i)` down to one of only *six* possibilities, two at a time per remaining
crystallographic value of `M i i'`: `M i i' = 2` forces `(n, m) = (0, 0)`; `M i i' = 3` forces
`(n, m) = (1, 1)` (`n * m = 1` leaves no room for a long/short distinction); `M i i' = 4` allows
`(n, m) = (1, 2)` or `(2, 1)` (the long/short choice); `M i i' = 6` allows `(n, m) = (1, 3)` or
`(3, 1)`. Without excluding `M i i' = 0`, a seventh, ambiguous case (`M i i' = 0`, `n * m = 4`,
hence `(n, m) ∈ {(1, 4), (2, 2), (4, 1)}`) would also be possible. -/
theorem generalizedCartanMatrix_pair_mem_of_ne_zero
    (scale : cg.B → ℝ) (hscale : ∀ i, 0 < scale i) (i i' : cg.B) (hii' : i ≠ i')
    (n : ℕ) (hn : 2 * scale i' * Real.cos (Real.pi / cg.M i i') = n * scale i)
    (m : ℕ) (hm : 2 * scale i * Real.cos (Real.pi / cg.M i i') = m * scale i')
    (hM0 : cg.M i i' ≠ 0) :
    (n = 0 ∧ m = 0) ∨ (n = 1 ∧ m = 1) ∨ (n = 1 ∧ m = 2) ∨ (n = 2 ∧ m = 1) ∨
      (n = 1 ∧ m = 3) ∨ (n = 3 ∧ m = 1) := by
  have hprod : (n : ℝ) * m = 4 * Real.cos (Real.pi / cg.M i i') ^ 2 :=
    generalizedCartanMatrix_mul_eq scale hscale i i' n hn m hm
  rcases crystallographic_of_four_cos_sq_pi_div_nat (cg.M.off_diagonal i i' hii') (n * m)
      (by exact_mod_cast hprod) with h0 | h2 | h3 | h4 | h6
  · exact absurd h0 hM0
  · have hm' : 2 * scale i * Real.cos (Real.pi / cg.M i' i) = m * scale i' := by
      rw [cg.M.symmetric i' i]; exact hm
    have h2' : cg.M i' i = 2 := by rw [cg.M.symmetric i' i]; exact h2
    exact Or.inl ⟨(generalizedCartanMatrix_witness_eq_zero_iff i i' scale hscale n hn).mpr h2,
      (generalizedCartanMatrix_witness_eq_zero_iff i' i scale hscale m hm').mpr h2'⟩
  · have hcos : Real.cos (Real.pi / cg.M i i') = 1 / 2 := by
      rw [h3]; norm_num [Real.cos_pi_div_three]
    rw [hcos] at hprod
    have hnm : n * m = 1 := by
      have : (n : ℝ) * m = 1 := by rw [hprod]; norm_num
      exact_mod_cast this
    have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hnm
    have hnle : n ≤ 1 := Nat.le_of_dvd (by norm_num) ⟨m, hnm.symm⟩
    interval_cases n; omega
  · have hcos : Real.cos (Real.pi / cg.M i i') = Real.sqrt 2 / 2 := by
      rw [h4]; norm_num [Real.cos_pi_div_four]
    rw [hcos] at hprod
    have hnm : n * m = 2 := by
      have h2sq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]; norm_num
      have : (n : ℝ) * m = 2 := by rw [hprod, h2sq]; norm_num
      exact_mod_cast this
    have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hnm
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by simp [h] at hnm
    have hnle : n ≤ 2 := Nat.le_of_dvd (by norm_num) ⟨m, hnm.symm⟩
    interval_cases n <;> omega
  · have hcos : Real.cos (Real.pi / cg.M i i') = Real.sqrt 3 / 2 := by
      rw [h6]; norm_num [Real.cos_pi_div_six]
    rw [hcos] at hprod
    have hnm : n * m = 3 := by
      have h3sq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
      have : (n : ℝ) * m = 3 := by rw [hprod, h3sq]; norm_num
      exact_mod_cast this
    have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hnm
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by simp [h] at hnm
    have hnle : n ≤ 3 := Nat.le_of_dvd (by norm_num) ⟨m, hnm.symm⟩
    interval_cases n <;> omega

/-- A **symmetrizable generalized Cartan matrix** in the Kac–Moody sense: an integer matrix on a
generating set `B` with `2` on the diagonal, nonpositive off-diagonal entries, and the "symmetric
vanishing" condition `a i i' = 0 ↔ a i' i = 0` off the diagonal — together with a choice of
symmetrizing constants `d` witnessing symmetrizability. (Not every generalized Cartan matrix in the
classical sense is symmetrizable; requiring `d`/`d_symm` here means this structure only ever
represents the symmetrizable ones — which is all that ever arises from a Coxeter system's
`HasGeneralizedCartanMatrix`, via `HasGeneralizedCartanMatrix.cartanMatrix`.) -/
structure SymmetrizableGeneralizedCartanMatrix (B : Type*) where
  /-- The matrix entries. -/
  a : B → B → ℤ
  /-- The diagonal is always `2`. -/
  diag : ∀ i, a i i = 2
  /-- Off-diagonal entries are nonpositive. -/
  off_diag_nonpos : ∀ i i', i ≠ i' → a i i' ≤ 0
  /-- An off-diagonal entry vanishes iff its "partner" does. -/
  off_diag_zero_iff : ∀ i i', i ≠ i' → (a i i' = 0 ↔ a i' i = 0)
  /-- Symmetrizing constants, as a *ray* `Module.Ray ℝ (B → ℝ)` (nonzero vectors up to a
  *positive* scalar) rather than a bare vector: only the *ratios* `d i / d i'` matter for `d_symm`
  below, quotienting by the positive overall scalar also rules out the vacuous `d = 0`, and using
  `Module.Ray` instead of the finer projective space `ℙ ℝ (B → ℝ)` avoids conflating a valid
  positive `d` with `-d` (a genuinely different, disallowed sign choice). When `B` is empty, `B → ℝ`
  has only the zero vector, so `Module.Ray ℝ (B → ℝ)` itself has no elements — the left summand
  records a proof of `IsEmpty B` to cover exactly that case, where there is nothing to symmetrize
  anyway. -/
  d : PLift (IsEmpty B) ⊕ Module.Ray ℝ (B → ℝ)
  /-- The `d`'s symmetrize `a` (vacuously, if `B` is empty). -/
  d_symm : d.elim (fun _ => True)
    fun p => ∀ i i', p.someVector i * (a i i' : ℝ) = p.someVector i' * (a i' i : ℝ)

namespace SymmetrizableGeneralizedCartanMatrix

variable {B : Type*} (M : SymmetrizableGeneralizedCartanMatrix B)

/-- The symmetrizing value at `i`
read off a representative vector of the ray `M.d`
Because i is provided, this is not in the
vacuous empty B case. -/
noncomputable def dVal (i : B) : ℝ := M.d.elim (fun _ => 0) fun p => p.someVector i

/-- The **symmetrized matrix** `S := D * A`
i.e. `S i i' = d_i * a i i'`.
d_i is chosen with someVector so it should only
be interpreted literally up to scaling. -/
noncomputable def S (i i' : B) : ℝ := M.dVal i * (M.a i i' : ℝ)

/-- `S` is symmetric
this is exactly `d_symm` restated in terms of `dVal`/`S`.
Having `i : B` in hand already rules out `B` being empty,
so `M.d` can only be the `Sum.inr` (ray) branch. -/
theorem S_symm (i i' : B) : M.S i i' = M.S i' i := by
  have hd := M.d_symm
  unfold S dVal
  rcases hM : M.d with h | p
  · exact h.down.elim i
  · rw [hM] at hd; simpa using hd i i'

open Classical in
/-- `S` realized as a bilinear form on the finitely-supported functions `B →₀ ℝ`
via the standard basis — mirroring `Coxeter.bil`.
Working with `B →₀ ℝ` (not `B → ℝ`) is what lets this make sense
even when the generating set `B` is infinite. -/
noncomputable def bil : LinearMap.BilinForm ℝ (B →₀ ℝ) :=
  Matrix.toBilin Finsupp.basisSingleOne M.S

/-- `S` is positive semidefinite. -/
def IsPosSemidef : Prop := M.bil.IsPosSemidef

/-- `S` is positive definite
stated, as with `Coxeter.IsFiniteCoxeter`
as positive semidefinite and nondegenerate.
(`IsPosDef` isn't a separate notion in Mathlib for bilinear forms). -/
def IsPosDef : Prop := M.bil.IsPosSemidef ∧ M.bil.Nondegenerate

end SymmetrizableGeneralizedCartanMatrix

/-- `scale i ^ 2` is nonzero as soon as `B` is nonempty (`scale` is everywhere positive). -/
theorem generalizedCartanMatrix_scaleSq_ne_zero
    (scale : cg.B → ℝ) (hscale : ∀ i, 0 < scale i) (hB : ¬ IsEmpty cg.B) :
    (fun i => scale i ^ 2 : cg.B → ℝ) ≠ 0 := by
  rw [ne_eq, funext_iff]
  push Not
  obtain ⟨i⟩ := not_isEmpty_iff.mp hB
  exact ⟨i, by have := hscale i; positivity⟩

open Classical in
/-- The `d` field of `GeneralizedCartanMatrix`, built from a `HasGeneralizedCartanMatrix`-style
`scale`: the ray `⟦scale i ^ 2⟧` when `B` is nonempty, or a record of `IsEmpty B` otherwise. -/
noncomputable def generalizedCartanMatrix_dValue
    (scale : cg.B → ℝ) (hscale : ∀ i, 0 < scale i) :
    PLift (IsEmpty cg.B) ⊕ Module.Ray ℝ (cg.B → ℝ) :=
  if hB : IsEmpty cg.B then Sum.inl ⟨hB⟩
  else Sum.inr (rayOfNeZero ℝ (fun i => scale i ^ 2)
    (generalizedCartanMatrix_scaleSq_ne_zero scale hscale hB))

/-- `someVector` of a ray built from a nonzero vector `v` is `t • v` for some *positive* `t`: `v`
and `someVector` give the same ray (`someVector_ray`), so they're `SameRay`, and
`SameRay.exists_pos_right` turns that into a positive scalar. -/
private theorem exists_pos_smul_someVector_eq
    {v : cg.B → ℝ} (hv : v ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (rayOfNeZero ℝ v hv).someVector = t • v := by
  have hsame : SameRay ℝ (rayOfNeZero ℝ v hv).someVector v :=
    (ray_eq_iff (rayOfNeZero ℝ v hv).someVector_ne_zero hv).mp
      (rayOfNeZero ℝ v hv).someVector_ray
  exact hsame.exists_pos_right (rayOfNeZero ℝ v hv).someVector_ne_zero hv

open Classical in
/-- `generalizedCartanMatrix_dValue` symmetrizes the off-diagonal entries `-n`/`-m` coming from
`scale_ii'`'s witnesses: on the nonempty branch, its representative (`someVector`) is `scale i ^ 2`
up to one common *positive* scalar `t` (`exists_pos_smul_someVector_eq`), which cancels out of the
symmetrizing equation, leaving exactly `scale_ratio_sq_eq_of_generalizedCartanMatrix_cond`. -/
theorem generalizedCartanMatrix_dValue_symm
    (scale : cg.B → ℝ) (hscale : ∀ i, 0 < scale i)
    (scale_ii' : ∀ i i' : cg.B, i ≠ i' →
      ∃ n : ℕ, 2 * scale i' * Real.cos (Real.pi / cg.M i i') = n * scale i) :
    (generalizedCartanMatrix_dValue scale hscale).elim (fun _ => True)
      fun p => ∀ i i',
        p.someVector i * ((if hii' : i = i' then (2 : ℤ) else -(scale_ii' i i' hii').choose : ℤ)
          : ℝ) =
        p.someVector i' * ((if hii' : i' = i then (2 : ℤ) else -(scale_ii' i' i hii').choose : ℤ)
          : ℝ) := by
  unfold generalizedCartanMatrix_dValue
  by_cases hB : IsEmpty cg.B
  · simp [dif_pos hB]
  · simp only [dif_neg hB, Sum.elim_inr]
    intro i i'
    by_cases hii' : i = i'
    · subst hii'; rfl
    · obtain ⟨t, ht, hteq⟩ :=
        exists_pos_smul_someVector_eq (generalizedCartanMatrix_scaleSq_ne_zero scale hscale hB)
      have hrep : ∀ j, (rayOfNeZero ℝ (fun i => scale i ^ 2)
          (generalizedCartanMatrix_scaleSq_ne_zero scale hscale hB)).someVector j =
          t * scale j ^ 2 := fun j => by rw [hteq]; rfl
      rw [hrep i, hrep i']
      simp only [dif_neg hii', dif_neg (Ne.symm hii')]
      have hn := (scale_ii' i i' hii').choose_spec
      have hm' : 2 * scale i * Real.cos (Real.pi / cg.M i i') =
          (scale_ii' i' i (Ne.symm hii')).choose * scale i' := by
        rw [← cg.M.symmetric i' i]; exact (scale_ii' i' i (Ne.symm hii')).choose_spec
      have hratio := scale_ratio_sq_eq_of_generalizedCartanMatrix_cond scale i i' _ hn _ hm'
      push_cast
      linear_combination t * (-hratio)

open Classical in
/-- Realize the generalized Cartan matrix promised by `HasGeneralizedCartanMatrix`. Its
off-diagonal entry `a i i'` is `-n`, the negation of the integer witness `n` from
`HasGeneralizedCartanMatrix` satisfying `2 * scale i' * cos (π / M i i') = n * scale i` — negated
to match the Kac–Moody sign convention `a i i' ≤ 0`, since `n ≥ 0` (as `cos (π / M i i') ≥ 0` for
every crystallographic `M i i'`, and `scale` is positive). -/
noncomputable def HasGeneralizedCartanMatrix.cartanMatrix (h : @HasGeneralizedCartanMatrix W cg) :
    SymmetrizableGeneralizedCartanMatrix cg.B :=
  let scale := h.choose
  let scale_pos := h.choose_spec.1
  let scale_ii' := h.choose_spec.2
  { a := fun i i' => if hii' : i = i' then 2 else -(scale_ii' i i' hii').choose
    diag := fun i => by simp
    off_diag_nonpos := fun i i' hii' => by
      simp only [dif_neg hii', neg_nonpos]
      exact Int.natCast_nonneg _
    off_diag_zero_iff := fun i i' hii' => by
      simp only [dif_neg hii', dif_neg (Ne.symm hii'), neg_eq_zero, Nat.cast_eq_zero]
      rw [generalizedCartanMatrix_witness_eq_zero_iff i i' scale scale_pos _
          (scale_ii' i i' hii').choose_spec,
        generalizedCartanMatrix_witness_eq_zero_iff i' i scale scale_pos _
          (scale_ii' i' i (Ne.symm hii')).choose_spec,
        cg.M.symmetric i i']
    d := generalizedCartanMatrix_dValue scale scale_pos
    d_symm := generalizedCartanMatrix_dValue_symm scale scale_pos scale_ii' }

/-- The Kac–Moody Cartan-integer formula: `a i i'` equals the usual `2⟨αᵢ', αᵢ⟩ / ⟨αᵢ, αᵢ⟩` ratio
(writing `⟨·,·⟩` for `bil`), computed on the *rescaled* roots `scale i • stdBasis i`. The numerator
is symmetric in `i`/`i'` (`bil` is a symmetric form), and the denominator `⟨αᵢ,αᵢ⟩ = scale i ^ 2` is
positive regardless of which root's self-pairing is used to normalize — so the sign of `a i i'`
comes entirely from the numerator, matching `off_diag_nonpos`. -/
private theorem HasGeneralizedCartanMatrix.cartanMatrix_apply_eq
  (h : @HasGeneralizedCartanMatrix W cg) (i i' : cg.B) (hii' : i ≠ i') :
    (h.cartanMatrix.a i i' : ℝ) =
    2 * bil (h.choose i' • stdBasis i') (h.choose i • stdBasis i) /
      bil (h.choose i • stdBasis i) (h.choose i • stdBasis i) := by
  have hn := (h.choose_spec.2 i i' hii').choose_spec
  have hi := (h.choose_spec.1 i).ne'
  classical
  have key : h.cartanMatrix.a i i' = -(h.choose_spec.2 i i' hii').choose := by
    change (if hii' : i = i' then (2 : ℤ) else -(h.choose_spec.2 i i' hii').choose) = _
    rw [dif_neg hii']
  have hbil_off : bil (stdBasis i') (stdBasis i) = -Real.cos (Real.pi / cg.M i i') := by
    rw [bil_eq, cg.M.symmetric i' i]
  have hden : bil (h.choose i • stdBasis i) (h.choose i • stdBasis i)
      = h.choose i * h.choose i := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, bil_diag, mul_one]
  have hnum : bil (h.choose i' • stdBasis i') (h.choose i • stdBasis i)
      = -(h.choose i' * h.choose i * Real.cos (Real.pi / cg.M i i')) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hbil_off]
    ring
  rw [key, hden, hnum, eq_div_iff (mul_ne_zero hi hi)]
  push_cast
  linear_combination h.choose i * hn

/-- The concrete payoff of `cartanMatrix_apply_eq`: the reflection formula `s_i(αᵢ') = αᵢ' -
a_{i i'} αᵢ`, valid for *every* pair `i, i'` (including `i = i'`, via `diag`). Since
`h.cartanMatrix.a i i' : ℤ`, this exhibits `geomRepAux i` sending each rescaled root
`scale i' • stdBasis i'` to an integer combination of the rescaled roots `scale i • stdBasis i` and
`scale i' • stdBasis i'` — i.e. `geomRepAux i` preserves the lattice `ℤ`-spanned by
`{scale j • stdBasis j : j}`. -/
private theorem HasGeneralizedCartanMatrix.geomRepAux_smul_stdBasis
  (h : @HasGeneralizedCartanMatrix W cg) (i i' : cg.B) :
    geomRepAux i (h.choose i' • stdBasis i') =
    h.choose i' • stdBasis i' - (h.cartanMatrix.a i i' : ℝ) • (h.choose i • stdBasis i) := by
  have hi := (h.choose_spec.1 i).ne'
  have hscalar : 2 * bil (stdBasis i) (h.choose i' • stdBasis i')
      = (h.cartanMatrix.a i i' : ℝ) * h.choose i := by
    by_cases hii' : i = i'
    · subst hii'
      rw [h.cartanMatrix.diag, map_smul, smul_eq_mul, bil_diag]
      push_cast; ring
    · have key := h.cartanMatrix_apply_eq i i' hii'
      have hden : bil (h.choose i • stdBasis i) (h.choose i • stdBasis i)
          = h.choose i * h.choose i := by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, bil_diag, mul_one]
      rw [hden, eq_div_iff (mul_ne_zero hi hi)] at key
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at key
      rw [bil_isSymm.eq (stdBasis i') (stdBasis i)] at key
      apply mul_right_cancel₀ hi
      simp only [map_smul, smul_eq_mul]
      linear_combination -key
  rw [geomRepAux_apply, hscalar, mul_smul]

/-- The `ℤ`-lattice spanned by the rescaled roots `scale j • stdBasis j` promised by
`HasGeneralizedCartanMatrix`. -/
noncomputable def HasGeneralizedCartanMatrix.lattice (h : @HasGeneralizedCartanMatrix W cg) :
    Submodule ℤ (V W) :=
  Submodule.span ℤ (Set.range fun j => h.choose j • stdBasis j)

/-- `geomRepAux i` preserves the *whole* lattice `h.lattice`, not just its generators: since
`geomRepAux i` is `ℝ`-linear (hence also `ℤ`-linear) and, by `geomRepAux_smul_stdBasis`, sends each
generator `scale i' • stdBasis i'` back into `h.lattice`, it sends the entire `ℤ`-span into itself.
This is the honest statement of lattice preservation — every simple reflection maps `h.lattice`
into `h.lattice`. -/
private theorem HasGeneralizedCartanMatrix.geomRepAux_mapsTo_lattice
  (h : @HasGeneralizedCartanMatrix W cg) (i : cg.B) :
  Set.MapsTo (geomRepAux i) h.lattice h.lattice := by
  rw [Set.mapsTo_iff_image_subset]
  change Submodule.map ((geomRepAux i).toLinearMap.restrictScalars ℤ) h.lattice ≤ h.lattice
  rw [HasGeneralizedCartanMatrix.lattice, LinearMap.map_span_le]
  rintro _ ⟨j, rfl⟩
  rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_toLinearMap, h.geomRepAux_smul_stdBasis i j,
    Int.cast_smul_eq_zsmul]
  exact sub_mem (Submodule.subset_span (Set.mem_range_self j))
    (Submodule.smul_mem _ (h.cartanMatrix.a i j) (Submodule.subset_span (Set.mem_range_self i)))

/-- `geomRep w` preserves `h.lattice` for *every* group element `w`, not just simple reflections:
the simple reflections generate `W` (`CoxeterSystem.simple_induction`), lattice preservation holds
at the identity and at each simple reflection (`geomRepAux_mapsTo_lattice`), and is closed under
multiplication (composition of `Set.MapsTo`s) — so it holds everywhere. This is the honest,
whole-group statement of lattice preservation. -/
theorem HasGeneralizedCartanMatrix.geomRep_mapsTo_lattice (h : @HasGeneralizedCartanMatrix W cg)
    (w : W) : Set.MapsTo (geomRep w) h.lattice h.lattice := by
  refine cg.cs.simple_induction (p := fun w => Set.MapsTo (geomRep w) h.lattice h.lattice)
    w (fun i => ?_) ?_ (fun w w' hw hw' => ?_)
  · dsimp only
    rw [geomRep_simple]
    exact h.geomRepAux_mapsTo_lattice i
  · dsimp only
    rw [map_one]
    exact Set.mapsTo_id _
  · dsimp only at hw hw' ⊢
    rw [map_mul]
    exact hw.comp hw'

end Coxeter
