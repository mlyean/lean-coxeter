module

public import Coxeter.SpecialFeatures

/-!
# Tridiagonal sum-of-squares identities

Generic algebraic lemmas about tridiagonal ("path graph") quadratic forms, shared by the
positive-definiteness arguments for `Coxeter.FiniteOrAffine.TypeA` and
`Coxeter.FiniteOrAffine.TypeBC`.

The tridiagonal quadratic form `Q(y) = ∑_{i<m+1} y_i^2 - ∑_{i<m} y_i * y_{i+1}` (the diagonal `1`s
and off-diagonal `-1/2`s of a path-shaped Coxeter matrix, doubled) is a sum of squares:
`2 * Q(y) = y_0^2 + y_m^2 + ∑ (y_i - y_{i+1})^2`. Reading off `≥ 0` gives `IsPosSemidef`; forcing
every square to vanish when the form is `0` gives `Nondegenerate`. Type `A`'s Coxeter matrix *is*
this tridiagonal form outright.

`sos_identity_lastEdge`/`lastEdgeEntry`/`lastEdgeEntry_sum_range_double` generalize this further to
a path graph on `n + 2` vertices whose *last* edge (between generators `n` and `n + 1`) has its
weight changed from `-1/2` to an arbitrary `-k/2`. Completing the square on that last edge only
fully collapses to a clean sum of squares when `k = √2` (used by
`Coxeter.FiniteOrAffine.TypeBC`, type `B`/`C`'s Coxeter matrix); for other `k` an extra
`(2 - k ^ 2) * y (n + 1) ^ 2` correction term remains.

## Main statements

* `Coxeter.sos_identity`
* `Coxeter.pathEntry_sum_range_double`
* `Coxeter.sos_identity_lastEdge`
* `Coxeter.lastEdgeEntry_sum_range_double`
-/

@[expose] public section

namespace Coxeter

/-- Sum-of-squares identity for a tridiagonal quadratic form. -/
theorem sos_identity
  {R : Type*} [CommRing R] (y : ℕ → R) (m : ℕ) :
    2 * (∑ i ∈ Finset.range (m + 1), (y i) ^ 2 - ∑ i ∈ Finset.range m, y i * y (i + 1))
      = y 0 ^ 2 + y m ^ 2 + ∑ i ∈ Finset.range m, (y i - y (i + 1)) ^ 2 := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
      rw [Finset.sum_range_succ (f := fun i => (y i) ^ 2),
        Finset.sum_range_succ (f := fun i => y i * y (i + 1)),
        Finset.sum_range_succ (f := fun i => (y i - y (i + 1)) ^ 2)]
      linear_combination ih

/-- The entry function of the (doubled) tridiagonal ("path graph") quadratic form: `1` on the
diagonal, `-1/2` on adjacent off-diagonal entries, `0` elsewhere. -/
noncomputable def pathEntry (i j : ℕ) : ℚ :=
  if i = j then 1 else if j + 1 = i ∨ i + 1 = j then -(1 / 2) else 0

/-- The double sum against `pathEntry` collapses to the tridiagonal quadratic form `Q(y)` from
`sos_identity`: only the diagonal and immediately-adjacent entries of `pathEntry` are nonzero. -/
theorem pathEntry_sum_range_double (y : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1), y i * y j * pathEntry i j)
      = ∑ i ∈ Finset.range (m + 1), (y i) ^ 2 - ∑ i ∈ Finset.range m, y i * y (i + 1) := by
  induction m with
  | zero => simp [pathEntry]; ring
  | succ m ih =>
      have hL : ∀ i ∈ Finset.range (m + 1),
          y i * y (m + 1) * pathEntry i (m + 1) =
            if i = m then y i * y (m + 1) * (-(1 / 2)) else 0 := by
        intro i hi
        simp only [Finset.mem_range] at hi
        by_cases hc : i = m
        · subst hc
          simp [pathEntry]
        · rw [if_neg hc]
          unfold pathEntry
          rw [if_neg (by omega : ¬ i = m + 1),
            if_neg (by omega : ¬ ((m + 1) + 1 = i ∨ i + 1 = m + 1))]
          ring
      have hR : ∀ j ∈ Finset.range (m + 1),
          y (m + 1) * y j * pathEntry (m + 1) j =
            if j = m then y (m + 1) * y j * (-(1 / 2)) else 0 := by
        intro j hj
        simp only [Finset.mem_range] at hj
        by_cases hc : j = m
        · subst hc
          simp [pathEntry]
        · rw [if_neg hc]
          unfold pathEntry
          rw [if_neg (by omega : ¬ (m + 1) = j),
            if_neg (by omega : ¬ (j + 1 = m + 1 ∨ (m + 1) + 1 = j))]
          ring
      have hmem : m ∈ Finset.range (m + 1) := Finset.self_mem_range_succ m
      have expand : ∀ i ∈ Finset.range (m + 1),
          ∑ j ∈ Finset.range (m + 1 + 1), y i * y j * pathEntry i j
            = (∑ j ∈ Finset.range (m + 1), y i * y j * pathEntry i j)
              + (if i = m then y i * y (m + 1) * (-(1 / 2)) else 0) := by
        intro i hi
        rw [Finset.sum_range_succ, hL i hi]
      rw [Finset.sum_range_succ (f := fun i =>
          ∑ j ∈ Finset.range (m + 1 + 1), y i * y j * pathEntry i j),
        Finset.sum_congr rfl expand, Finset.sum_add_distrib,
        Finset.sum_ite_eq' (Finset.range (m + 1)) m
          (fun i => y i * y (m + 1) * (-(1 / 2 : ℝ))),
        if_pos hmem]
      rw [Finset.sum_range_succ (f := fun j => y (m + 1) * y j * pathEntry (m + 1) j),
        Finset.sum_congr rfl hR,
        Finset.sum_ite_eq' (Finset.range (m + 1)) m
          (fun j => y (m + 1) * y j * (-(1 / 2 : ℝ))),
        if_pos hmem]
      have hdiag : pathEntry (m + 1) (m + 1) = 1 := if_pos rfl
      rw [hdiag, ih, Finset.sum_range_succ (f := fun i => (y i) ^ 2) (n := m + 1),
        Finset.sum_range_succ (f := fun i => y i * y (i + 1)) (n := m)]
      ring

/-! ### A path graph with one modified edge

The same tridiagonal quadratic form, but on `n + 2` vertices, with the *last* edge (between
generators `n` and `n + 1`) reweighted from `-1/2` to `-k/2` for an arbitrary `k : ℝ`. -/

/-- Sum-of-squares identity for the tridiagonal (doubled) quadratic form on `n + 2` generators
whose last edge `(n, n + 1)` has weight `-k/2` instead of `-1/2`: `sos_identity` on the first
`n + 1` generators, plus completing the square on the last edge. The leftover
`(2 - k ^ 2) * y (n + 1) ^ 2` term vanishes exactly when `k ^ 2 = 2`. -/
theorem sos_identity_lastEdge (n : ℕ) (y : ℕ → ℝ) (k : ℝ) :
    2 * (∑ i ∈ Finset.range (n + 2), (y i) ^ 2 - ∑ i ∈ Finset.range n, y i * y (i + 1)
        - k * y n * y (n + 1))
      = y 0 ^ 2 + ∑ i ∈ Finset.range n, (y i - y (i + 1)) ^ 2
        + (y n - k * y (n + 1)) ^ 2 + (2 - k ^ 2) * y (n + 1) ^ 2 := by
  have hA := sos_identity y n
  rw [Finset.sum_range_succ (f := fun i => (y i) ^ 2) (n := n + 1)]
  linear_combination hA

/-- The entry function of the (doubled) tridiagonal quadratic form on `n + 2` generators, with the
last edge `(n, n + 1)` reweighted from `-1/2` to `-k/2`: `1` on the diagonal, `-k/2` on the last
edge, `-1/2` on the other adjacent off-diagonal entries, `0` elsewhere. -/
noncomputable def lastEdgeEntry (n : ℕ) (k : ℝ) (i j : ℕ) : ℝ :=
  if i = j then 1
  else if (i = n ∧ j = n + 1) ∨ (j = n ∧ i = n + 1) then -(k / 2)
  else if j + 1 = i ∨ i + 1 = j then -(1 / 2) else 0

/-- `lastEdgeEntry` is symmetric: its diagonal, special-pair, and adjacency conditions are all
symmetric under swapping the two indices. -/
theorem lastEdgeEntry_symm (n : ℕ) (k : ℝ) (i j : ℕ) :
    lastEdgeEntry n k i j = lastEdgeEntry n k j i := by
  unfold lastEdgeEntry
  by_cases hij : i = j
  · simp [hij]
  · rw [if_neg hij, if_neg (Ne.symm hij)]
    by_cases hspec : (i = n ∧ j = n + 1) ∨ (j = n ∧ i = n + 1)
    · rw [if_pos hspec, if_pos (Or.symm hspec)]
    · rw [if_neg hspec, if_neg (fun h => hspec (Or.symm h))]
      by_cases hadj : j + 1 = i ∨ i + 1 = j
      · rw [if_pos hadj, if_pos (Or.symm hadj)]
      · rw [if_neg hadj, if_neg (fun h => hadj (Or.symm h))]

theorem lastEdgeEntry_diag (n : ℕ) (k : ℝ) (i : ℕ) : lastEdgeEntry n k i i = 1 := by
  unfold lastEdgeEntry; rw [if_pos rfl]

theorem lastEdgeEntry_last_row (n : ℕ) (k : ℝ) {i : ℕ} (hi : i < n) :
    lastEdgeEntry n k i (n + 1) = 0 := by
  unfold lastEdgeEntry
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem lastEdgeEntry_special (n : ℕ) (k : ℝ) : lastEdgeEntry n k n (n + 1) = -(k / 2) := by
  unfold lastEdgeEntry
  rw [if_neg (by omega), if_pos (Or.inl ⟨rfl, rfl⟩)]

/-- Away from the last edge, `lastEdgeEntry` agrees with `pathEntry`. -/
theorem lastEdgeEntry_eq_pathEntry (n : ℕ) (k : ℝ) {i j : ℕ} (hi : i < n + 1) (hj : j < n + 1) :
    lastEdgeEntry n k i j = (pathEntry i j : ℝ) := by
  unfold lastEdgeEntry pathEntry
  have hspec : ¬((i = n ∧ j = n + 1) ∨ (j = n ∧ i = n + 1)) := by omega
  by_cases hij : i = j
  · simp [hij]
  · rw [if_neg hij, if_neg hij, if_neg hspec]
    split_ifs <;> norm_num

/-- The double sum against `lastEdgeEntry` collapses to the tridiagonal quadratic form from
`sos_identity_lastEdge`: on the first `n + 1` generators it agrees with `pathEntry`
(`pathEntry_sum_range_double`), and the remaining corner terms involving generator `n + 1` collapse
(via `lastEdgeEntry_symm`) to twice the single `(n, n + 1)`-entry contribution plus the diagonal. -/
theorem lastEdgeEntry_sum_range_double (n : ℕ) (k : ℝ) (y : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 2), ∑ j ∈ Finset.range (n + 2), y i * y j * lastEdgeEntry n k i j)
      = ∑ i ∈ Finset.range (n + 2), (y i) ^ 2 - ∑ i ∈ Finset.range n, y i * y (i + 1)
        - k * y n * y (n + 1) := by
  have hsquare : ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      y i * y j * lastEdgeEntry n k i j
      = ∑ i ∈ Finset.range (n + 1), (y i) ^ 2 - ∑ i ∈ Finset.range n, y i * y (i + 1) := by
    rw [← pathEntry_sum_range_double y n]
    exact Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj =>
      by rw [lastEdgeEntry_eq_pathEntry n k (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]))
  have hcorner : ∀ i ∈ Finset.range (n + 1),
      y i * y (n + 1) * lastEdgeEntry n k i (n + 1) =
        if i = n then y i * y (n + 1) * (-(k / 2)) else 0 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    by_cases hc : i = n
    · rw [if_pos hc, hc, lastEdgeEntry_special]
    · rw [if_neg hc, lastEdgeEntry_last_row n k (show i < n by omega)]; ring
  have hrow : ∑ i ∈ Finset.range (n + 1), y i * y (n + 1) * lastEdgeEntry n k i (n + 1)
      = y n * y (n + 1) * (-(k / 2)) := by
    rw [Finset.sum_congr rfl hcorner,
      Finset.sum_ite_eq' (Finset.range (n + 1)) n (fun i => y i * y (n + 1) * (-(k / 2))),
      if_pos (Finset.self_mem_range_succ n)]
  have hcol : ∑ j ∈ Finset.range (n + 1), y (n + 1) * y j * lastEdgeEntry n k (n + 1) j
      = y n * y (n + 1) * (-(k / 2)) := by
    rw [← hrow]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [lastEdgeEntry_symm n k (n + 1) j]
    ring
  have hstep : (∑ i ∈ Finset.range (n + 2), ∑ j ∈ Finset.range (n + 2),
      y i * y j * lastEdgeEntry n k i j)
      = (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          y i * y j * lastEdgeEntry n k i j)
        + (∑ i ∈ Finset.range (n + 1), y i * y (n + 1) * lastEdgeEntry n k i (n + 1))
        + ((∑ j ∈ Finset.range (n + 1), y (n + 1) * y j * lastEdgeEntry n k (n + 1) j)
           + y (n + 1) * y (n + 1) * lastEdgeEntry n k (n + 1) (n + 1)) := by
    rw [Finset.sum_range_succ (f := fun i =>
      ∑ j ∈ Finset.range (n + 2), y i * y j * lastEdgeEntry n k i j) (n := n + 1)]
    congr 1
    · rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range (n + 1)) =>
        Finset.sum_range_succ (f := fun j => y i * y j * lastEdgeEntry n k i j) (n := n + 1)),
        Finset.sum_add_distrib]
    · exact Finset.sum_range_succ (f := fun j => y (n + 1) * y j * lastEdgeEntry n k (n + 1) j)
        (n := n + 1)
  rw [hstep, hsquare, hrow, hcol, lastEdgeEntry_diag,
    Finset.sum_range_succ (f := fun i => (y i) ^ 2) (n := n + 1)]
  ring

end Coxeter
