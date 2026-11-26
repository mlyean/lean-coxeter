module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Reading `Fin`-indexed families at natural-number indices

For a family `y : Fin N → M`, `Coxeter.finNatGet y k` reads `y` at the natural number `k`, and
is `0` out of range. Sums over `Fin N` of indicators of a single index then collapse to a
`finNatGet`, which keeps index arithmetic in `ℕ` (where `omega` applies) rather than in `Fin N`.

## Main definitions

* `Coxeter.finNatGet`

## Main statements

* `Coxeter.sum_ite_and_val_eq`, `Coxeter.sum_ite_val_eq`, and their weighted versions
  `Coxeter.sum_mul_ite_and_val_eq`, `Coxeter.sum_mul_ite_val_eq`
-/

@[expose] public section

namespace Coxeter

variable {N : ℕ} {M : Type*}

/-- `y` read at the natural-number index `k`, `0` out of range. -/
def finNatGet [Zero M] (y : Fin N → M) (k : ℕ) : M :=
  if h : k < N then y ⟨k, h⟩ else 0

theorem finNatGet_val [Zero M] (y : Fin N → M) (i : Fin N) : finNatGet y i = y i :=
  dite_eq_left i.isLt

theorem finNatGet_of_lt [Zero M] (y : Fin N → M) {k : ℕ} (hk : k < N) :
    finNatGet y k = y ⟨k, hk⟩ :=
  dite_eq_left hk

theorem finNatGet_mul_const {R : Type*} [MulZeroClass R] (y : Fin N → R) (c : R) (k : ℕ) :
    finNatGet (fun i ↦ y i * c) k = finNatGet y k * c := by
  unfold finNatGet
  split_ifs <;> simp

/-- Summing against the indicator of a single index, given by its value in `ℕ`, guarded by a
condition not depending on the summation variable. -/
theorem sum_ite_and_val_eq [AddCommMonoid M] (P : Prop) [Decidable P] (k : ℕ) (f : Fin N → M) :
    (∑ i : Fin N, if P ∧ (i : ℕ) = k then f i else 0) = if P then finNatGet f k else 0 := by
  by_cases hP : P
  · simp only [hP, true_and, ↓reduceIte, finNatGet]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨k, h⟩ (fun j _ hj ↦ ite_eq_right fun hjk ↦ hj (Fin.ext hjk))
        (fun h' ↦ absurd (Finset.mem_univ _) h'), ite_eq_left rfl]
    · exact Finset.sum_eq_zero fun j _ ↦ ite_eq_right fun (hjk : (j : ℕ) = k) ↦ h (hjk ▸ j.isLt)
  · simp only [hP, false_and, ↓reduceIte, Finset.sum_const_zero]

/-- Summing against the indicator of a single index, given by its value in `ℕ`. -/
theorem sum_ite_val_eq [AddCommMonoid M] (k : ℕ) (f : Fin N → M) :
    (∑ i : Fin N, if (i : ℕ) = k then f i else 0) = finNatGet f k := by
  simpa using sum_ite_and_val_eq True k f

/-- `sum_ite_and_val_eq` against a weight `f`, with the indicator scaled by `c`. -/
theorem sum_mul_ite_and_val_eq {R : Type*} [NonUnitalNonAssocSemiring R] (P : Prop) [Decidable P]
    (k : ℕ) (f : Fin N → R) (c : R) :
    (∑ i : Fin N, f i * (if P ∧ (i : ℕ) = k then c else 0)) =
      if P then finNatGet f k * c else 0 := by
  simp only [mul_ite, mul_zero]
  rw [sum_ite_and_val_eq, finNatGet_mul_const]

/-- `sum_ite_val_eq` against a weight `f`, with the indicator scaled by `c`. -/
theorem sum_mul_ite_val_eq {R : Type*} [NonUnitalNonAssocSemiring R] (k : ℕ) (f : Fin N → R)
    (c : R) : (∑ i : Fin N, f i * (if (i : ℕ) = k then c else 0)) = finNatGet f k * c := by
  simp only [mul_ite, mul_zero]
  rw [sum_ite_val_eq, finNatGet_mul_const]

end Coxeter
