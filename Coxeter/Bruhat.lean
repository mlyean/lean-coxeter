import Coxeter.StrongExchange

/-!
# Bruhat order

This file defines the Bruhat order.

## Main definitions

* `Coxeter.le` : The Bruhat order

## References

* [bjorner2005] A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*

-/

namespace Coxeter

open List CoxeterSystem CoxeterGroup

variable {W : Type*} [CoxeterGroup W]

inductive le : W → W → Prop
  | rfl (u : W) : le u u
  | step (u v w : W) (h1 : le u v) (h2 : cs.IsReflection (w * v⁻¹))
      (h3 : cs.length v < cs.length w) : le u w

instance : LE W where
  le := le

def lt (u w : W) : Prop := u ≤ w ∧ u ≠ w

instance : LT W where
  lt := lt

theorem length_le_of_bruhat_le {u w : W} (h : u ≤ w) : cs.length u ≤ cs.length w := by
  induction h with
  | rfl => apply le_refl
  | step => grind

theorem length_lt_of_bruhat_lt {u w : W} (h : u < w) : cs.length u < cs.length w := by
  have := length_le_of_bruhat_le h.1
  suffices cs.length u ≠ cs.length w by grind
  cases h.1 with
  | rfl =>
      have := h.2
      contradiction
  | step _ _ h4 =>
      have := length_le_of_bruhat_le h4
      grind

instance : PartialOrder W where
  le_refl := le.rfl
  le_trans := by
    intro u v w huv hvw
    induction hvw with
    | rfl => tauto
    | step v w _ h1 h2 ih => exact le.step u v w ih h1 h2
  lt_iff_le_not_ge := by
    intro u w
    constructor
    · intro h
      constructor
      · exact h.1
      · intro h2
        have := length_lt_of_bruhat_lt h
        have := length_le_of_bruhat_le h2
        grind
    · intro h
      constructor
      · exact h.1
      · intro h2
        subst h2
        have := h.2
        grind
  le_antisymm := by
    intro u w h1 h2
    cases h1 with
    | rfl => rfl
    | step _ _ h3 =>
        have := length_le_of_bruhat_le h2
        have := length_le_of_bruhat_le h3
        grind

theorem lt_reflection_mul_iff {t : W} (ht : cs.IsReflection t) (w : W)
  : w < t * w ↔ cs.length w < cs.length (t * w) := by
  constructor
  · intro h
    apply length_lt_of_bruhat_lt
    exact h
  · intro h
    constructor
    · apply le.step w w (t * w) (le.rfl _)
      · rw [mul_inv_cancel_right]
        exact ht
      · exact h
    · intro h2
      rw [←h2] at h
      grind

theorem reflection_mul_lt_iff {t : W} (ht : cs.IsReflection t) (w : W)
  : t * w < w ↔ cs.length (t * w) < cs.length w := by
  have h := lt_reflection_mul_iff ht (t * w)
  rw [←mul_assoc, ht.mul_self, one_mul] at h
  exact h

theorem mul_reflection_lt_or_gt (w : W) {t : W} (ht : cs.IsReflection t) :
  t * w < w ∨ t * w > w := by
  conv in t * w > w => change w < t * w
  rw [reflection_mul_lt_iff ht, lt_reflection_mul_iff ht]
  exact Nat.lt_or_gt_of_ne (ht.length_mul_right_ne w)

def ReducedWord (w : W) := {ω : List (B W) // w = cs.wordProd ω ∧ cs.IsReduced ω}

instance {w : W} : CoeOut (ReducedWord w) (List (B W)) where
  coe := fun ω => ω.val

/-- Bjorner--Brenti Theorem 2.2.2 (only if) -/
theorem exists_reduced_subword_of_le (u w : W) (h : u ≤ w) (ω : ReducedWord w) :
  ∃ μ : ReducedWord u, μ.val <+ ω.val := by
  revert ω
  induction h with
  | rfl =>
      intro ω
      exists ω
  | step v w _ h1 h2 ih =>
      intro ω
      let t := w * v⁻¹
      change cs.IsReflection t at h1
      have h3 : w = t * v := by simp only [inv_mul_cancel_right, t]
      have h4 : cs.IsLeftInversion (cs.wordProd ω) t := by
        constructor
        · exact h1
        · rw [←ω.prop.1]
          nth_rw 1 [h3]
          rw [←mul_assoc, h1.mul_self, one_mul]
          exact h2
      have ⟨i, _, h5⟩ := strong_exchange h4
      nth_rw 1 [←ω.prop.1, h3, ←mul_assoc, h1.mul_self, one_mul] at h5
      have ⟨ω', h6, _, _⟩ := exists_reduced_subword (ω.val.eraseIdx i)
      have ⟨μ, h7⟩ := ih ⟨ω', by grind⟩
      exists μ
      calc
        μ <+ ω' := h7
        _ <+ ω.val.eraseIdx i := h6
        _ <+ ω := eraseIdx_sublist _ _

-- open Classical in
-- Bjorner--Brenti Lemma 2.2.1 -/
-- theorem reduced_subword_extend {u w : W} (ω : ReducedWord w)
--   (h1 : u ≠ cs.wordProd ω) (h2 : ∃ (μ : ReducedWord u), μ.val <+ ω.val) :
--   ∃ (ν : List (B W)), ν <+ ω ∧ cs.IsReduced ν
--     ∧ cs.wordProd ν > u ∧ ν.length = cs.length u + 1 := by
--   let P (i : ℕ) := ∃ (μ : ReducedWord u), μ.val <+ ω.val ∧ take i μ.val = take i ω.val
--   let i := Nat.findGreatest P ω.val.length
--   have h3 : P i := by
--     unfold i
--     apply Nat.findGreatest_spec (zero_le _)
--     unfold P
--     simp only [take_zero, and_true]
--     exact h2
--   have h4 : ∀ k > i, ¬ P k := by
--     intro k hk
--     cases Nat.le_or_ge k ω.val.length with
--     | inl h => exact Nat.findGreatest_is_greatest hk h
--     | inr h =>
--         intro ⟨μ, hμ⟩
--         have hμ2 : μ.val.length ≤ k := by grind
--         rw [take_of_length_le hμ2, take_of_length_le h] at hμ
--         grind
--   have ⟨μ, h5, h6⟩ := h3
--   have h7 : i < ω.val.length := by
--     suffices i ≠ ω.val.length by
--       have : i ≤ ω.val.length := Nat.findGreatest_le _
--       grind
--     intro h
--     rw [h, take_length] at h6
--     grind
--   have h6 : take (i + 1) μ ≠ take (i + 1) ω.val := by grind
--   let t := cs.wordProd (take i ω) * cs.simple ω.val[i] * (cs.wordProd (take i ω))⁻¹
--   have ht : cs.IsReflection t := by exists cs.wordProd (take i ω.val), ω.val[i]
--   cases mul_reflection_lt_or_gt u ht with
--   | inl h => sorry
--   | inr h => sorry


end Coxeter
