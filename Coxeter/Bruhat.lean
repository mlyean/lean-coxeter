import Coxeter.StrongExchange

namespace Coxeter

open CoxeterSystem CoxeterGroup

variable {W : Type*} [CoxeterGroup W]

inductive lt : W → W → Prop
  | step {u w : W} (h1 : cs.IsReflection (u⁻¹ * w)) (h2 : cs.length u < cs.length w) : lt u w
  | trans {u v w : W} (h1 : lt u v) (h2 : lt v w) : lt u w

def le (u w : W) : Prop := u = w ∨ lt u w

instance : LT W where
  lt := lt

instance : LE W where
  le := le

theorem length_lt_of_bruhat_lt {u w : W} (h : u < w) : cs.length u < cs.length w := by
  induction h with
  | step h1 h2 => exact h2
  | trans h1 h2 ih1 ih2 => exact Nat.lt_trans ih1 ih2

theorem length_le_of_bruhat_le {u w : W} (h : u ≤ w) : cs.length u ≤ cs.length w := by
  cases h with
  | inl h1 => rw [h1]
  | inr h1 => exact Nat.le_of_lt (length_lt_of_bruhat_lt h1)

instance : PartialOrder W where
  le_refl := by
    intro w
    left
    rfl
  le_trans := by
    intro u v w huv hvw
    cases huv with
    | inl h =>
        rw [h]
        exact hvw
    | inr h =>
        cases hvw with
        | inl h2 =>
            rw [←h2]
            right
            exact h
        | inr h2 =>
            right
            exact lt.trans h h2
  lt_iff_le_not_ge := by
    intro u w
    constructor
    · intro h
      constructor
      · right
        exact h
      · intro h2
        have := length_lt_of_bruhat_lt h
        have := length_le_of_bruhat_le h2
        grind
    · intro ⟨h1, h2⟩
      cases h1 with
      | inl h3 =>
          subst h3
          suffices u ≤ u by contradiction
          left
          rfl
      | inr h3 => exact h3
  le_antisymm := by
    intro u w h1 h2
    cases h1 with
    | inl h3 => exact h3
    | inr h3 =>
        have := length_lt_of_bruhat_lt h3
        have := length_le_of_bruhat_le h2
        grind

end Coxeter
