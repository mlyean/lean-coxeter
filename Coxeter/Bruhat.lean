import Coxeter.StrongExchange

namespace Coxeter

open CoxeterSystem CoxeterGroup

variable {W : Type*} [CoxeterGroup W]

inductive le : W → W → Prop
  | rfl (u : W) : le u u
  | step (u v w : W) (h1 : le u v) (h2 : cs.IsReflection (v⁻¹ * w))
      (h3 : cs.length v < cs.length w) : le u w

def lt (u w : W) : Prop := le u w ∧ u ≠ w

instance : LT W where
  lt := lt

instance : LE W where
  le := le

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

end Coxeter
