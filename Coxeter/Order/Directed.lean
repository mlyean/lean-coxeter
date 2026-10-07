/-
Copyright (c) 2026 Ming Yean Lim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ming Yean Lim
-/
module

public import Mathlib.Order.Preorder.Finite

/-! Lemmas about directed orders -/

@[expose] public section

namespace Coxeter

@[implicit_reducible]
noncomputable def orderTop_ofFiniteDirectedOrder {α : Type*}
  [Nonempty α] [Preorder α] [Finite α] [IsDirectedOrder α] : OrderTop α where
  top := (Set.finite_univ.exists_maximal Set.univ_nonempty).choose
  le_top := by
    apply IsMax.isTop
    intro a
    exact (Set.finite_univ.exists_maximal Set.univ_nonempty).choose_spec.2 (Set.mem_univ a)

end Coxeter
