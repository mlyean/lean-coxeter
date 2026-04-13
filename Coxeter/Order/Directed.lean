module

public import Mathlib.Order.Preorder.Finite

@[expose] public section

namespace Coxeter

variable (α : Type*) [Nonempty α] [Preorder α] [Finite α] [IsDirectedOrder α]

noncomputable instance : OrderTop α where
  top := (Set.finite_univ.exists_maximal Set.univ_nonempty).choose
  le_top := by
    apply IsMax.isTop
    intro a
    exact (Set.finite_univ.exists_maximal Set.univ_nonempty).choose_spec.2 (Set.mem_univ a)

end Coxeter
