/-
Copyright (c) 2026 Ming Yean Lim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ming Yean Lim
-/
module

public import Mathlib.Data.Fintype.Order

/-! Lemmas about directed orders -/

@[expose] public section

namespace Coxeter

@[implicit_reducible]
noncomputable def orderTop_ofFiniteDirectedOrder {α : Type*}
  [Finite α] [Nonempty α] [Preorder α] [IsDirectedOrder α] : OrderTop α where
  top := (Finite.exists_le id).choose
  le_top := (Finite.exists_le id).choose_spec

end Coxeter
