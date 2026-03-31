import Coxeter.Basic

/-!
# Opposite Coxeter group

This file proves properties of the opposite of a Coxeter group.

-/

namespace Coxeter

variable {W : Type*} [CoxeterGroup W]

open CoxeterGroup CoxeterSystem MulOpposite List

def cs_op : CoxeterSystem (@M W _) Wᵐᵒᵖ where
  mulEquiv := MulEquiv.trans (MulEquiv.inv' W).symm cs.mulEquiv

instance : CoxeterGroup Wᵐᵒᵖ where
  B := B W
  M := M
  cs := cs_op

theorem simple_op (i : B W) : (@cs Wᵐᵒᵖ).simple i = op (cs.simple i) := by
  change (op (cs.simple i))⁻¹ = op (cs.simple i)
  rw [←op_inv, inv_simple]

theorem wordProd_op (ω : List (B W)) :
  (@cs Wᵐᵒᵖ).wordProd ω = op (cs.wordProd ω.reverse) := by
  induction ω with
  | nil => rfl
  | cons i is hi =>
      rw [wordProd_cons, reverse_cons, wordProd_append, op_mul, hi, wordProd_singleton, simple_op]

theorem length_op (w : W) : cs.length (op w) = cs.length w := by
  apply eq_of_le_of_ge
  · have ⟨ω, hω1, hω2⟩ := cs.exists_isReduced w
    rw [hω2, hω1]
    nth_rw 1 [←reverse_reverse ω, ←wordProd_op, ←length_reverse]
    apply cs.length_wordProd_le
  · have ⟨ω, hω1, hω2⟩ := cs.exists_isReduced (op w)
    rw [hω2, hω1]
    rw [wordProd_op, op_inj] at hω2
    rw [hω2, wordProd_reverse, length_inv]
    apply cs.length_wordProd_le

theorem isLeftDescent_op_iff (w : W) (i : B W) :
  cs.IsLeftDescent (op w) i ↔ cs.IsRightDescent w i := by
  unfold IsLeftDescent IsRightDescent
  rw [simple_op, ←op_mul, length_op, length_op]

theorem isReflection_op_iff (t : W) :
  cs.IsReflection (op t) ↔ cs.IsReflection t := by
  unfold IsReflection
  constructor
  · intro ⟨w, i, hi⟩
    cases w with
    | h w =>
        rw [simple_op, ←op_inv, ←op_mul, ←op_mul, ←mul_assoc, op_inj] at hi
        exists w⁻¹, i
        rw [inv_inv]
        exact hi
  · intro ⟨w, i, hi⟩
    exists op w⁻¹, i
    rw [simple_op, ←op_inv, ←op_mul, ←op_mul, inv_inv, ←mul_assoc, hi]

theorem isLeftInversion_op_iff (w t : W) :
  cs.IsLeftInversion (op w) (op t) ↔ cs.IsRightInversion w t := by
  unfold IsLeftInversion IsRightInversion
  rw [isReflection_op_iff, ←op_mul, length_op, length_op]

theorem leftInvSeq_op (ω : List (B W)) : (@cs Wᵐᵒᵖ).leftInvSeq ω = map op (cs.leftInvSeq ω) := by
  induction ω with
  | nil => rfl
  | cons i is ih =>
      dsimp [leftInvSeq]
      rw [ih, simple_op, map_map, map_map]
      congr 2
      ext w
      dsimp
      rw [←op_inv, ←op_mul, ←op_mul, ←op_mul, ←op_mul, op_inj, ←mul_assoc, inv_simple]

end Coxeter
