import Mathlib.GroupTheory.Coxeter.Inversion

namespace Coxeter

/-- Experimental wrapper for the Coxeter group datum -/
class CoxeterGroup (W : Type*) extends Group W where
  B : Type*
  M : CoxeterMatrix B
  cs : CoxeterSystem M W

end Coxeter

/- Misc. theorems -/

namespace CoxeterSystem

open Function List

variable {B : Type*}
variable {W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

theorem drop_leftInvSeq (j : ℕ) (ω : List B) :
  drop j (cs.leftInvSeq ω)
  = map (MulAut.conj (cs.wordProd (take j ω))) (cs.leftInvSeq (drop j ω)) := by
  revert ω
  induction j with
  | zero => simp
  | succ j ih =>
      intro
      | nil => rfl
      | cons i is =>
          simp only [leftInvSeq, drop_succ_cons, take_succ_cons, wordProd_cons, map_mul,
            MulAut.coe_mul]
          rw [←map_drop, ih, map_map]

theorem tail_alternatingWord (i j : B) (p : ℕ) :
  tail (alternatingWord i j (p + 1)) = alternatingWord i j p := by
  rw [alternatingWord_succ']
  rfl

theorem drop_alternatingWord (i j : B) (p q : ℕ) :
  drop p (alternatingWord i j (p + q))
  = alternatingWord i j q := by
  revert q
  induction p with
  | zero => simp
  | succ p ih =>
      intro q
      rw [←tail_drop, add_assoc]
      nth_rw 2 [add_comm]
      rw [ih (q + 1)]
      apply tail_alternatingWord

end CoxeterSystem
