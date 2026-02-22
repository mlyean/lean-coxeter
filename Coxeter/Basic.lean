import Mathlib.GroupTheory.Coxeter.Inversion

/-!
# Coxeter groups

We build upon the the theory of Coxeter systems currently available in `mathlib`.

## Main definitions

* `Coxeter.CoxeterGroup`

-/

namespace Coxeter

class CoxeterGroup (W : Type*) extends Group W where
  B : Type*
  M : CoxeterMatrix B
  cs : CoxeterSystem M W

end Coxeter

namespace List

variable {α : Type*}

theorem drop_eraseIdx (l : List α) (i j : ℕ) :
  (drop i l).eraseIdx j = drop i (l.eraseIdx (i + j)) := by
  revert l
  induction i with
  | zero => simp
  | succ i ih =>
      intro l
      cases l with
      | nil => simp
      | cons a as =>
          rw [add_right_comm]
          apply ih

theorem reverse_eraseIdx {l : List α} {i : ℕ} (hi : i < l.length) :
  l.reverse.eraseIdx i = (l.eraseIdx (l.length - i - 1)).reverse := by
  calc
    l.reverse.eraseIdx i = take i (l.reverse) ++ drop (i + 1) (l.reverse) :=
      eraseIdx_eq_take_drop_succ _ _
    _ = (drop (l.length - i) l).reverse ++ (take (l.length - i - 1) l).reverse := ?_
    _ = (take (l.length - i - 1) l ++ drop (l.length - i) l).reverse := reverse_append.symm
    _ = (l.eraseIdx (l.length - i - 1)).reverse := ?_
  · rw [take_reverse, drop_reverse]
    grind
  · rw [eraseIdx_eq_take_drop_succ ]
    congr
    grind

end List

namespace Coxeter

open List CoxeterSystem CoxeterGroup

variable {W : Type*} [CoxeterGroup W]

theorem IsReduced_nil (W : Type*) [CoxeterGroup W] : (@cs W).IsReduced [] := by
  unfold CoxeterSystem.IsReduced
  rw [wordProd_nil, length_one, length_nil]

theorem not_IsReduced_cons {ω : List (B W)} (i : B W) (hω : cs.IsReduced ω) :
  ¬ cs.IsReduced (i :: ω) ↔ cs.IsLeftDescent (cs.wordProd ω) i := by
  unfold CoxeterSystem.IsReduced IsLeftDescent at *
  rw [hω, wordProd_cons, length_cons]
  have := cs.length_simple_mul (cs.wordProd ω) i
  grind

theorem drop_leftInvSeq (j : ℕ) (ω : List (B W)) :
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

theorem tail_alternatingWord (i j : (B W)) (p : ℕ) :
  tail (alternatingWord i j (p + 1)) = alternatingWord i j p := by
  rw [alternatingWord_succ']
  rfl

theorem drop_alternatingWord (i j : (B W)) (p q : ℕ) :
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

end Coxeter
