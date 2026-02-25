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
  · rw [take_reverse, drop_reverse, Nat.sub_add_eq]
  · rw [eraseIdx_eq_take_drop_succ, Nat.sub_add_cancel]
    apply Nat.le_sub_of_add_le
    rw [add_comm]
    exact hi

theorem sublist_tail_of_head_neq {l₁ l₂ : List α} (hl₁ : l₁ ≠ [])
  (hsub : l₁ <+ l₂) (h : head l₁ hl₁ ≠ head l₂ (by grind)) :
  l₁ <+ tail l₂ := by
  induction hsub with
  | slnil => rfl
  | cons =>
      simp_all only [ne_eq, not_false_eq_true, forall_true_left, head_cons, tail_cons]
  | cons₂ =>
      simp_all only [ne_eq, head_cons, not_true_eq_false]

theorem sublist_take_drop {l₁ l₂ : List α} {i : ℕ}
  (h1 : take i l₁ <+ take i l₂) (h2 : drop i l₁ <+ drop i l₂) : l₁ <+ l₂ := by
  calc
    l₁ = take i l₁ ++ drop i l₁ := by rw [take_append_drop]
    _ <+ take i l₂ ++ drop i l₂ := List.Sublist.append h1 h2
    _ <+ l₂ := by rw [take_append_drop]

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

theorem getD_leftInvSeq_mul_wordProd₂ {i j : ℕ} (ω : List (B W)) (hij : i < j) :
  (cs.leftInvSeq ω).getD i 1 * (cs.leftInvSeq ω).getD j 1 * cs.wordProd ω
  = cs.wordProd ((ω.eraseIdx j).eraseIdx i) := by
  rw [←cs.getD_leftInvSeq_mul_wordProd (ω.eraseIdx j) i, ←cs.getD_leftInvSeq_mul_wordProd ω j,
    mul_assoc]
  congr 1
  cases (Nat.lt_or_ge i ω.length) with
  | inl h =>
      rw [getD_eq_getElem, getD_eq_getElem]
      · rw [getElem_leftInvSeq, getElem_leftInvSeq]
        · grind
        · grind
        · exact h
      · rw [length_leftInvSeq, length_eraseIdx]
        grind
      · rw [length_leftInvSeq]
        exact h
  | inr h =>
      rw [getD_eq_default, getD_eq_default]
      · rw [length_leftInvSeq, length_eraseIdx]
        grind
      · rw [length_leftInvSeq]
        exact h

theorem getElem_leftInvSeq_mul_wordProd₂ {i j : ℕ}
  (ω : List (B W)) (h1 : i < j) (h2 : j < ω.length) :
  (cs.leftInvSeq ω)[i]'(by rw [length_leftInvSeq]; exact lt_trans h1 h2)
  * (cs.leftInvSeq ω)[j]'(by rw [length_leftInvSeq]; exact h2)
  * cs.wordProd ω
  = cs.wordProd ((ω.eraseIdx j).eraseIdx i) := by
  rw [←getD_leftInvSeq_mul_wordProd₂ ω h1]
  grind

theorem neq_of_adjacent {i : ℕ} {ω : List (B W)}
  (hi : i + 1 < ω.length) (hω : cs.IsReduced ω) : ω[i] ≠ ω[i + 1] := by
  intro h
  have hlt : ω.length < ω.length := by
    calc
      ω.length = cs.length (cs.wordProd ω) := hω.symm
      _ = cs.length (cs.wordProd (take i ω ++ [ω[i], ω[i + 1]] ++ drop (i + 2) ω)) := by simp
      _ = cs.length (cs.wordProd (take i ω) * cs.wordProd [ω[i], ω[i + 1]]
            * cs.wordProd (drop (i + 2) ω)) := by rw [wordProd_append, wordProd_append]
      _ = cs.length (cs.wordProd (take i ω) * cs.wordProd (drop (i + 2) ω)) := ?_
      _ = cs.length (cs.wordProd (take i ω ++ drop (i + 2) ω)) := by rw [wordProd_append]
      _ ≤ (take i ω ++ drop (i + 2) ω).length := length_wordProd_le _ _
      _ < ω.length := by grind
    · rw [h]
      simp [wordProd]
  rw [lt_self_iff_false] at hlt
  exact hlt

end Coxeter
