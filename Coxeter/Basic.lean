import Mathlib.GroupTheory.Coxeter.Inversion

/-!
# Coxeter groups

We build upon the the theory of Coxeter systems currently available in `mathlib`.

## Main definitions

* `Coxeter.CoxeterGroup`
* `Coxeter.ReducedWord`

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
      | cons =>
          rw [add_right_comm]
          apply ih

theorem reverse_eraseIdx {l : List α} {i : ℕ} (hi : i < l.length) :
  l.reverse.eraseIdx i = (l.eraseIdx (l.length - i - 1)).reverse := by
  calc
    l.reverse.eraseIdx i = take i (l.reverse) ++ drop (i + 1) l.reverse :=
      eraseIdx_eq_take_drop_succ _ _
    _ = (drop (l.length - i) l).reverse ++ (take (l.length - i - 1) l).reverse := ?_
    _ = (take (l.length - i - 1) l ++ drop (l.length - i) l).reverse := reverse_append.symm
    _ = (l.eraseIdx (l.length - i - 1)).reverse := ?_
  · rw [take_reverse, drop_reverse, Nat.sub_add_eq]
  · rw [eraseIdx_eq_take_drop_succ, Nat.sub_add_cancel]
    apply Nat.le_sub_of_add_le
    rwa [add_comm]

theorem sublist_tail_of_head_ne {l₁ l₂ : List α} (hl₁ : l₁ ≠ [])
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

def ReducedWord (w : W) := {ω : List (B W) // cs.IsReduced ω ∧ w = cs.wordProd ω}

instance {w : W} : CoeOut (ReducedWord w) (List (B W)) where
  coe := fun ω => ω.val

open Classical in
noncomputable instance {w : W} : Inhabited (ReducedWord w) where
  default := ⟨Classical.choose (cs.exists_reduced_word' w),
              Classical.choose_spec (cs.exists_reduced_word' w)⟩

namespace ReducedWord

@[simp]
def reverse {w : W} (ω : ReducedWord w) : ReducedWord w⁻¹ :=
  ⟨ω.1.reverse, ω.prop.1.reverse,
    Eq.trans (congr_arg Inv.inv ω.prop.2) (cs.wordProd_reverse _).symm⟩

abbrev length {w : W} (ω : ReducedWord w) : ℕ := ω.val.length

theorem length_eq {w : W} (ω : ReducedWord w) : ω.length = cs.length w := by
  unfold length
  rw [←ω.2.1, ←ω.2.2]

theorem wordProd_eq {w : W} (ω : ReducedWord w) : cs.wordProd ω = w := ω.2.2.symm

end ReducedWord

theorem IsReduced_nil : cs.IsReduced ([] : List (B W)) := by
  unfold CoxeterSystem.IsReduced
  rw [wordProd_nil, length_one, length_nil]

theorem IsReduced_cons {ω : List (B W)} (i : B W) (hω : cs.IsReduced ω) :
  cs.IsReduced (i :: ω) ↔ ¬ cs.IsLeftDescent (cs.wordProd ω) i := by
  unfold CoxeterSystem.IsReduced
  rw [not_isLeftDescent_iff, wordProd_cons, length_cons, hω]

theorem not_IsReduced_cons {ω : List (B W)} (i : B W) (hω : cs.IsReduced ω) :
  ¬ cs.IsReduced (i :: ω) ↔ cs.IsLeftDescent (cs.wordProd ω) i := by
  apply Iff.not_left
  apply IsReduced_cons
  exact hω

theorem tail_leftInvSeq (i : B W) (ω : List (B W)) :
  tail (cs.leftInvSeq (i :: ω)) = map (MulAut.conj (cs.simple i)) (cs.leftInvSeq ω) := rfl

theorem drop_leftInvSeq (j : ℕ) (ω : List (B W)) :
  drop j (cs.leftInvSeq ω)
  = map (MulAut.conj (cs.wordProd (take j ω))) (cs.leftInvSeq (drop j ω)) := by
  revert ω
  induction j with
  | zero =>
      intro ω
      dsimp
      rw [wordProd_nil, map_one, MulAut.coe_one, map_id]
  | succ _ ih =>
      intro
      | nil => rfl
      | cons _ _ =>
          rw [←drop_tail, tail_leftInvSeq, ←map_drop, ih, map_map,
            drop_succ_cons, take_succ_cons, ←MulAut.coe_mul, ←map_mul, wordProd_cons]

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

theorem alternatingWord_even_add (i i' : B W) (k m : ℕ) :
  alternatingWord i i' (2 * k + m) = alternatingWord i i' m ++ alternatingWord i i' (2 * k) := by
  revert i i'
  induction m with
  | zero => simp [alternatingWord]
  | succ n ih =>
      intro i i'
      rw [←add_assoc, alternatingWord_succ, alternatingWord_succ, ih]
      simp only [concat_eq_append, append_assoc, cons_append, nil_append, append_cancel_left_eq]
      rw [←concat_eq_append, ←alternatingWord_succ, alternatingWord_succ']
      simp

theorem reverse_alternatingWord (i i' : B W) (k : ℕ) :
  (alternatingWord i i' (2 * k)).reverse = alternatingWord i' i (2 * k) := by
  induction k with
  | zero =>
      simp [alternatingWord]
  | succ k ih =>
      simp only [alternatingWord, Nat.mul_eq, concat_eq_append, append_assoc, cons_append,
        nil_append, reverse_append, reverse_cons, reverse_nil]
      rw [ih]
      trans alternatingWord i' i (2 * k + 2)
      · rw [alternatingWord_succ', alternatingWord_succ']
        simp
      · simp [alternatingWord]

theorem getD_leftInvSeq_mul_wordProd₂ {i j : ℕ} (ω : List (B W)) (hij : i < j) :
  (cs.leftInvSeq ω).getD i 1 * (cs.leftInvSeq ω).getD j 1 * cs.wordProd ω
  = cs.wordProd ((ω.eraseIdx j).eraseIdx i) := by
  rw [←cs.getD_leftInvSeq_mul_wordProd (ω.eraseIdx j) i, ←cs.getD_leftInvSeq_mul_wordProd ω j,
    mul_assoc]
  congr 1
  cases (Nat.lt_or_ge i ω.length) with
  | inl h =>
      have h' : i < (ω.eraseIdx j).length := by
        rw [length_eraseIdx]
        split_ifs with h'
        · rw [Nat.lt_sub_iff_add_lt]
          exact lt_of_le_of_lt hij h'
        · exact h
      rw [getD_eq_getElem, getD_eq_getElem, cs.getElem_leftInvSeq _ _ h',
        cs.getElem_leftInvSeq _ _ h]
      · rw [take_eraseIdx_eq_take_of_le _ _ _ (le_of_lt hij), getElem_eraseIdx_of_lt h' hij]
      · rwa [length_leftInvSeq]
      · rwa [length_leftInvSeq]
  | inr h =>
      rw [getD_eq_default, getD_eq_default]
      · rw [length_leftInvSeq]
        apply le_trans _ h
        apply length_eraseIdx_le
      · rw [length_leftInvSeq]
        exact h

theorem getElem_leftInvSeq_mul_wordProd₂ {i j : ℕ}
  (ω : List (B W)) (h1 : i < j) (h2 : j < ω.length) :
  (cs.leftInvSeq ω)[i]'(by rw [length_leftInvSeq]; exact lt_trans h1 h2)
  * (cs.leftInvSeq ω)[j]'(by rw [length_leftInvSeq]; exact h2)
  * cs.wordProd ω
  = cs.wordProd ((ω.eraseIdx j).eraseIdx i) := by
    rw [←getD_leftInvSeq_mul_wordProd₂ ω h1, getD_eq_getElem, getD_eq_getElem]

theorem adjacent_ne_of_isReduced {i : ℕ} {ω : List (B W)}
  (hi : i + 1 < ω.length) (hω : cs.IsReduced ω) : ω[i] ≠ ω[i + 1] := by
  wlog h : i = 0 with H
  · have := @H _ _ 0 (drop i ω) (by grind) (hω.drop i) rfl
    simpa
  · subst h
    match ω with
    | i :: j :: is =>
        dsimp
        intro h
        subst h
        have h2 := hω.take 2
        simp [CoxeterSystem.IsReduced, wordProd] at h2

@[simp]
theorem simple_ne_one (i : B W) : cs.simple i ≠ 1 := by
  intro h
  have h2 := congr_arg cs.length h
  simp at h2

@[simp]
theorem isReduced_of_singleton (i : B W) : cs.IsReduced [i] := by
  unfold CoxeterSystem.IsReduced
  rw [wordProd_singleton, length_simple, length_cons, length_nil, zero_add]

theorem not_isLeftInversion_one (t : W) : ¬ cs.IsLeftInversion 1 t := by
  intro ⟨_, h⟩
  rw [length_one] at h
  exact Nat.not_lt_zero _ h

theorem not_isRightInversion_one (t : W) : ¬ cs.IsRightInversion 1 t := by
  intro ⟨_, h⟩
  rw [length_one] at h
  exact Nat.not_lt_zero _ h

end Coxeter
