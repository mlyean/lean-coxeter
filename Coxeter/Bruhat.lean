import Coxeter.StrongExchange

/-!
# Bruhat order

This file defines the Bruhat order.

## Main definitions

* `Coxeter.le` : The Bruhat order

## Main Statements

* `Coxeter.subword_property`

## References

* [bjorner2005] A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*

-/

namespace Coxeter

open List CoxeterSystem CoxeterGroup

variable {W : Type*} [CoxeterGroup W]

inductive le : W → W → Prop
  | rfl (u : W) : le u u
  | step (u v w : W) (h1 : le u v) (h2 : cs.IsReflection (w * v⁻¹))
      (h3 : cs.length v < cs.length w) : le u w

instance : LE W where
  le := le

def lt (u w : W) : Prop := u ≤ w ∧ u ≠ w

instance : LT W where
  lt := lt

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

theorem lt_reflection_mul_iff {t : W} (ht : cs.IsReflection t) (w : W)
  : w < t * w ↔ cs.length w < cs.length (t * w) := by
  constructor
  · intro h
    apply length_lt_of_bruhat_lt
    exact h
  · intro h
    constructor
    · apply le.step w w (t * w) (le.rfl _)
      · rw [mul_inv_cancel_right]
        exact ht
      · exact h
    · intro h2
      rw [←h2] at h
      grind

theorem reflection_mul_lt_iff {t : W} (ht : cs.IsReflection t) (w : W)
  : t * w < w ↔ cs.length (t * w) < cs.length w := by
  have h := lt_reflection_mul_iff ht (t * w)
  rw [←mul_assoc, ht.mul_self, one_mul] at h
  exact h

theorem mul_reflection_lt_or_gt (w : W) {t : W} (ht : cs.IsReflection t) :
  t * w < w ∨ t * w > w := by
  conv in t * w > w => change w < t * w
  rw [reflection_mul_lt_iff ht, lt_reflection_mul_iff ht]
  exact Nat.lt_or_gt_of_ne (ht.length_mul_right_ne w)

def ReducedWord (w : W) := {ω : List (B W) // w = cs.wordProd ω ∧ cs.IsReduced ω}

instance {w : W} : CoeOut (ReducedWord w) (List (B W)) where
  coe := fun ω => ω.val

/-- Bjorner--Brenti Theorem 2.2.2 (only if) -/
theorem exists_reduced_subword_of_le {u w : W} (h : u ≤ w) (ω : ReducedWord w) :
  ∃ μ : ReducedWord u, μ.val <+ ω.val := by
  revert ω
  induction h with
  | rfl =>
      intro ω
      exists ω
  | step v w _ h1 h2 ih =>
      intro ω
      let t := w * v⁻¹
      change cs.IsReflection t at h1
      have h3 : w = t * v := by simp only [inv_mul_cancel_right, t]
      have h4 : cs.IsLeftInversion (cs.wordProd ω) t := by
        constructor
        · exact h1
        · rw [←ω.prop.1]
          nth_rw 1 [h3]
          rw [←mul_assoc, h1.mul_self, one_mul]
          exact h2
      have ⟨i, _, h5⟩ := strong_exchange h4
      nth_rw 1 [←ω.prop.1, h3, ←mul_assoc, h1.mul_self, one_mul] at h5
      have ⟨ω', h6, _, _⟩ := exists_reduced_subword (ω.val.eraseIdx i)
      have ⟨μ, h7⟩ := ih ⟨ω', by grind⟩
      exists μ
      calc
        μ <+ ω' := h7
        _ <+ ω.val.eraseIdx i := h6
        _ <+ ω := eraseIdx_sublist _ _

theorem sublist_tail_of_head_neq {α : Type*}
  {l₁ l₂ : List α} (hl₁ : l₁ ≠ [])
  (hsub : l₁ <+ l₂) (h : head l₁ hl₁ ≠ head l₂ (by grind)) :
  l₁ <+ tail l₂ := by
  cases l₁ with
  | nil => simp
  | cons x xs =>
      cases l₂ with
      | nil => grind
      | cons y ys => grind

private theorem thm {i j : ℕ} (ω : List (B W)) (hij : i < j) :
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

private theorem thm' {i j : ℕ} (ω : List (B W)) (h1 : i < j) (h2 : j < ω.length) :
  (cs.leftInvSeq ω)[i]'(by rw [length_leftInvSeq]; grind)
  * (cs.leftInvSeq ω)[j]'(by rw [length_leftInvSeq]; exact h2)
  * cs.wordProd ω
  = cs.wordProd ((ω.eraseIdx j).eraseIdx i) := by
  rw [←thm ω h1]
  grind

private theorem thm'' {i : ℕ} {ω : List (B W)} (hi : i + 1 < ω.length) (hω : cs.IsReduced ω) :
  ω[i] ≠ ω[i + 1] := by
  intro h
  have h1 : ω = take i ω ++ [ω[i], ω[i + 1]] ++ drop (i + 2) ω := by
    simp
  have : ω.length < ω.length := by
    calc
      ω.length = cs.length (cs.wordProd ω) := hω.symm
      _ = cs.length (cs.wordProd (take i ω ++ [ω[i], ω[i + 1]] ++ drop (i + 2) ω)) := by
        nth_rw 1 [h1]
      _ = cs.length (cs.wordProd (take i ω) * cs.wordProd [ω[i], ω[i + 1]]
            * cs.wordProd (drop (i + 2) ω)) := ?_
      _ = cs.length (cs.wordProd (take i ω) * cs.wordProd (drop (i + 2) ω)) := ?_
      _ = cs.length (cs.wordProd (take i ω ++ drop (i + 2) ω)) := ?_
      _ ≤ (take i ω ++ drop (i + 2) ω).length := ?_
      _ < ω.length := ?_
    · rw [wordProd_append, wordProd_append]
    · conv in cs.wordProd [ω[i], ω[i + 1]] =>
        rw [h]
        simp [wordProd]
      simp
    · rw [wordProd_append]
    · apply length_wordProd_le
    · grind
  grind

set_option maxHeartbeats 300000 in
-- Avoid timeout
open Classical in
/-- Bjorner--Brenti Lemma 2.2.1 -/
theorem reduced_subword_extend {u w : W} (ω : ReducedWord w)
  (h1 : u ≠ w) (h2 : ∃ (μ : ReducedWord u), μ.val <+ ω.val) :
  ∃ (v : W), v > u ∧ cs.length v = cs.length u + 1 ∧ ∃ (ν : ReducedWord v), ν.val <+ ω.val := by
  let P (i : ℕ) := ∃ (μ : ReducedWord u), take i μ.val = take i ω.val ∧ drop i μ.val <+ drop i ω.val
  let i := Nat.findGreatest P ω.val.length
  have h3 : P i := by
    unfold i
    apply Nat.findGreatest_spec (zero_le _)
    unfold P
    simp only [take_zero, drop_zero, true_and]
    exact h2
  have h4 : ∀ k > i, ¬ P k := by
    intro k hk
    cases Nat.le_or_ge k ω.val.length with
    | inl h => exact Nat.findGreatest_is_greatest hk h
    | inr h =>
        intro ⟨μ, hμ⟩
        have : μ.val <+ ω.val := by
          calc
            μ.val = take k μ.val ++ drop k μ.val := by rw [take_append_drop]
            _ <+ take k ω.val ++ drop k ω.val := ?_
            _ <+ ω.val := by rw [take_append_drop]
          · apply List.Sublist.append
            · rw [hμ.1]
            · exact hμ.2
        have hμ2 : μ.val.length ≤ k := by grind
        rw [take_of_length_le hμ2, take_of_length_le h] at hμ
        grind
  have ⟨μ, h5, h6⟩ := h3
  have h7 : μ.val <+ ω.val := by
    calc
      μ.val = take i μ.val ++ drop i μ.val := by rw [take_append_drop]
      _ <+ take i ω.val ++ drop i ω.val := ?_
      _ <+ ω.val := by rw [take_append_drop]
    · apply List.Sublist.append
      · rw [h5]
      · exact h6
  have h8 : i ≤ μ.val.length := by
    by_contra! h
    unfold P at h3
    rw [take_of_length_le (by grind)] at h5
    rw [h5, length_take_of_le (by grind)] at h
    grind
  have h9 : i < ω.val.length := by
    suffices i ≠ ω.val.length by
      have : i ≤ ω.val.length := Nat.findGreatest_le _
      grind
    intro h
    rw [h, take_length] at h5
    grind
  have h6' : drop i μ.val <+ drop (i + 1) ω.val := by
    cases Nat.lt_or_eq_of_le h8 with
    | inl h =>
        rw [←tail_drop]
        have h' : drop i μ.val ≠ [] := by
          simp only [ne_eq, drop_eq_nil_iff, not_le]
          exact h
        apply sublist_tail_of_head_neq h' h6
        simp only [head_drop, ne_eq]
        intro h''
        have h5' : take (i + 1) μ.val = take (i + 1) ω.val := by
          calc
            take (i + 1) μ.val = (take i μ.val).concat μ.val[i] := by rw [take_concat_get]
            _ = (take i ω.val).concat ω.val[i] := by rw [h'', h5]
            _ = take (i + 1) ω.val := by rw [take_concat_get]
        grind
    | inr h =>
        rw [h]
        simp only [drop_length, nil_sublist]
  have h10 : take (i + 1) μ.val ≠ take (i + 1) ω.val := by grind
  let t := cs.wordProd (take i ω) * cs.simple ω.val[i] * (cs.wordProd (take i ω))⁻¹
  have ht : cs.IsReflection t := by exists cs.wordProd (take i ω.val), ω.val[i]
  have h11 : t * u = cs.wordProd (take (i + 1) ω ++ drop i μ) := by
    calc
      t * u = cs.wordProd (take (i + 1) ω) * (cs.wordProd (take i ω))⁻¹ * cs.wordProd μ := ?_
      _ = cs.wordProd (take (i + 1) ω) * (cs.wordProd (take i ω))⁻¹
        * cs.wordProd (take i μ ++ drop i μ) := by rw [take_append_drop]
      _ = cs.wordProd (take (i + 1) ↑ω ++ drop i ↑μ) := ?_
    · unfold t
      nth_rw 1 [μ.2.1]
      rw [←wordProd_concat, concat_eq_append, take_append_getElem]
    · rw [wordProd_append, wordProd_append, h5]
      group
  have h12 : cs.length (t * u) ≤ cs.length u + 1 := by
    calc
      cs.length (t * u)
        = cs.length (cs.wordProd (take (i + 1) ω.val ++ drop i μ.val)) := by rw [h11]
      _ ≤ (take (i + 1) ω.val ++ drop i μ.val).length := cs.length_wordProd_le _
      _ = μ.val.length + 1 := by grind
      _ = cs.length u + 1 := by rw [←μ.2.2, ←μ.2.1]
  cases mul_reflection_lt_or_gt u ht with
  | inl h =>
      exfalso
      rw [reflection_mul_lt_iff ht] at h
      replace ht : cs.IsLeftInversion u t := by
        constructor
        · exact ht
        · exact h
      rw [μ.2.1, isLeftInversion_iff_mem_leftInvSeq t μ.2.2] at ht
      have ⟨⟨j, hj1⟩, hj2⟩ := get_of_mem ht
      replace hj2 : t = (cs.leftInvSeq μ.val)[j] := by grind
      cases Nat.lt_or_ge j i with
      | inl h' =>
          have : i < (cs.leftInvSeq ω.val).length := by
            rw [length_leftInvSeq]
            grind
          have ht' : t = (cs.leftInvSeq ω)[i] := by
            rw [getElem_leftInvSeq]
          have ht'' : t = (cs.leftInvSeq ω)[j] := by
            rw [hj2]
            rw [getElem_leftInvSeq, getElem_leftInvSeq]
            · have : take j μ.val = take j ω.val := by
                calc
                  take j μ.val = take j (take i μ.val) := by grind
                  _ = take j (take i ω.val) := by grind
                  _ = take j ω.val := by grind
              rw [this]
              have : μ.val[j] = ω.val[j] := by
                calc
                  μ.val[j] = (take i μ.val)[j]'(by grind) := by grind
                  _ = (take i ω.val)[j]'(by grind) := by grind
                  _ = ω.val[j] := by grind
              rw [this]
            · grind
          have hweq : w = cs.wordProd ((ω.val.eraseIdx i).eraseIdx j) := by
            calc
              w = t * t * w := by rw [(cs.isReflection_of_mem_leftInvSeq _ ht).mul_self, one_mul]
              _ = (cs.leftInvSeq ↑ω)[j] * (cs.leftInvSeq ↑ω)[i] * cs.wordProd ω.val := by grind
              _ = cs.wordProd ((ω.val.eraseIdx i).eraseIdx j) := thm' ω.val h' h9
          have hlt : cs.length w < ω.val.length := by
            calc
              cs.length w = cs.length (cs.wordProd ((ω.val.eraseIdx i).eraseIdx j)) := by
                nth_rw 1 [hweq]
              _ ≤ ((ω.val.eraseIdx i).eraseIdx j).length := cs.length_wordProd_le _
              _ < ω.val.length := by grind
          have heq' : cs.length (cs.wordProd ω.val) = ω.val.length := ω.2.2
          grind
      | inr h' =>
          let μ' := take (i + 1) ω.val ++ drop i (μ.val.eraseIdx j)
          have h'' : u = cs.wordProd μ' := by
            calc
              u = t * t * u := by rw [(cs.isReflection_of_mem_leftInvSeq _ ht).mul_self, one_mul]
              _ = t * ((cs.leftInvSeq ↑μ)[j] * cs.wordProd μ) := by
                nth_rw 1 [←hj2, μ.2.1, mul_assoc]
              _ = t * cs.wordProd (μ.val.eraseIdx j) := ?_
              _ = cs.wordProd (take (i + 1) ω.val) * ((cs.wordProd (take i ω.val))⁻¹
                  * cs.wordProd (μ.val.eraseIdx j)) := ?_
              _ = cs.wordProd (take (i + 1) ω.val) * ((cs.wordProd (take i ω.val))⁻¹
                  * cs.wordProd (take i (μ.val.eraseIdx j))
                  * cs.wordProd (drop i (μ.val.eraseIdx j))) := ?_
              _ = cs.wordProd (take (i + 1) ω.val) * cs.wordProd (drop i (μ.val.eraseIdx j)) := ?_
              _ = cs.wordProd (take (i + 1) ω.val ++ drop i (μ.val.eraseIdx j)) := by
                rw [wordProd_append]
            · rw [←cs.getD_leftInvSeq_mul_wordProd (μ.val) j]
              grind
            · unfold t
              rw [←wordProd_concat, concat_eq_append, take_append_getElem, mul_assoc]
            · rw [mul_right_inj, mul_assoc, mul_right_inj, ←wordProd_append, take_append_drop]
            · simp only [mul_right_inj, mul_eq_right]
              rw [inv_mul_eq_one]
              congr 1
              grind
          have hμ_len : μ.val.length = μ'.length := by grind
          have hμ' : cs.IsReduced μ' := by
            unfold CoxeterSystem.IsReduced
            rw [←h'', ←hμ_len]
            have h := μ.2.2
            unfold CoxeterSystem.IsReduced at h
            grind
          have h''' : P (i + 1) := by
            unfold P
            exists ⟨μ', ⟨h'', hμ'⟩⟩
            unfold μ'
            have : (take (i + 1) ω.val).length = i + 1 := by
              grind
            simp only [this, take_left', drop_left', true_and]
            rw [←tail_drop]
            have : drop i (μ.val.eraseIdx j) <+ (drop i ω.val) := by
              calc
                drop i (μ.val.eraseIdx j) <+ drop i μ.val := by grind
                _ <+ drop i ω.val := h6
            cases Classical.em (drop i (μ.val.eraseIdx j) = []) with
            | inl heqnil => grind
            | inr hneqnil =>
                apply sublist_tail_of_head_neq hneqnil this
                · rw [head_drop, head_drop]
                  cases lt_or_eq_of_le h' with
                  | inl hijlt =>
                      rw [getElem_eraseIdx_of_lt _ hijlt]
                      intro heq
                      have h10' : take (i + 1) μ.val = take (i + 1) ω.val := by
                        calc
                          take (i + 1) μ.val = (take i μ.val).concat (μ.val[i]'(by grind)) := by
                            rw [take_concat_get]
                          _ = (take i ω.val).concat ω.val[i] := by grind
                          _ = take (i + 1) ω.val := by rw [take_concat_get]
                      contradiction
                  | inr hijeq =>
                      rw [getElem_eraseIdx_of_ge _ (by grind)]
                      intro h
                      have h13 : μ'[i + 1]'(by grind) = ω.val[i]'(by grind) := by grind
                      have h14 : μ'[i]'(by grind) = ω.val[i]'(by grind) := by grind
                      have := thm'' (by grind : i + 1 < μ'.length) hμ'
                      grind
          apply h4 (i + 1)
          · simp
          · exact h'''
  | inr h =>
      let v := t * u
      let ν := take (i + 1) ω.val ++ drop i μ.val
      change v = cs.wordProd ν at h11
      change u < v at h
      have h13 : ν.length = μ.val.length + 1 := by grind
      have hν : cs.IsReduced ν := by
        rw [lt_reflection_mul_iff ht u] at h
        unfold CoxeterSystem.IsReduced
        rw [←h11, h13, ←μ.2.2, ←μ.2.1]
        grind
      exists v
      constructor
      · exact h
      · constructor
        · rw [lt_reflection_mul_iff ht u] at h
          rw [h11, hν, μ.2.1, μ.2.2]
          exact h13
        · exists ⟨ν, ⟨h11, hν⟩⟩
          calc
            take (i + 1) ω.val ++ drop i μ.val <+ take (i + 1) ω.val ++ drop (i + 1) ω.val := ?_
            _ = ω.val := by rw [take_append_drop]
          · apply Sublist.append
            · rfl
            · exact h6'

theorem le_of_reduced_subword {u w : W} (μ : ReducedWord u) (ω : ReducedWord w)
  (h : μ.val <+ ω.val) : u ≤ w := by
  revert u
  suffices h : ∀ (k : ℕ), k ≤ ω.val.length →
    ∀ (u : W) (μ : ReducedWord u), μ.val <+ ω.val → μ.val.length = k → u ≤ w by
    intro u μ h2
    apply h (μ.val.length) _ u μ h2
    · rfl
    · exact h2.length_le
  apply Nat.decreasingInduction
  · intro k hk ih u μ h1 h2
    have hneq : u ≠ w := by
      intro h
      have h3 : cs.length u = cs.length w := by rw [h]
      rw [μ.2.1, μ.2.2, ω.2.1, ω.2.2] at h3
      grind
    have ⟨v, hv1, hv2, ν, hν⟩ := reduced_subword_extend ω hneq ⟨μ, h1⟩
    rw [ν.2.1, ν.2.2, μ.2.1, μ.2.2, h2] at hv2
    have := ih v ν hν hv2
    grind
  · intro u μ h1 h2
    have : μ.val = ω.val := by grind
    have : u = w := by grind
    rw [this]

theorem subword_property (u : W) {w : W} (ω : ReducedWord w) :
  u ≤ w ↔ ∃ (μ : ReducedWord u), μ.val <+ ω.val := by
  constructor
  · intro h
    apply exists_reduced_subword_of_le
    exact h
  · intro ⟨μ, h⟩
    apply le_of_reduced_subword _ _ h

end Coxeter
