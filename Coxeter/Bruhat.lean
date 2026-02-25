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

open List Function CoxeterSystem CoxeterGroup

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
  | rfl => rfl
  | step _ _ _ _ h3 ih => exact le_of_lt (lt_of_le_of_lt ih h3)

theorem length_lt_of_bruhat_lt {u w : W} (h : u < w) : cs.length u < cs.length w := by
  cases h.1 with
  | rfl =>
      have := h.2
      contradiction
  | step _ _ h1 _ h3 =>
      exact lt_of_le_of_lt (length_le_of_bruhat_le h1) h3

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
        have h3 := lt_of_lt_of_le (length_lt_of_bruhat_lt h) (length_le_of_bruhat_le h2)
        rw [lt_self_iff_false] at h3
        contradiction
    · intro h
      constructor
      · exact h.1
      · intro h2
        subst h2
        exact h.2 (le.rfl u)
  le_antisymm := by
    intro u w h1 h2
    cases h1 with
    | rfl => rfl
    | step v w h3 h4 h5 =>
        suffices cs.length v < cs.length v by
          rw [lt_self_iff_false] at this
          contradiction
        calc
          cs.length v < cs.length w := h5
          _ ≤ cs.length u := length_le_of_bruhat_le h2
          _ ≤ cs.length v := length_le_of_bruhat_le h3

instance : OrderBot W where
  bot := 1
  bot_le := by
    intro w
    let ⟨ω, hω1, hω2⟩ := cs.exists_reduced_word' w
    subst hω2
    revert hω1
    induction ω with
    | nil => simp
    | cons a as ih =>
        intro h
        have h' := h.drop 1
        simp only [drop_succ_cons, drop_zero] at h'
        specialize ih h'
        apply le.step 1 (cs.wordProd as) _ _
        · simp only [wordProd, map_cons, prod_cons, mul_inv_cancel_right]
          exact cs.isReflection_simple a
        · rw [h, h']
          simp
        · exact ih

theorem lt_reflection_mul_iff {t : W} (ht : cs.IsReflection t) (w : W)
  : w < t * w ↔ cs.length w < cs.length (t * w) := by
  constructor
  · intro h
    apply length_lt_of_bruhat_lt
    exact h
  · intro h
    constructor
    · apply le.step w w (t * w) (le.rfl _) _ h
      rwa [mul_inv_cancel_right]
    · intro h2
      rwa [←h2, lt_self_iff_false] at h

theorem reflection_mul_lt_iff {t : W} (ht : cs.IsReflection t) (w : W)
  : t * w < w ↔ cs.length (t * w) < cs.length w := by
  have h := lt_reflection_mul_iff ht (t * w)
  rwa [←mul_assoc, ht.mul_self, one_mul] at h

theorem mul_reflection_lt_or_gt (w : W) {t : W} (ht : cs.IsReflection t) :
  t * w < w ∨ t * w > w := by
  conv in t * w > w => change w < t * w
  rw [reflection_mul_lt_iff ht, lt_reflection_mul_iff ht]
  exact Nat.lt_or_gt_of_ne (ht.length_mul_right_ne w)

def ReducedWord (w : W) := {ω : List (B W) // cs.IsReduced ω ∧ w = cs.wordProd ω}

instance {w : W} : CoeOut (ReducedWord w) (List (B W)) where
  coe := fun ω => ω.val

open Classical in
noncomputable instance {w : W} : Inhabited (ReducedWord w) where
  default := ⟨Classical.choose (cs.exists_reduced_word' w),
              Classical.choose_spec (cs.exists_reduced_word' w)⟩

namespace ReducedWord

@[simp]
def reverse {w : W} : ReducedWord w → ReducedWord w⁻¹ := by
  intro ω
  refine ⟨ω.1.reverse, ⟨?_, ?_⟩⟩
  · exact ω.prop.1.reverse
  · rw [wordProd_reverse, ←ω.prop.2]

end ReducedWord

open Classical in
/-- Bjorner--Brenti Lemma 2.2.1 -/
theorem reduced_subword_extend {u w : W} (ω : ReducedWord w)
  (h1 : u ≠ w) (h2 : ∃ (μ : ReducedWord u), μ.val <+ ω.val) :
  ∃ (v : W), v > u ∧ cs.length v = cs.length u + 1 ∧ ∃ (ν : ReducedWord v), ν.val <+ ω.val := by
  let P (i : ℕ) := ∃ (μ : ReducedWord u), take i μ.val = take i ω.val ∧ drop i μ.val <+ drop i ω.val
  let i := Nat.findGreatest P ω.val.length
  have h_P_i : P i := by
    apply Nat.findGreatest_spec (zero_le _)
    simp only [P, take_zero, drop_zero, true_and]
    exact h2
  unfold P at h_P_i
  have ⟨μ, h_take_eq, h_drop_sublist⟩ := h_P_i
  have h_i_le : i ≤ μ.val.length := by
    by_contra! h
    rw [take_of_length_le (le_of_lt h)] at h_take_eq
    rwa [h_take_eq, length_take_of_le (Nat.findGreatest_le _), lt_self_iff_false] at h
  have h_i_lt : i < ω.val.length := by
    have hsub : μ.val <+ ω.val := by
      apply sublist_take_drop _ h_drop_sublist
      rw [h_take_eq]
    apply lt_of_lt_of_le (add_le_add_left h_i_le 1)
    apply lt_of_le_of_ne hsub.length_le
    intro h
    rw [hsub.length_eq] at h
    rw [μ.2.2, h, ←ω.2.2] at h1
    contradiction
  have h_not_P_succ_i : ¬ P (i + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self i) h_i_lt
  have h_get_i_neq : (hi : i < μ.val.length) → μ.val[i] ≠ ω.val[i] := by
    intro h h'
    apply h_not_P_succ_i
    exists μ
    constructor
    · calc
        take (i + 1) μ.val = (take i μ.val).concat μ.val[i] := by rw [take_concat_get]
        _ = (take i ω.val).concat ω.val[i] := by rw [h', h_take_eq]
        _ = take (i + 1) ω.val := by rw [take_concat_get]
    · have h'' := h_drop_sublist.drop 1
      rwa [drop_drop, drop_drop] at h''
  let t := cs.wordProd (take i ω) * cs.simple ω.val[i] * (cs.wordProd (take i ω))⁻¹
  have ht : cs.IsReflection t := by exists cs.wordProd (take i ω.val), ω.val[i]
  let v := t * u
  let ν := take (i + 1) ω.val ++ drop i μ.val
  have h3 : v = cs.wordProd ν := by
    calc
      t * u = cs.wordProd (take (i + 1) ω) * (cs.wordProd (take i ω))⁻¹ * cs.wordProd μ := ?_
      _ = cs.wordProd (take (i + 1) ω) * (cs.wordProd (take i ω))⁻¹
        * cs.wordProd (take i μ ++ drop i μ) := by rw [take_append_drop]
      _ = cs.wordProd (take (i + 1) ↑ω ++ drop i ↑μ) := ?_
    · unfold t
      nth_rw 1 [μ.2.2]
      rw [←wordProd_concat, concat_eq_append, take_append_getElem]
    · rw [wordProd_append, wordProd_append, h_take_eq]
      group
  cases mul_reflection_lt_or_gt u ht with
  | inl h =>
      exfalso
      rw [reflection_mul_lt_iff ht] at h
      replace ht : cs.IsLeftInversion u t := ⟨ht, h⟩
      rw [μ.2.2, isLeftInversion_iff_mem_leftInvSeq t μ.2.1] at ht
      have ⟨⟨j, hj1⟩, hj2⟩ := get_of_mem ht
      rw [length_leftInvSeq] at hj1
      replace hj2 : t = (cs.leftInvSeq μ.val)[j] := hj2.symm
      cases Nat.lt_or_ge j i with
      | inl h' =>
          have : i < (cs.leftInvSeq ω.val).length := by
            rwa [length_leftInvSeq]
          have ht' : t = (cs.leftInvSeq ω)[i] := by
            rw [getElem_leftInvSeq]
          have ht'' : t = (cs.leftInvSeq ω)[j] := by
            rw [hj2, getElem_leftInvSeq, getElem_leftInvSeq]
            · have : take j μ.val = take j ω.val := calc
                take j μ.val = take j (take i μ.val) := by rw [take_take, min_eq_left (le_of_lt h')]
                _ = take j (take i ω.val) := by rw [h_take_eq]
                _ = take j ω.val := by rw [take_take, min_eq_left (le_of_lt h')]
              rw [this]
              have : μ.val[j] = ω.val[j] := calc
                μ.val[j] = (take i μ.val)[j]'(by rw [length_take_of_le h_i_le]; exact h') := by
                  rw [getElem_take]
                _ = (take i ω.val)[j]'(by rw [length_take_of_le (le_of_lt h_i_lt)]; exact h') := by
                  simp only [h_take_eq, getElem_take]
                _ = ω.val[j] := by rw [getElem_take]
              rw [this]
            · exact lt_of_lt_of_le h' h_i_le
          have hweq : w = cs.wordProd ((ω.val.eraseIdx i).eraseIdx j) := calc
            w = t * t * w := by rw [(cs.isReflection_of_mem_leftInvSeq _ ht).mul_self, one_mul]
            _ = (cs.leftInvSeq ↑ω)[j] * (cs.leftInvSeq ↑ω)[i] * cs.wordProd ω.val := by
              rw [←ht', ←ht'', ←ω.2.2]
            _ = cs.wordProd ((ω.val.eraseIdx i).eraseIdx j) :=
              getElem_leftInvSeq_mul_wordProd₂ ω.val h' h_i_lt
          have hlt : cs.length w < cs.length w := calc
            cs.length w = cs.length (cs.wordProd ((ω.val.eraseIdx i).eraseIdx j)) := by
              nth_rw 1 [hweq]
            _ ≤ ((ω.val.eraseIdx i).eraseIdx j).length := cs.length_wordProd_le _
            _ < ω.val.length := by grind
            _ = cs.length w := by rw [←ω.2.1, ←ω.2.2]
          rwa [lt_self_iff_false] at hlt
      | inr h' =>
          have h_i_lt2 : i < μ.val.length := lt_of_le_of_lt h' hj1
          specialize h_get_i_neq h_i_lt2
          let μ' := take (i + 1) ω.val ++ drop i (μ.val.eraseIdx j)
          have h'' : u = cs.wordProd μ' := by
            calc
              u = t * t * u := by rw [(cs.isReflection_of_mem_leftInvSeq _ ht).mul_self, one_mul]
              _ = t * ((cs.leftInvSeq ↑μ)[j] * cs.wordProd μ) := by
                nth_rw 1 [←hj2, μ.2.2, mul_assoc]
              _ = t * cs.wordProd (μ.val.eraseIdx j) := ?_
              _ = cs.wordProd (take (i + 1) ω.val) * ((cs.wordProd (take i ω.val))⁻¹
                  * cs.wordProd (μ.val.eraseIdx j)) := ?_
              _ = cs.wordProd (take (i + 1) ω.val) * ((cs.wordProd (take i ω.val))⁻¹
                  * cs.wordProd (take i (μ.val.eraseIdx j))
                  * cs.wordProd (drop i (μ.val.eraseIdx j))) := ?_
              _ = cs.wordProd (take (i + 1) ω.val) * cs.wordProd (drop i (μ.val.eraseIdx j)) := ?_
              _ = cs.wordProd (take (i + 1) ω.val ++ drop i (μ.val.eraseIdx j)) := by
                rw [wordProd_append]
            · rw [←cs.getD_leftInvSeq_mul_wordProd (μ.val) j,
                getD_eq_get (cs.leftInvSeq μ.val) 1 ⟨j, _⟩]
              rfl
            · unfold t
              rw [←wordProd_concat, concat_eq_append, take_append_getElem, mul_assoc]
            · rw [mul_right_inj, mul_assoc, mul_right_inj, ←wordProd_append, take_append_drop]
            · simp only [mul_right_inj, mul_eq_right]
              rw [inv_mul_eq_one]
              congr 1
              rw [take_eraseIdx_eq_take_of_le _ _ _ h']
              exact h_take_eq.symm
          have hμ_len : μ.val.length = μ'.length := by
            unfold μ'
            rw [length_append, length_take_of_le h_i_lt, length_drop, length_eraseIdx_of_lt hj1,
              ←Nat.sub_add_eq]
            nth_rw 2 [add_comm]
            exact (Nat.add_sub_of_le h_i_lt2).symm
          have hμ' : cs.IsReduced μ' := by
            unfold CoxeterSystem.IsReduced
            nth_rw 1 [←h'', ←hμ_len, μ.2.2]
            exact μ.2.1
          apply h_not_P_succ_i
          exists ⟨μ', hμ', h''⟩
          unfold μ'
          have : (take (i + 1) ω.val).length = i + 1 := length_take_of_le h_i_lt
          simp only [this, take_left', drop_left', true_and]
          rw [←tail_drop]
          cases Classical.em (drop i (μ.val.eraseIdx j) = []) with
          | inl heqnil =>
              rw [heqnil]
              exact nil_sublist _
          | inr hneqnil =>
              have h4 : drop i (μ.val.eraseIdx j) <+ (drop i ω.val) := calc
                drop i (μ.val.eraseIdx j) <+ drop i μ.val := (eraseIdx_sublist _ j).drop i
                _ <+ drop i ω.val := h_drop_sublist
              apply sublist_tail_of_head_neq hneqnil h4
              · rw [head_drop, head_drop]
                cases lt_or_eq_of_le h' with
                | inl hijlt => rwa [getElem_eraseIdx_of_lt _ hijlt]
                | inr hijeq =>
                    subst hijeq
                    rw [getElem_eraseIdx_of_ge _ le_rfl]
                    intro h
                    have h5 : i + 1 < μ'.length := by
                      rw [drop_eq_nil_iff, length_eraseIdx_of_lt, Nat.not_le] at hneqnil
                      · rw [←hμ_len]
                        apply Nat.add_lt_of_lt_sub
                        exact hneqnil
                      · exact hj1
                    apply neq_of_adjacent h5 hμ'
                    have h6 : μ'[i + 1] = ω.val[i] := by
                      unfold μ'
                      rw [getElem_append_right (length_take_le _ _)]
                      conv in (take (i + 1) ω.val).length =>
                        rw [length_take_of_le h_i_lt]
                      conv in i + 1 - i.succ =>
                        rw [Nat.sub_self]
                      rw [getElem_drop, getElem_eraseIdx_of_ge _ (le_refl _)]
                      exact h
                    have h7 : μ'[i] = ω.val[i] := by
                      unfold μ'
                      rw [getElem_append_left]
                      · rw [getElem_take]
                      · rw [length_take_of_le h_i_lt]
                        apply Nat.lt_add_one
                    rw [h6, h7]
  | inr h =>
      change u < v at h
      exists v
      have h4 : ν.length = μ.val.length + 1 := by
        unfold ν
        rw [length_append, length_take_of_le h_i_lt, length_drop]
        grind
      have hν : cs.IsReduced ν := by
        unfold CoxeterSystem.IsReduced
        apply eq_of_le_of_ge (cs.length_wordProd_le _)
        rw [h4, ←μ.2.1, ←μ.2.2, ←h3]
        exact length_lt_of_bruhat_lt h
      constructor
      · exact h
      · constructor
        · rw [lt_reflection_mul_iff ht u] at h
          rw [h3, hν, μ.2.2, μ.2.1]
          exact h4
        · exists ⟨ν, hν, h3⟩
          calc
            take (i + 1) ω.val ++ drop i μ.val <+ take (i + 1) ω.val ++ drop (i + 1) ω.val := ?_
            _ = ω.val := by rw [take_append_drop]
          · apply Sublist.append (Sublist.refl _)
            cases Nat.lt_or_eq_of_le h_i_le with
            | inl h' =>
                rw [←tail_drop]
                have h'' : drop i μ.val ≠ [] := by
                  rw [ne_eq, drop_eq_nil_iff, not_le]
                  exact h'
                apply sublist_tail_of_head_neq h'' h_drop_sublist
                rw [head_drop, head_drop]
                exact h_get_i_neq h'
            | inr h =>
                rw [h, drop_length]
                apply nil_sublist

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
      have h3 : w = t * v := by
        unfold t
        rw [inv_mul_cancel_right]
      have h4 : cs.IsLeftInversion (cs.wordProd ω) t := by
        constructor
        · exact h1
        · rw [←ω.prop.2]
          nth_rw 1 [h3]
          rwa [←mul_assoc, h1.mul_self, one_mul]
      have ⟨i, _, h5⟩ := strong_exchange h4
      nth_rw 1 [←ω.prop.2, h3, ←mul_assoc, h1.mul_self, one_mul] at h5
      have ⟨ω', h6, h7, h8⟩ := exists_reduced_subword (ω.val.eraseIdx i)
      have ⟨μ, h9⟩ := ih ⟨ω', h7, Eq.trans h5 h8⟩
      exists μ
      calc
        μ <+ ω' := h9
        _ <+ ω.val.eraseIdx i := h6
        _ <+ ω := eraseIdx_sublist _ _

theorem le_of_reduced_subword {u w : W} (μ : ReducedWord u) (ω : ReducedWord w)
  (h : μ.val <+ ω.val) : u ≤ w := by
  revert u
  suffices h : ∀ (k : ℕ), k ≤ ω.val.length →
    ∀ (u : W) (μ : ReducedWord u), μ.val <+ ω.val → μ.val.length = k → u ≤ w by
    intro u μ h2
    exact h (μ.val.length) (h2.length_le) u μ h2 rfl
  apply Nat.decreasingInduction
  · intro k hk ih u μ h1 h2
    subst h2
    have hneq : u ≠ w := by
      intro h
      apply ne_of_lt hk
      calc
        μ.val.length = cs.length u := by rw [←μ.2.1, ←μ.2.2]
        _ = cs.length w := by rw [h]
        _ = ω.val.length := by rw [←ω.2.1, ←ω.2.2]
    have ⟨v, hv1, hv2, ν, hν⟩ := reduced_subword_extend ω hneq ⟨μ, h1⟩
    rw [ν.2.2, ν.2.1, μ.2.2, μ.2.1] at hv2
    exact le_of_lt (lt_of_lt_of_le hv1 (ih v ν hν hv2))
  · intro u μ h1 h2
    rw [h1.length_eq] at h2
    rw [μ.2.2, ω.2.2, h2]

/-- Bjorner--Brenti Theorem 2.2.2 -/
theorem subword_property (u : W) {w : W} (ω : ReducedWord w) :
  u ≤ w ↔ ∃ (μ : ReducedWord u), μ.val <+ ω.val := by
  constructor
  · intro h
    apply exists_reduced_subword_of_le
    exact h
  · intro ⟨μ, h⟩
    exact le_of_reduced_subword _ _ h

theorem subword_property' {u w : W} :
  u ≤ w ↔ ∃ (μ : ReducedWord u) (ω : ReducedWord w), μ.val <+ ω.val := by
  constructor
  · intro h
    let ω : ReducedWord w := default
    rw [subword_property u ω] at h
    let ⟨μ, hμ⟩ := h
    exists μ, ω
  · intro ⟨μ, ω, h⟩
    rw [subword_property u ω]
    exists μ

/-- Bjorner--Brenti Corollary 2.2.4 (finiteness) -/
instance {u w : W} : Finite (Set.Icc u w) := by
  let ω : ReducedWord w := default
  let f : Set.Icc u w → {μ : List (B W) | μ <+ ω} :=
    fun x => ⟨(Classical.choose (exists_reduced_subword_of_le x.prop.2 ω)).val,
                Classical.choose_spec (exists_reduced_subword_of_le x.prop.2 ω)⟩
  have h_prod : ∀ x : Set.Icc u w, cs.wordProd ((f x).val) = x := by
    intro x
    symm
    exact (Classical.choose (exists_reduced_subword_of_le x.prop.2 ω)).prop.2
  have h_inj : Injective f := by
    intro x y h
    ext
    rw [←h_prod x, ←h_prod y, h]
  haveI : Finite {x | x <+ ω.val} := by
    have h := List.finite_toSet ω.val.sublists
    simp only [mem_sublists] at h
    exact h
  exact Finite.of_injective f h_inj

theorem inv_le_inv_of_le {u w : W} (h : u ≤ w) : u⁻¹ ≤ w⁻¹ := by
  rw [subword_property'] at h ⊢
  let ⟨μ, ω, h'⟩ := h
  exists μ.reverse, ω.reverse
  rwa [ReducedWord.reverse, ReducedWord.reverse, reverse_sublist]

/-- Bjorner--Brenti Corollary 2.2.5 -/
theorem inv_le_inv_iff {u w : W} : u⁻¹ ≤ w⁻¹ ↔ u ≤ w := by
  constructor
  · intro h
    rw [←inv_inv u, ←inv_inv w]
    exact inv_le_inv_of_le h
  · exact inv_le_inv_of_le

end Coxeter
