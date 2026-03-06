import Mathlib.Order.Grade
import Coxeter.StrongExchange

/-!
# Bruhat order

This file defines the Bruhat order.

## Main definitions

* `Coxeter.le` : The Bruhat order
* `Coxeter.w₀` : The longest element

## Main Statements

* `Coxeter.subword_property`
* `Coxeter.lifting_property`
* `Coxeter.length_cover`

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

private theorem length_le_of_le {u w : W} (h : u ≤ w) : cs.length u ≤ cs.length w := by
  induction h with
  | rfl => rfl
  | step _ _ _ _ h3 ih => exact le_of_lt (lt_of_le_of_lt ih h3)

private theorem length_lt_of_lt {u w : W} (h : u < w) : cs.length u < cs.length w := by
  cases h.1 with
  | rfl =>
      exfalso
      apply h.2
      rfl
  | step _ _ h1 _ h3 =>
      exact lt_of_le_of_lt (length_le_of_le h1) h3

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
        apply lt_irrefl (cs.length u)
        exact lt_of_lt_of_le (length_lt_of_lt h) (length_le_of_le h2)
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
        exfalso
        apply lt_irrefl (cs.length v)
        calc
          cs.length v < cs.length w := h5
          _ ≤ cs.length u := length_le_of_le h2
          _ ≤ cs.length v := length_le_of_le h3

theorem monotone_length : Monotone (@cs W).length := by apply length_le_of_le

theorem strictMono_length : StrictMono (@cs W).length := by apply length_lt_of_lt

theorem eq_of_le_of_length_eq {u w : W} (h : u ≤ w) (h2 : cs.length u = cs.length w) : u = w := by
  apply eq_of_le_of_not_lt h
  intro h3
  replace h3 := strictMono_length h3
  rw [h2] at h3
  exact lt_irrefl _ h3

instance : OrderBot W where
  bot := 1
  bot_le := by
    intro w
    let ⟨ω, hω1, hω2⟩ := cs.exists_reduced_word' w
    subst hω2
    revert hω1
    induction ω with
    | nil =>
        intro
        rw [wordProd_nil]
    | cons a as ih =>
        intro h
        have h' := h.drop 1
        dsimp at h'
        specialize ih h'
        apply le.step 1 (cs.wordProd as) _ ih
        · rw [wordProd_cons, mul_inv_cancel_right]
          exact cs.isReflection_simple a
        · rw [h, h', length_cons]
          apply Nat.le_refl

theorem lt_reflection_mul_iff {t : W} (ht : cs.IsReflection t) (w : W)
  : w < t * w ↔ cs.length w < cs.length (t * w) := by
  constructor
  · intro h
    apply strictMono_length
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

theorem simple_mul_gt_iff (i : B W) (w : W) : cs.simple i * w > w ↔ ¬ cs.IsLeftDescent w i := by
  rw [gt_iff_lt, cs.not_isLeftDescent_iff, lt_reflection_mul_iff (cs.isReflection_simple i) w]
  have := cs.length_simple_mul w i
  grind

theorem simple_mul_lt_iff (i : B W) (w : W) : cs.simple i * w < w ↔ cs.IsLeftDescent w i := by
  apply reflection_mul_lt_iff (cs.isReflection_simple i)

theorem mul_reflection_lt_or_gt (w : W) {t : W} (ht : cs.IsReflection t) :
  t * w < w ∨ t * w > w := by
  conv in t * w > w => change w < t * w
  rw [reflection_mul_lt_iff ht, lt_reflection_mul_iff ht]
  exact Nat.lt_or_gt_of_ne (ht.length_mul_right_ne w)

open Classical in
/-- Bjorner--Brenti Lemma 2.2.1 -/
theorem reduced_subword_extend {u w : W} (ω : ReducedWord w)
  (h1 : u ≠ w) (h2 : ∃ (μ : ReducedWord u), μ.val <+ ω.val) :
  ∃ (v : W), v > u ∧ cs.length v = cs.length u + 1 ∧ ∃ (ν : ReducedWord v), ν.val <+ ω.val := by
  let P (i : ℕ) := ∃ (μ : ReducedWord u), take i μ.val = take i ω.val ∧ drop i μ.val <+ drop i ω.val
  let i := Nat.findGreatest P ω.length
  have h_P_i : P i := by
    apply Nat.findGreatest_spec (zero_le _)
    simp only [P, take_zero, drop_zero, true_and]
    exact h2
  unfold P at h_P_i
  have ⟨μ, h_take_eq, h_drop_sublist⟩ := h_P_i
  have h_i_le : i ≤ μ.length := by
    by_contra! h
    apply lt_irrefl i
    rw [take_of_length_le (le_of_lt h)] at h_take_eq
    unfold ReducedWord.length at h
    rwa [h_take_eq, length_take_of_le (Nat.findGreatest_le _)] at h
  have hsub : μ.val <+ ω.val := by
    apply sublist_take_drop _ h_drop_sublist
    rw [h_take_eq]
  have h_i_lt : i < ω.length := by
    apply lt_of_lt_of_le (add_le_add_left h_i_le 1)
    apply lt_of_le_of_ne hsub.length_le
    intro h
    rw [hsub.length_eq] at h
    rw [←μ.wordProd_eq, h, ω.wordProd_eq] at h1
    contradiction
  have h_not_P_succ_i : ¬ P (i + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self i) h_i_lt
  have h_get_i_ne : (hi : i < μ.length) → μ.val[i] ≠ ω.val[i] := by
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
      rw [μ.wordProd_eq, ←wordProd_concat, concat_eq_append, take_append_getElem]
    · rw [wordProd_append, wordProd_append, h_take_eq]
      group
  cases mul_reflection_lt_or_gt u ht with
  | inl h =>
      exfalso
      rw [reflection_mul_lt_iff ht] at h
      replace ht : cs.IsLeftInversion u t := ⟨ht, h⟩
      rw [←μ.wordProd_eq, isLeftInversion_iff_mem_leftInvSeq t μ.prop.1] at ht
      have ⟨⟨j, hj1⟩, hj2⟩ := get_of_mem ht
      rw [length_leftInvSeq] at hj1
      replace hj2 : t = (cs.leftInvSeq μ.val)[j] := hj2.symm
      cases Nat.lt_or_ge j i with
      | inl h' =>
          apply lt_irrefl (cs.length w)
          have : i < (cs.leftInvSeq ω.val).length := by rwa [length_leftInvSeq]
          have : j < ω.length := Nat.lt_of_lt_of_le hj1 hsub.length_le
          have ht' : t = (cs.leftInvSeq ω)[i] := by rw [getElem_leftInvSeq]
          have ht'' : t = (cs.leftInvSeq ω)[j] := by
            rw [hj2]
            rw [ReducedWord.length, ←cs.length_leftInvSeq μ.val] at h_i_le
            conv =>
              lhs
              rw [←@getElem_take _ _ i _ (by rwa [length_take_of_le h_i_le])]
              congr
              rw [←leftInvSeq_take, h_take_eq, leftInvSeq_take]
            rw [getElem_take]
          have hweq : w = cs.wordProd ((ω.val.eraseIdx i).eraseIdx j) := calc
            w = t * t * w := by rw [(cs.isReflection_of_mem_leftInvSeq _ ht).mul_self, one_mul]
            _ = (cs.leftInvSeq ↑ω)[j] * (cs.leftInvSeq ↑ω)[i] * cs.wordProd ω.val := by
              rw [←ht', ←ht'', ω.wordProd_eq]
            _ = cs.wordProd ((ω.val.eraseIdx i).eraseIdx j) :=
              getElem_leftInvSeq_mul_wordProd₂ ω.val h' h_i_lt
          calc
            cs.length w = cs.length (cs.wordProd ((ω.val.eraseIdx i).eraseIdx j)) := by
              nth_rw 1 [hweq]
            _ ≤ ((ω.val.eraseIdx i).eraseIdx j).length := cs.length_wordProd_le _
            _ < ω.length := by grind
            _ = cs.length w := ω.length_eq
      | inr h' =>
          have h_i_lt2 : i < μ.length := lt_of_le_of_lt h' hj1
          specialize h_get_i_ne h_i_lt2
          let μ' := take (i + 1) ω.val ++ drop i (μ.val.eraseIdx j)
          have h'' : u = cs.wordProd μ' := by
            calc
              u = t * t * u := by rw [(cs.isReflection_of_mem_leftInvSeq _ ht).mul_self, one_mul]
              _ = t * ((cs.leftInvSeq ↑μ)[j] * cs.wordProd μ) := by
                nth_rw 1 [←hj2, μ.wordProd_eq, mul_assoc]
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
          have hμ_len : μ.length = μ'.length := by
            unfold μ'
            rw [length_append, length_take_of_le h_i_lt, length_drop, length_eraseIdx_of_lt hj1,
              ←Nat.sub_add_eq]
            nth_rw 2 [add_comm]
            exact (Nat.add_sub_of_le h_i_lt2).symm
          have hμ' : cs.IsReduced μ' := by
            unfold CoxeterSystem.IsReduced
            nth_rw 1 [←h'', ←hμ_len, ←μ.wordProd_eq]
            exact μ.prop.1
          apply h_not_P_succ_i
          exists ⟨μ', hμ', h''⟩
          unfold μ'
          simp only [length_take_of_le h_i_lt, take_left', drop_left', true_and]
          rw [←tail_drop]
          cases lt_or_eq_of_le h' with
          | inl hlt =>
              have h4 : i < (μ.val.eraseIdx j).length := by
                rw [length_eraseIdx_of_lt hj1, Nat.lt_sub_iff_add_lt]
                exact lt_of_le_of_lt hlt hj1
              have h5 : drop i (μ.val.eraseIdx j) ≠ [] := by
                rwa [ne_eq, drop_eq_nil_iff, not_le]
              apply sublist_tail_of_head_ne h5
              · simp only [head_drop, ne_eq]
                rw [getElem_eraseIdx_of_lt h4 hlt]
                exact h_get_i_ne
              · apply List.Sublist.drop
                exact Sublist.trans (eraseIdx_sublist _ _) hsub
          | inr heq =>
              rw [←add_zero j, ←heq, ←drop_eraseIdx μ.val i 0, eraseIdx_zero, ←drop_one, ←drop_one]
              exact h_drop_sublist.drop 1
  | inr h =>
      change u < v at h
      exists v
      have h4 : ν.length = μ.length + 1 := by
        rw [length_append, length_take_of_le h_i_lt, length_drop,
          add_comm, Nat.succ_eq_add_one, ←add_assoc, Nat.sub_add_cancel h_i_le]
      have hν : cs.IsReduced ν := by
        unfold CoxeterSystem.IsReduced
        apply eq_of_le_of_ge (cs.length_wordProd_le _)
        rw [h4, μ.length_eq, ←h3]
        exact strictMono_length h
      constructor
      · exact h
      · constructor
        · rwa [h3, hν, ←μ.length_eq]
        · exists ⟨ν, hν, h3⟩
          dsimp [ν]
          nth_rw 2 [←take_append_drop (i + 1) ω.val]
          apply Sublist.append (Sublist.refl _)
          cases Nat.lt_or_eq_of_le h_i_le with
          | inl h' =>
              rw [←tail_drop]
              have h'' : drop i μ.val ≠ [] := by
                rw [ne_eq, drop_eq_nil_iff, not_le]
                exact h'
              apply sublist_tail_of_head_ne h'' h_drop_sublist
              rw [head_drop, head_drop]
              exact h_get_i_ne h'
          | inr h' =>
              rw [h', drop_length]
              apply nil_sublist

theorem exists_reduced_subword_of_le {u w : W} (h : u ≤ w) (ω : ReducedWord w) :
  ∃ (μ : ReducedWord u), μ.val <+ ω.val := by
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
        · rw [ω.wordProd_eq]
          nth_rw 1 [h3]
          rwa [←mul_assoc, h1.mul_self, one_mul]
      have ⟨i, _, h5⟩ := strong_exchange h4
      nth_rw 1 [ω.wordProd_eq, h3, ←mul_assoc, h1.mul_self, one_mul] at h5
      have ⟨ω', h6⟩ := exists_reduced_subword' h5
      have ⟨μ, h7⟩ := ih ω'
      exists μ
      calc
        μ <+ ω' := h7
        _ <+ ω.val.eraseIdx i := h6
        _ <+ ω := eraseIdx_sublist _ _

theorem le_of_reduced_subword {u w : W} (μ : ReducedWord u) (ω : ReducedWord w)
  (h : μ.val <+ ω.val) : u ≤ w := by
  revert u
  suffices h : ∀ (k : ℕ), k ≤ ω.length →
    ∀ (u : W) (μ : ReducedWord u), μ.val <+ ω.val → μ.length = k → u ≤ w by
    intro u μ h2
    exact h μ.length h2.length_le u μ h2 rfl
  apply Nat.decreasingInduction
  · intro k hk ih u μ h1 h2
    subst h2
    have hne : u ≠ w := by
      intro h
      apply ne_of_lt hk
      calc
        μ.length = cs.length u := μ.length_eq
        _ = cs.length w := by rw [h]
        _ = ω.length := ω.length_eq.symm
    have ⟨v, hv1, hv2, ν, hν⟩ := reduced_subword_extend ω hne ⟨μ, h1⟩
    rw [←ν.length_eq, ←μ.length_eq] at hv2
    exact le_of_lt (lt_of_lt_of_le hv1 (ih v ν hν hv2))
  · intro u μ h1 h2
    rw [h1.length_eq] at h2
    rw [←μ.wordProd_eq, ←ω.wordProd_eq, h2]

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

private noncomputable def chooseReducedSubword {w : W} (ω : ReducedWord w) :
  Set.Iic w → {μ : List (B W) | μ <+ ω} :=
  fun ⟨_, hx⟩ =>
    ⟨(Classical.choose (exists_reduced_subword_of_le hx ω)).val,
      Classical.choose_spec (exists_reduced_subword_of_le hx ω)⟩

private theorem wordProd_chooseReducedSubword {w : W} (ω : ReducedWord w) (x : Set.Iic w) :
  cs.wordProd ((chooseReducedSubword ω x).val) = x :=
  (Classical.choose (exists_reduced_subword_of_le x.prop ω)).prop.2.symm

private theorem chooseReducedSubword_inj {w : W} (ω : ReducedWord w) :
  Injective (chooseReducedSubword ω) := by
  intro x y h
  ext
  rw [←wordProd_chooseReducedSubword ω, h, wordProd_chooseReducedSubword ω]

theorem finite_Icc (u w : W) : Finite (Set.Icc u w) := by
  let ω : ReducedWord w := default
  have hsubs : Set.Icc u w ⊆ Set.Iic w := by grind
  let f : Set.Icc u w → {μ : List (B W) | μ <+ ω} :=
    @Set.restrict₂ _ (fun _ => {μ : List (B W) | μ <+ ω}) _ _ hsubs (chooseReducedSubword ω)
  haveI : Finite {x | x <+ ω.val} := by
    have h := List.finite_toSet ω.val.sublists
    simp only [mem_sublists] at h
    exact h
  apply Finite.of_injective f
  intro x y h
  ext
  replace h := chooseReducedSubword_inj ω h
  rwa [Subtype.mk.injEq] at h

noncomputable instance : LocallyFiniteOrder W := LocallyFiniteOrder.ofFiniteIcc finite_Icc

open Classical in
/-- Bjorner--Brenti Corollary 2.2.4 -/
theorem card_Icc_le (u w : W) : Finset.card (Finset.Icc u w) ≤ 2 ^ cs.length w := by
  let ω : ReducedWord w := default
  let f : Finset.Icc u w → ω.val.sublists.toFinset :=
    fun x => ⟨chooseReducedSubword ω ⟨x.val, (Finset.mem_Icc.mp x.prop).2⟩, ?_⟩
  swap
  · change (chooseReducedSubword ω ⟨x.val, (Finset.mem_Icc.mp x.prop).2⟩).val
      ∈ ω.val.sublists.toFinset
    rw [@List.mem_toFinset _ _ (ω.val.sublists)]
    rw [mem_sublists]
    exact (chooseReducedSubword ω ⟨x.val, (Finset.mem_Icc.mp x.prop).2⟩).prop
  have hf_inj : Injective f := by
    intro x y h
    unfold f at h
    rw [Subtype.mk.injEq, Subtype.val_inj] at h
    replace h := chooseReducedSubword_inj ω h
    rw [Subtype.mk.injEq, Subtype.val_inj] at h
    exact h
  rw [←ω.length_eq]
  have hle := le_trans (Finset.card_le_card_of_injective hf_inj) (List.toFinset_card_le _)
  rw [length_sublists] at hle
  unfold ReducedWord.length
  exact hle

/-- Bjorner--Brenti Corollary 2.2.5 -/
theorem monotone_inv : Monotone (@Inv.inv W _) := by
  intro u w h
  rw [subword_property'] at h ⊢
  let ⟨μ, ω, h'⟩ := h
  exists μ.reverse, ω.reverse
  rwa [ReducedWord.reverse, ReducedWord.reverse, reverse_sublist]

theorem strictMono_inv : StrictMono (@Inv.inv W _) := by
  intro u w h
  constructor
  · exact monotone_inv h.1
  · intro h2
    rw [inv_inj] at h2
    exact h.2 h2

theorem length_cover {u w : W} (h : u ⋖ w) : cs.length w = cs.length u + 1 := by
  apply eq_of_le_of_ge
  · by_contra! h2
    let ω : ReducedWord w := default
    have hne : u ≠ w := by grind
    let ⟨v, h3, h4, ν, hν⟩ := reduced_subword_extend ω hne (exists_reduced_subword_of_le h.1.1 ω)
    apply h.2 h3
    constructor
    · exact le_of_reduced_subword ν ω hν
    · intro heq
      rw [←h4, heq, lt_self_iff_false] at h2
      contradiction
  · exact strictMono_length h.1

theorem cover_iff {u w : W} : u ⋖ w ↔ u ≤ w ∧ cs.length w = cs.length u + 1 := by
  constructor
  · intro h
    constructor
    · exact le_of_lt h.1
    · exact length_cover h
  · intro h
    constructor
    · apply lt_of_le_of_ne h.1
      grind
    · intro z hz1 hz2
      apply not_le_of_gt (strictMono_length hz1)
      have h2 := strictMono_length hz2
      rwa [h.2, Nat.lt_succ_iff] at h2

/-- Bjorner--Brenti Theorem 2.2.6 -/
theorem exists_cover_of_lt {u w : W} (h : u < w) : ∃ (v : W), u ⋖ v ∧ v ≤ w := by
  let ω : ReducedWord w := default
  have ⟨v, h2, h3, ν, hν⟩ := reduced_subword_extend ω (ne_of_lt h)
    (exists_reduced_subword_of_le (le_of_lt h) ω)
  exists v
  constructor
  · rw [cover_iff]
    constructor
    · exact (le_of_lt h2)
    · exact h3
  · exact le_of_reduced_subword ν ω hν

noncomputable instance : GradeMinOrder ℕ W where
  grade := cs.length
  grade_strictMono := strictMono_length
  covBy_grade := by
    intro u w h
    rw [Nat.covBy_iff_add_one_eq]
    exact (length_cover h).symm
  isMin_grade := by
    intro x hx
    rw [isMin_iff_eq_bot] at *
    rw [hx, Nat.bot_eq_zero, CoxeterSystem.length_eq_zero_iff]
    rfl

instance : WellFoundedLT W := inferInstance

/-- Bjorner--Brenti Proposition 2.2.7 -/
theorem lifting_property {u w : W} {i : B W}
  (h1 : u ≤ w) (h2 : cs.IsLeftDescent w i) (h3 : ¬ cs.IsLeftDescent u i) :
  u ≤ cs.simple i * w ∧ cs.simple i * u ≤ w := by
  let ⟨ω, hω1, hω2⟩ := cs.exists_reduced_word' (cs.simple i * w)
  have h4 : cs.IsReduced (i :: ω) := by
    unfold CoxeterSystem.IsReduced at *
    rw [isLeftDescent_iff, hω2, hω1] at h2
    rw [wordProd_cons, ←hω2, simple_mul_simple_cancel_left, length_cons]
    exact h2.symm
  rw [←eq_inv_mul_iff_mul_eq, inv_simple, ←wordProd_cons] at hω2
  have ⟨μ, hμ⟩ := exists_reduced_subword_of_le h1 ⟨i :: ω, h4, hω2⟩
  dsimp at hμ
  cases em (u = 1) with
  | inl hu =>
      subst hu
      constructor
      · exact bot_le
      · rw [mul_one, hω2]
        apply le_of_reduced_subword ⟨[i], _⟩ ⟨i :: ω, _⟩
        · simp
        · simp
        · simp [h4]
  | inr hu =>
      have h5 : ¬ μ.val = [] := by
        intro h
        apply hu
        have heq := μ.wordProd_eq
        rw [h, wordProd_nil] at heq
        exact heq.symm
      have h6 : head μ.val h5 ≠ i := by
        intro h
        apply h3
        unfold IsLeftDescent
        rw [←μ.wordProd_eq]
        nth_rw 1 [←cons_head_tail h5, h, wordProd_cons]
        have h7 := μ.2.1.drop 1
        rw [drop_one] at h7
        rw [simple_mul_simple_cancel_left, h7, μ.2.1, length_tail]
        apply Nat.sub_one_lt
        simp only [ne_eq, List.length_eq_zero_iff]
        exact h5
      have h7 : μ.val <+ ω := by
        rw [←cons_head_tail h5] at hμ
        have h8 := List.Sublist.of_cons_of_ne h6 hμ
        rwa [cons_head_tail h5] at h8
      have h8 : i :: μ.val <+ i :: ω := by grind
      constructor
      · apply le_of_reduced_subword μ ⟨ω, hω1, _⟩
        · exact h7
        · rw [wordProd_cons] at hω2
          rw [hω2]
          simp
      · apply le_of_reduced_subword ⟨i :: μ.val, _, _⟩ ⟨i :: ω, h4, hω2⟩
        · exact h8
        · unfold CoxeterSystem.IsReduced
          rw [not_isLeftDescent_iff] at h3
          rw [wordProd_cons, μ.wordProd_eq, h3, length_cons, ←μ.2.1, ←μ.2.2]
        · rw [wordProd_cons, μ.wordProd_eq]

/-- Bjorner--Brenti Corollary 2.2.8 (i) -/
theorem local_configuration {i : B W} {t w : W}
  (h : cs.simple i ≠ t) (h2 : w ⋖ cs.simple i * w) (h3 : w ⋖ t * w) :
  cs.simple i * w ⋖ cs.simple i * t * w ∧ t * w ⋖ cs.simple i * t * w := by
  cases mul_reflection_lt_or_gt (t * w) (cs.isReflection_simple i) with
  | inl h4 =>
      exfalso
      apply h
      have : cs.simple i * w ≤ t * w := by
        apply (lifting_property (le_of_lt h3.1) _ _).2
        · rwa [←simple_mul_lt_iff]
        · rw [←simple_mul_gt_iff]
          exact h2.1
      rw [cover_iff] at h2 h3
      have := eq_of_le_of_length_eq this (by grind)
      rwa [mul_left_inj] at this
  | inr h4 =>
      have h5 : cs.IsLeftDescent (cs.simple i * (t * w)) i := by
        rwa [simple_mul_gt_iff, isLeftDescent_iff_not_isLeftDescent_mul, not_not] at h4
      have h6 : ¬ cs.IsLeftDescent w i := by
        rw [←simple_mul_gt_iff]
        exact h2.1
      have h7 := lifting_property (le_of_lt (lt_trans h3.1 h4)) h5 h6
      simp only [←mul_assoc, simple_mul_simple_self, one_mul] at h7
      constructor
      · rw [cover_iff]
        constructor
        · exact h7.2
        · rw [simple_mul_gt_iff, not_isLeftDescent_iff, ←mul_assoc] at h4
          rw [cover_iff] at h2 h3
          rw [h4, h2.2, h3.2]
      · rw [cover_iff]
        constructor
        · rw [mul_assoc]
          exact le_of_lt h4
        · rwa [simple_mul_gt_iff, not_isLeftDescent_iff, ←mul_assoc] at h4

/-- Bjorner--Brenti Proposition 2.2.9 -/
instance : IsDirectedOrder W where
  directed := by
    intro u
    induction u using WellFoundedLT.induction with
    | ind u ih =>
        intro w
        cases em (u = 1) with
        | inl h =>
            exists w
            rw [h]
            simp only [le_refl, and_true]
            exact bot_le
        | inr h =>
            let ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h
            have hlt : cs.simple i * u < u := by
              rw [reflection_mul_lt_iff (cs.isReflection_simple i)]
              exact hi
            let ⟨x, hx1, hx2⟩ := ih (cs.simple i * u) hlt w
            cases em (cs.IsLeftDescent x i) with
            | inl h2 =>
                exists x
                rw [isLeftDescent_iff_not_isLeftDescent_mul] at hi
                have ⟨h3, h4⟩ := lifting_property hx1 h2 hi
                rw [simple_mul_simple_cancel_left] at h4
                constructor
                · exact h4
                · exact hx2
            | inr h2 =>
                exists cs.simple i * x
                have h3 : cs.simple i * x ≥ x := by
                  apply le_of_lt
                  rwa [←simple_mul_gt_iff] at h2
                rw [isLeftDescent_iff_not_isLeftDescent_mul, not_not] at h2
                rw [isLeftDescent_iff_not_isLeftDescent_mul] at hi
                have ⟨h4, h5⟩ := lifting_property (le_trans hx1 h3) h2 hi
                rw [simple_mul_simple_cancel_left] at h4 h5
                constructor
                · exact h5
                · apply le_trans hx2 h3

section finite

/-! ### Bruhat order on finite Coxeter groups -/

theorem isTop_iff_all_isLeftDescent {x : W} : (∀ (i : B W), cs.IsLeftDescent x i) ↔ IsTop x := by
  constructor
  · intro h u
    induction u using WellFoundedLT.induction with
    | ind u ih =>
        cases em (u = 1) with
        | inl h2 =>
            rw [h2]
            exact bot_le
        | inr h2 =>
            let ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h2
            rw [←simple_mul_lt_iff] at hi
            have h3 := ih _ hi
            rw [simple_mul_lt_iff, isLeftDescent_iff_not_isLeftDescent_mul] at hi
            have h4 := (lifting_property h3 (h i) hi).2
            rwa [simple_mul_simple_cancel_left] at h4
  · intro h i
    rw [←simple_mul_lt_iff]
    apply lt_of_le_of_ne
    · apply h
    · simp

instance [OrderTop W] : Finite W := by
  apply Finite.of_finite_univ
  apply Set.Finite.ofFinset (Finset.Icc (⊥ : W) (⊤ : W))
  intro w
  simp

/-- Bjorner--Brenti Proposition 2.3.1 (ii) -/
theorem finite_of_exists_all_isLeftDescent {x : W} (h : ∀ (i : B W), cs.IsLeftDescent x i) :
  Finite W := by
  haveI : OrderTop W := {
    top := x
    le_top := isTop_iff_all_isLeftDescent.mp h
  }
  infer_instance

variable [Finite W]

noncomputable irreducible_def w₀ : W :=
  Classical.choose (@Finite.exists_le_maximal W _ _ (fun _ => PUnit) 1 PUnit.unit)

/-- Bjorner--Brenti Proposition 2.3.1 (i) -/
noncomputable instance : OrderTop W where
  top := w₀
  le_top := by
    apply IsMax.isTop
    intro w hw
    rw [w₀_def] at *
    exact (Classical.choose_spec
      (@Finite.exists_le_maximal W _ _ (fun _ => PUnit) 1 PUnit.unit)).2.2 PUnit.unit hw

/-- Bjorner--Brenti Proposition 2.3.1 (ii) continued -/
theorem all_isLeftDescent_iff (x : W) : (∀ (i : B W), cs.IsLeftDescent x i) ↔ x = w₀ := by
  rw [isTop_iff_all_isLeftDescent]
  constructor
  · intro h
    apply top_unique
    apply h
  · intro h w
    rw [h]
    exact le_top

theorem exists_left_ascent_of_ne_w₀ {x : W} (h : x ≠ w₀) : ∃ (i : B W), cs.simple i * x > x := by
  by_contra! h2
  apply h
  rw [←all_isLeftDescent_iff]
  conv at h2 =>
    intro i
    rw [simple_mul_gt_iff, not_not]
  exact h2

theorem length_le_length_w₀ (w : W) : cs.length w ≤ cs.length (w₀ : W) :=
  monotone_length le_top

theorem eq_w₀_of_length_ge {x : W} (h : cs.length x ≥ cs.length (w₀ : W)) : x = w₀ := by
  apply eq_of_le_of_not_lt le_top
  intro h2
  exact not_le_of_gt (strictMono_length h2) h

@[simp]
theorem inv_w₀ : (w₀⁻¹ : W) = w₀ := by
  apply eq_w₀_of_length_ge
  rw [length_inv]

@[simp]
theorem w₀_mul_self : (w₀ : W) * w₀ = 1 := by
  nth_rw 1 [←inv_w₀, inv_mul_cancel]

/-- Bjorner--Brenti Proposition 2.3.2 (i) -/
@[simp]
theorem w₀_sq : (w₀ : W) ^ 2 = 1 := by
  rw [sq, w₀_mul_self]

/-- Bjorner--Brenti Proposition 2.3.2 (ii) -/
theorem length_mul_w₀ (w : W) : cs.length (w * w₀) = cs.length (w₀ : W) - cs.length w := by
  apply le_antisymm
  · revert w
    suffices h : ∀ (k : ℕ), k ≤ cs.length w₀ → ∀ (w : W), cs.length w = k →
      cs.length (w * w₀) ≤ cs.length (w₀ : W) - cs.length w by
      intro w
      exact h (cs.length w) (length_le_length_w₀ w) w rfl
    apply Nat.decreasingInduction
    · intro k hk ih w hw
      rw [←hw] at hk
      have h : w ≠ w₀ := by grind
      let ⟨i, hi⟩ := exists_left_ascent_of_ne_w₀ h
      rw [simple_mul_gt_iff, not_isLeftDescent_iff] at hi
      have h2 : cs.length (cs.simple i * w * w₀) ≤
        cs.length (w₀ : W) - cs.length (cs.simple i * w) := by
        rw [hw] at hi
        exact ih (cs.simple i * w) hi
      calc
        cs.length (w * w₀) ≤ cs.length (cs.simple i * w * w₀) + 1 := ?_
        _ ≤ cs.length (w₀ : W) - cs.length (cs.simple i * w) + 1 := add_le_add_left h2 1
        _ = cs.length (w₀ : W) - (cs.length w + 1) + 1 := by rw [hi]
        _ = cs.length w₀ - cs.length w := by grind
      · have h3 := cs.length_mul_le (cs.simple i) (cs.simple i * w * w₀)
        rw [mul_assoc] at h3
        simp at h3
        grind
    · intro w hw
      replace hw := eq_w₀_of_length_ge (ge_of_eq hw)
      subst hw
      simp
  · apply length_mul_ge_length_sub_length'

/-- Bjorner--Brenti Proposition 2.3.2 (iii) -/
theorem isLeftInversion_mul_w₀_iff {w t : W} (ht : cs.IsReflection t) :
  cs.IsLeftInversion (w * w₀) t ↔ ¬ cs.IsLeftInversion w t := by
  unfold IsLeftInversion
  rw [←mul_assoc, length_mul_w₀, length_mul_w₀]
  have := ht.length_mul_right_ne w
  have := length_le_length_w₀ w
  have := length_le_length_w₀ (t * w)
  grind

theorem isLeftInversion_w₀_iff (t : W) : cs.IsLeftInversion w₀ t ↔ cs.IsReflection t := by
  constructor
  · intro ht
    exact ht.1
  · intro ht
    rw [←one_mul w₀, isLeftInversion_mul_w₀_iff ht]
    unfold IsLeftInversion
    simp

private def isLeftInversion_equiv_isReflection :
  {t : W // cs.IsLeftInversion w₀ t} ≃ ReflectionSet W :=
  Equiv.subtypeEquivRight (@isLeftInversion_w₀_iff W _ _)

instance : Finite (ReflectionSet W) :=
  Finite.of_equiv _ isLeftInversion_equiv_isReflection

/-- Bjorner--Brenti Proposition 2.3.2 (iv) -/
theorem length_w₀_eq_card_reflectionSet :
  cs.length (w₀ : W) = Nat.card (ReflectionSet W) := by
  rw [←card_of_IsLeftInversion]
  exact Nat.card_congr isLeftInversion_equiv_isReflection

/-- Bjorner--Brenti Corollary 2.3.3 (i) -/
theorem length_w₀_mul (w : W) : cs.length (w₀ * w) = cs.length (w₀ : W) - cs.length w := by
  rw [←length_inv, mul_inv_rev, inv_w₀, length_mul_w₀, length_inv]

/-- Bjorner--Brenti Corollary 2.3.3 (ii) -/
theorem length_conj_w₀ (w : W) : cs.length (MulAut.conj w₀ w) = cs.length w := by
  dsimp
  rw [inv_w₀, length_mul_w₀, length_w₀_mul]
  have := length_le_length_w₀ w
  grind

/-- Bjorner--Brenti Proposition 2.3.4 (i) -/
theorem antitone_mul_w₀ {u w : W} (h : u ≤ w) : w * w₀ ≤ u * w₀ := by
  induction h with
  | rfl => rfl
  | step v w h1 h2 h3 ih =>
      apply le_trans _ ih
      apply le.step (w * w₀) (w * w₀) (v * w₀) (le.rfl _)
      · rw [mul_inv_rev, mul_assoc, mul_inv_cancel_left]
        rwa [←h2.inv, mul_inv_rev, inv_inv] at h2
      · rw [length_mul_w₀, length_mul_w₀]
        have := length_le_length_w₀ w
        grind

theorem antitone_w₀_mul {u w : W} (h : u ≤ w) : w₀ * w ≤ w₀ * u := by
  rw [←inv_inv (w₀ * w), ←inv_inv (w₀ * u)]
  apply monotone_inv
  rw [mul_inv_rev, mul_inv_rev, inv_w₀]
  apply antitone_mul_w₀
  exact monotone_inv h

/-- Bjorner--Brenti Proposition 2.3.4 (ii) -/
theorem monotone_conj_w₀ {u w : W} (h : u ≤ w) : MulAut.conj w₀ u ≤ MulAut.conj w₀ w := by
  dsimp
  rw [inv_w₀]
  apply antitone_mul_w₀
  apply antitone_w₀_mul
  exact h

end finite

end Coxeter
