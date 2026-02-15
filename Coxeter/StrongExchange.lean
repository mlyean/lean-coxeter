import Coxeter.PermutationRepresentation

/-!
# Strong Exchange

This file proves the strong exchange property of Coxeter groups and friends.
-/

namespace CoxeterSystem

open Function List

variable {B : Type*}
variable {W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

open Classical in
/-- Bjorner--Brenti Corollary 1.4.4 (a) implies (c) -/
theorem mem_leftInvSeq_of_isLeftInversion
  {ω : List B} {t : W} (ht : cs.IsReflection t) (h : cs.IsLeftInversion (cs.wordProd ω) t) :
  t ∈ cs.leftInvSeq ω := by
  have hrw := cs.eta_eq_one_iff (cs.wordProd ω) t ht
  rw [IsLeftInversion, ←hrw, eta_spec] at h
  have h2 : 0 < count t (cs.leftInvSeq ω) := by
    rw [pos_iff_ne_zero]
    intro heq
    rw [heq] at h
    have := h.2
    contradiction
  rw [←count_pos_iff]
  exact h2

/-- Bjorner--Brenti Corollary 1.4.4 (a) iff (c) -/
theorem isLeftInversion_iff_mem_leftInvSeq
  {ω : List B} (t : W) (hω : cs.IsReduced ω) :
  cs.IsLeftInversion (cs.wordProd ω) t ↔ t ∈ cs.leftInvSeq ω := by
  constructor
  · intro h
    exact cs.mem_leftInvSeq_of_isLeftInversion h.1 h
  · exact cs.isLeftInversion_of_mem_leftInvSeq hω

open Classical in
/-- Bjorner--Brenti Theorem 1.4.3 -/
theorem strong_exchange
  {ω : List B} {t : W} (ht : cs.IsReflection t) (h : cs.IsLeftInversion (cs.wordProd ω) t) :
  ∃ i < ω.length, t * cs.wordProd ω = cs.wordProd (ω.eraseIdx i) := by
  have h2 := cs.mem_leftInvSeq_of_isLeftInversion ht h
  rw [mem_iff_get] at h2
  let ⟨i, hi⟩ := h2
  exists i
  constructor
  · rw [←cs.length_leftInvSeq ω]
    exact i.prop
  · rw [←hi, ←getD_leftInvSeq_mul_wordProd, getD_eq_get]

open Classical in
theorem leftInversionSet_eq {ω : List B} (hω : cs.IsReduced ω) :
  setOf (cs.IsLeftInversion (cs.wordProd ω)) = (cs.leftInvSeq ω).toFinset := by
  ext t
  simp only [Set.mem_setOf_eq, coe_toFinset]
  exact cs.isLeftInversion_iff_mem_leftInvSeq _ hω

theorem finite_of_isLeftInversion (w : W) : Set.Finite (cs.IsLeftInversion w) := by
  let ⟨ω, ⟨hω1, hω2⟩⟩ := cs.exists_reduced_word w
  subst hω2
  rw [Eq.comm] at hω1
  change cs.IsReduced ω at hω1
  change Finite (setOf (cs.IsLeftInversion (cs.wordProd ω)))
  rw [cs.leftInversionSet_eq hω1]
  apply finite_toSet

open Classical in
/-- Bjorner--Brenti Corollary 1.4.5 -/
theorem card_of_leftInversionSet (w : W) :
  Nat.card (setOf (cs.IsLeftInversion w)) = cs.length w := by
  let ⟨ω, ⟨hω1, hω2⟩⟩ := cs.exists_reduced_word w
  subst hω2
  rw [Eq.comm] at hω1
  change cs.IsReduced ω at hω1
  rw [Nat.subtype_card (cs.leftInvSeq ω).toFinset]
  · rw [toFinset_card_of_nodup]
    · simp only [length_leftInvSeq]
      exact hω1.symm
    · exact hω1.nodup_leftInvSeq
  · simp only [mem_toFinset, Set.mem_setOf_eq]
    intro x
    exact (cs.isLeftInversion_iff_mem_leftInvSeq x hω1).symm

private theorem drop_eraseIdx (l : List B) (i j : ℕ) :
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

open Classical in
/-- Bjorner--Brenti Proposition 1.4.7 -/
theorem deletion_property {ω : List B} (hω : cs.length (cs.wordProd ω) < ω.length) :
  ∃ i j, i < j ∧ j < ω.length ∧ cs.wordProd ω = cs.wordProd ((ω.eraseIdx j).eraseIdx i) := by
  have h1 : cs.IsReduced (drop ((ω.length - 1) + 1) ω) := by
    rw [Nat.sub_one_add_one]
    · simp [IsReduced]
    · grind
  have h2 : ∃ i, cs.IsReduced (drop (i + 1) ω) := by
    exists ω.length - 1
  let i := Nat.find h2
  have h3 : cs.IsReduced (drop (i + 1) ω) := Nat.find_spec h2
  have h4 : ¬ cs.IsReduced (drop i ω) := by
    cases Nat.eq_zero_or_pos i with
    | inl h =>
        rw [h]
        unfold IsReduced
        grind
    | inr h =>
        replace h : i ≠ 0 := by grind
        rw [←Nat.sub_one_add_one h]
        apply Nat.find_min h2
        exact Nat.sub_one_lt h
  have h5 : i < ω.length := by
    rw [Nat.find_lt_iff]
    exists ω.length - 1
    grind
  have h6 : cs.length (cs.simple ω[i] * cs.wordProd (drop (i + 1) ω)) + 1
    = cs.length (cs.wordProd (drop (i + 1) ω)):= by
    rw [←isLeftDescent_iff]
    by_contra h
    rw [not_isLeftDescent_iff, ←wordProd_cons] at h
    simp only [getElem_cons_drop] at h
    unfold IsReduced at *
    grind
  have h7 : cs.IsLeftInversion (cs.wordProd (drop (i + 1) ω)) (cs.simple ω[i]) := by
    constructor
    · exact cs.isReflection_simple _
    · grind
  let ⟨k, ⟨hk1, hk2⟩⟩ := cs.strong_exchange (cs.isReflection_simple ω[i]) h7
  exists i
  exists i + k + 1
  dsimp at *
  apply And.intro (by grind) (And.intro (by grind) _)
  rw [eraseIdx_eq_take_drop_succ, take_eraseIdx_eq_take_of_le _ i (i + k + 1) (by grind)]
  nth_rw 1 [←take_append_drop i ω]
  rw [←wordProd_cons, getElem_cons_drop] at hk2
  rw [wordProd_append, wordProd_append, mul_right_inj, hk2, add_right_comm]
  congr
  apply drop_eraseIdx

theorem deletion_property' {ω : List B} (hω : ¬ cs.IsReduced ω) :
  ∃ i j, i < j ∧ j < ω.length ∧ cs.wordProd ω = cs.wordProd ((ω.eraseIdx j).eraseIdx i) := by
  apply deletion_property
  unfold IsReduced at hω
  have := cs.length_wordProd_le ω
  grind

/-- Bjorner--Brenti Corollary 1.4.8 (i) -/
theorem exists_reduced_subword (ω : List B) :
  ∃ (ω' : List B), ω' <+ ω ∧ cs.IsReduced ω' ∧ cs.wordProd ω = cs.wordProd ω' := by
  revert ω
  suffices h : ∀ k, ∀ ω : List B, ω.length < k →
    ∃ (ω' : List B), ω' <+ ω ∧ cs.IsReduced ω' ∧ cs.wordProd ω = cs.wordProd ω' from by
    intro ω
    apply h (ω.length + 1)
    simp
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro ω h
      cases em (cs.IsReduced ω) with
      | inl h2 => exists ω
      | inr h2 =>
          let ⟨i, j, h3⟩ := cs.deletion_property' h2
          have ⟨ω', h4⟩ := ih ((ω.eraseIdx j).eraseIdx i) (by grind)
          exists ω'
          apply And.intro
          · trans
            · exact h4.1
            · trans
              · apply eraseIdx_sublist
              · apply eraseIdx_sublist
          · apply And.intro
            · exact h4.2.1
            · grind

end CoxeterSystem
