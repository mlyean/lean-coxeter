import Coxeter.PermutationRepresentation

/-!
# Strong exchange

This file proves the strong exchange and related properties of Coxeter groups.

## Main statements

* `Coxeter.strong_exchange`
* `Coxeter.exchange_property`
* `Coxeter.deletion_property`
* `Coxeter.exists_reduced_subword`
* `Coxeter.card_of_IsLeftInversion`

## References

* [bjorner2005] A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*

-/

namespace Coxeter

open List CoxeterSystem CoxeterGroup

variable {W : Type*} [CoxeterGroup W]

open Classical in
/-- Bjorner--Brenti Corollary 1.4.4 (a) implies (c) -/
theorem mem_leftInvSeq_of_isLeftInversion
  {ω : List (B W)} {t : W} (h : cs.IsLeftInversion (cs.wordProd ω) t) :
  t ∈ cs.leftInvSeq ω := by
  rw [←count_pos_iff, pos_iff_ne_zero]
  intro heq
  have hrw := eta_eq_one_iff (cs.wordProd ω) t h.1
  rw [IsLeftInversion, ←hrw, eta_spec, heq] at h
  tauto

/-- Bjorner--Brenti Corollary 1.4.4 (a) iff (c) -/
theorem isLeftInversion_iff_mem_leftInvSeq
  {ω : List (B W)} (t : W) (hω : cs.IsReduced ω) :
  cs.IsLeftInversion (cs.wordProd ω) t ↔ t ∈ cs.leftInvSeq ω := by
  constructor
  · intro h
    exact mem_leftInvSeq_of_isLeftInversion h
  · exact cs.isLeftInversion_of_mem_leftInvSeq hω

open Classical in
/-- Bjorner--Brenti Theorem 1.4.3 -/
theorem strong_exchange
  {ω : List (B W)} {t : W} (h : cs.IsLeftInversion (cs.wordProd ω) t) :
  ∃ i < ω.length, t * cs.wordProd ω = cs.wordProd (ω.eraseIdx i) := by
  have h2 := mem_leftInvSeq_of_isLeftInversion h
  rw [mem_iff_get] at h2
  let ⟨i, hi⟩ := h2
  exists i
  constructor
  · rw [←cs.length_leftInvSeq ω]
    exact i.prop
  · rw [←hi, ←getD_leftInvSeq_mul_wordProd, getD_eq_get]

theorem strong_exchange'
  {ω : List (B W)} {t : W} (h : cs.IsRightInversion (cs.wordProd ω) t) :
  ∃ i < ω.length, cs.wordProd ω * t = cs.wordProd (ω.eraseIdx i) := by
  rw [←isLeftInversion_inv_iff, ←wordProd_reverse] at h
  have ⟨i, hi, h2⟩ := strong_exchange h
  rw [length_reverse] at hi
  rw [←inv_inj, mul_inv_rev, wordProd_reverse, inv_inv, h.1.inv] at h2
  rw [←wordProd_reverse, reverse_eraseIdx hi, reverse_reverse] at h2
  exists ω.length - i - 1
  constructor
  · grind
  · exact h2

theorem exchange_property
  {ω : List (B W)} {i : B W} (h : cs.IsLeftDescent (cs.wordProd ω) i) :
  ∃ j < ω.length, cs.simple i * cs.wordProd ω = cs.wordProd (ω.eraseIdx j) :=
  strong_exchange ⟨cs.isReflection_simple i, h⟩

theorem exchange_property'
  {ω : List (B W)} {i : B W} (h : cs.IsRightDescent (cs.wordProd ω) i) :
  ∃ j < ω.length, cs.wordProd ω * cs.simple i = cs.wordProd (ω.eraseIdx j) :=
  strong_exchange' ⟨cs.isReflection_simple i, h⟩

open Classical in
def equiv_IsLeftInversion (ω : List (B W)) (hω : cs.IsReduced ω) :
  {t : W // cs.IsLeftInversion (cs.wordProd ω) t} ≃ {t : W // t ∈ cs.leftInvSeq ω} :=
    Equiv.subtypeEquivRight (fun t => isLeftInversion_iff_mem_leftInvSeq t hω)

open Classical in
noncomputable instance {w : W} : Fintype {t : W // cs.IsLeftInversion w t} := by
  have ⟨h1, h2⟩ := choose_spec (cs.exists_reduced_word' w)
  have h := equiv_IsLeftInversion (choose (cs.exists_reduced_word' w)) h1
  rw [←h2] at h
  exact Fintype.ofEquiv _ h.symm

def equiv_IsLeftInversion_inv {w : W} :
  {t : W // cs.IsLeftInversion w⁻¹ t} ≃ {t : W // cs.IsRightInversion w t} := by
  apply Equiv.subtypeEquivRight
  apply isLeftInversion_inv_iff

open Classical in
noncomputable instance {w : W} : Fintype {t : W // cs.IsRightInversion w t} :=
  Fintype.ofEquiv _ equiv_IsLeftInversion_inv

open Classical in
/-- Bjorner--Brenti Corollary 1.4.5 -/
theorem card_of_IsLeftInversion (w : W) :
  Fintype.card {t : W // cs.IsLeftInversion w t} = cs.length w := by
  let ⟨ω, ⟨hω1, hω2⟩⟩ := cs.exists_reduced_word' w
  subst hω2
  rw [hω1, Fintype.card_congr (equiv_IsLeftInversion ω hω1),
    Fintype.card_of_subtype (cs.leftInvSeq ω).toFinset (by simp),
    toFinset_card_of_nodup (hω1.nodup_leftInvSeq), length_leftInvSeq]

theorem card_of_IsRightInversion (w : W) :
  Fintype.card {t : W // cs.IsRightInversion w t} = cs.length w := by
  rw [Fintype.ofEquiv_card equiv_IsLeftInversion_inv, card_of_IsLeftInversion, length_inv]

open Classical in
/-- Bjorner--Brenti Proposition 1.4.7 -/
theorem deletion_property {ω : List (B W)} (hω : ¬ cs.IsReduced ω) :
  ∃ i j, i < j ∧ j < ω.length ∧ cs.wordProd ω = cs.wordProd ((ω.eraseIdx j).eraseIdx i) := by
  have h0 : ω ≠ [] := by
    intro h
    subst h
    have := IsReduced_nil W
    contradiction
  have h1 : cs.IsReduced (drop ((ω.length - 1) + 1) ω) := by
    rw [Nat.sub_one_add_one]
    · rw [drop_length]
      apply IsReduced_nil
    · rw [ne_eq, length_eq_zero_iff]
      exact h0
  have h2 : ∃ i, cs.IsReduced (drop (i + 1) ω) := by
    exists ω.length - 1
  let i := Nat.find h2
  have h3 : cs.IsReduced (drop (i + 1) ω) := Nat.find_spec h2
  have h4 : ¬ cs.IsReduced (drop i ω) := by
    cases Nat.eq_zero_or_pos i with
    | inl h =>
        rw [h]
        exact hω
    | inr h =>
        replace h : i ≠ 0 := Nat.ne_of_gt h
        rw [←Nat.sub_one_add_one h]
        apply Nat.find_min h2
        exact Nat.sub_one_lt h
  have h5 : i < ω.length := by
    rw [Nat.find_lt_iff]
    exists ω.length - 1
    constructor
    · apply Nat.sub_one_lt
      rw [ne_eq, List.length_eq_zero_iff]
      exact h0
    · exact h1
  have h6 : cs.IsLeftDescent (cs.wordProd (drop (i + 1) ω)) ω[i] := by
    rw [←not_IsReduced_cons ω[i] h3, getElem_cons_drop]
    exact h4
  let ⟨k, hk1, hk2⟩ := exchange_property h6
  exists i, i + k + 1
  apply And.intro (by grind) (And.intro (by grind) _)
  rw [eraseIdx_eq_take_drop_succ, take_eraseIdx_eq_take_of_le _ i (i + k + 1) (by grind)]
  nth_rw 1 [←take_append_drop i ω]
  rw [←wordProd_cons, getElem_cons_drop] at hk2
  rw [wordProd_append, wordProd_append, mul_right_inj, hk2, add_right_comm]
  congr
  apply drop_eraseIdx

/-- Bjorner--Brenti Corollary 1.4.8 (i) -/
theorem exists_reduced_subword (ω : List (B W)) :
  ∃ (ω' : List (B W)), ω' <+ ω ∧ cs.IsReduced ω' ∧ cs.wordProd ω = cs.wordProd ω' := by
  induction ω using Nat.strongRecMeasure List.length with
  | ind ω ih =>
      cases em (cs.IsReduced ω) with
      | inl h => exists ω
      | inr h =>
          let ⟨i, j, _, _, h2⟩ := deletion_property h
          let ⟨ω', h3, h4, h5⟩ := ih ((ω.eraseIdx j).eraseIdx i) (by grind)
          exists ω'
          constructor
          · calc
              ω' <+ (ω.eraseIdx j).eraseIdx i := h3
              _ <+ (ω.eraseIdx j) := eraseIdx_sublist _ _
              _ <+ ω := eraseIdx_sublist _ _
          · constructor
            · exact h4
            · rw [h2, h5]

end Coxeter
