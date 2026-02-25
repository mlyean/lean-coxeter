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
  rw [←inv_inj, mul_inv_rev, wordProd_reverse, inv_inv, h.1.inv, ←wordProd_reverse,
    reverse_eraseIdx hi, reverse_reverse] at h2
  exists ω.length - i - 1
  constructor
  · calc
      ω.length - i - 1 < ω.length - i := Nat.sub_one_lt (Nat.sub_ne_zero_of_lt hi)
      _ ≤ ω.length := Nat.sub_le _ _
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
  have h1 : ¬ ω = [] := by
    intro h
    subst h
    apply hω
    apply IsReduced_nil
  have h2 : ∃ i < ω.length, cs.IsReduced (drop (i + 1) ω) := by
    exists ω.length - 1
    constructor
    · apply Nat.sub_one_lt
      rw [ne_eq, List.length_eq_zero_iff]
      exact h1
    · rw [Nat.sub_one_add_one]
      · rw [drop_length]
        apply IsReduced_nil
      · rw [ne_eq, length_eq_zero_iff]
        exact h1
  let i := Nat.find h2
  have ⟨h3, h4⟩ := Nat.find_spec h2
  have h5 : cs.IsLeftDescent (cs.wordProd (drop (i + 1) ω)) ω[i] := by
    rw [←not_IsReduced_cons ω[i] h4, getElem_cons_drop]
    cases Nat.eq_zero_or_pos i with
    | inl h => rwa [h]
    | inr h =>
        intro h'
        apply Nat.find_min h2 (Nat.sub_one_lt_of_lt h)
        constructor
        · exact lt_of_le_of_lt (Nat.sub_le _ _) h3
        · rw [Nat.sub_one_add_one_eq_of_pos h]
          exact h'
  let ⟨k, h6, h7⟩ := exchange_property h5
  exists i, i + k + 1
  have h8 : i < i + k + 1 := by
    rw [Nat.lt_succ_iff]
    apply Nat.le_add_right
  have h9 : i + k + 1 < ω.length := by
    rw [length_drop] at h6
    calc
      i + k + 1 = k + (i + 1) := by ring
      _ < ω.length - (i + 1) + (i + 1) := Nat.add_lt_add_right h6 _
      _ ≤ ω.length := ?_
    · rw [Nat.sub_add_cancel]
      exact h3
  apply And.intro h8 (And.intro h9 _)
  rw [eraseIdx_eq_take_drop_succ, take_eraseIdx_eq_take_of_le _ i (i + k + 1) (le_of_lt h8)]
  nth_rw 1 [←take_append_drop i ω]
  rw [←wordProd_cons, getElem_cons_drop] at h7
  rw [wordProd_append, wordProd_append, mul_right_inj, h7, add_right_comm]
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
