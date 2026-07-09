module

public import Mathlib.Data.List.Palindrome
public import Coxeter.PermutationRepresentation
public import Coxeter.Data.List.Lemmas

/-!
# Strong exchange

This file proves the strong exchange and related properties of Coxeter groups.

## Main statements

* `Coxeter.strong_exchange`
* `Coxeter.exchange_property`
* `Coxeter.deletion_property`
* `Coxeter.exists_reduced_subword`
* `Coxeter.card_of_isLeftInversion`

## References

* [bjorner2005] A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*
-/

@[expose] public section

namespace Coxeter

open List CoxeterSystem CoxeterGroup

variable {W : Type*} [CoxeterGroup W]

/-- Bjorner--Brenti Corollary 1.4.4 (a) implies (c) -/
theorem mem_leftInvSeq_of_isLeftInversion
  {ω : List (B W)} {t : W} (h : cs.IsLeftInversion (cs.wordProd ω) t) : t ∈ cs.leftInvSeq ω := by
  contrapose h
  classical rw [←eta_eq_zero_iff, eta_spec, count_eq_zero_of_not_mem h, Nat.cast_zero]

/-- Bjorner--Brenti Corollary 1.4.4 (a) iff (c) -/
theorem isLeftInversion_iff_mem_leftInvSeq {ω : List (B W)} (hω : cs.IsReduced ω) (t : W) :
  cs.IsLeftInversion (cs.wordProd ω) t ↔ t ∈ cs.leftInvSeq ω :=
  ⟨mem_leftInvSeq_of_isLeftInversion, cs.isLeftInversion_of_mem_leftInvSeq hω⟩

/-- Bjorner--Brenti Theorem 1.4.3 -/
theorem strong_exchange {ω : List (B W)} {t : W} (h : cs.IsLeftInversion (cs.wordProd ω) t) :
  ∃ i < ω.length, t * cs.wordProd ω = cs.wordProd (ω.eraseIdx i) := by
  apply mem_leftInvSeq_of_isLeftInversion at h
  rw [mem_iff_get] at h
  obtain ⟨i, hi⟩ := h
  exists i
  rw [←cs.length_leftInvSeq ω, ←hi, ←getD_leftInvSeq_mul_wordProd, getD_eq_get]
  exact ⟨i.prop, rfl⟩

theorem exchange_property {ω : List (B W)} {i : B W} (h : cs.IsLeftDescent (cs.wordProd ω) i) :
  ∃ j < ω.length, cs.simple i * cs.wordProd ω = cs.wordProd (ω.eraseIdx j) :=
  strong_exchange ⟨cs.isReflection_simple i, h⟩

def equiv_IsLeftInversion (ω : List (B W)) (hω : cs.IsReduced ω) :
  {t : W // cs.IsLeftInversion (cs.wordProd ω) t} ≃ {t : W // t ∈ cs.leftInvSeq ω} :=
    Equiv.subtypeEquivRight (isLeftInversion_iff_mem_leftInvSeq hω)

instance {w : W} : Finite {t : W // cs.IsLeftInversion w t} := by
  have ⟨ω, h1, h2⟩ := cs.exists_isReduced w
  subst h2
  haveI : Finite {x // x ∈ cs.leftInvSeq ω} := List.finite_toSet _
  exact Finite.of_equiv _ (equiv_IsLeftInversion ω h1).symm

/-- Bjorner--Brenti Corollary 1.4.5 -/
theorem card_of_isLeftInversion (w : W) :
  Nat.card {t : W // cs.IsLeftInversion w t} = cs.length w := by
  have ⟨ω, hω1, hω2⟩ := cs.exists_isReduced w
  subst hω2
  classical rw [hω1, Nat.card_congr (equiv_IsLeftInversion ω hω1),
    Nat.subtype_card (cs.leftInvSeq ω).toFinset (fun _ => List.mem_toFinset),
    toFinset_card_of_nodup hω1.nodup_leftInvSeq, length_leftInvSeq]

/-- Bjorner--Brenti Proposition 1.4.7 -/
theorem deletion_property {ω : List (B W)} (hω : ¬ cs.IsReduced ω) :
  ∃ i j, i < j ∧ j < ω.length ∧ cs.wordProd ω = cs.wordProd ((ω.eraseIdx j).eraseIdx i) := by
  induction ω with
  | nil =>
      absurd hω
      exact isReduced_nil
  | cons k ks ih =>
      by_cases h : cs.IsReduced ks
      · rw [not_isReduced_cons h k] at hω
        have ⟨j, h2, h3⟩ := exchange_property hω
        exists 0, j + 1
        rw [length_cons, eraseIdx_cons_succ, eraseIdx_zero, tail_cons, wordProd_cons,
          Nat.succ_lt_succ_iff]
        exact ⟨Nat.zero_lt_succ j, h2, h3⟩
      · have ⟨i, j, h2, h3, h4⟩ := ih h
        exists i + 1, j + 1
        rw [length_cons, eraseIdx_cons_succ, eraseIdx_cons_succ, wordProd_cons, wordProd_cons, h4,
          Nat.succ_lt_succ_iff, Nat.succ_lt_succ_iff]
        exact ⟨h2, h3, rfl⟩

/-- Bjorner--Brenti Corollary 1.4.8 (i) -/
theorem exists_reduced_subword (ω : List (B W)) :
  ∃ (ω' : List (B W)), ω' <+ ω ∧ cs.IsReduced ω' ∧ cs.wordProd ω = cs.wordProd ω' := by
  induction ω using Nat.strongRecMeasure length with | ind ω ih =>
  by_cases h : cs.IsReduced ω
  · exists ω
  · have ⟨i, j, _, _, h2⟩ := deletion_property h
    have ⟨ω', h3, h4, h5⟩ := ih ((ω.eraseIdx j).eraseIdx i) (by grind)
    exists ω'
    rw [h2, h5]
    refine ⟨?_, h4, rfl⟩
    calc
      ω' <+ (ω.eraseIdx j).eraseIdx i := h3
      _ <+ (ω.eraseIdx j) := eraseIdx_sublist ..
      _ <+ ω := eraseIdx_sublist ..

theorem exists_reduced_subword' {w : W} {ω : List (B W)} (h : w = cs.wordProd ω) :
  ∃ (ω' : ReducedWord w), ω'.val <+ ω := by
  rw [h]
  have ⟨ω', _, h2, h3⟩ := exists_reduced_subword ω
  exists ⟨ω', h2, h3⟩

theorem exists_palindromic_reducedWord_of_isReflection (t : W) (ht : cs.IsReflection t) :
  ∃ (τ : ReducedWord t), List.Palindrome τ.val := by
  have ⟨ω, hω1, hω2⟩ := cs.exists_isReduced t
  have h1 := eta_reflection_self ht
  nth_rw 1 [hω2] at h1
  rw [eta_eq_one_iff, isLeftInversion_iff_mem_leftInvSeq hω1, mem_iff_getElem] at h1
  obtain ⟨k, hk1, hk2⟩ := h1
  rw [length_leftInvSeq] at hk1
  rw [cs.getElem_leftInvSeq _ _ hk1, ←wordProd_reverse, ←wordProd_singleton, ←wordProd_append,
    ←wordProd_append] at hk2
  have hk3 : cs.length t = 2 * k + 1 := by
    rw [hω2, take_append_getElem] at hk2
    nth_rw 3 [←take_append_drop (k + 1) ω] at hk2
    rw [wordProd_append, wordProd_append, wordProd_reverse, mul_right_inj] at hk2
    apply_fun cs.length at hk2
    rw [length_inv, hω1.take k, hω1.drop (k + 1), length_take, length_drop, min_eq_left (by lia),
      ←hω1, ←hω2] at hk2
    rw [←hω1, ←hω2] at hk1
    rw [eq_tsub_iff_add_eq_of_le (by lia)] at hk2
    lia
  let τ : ReducedWord t := ⟨take k ω ++ [ω[k]] ++ (take k ω).reverse, ?_, hk2.symm⟩
  · exists τ
    dsimp [τ]
    rw [Palindrome.iff_reverse_eq, reverse_append, reverse_append, reverse_reverse,
      reverse_singleton, append_assoc]
  · grind [CoxeterSystem.IsReduced]

section rightVariants

open MulOpposite

/-! ### Right variants -/

theorem strong_exchange_right {ω : List (B W)} {t : W} (h : cs.IsRightInversion (cs.wordProd ω) t) :
  ∃ i < ω.length, cs.wordProd ω * t = cs.wordProd (ω.eraseIdx i) := by
  have ⟨i, hi1, hi2⟩ := @strong_exchange Wᵐᵒᵖ _ ω.reverse (op t) ?_
  · exists ω.length - i - 1
    rw [length_reverse] at hi1
    rw [wordProd_op, ←op_mul, reverse_reverse, wordProd_op, op_inj, reverse_eraseIdx hi1,
      reverse_reverse] at hi2
    refine ⟨?_, hi2⟩
    apply Nat.sub_one_lt_of_le
    · rwa [Nat.sub_pos_iff_lt]
    · apply Nat.sub_le
  · rwa [wordProd_op, isLeftInversion_op_iff, reverse_reverse]

theorem exchange_property_right
  {ω : List (B W)} {i : B W} (h : cs.IsRightDescent (cs.wordProd ω) i) :
  ∃ j < ω.length, cs.wordProd ω * cs.simple i = cs.wordProd (ω.eraseIdx j) :=
  strong_exchange_right ⟨cs.isReflection_simple i, h⟩

def equiv_isRightInversion {w : W} :
  {t : W // cs.IsRightInversion w t} ≃ {t : Wᵐᵒᵖ // cs.IsLeftInversion (op w) t} :=
  Equiv.subtypeEquiv MulOpposite.opEquiv (fun t => (isLeftInversion_op_iff w t).symm)

instance {w : W} : Finite {t : W // cs.IsRightInversion w t} :=
  Finite.of_equiv _ equiv_isRightInversion.symm

theorem card_of_isRightInversion (w : W) :
  Nat.card {t : W // cs.IsRightInversion w t} = cs.length w := by
  rw [Nat.card_congr equiv_isRightInversion, card_of_isLeftInversion, length_op]

/-- If `s` is a right inversion of `v`, it stays a right inversion of `w * v` provided `w * v` has
no length cancellation (`hlen`): right-multiplying the length-additive `w` onto the left of `v`
can't undo the length drop `s` already causes on `v`. One half of the classical fact that
`RightInversion (w * v)` splits as `RightInversion v` together with `w`'s inversions conjugated by
`v⁻¹` (the other half is `isRightInversion_conj_of_isRightInversion_mul_left`); a step toward the
"gate property" (`DihedralSubProperties.isRightDescent_mul_iff_of_not_rightDescent` in
`Coxeter/Hecke.lean`), though the disjointness/exhaustiveness of the two halves (needed to turn
this into an iff) isn't proved here. -/
theorem isRightInversion_of_isRightInversion_mul_right {w v s : W}
    (hs : cs.IsRightInversion v s) (hlen : cs.length (w * v) = cs.length w + cs.length v) :
    cs.IsRightInversion (w * v) s := by
  obtain ⟨hrefl, hlt⟩ := hs
  refine ⟨hrefl, ?_⟩
  rw [mul_assoc]
  have h1 := cs.length_mul_le w (v * s)
  omega

/-- If `t` is a right inversion of `w`, then its conjugate `v⁻¹ * t * v` is a right inversion of
`w * v`, provided `w * v` has no length cancellation (`hlen`): appending the length-additive `v`
on the right can't undo the length drop `t` already causes on `w`. The other half of the classical
"inversions of a length-additive product split" fact (see
`isRightInversion_of_isRightInversion_mul_right`). -/
theorem isRightInversion_conj_of_isRightInversion_mul_left {w v t : W}
    (ht : cs.IsRightInversion w t) (hlen : cs.length (w * v) = cs.length w + cs.length v) :
    cs.IsRightInversion (w * v) (v⁻¹ * t * v) := by
  obtain ⟨hrefl, hlt⟩ := ht
  refine ⟨by simpa using hrefl.conj v⁻¹, ?_⟩
  have h1 : w * v * (v⁻¹ * t * v) = w * t * v := by group
  rw [h1]
  have h2 := cs.length_mul_le (w * t) v
  omega

end rightVariants

end Coxeter
