import Coxeter.PermutationRepresentation
import Coxeter.Opposite

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

namespace Coxeter

open List CoxeterSystem CoxeterGroup

variable {W : Type*} [CoxeterGroup W]

/-- Bjorner--Brenti Corollary 1.4.4 (a) implies (c) -/
theorem mem_leftInvSeq_of_isLeftInversion
  {ω : List (B W)} {t : W} (h : cs.IsLeftInversion (cs.wordProd ω) t) :
  t ∈ cs.leftInvSeq ω := by
  classical
  rw [←count_pos_iff, pos_iff_ne_zero]
  intro heq
  rw [←eta_eq_one_iff, eta_spec, heq] at h
  contradiction

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
  rw [h2]
  haveI : Finite {x // x ∈ cs.leftInvSeq ω} := List.finite_toSet _
  exact Finite.of_equiv _ (equiv_IsLeftInversion ω h1).symm

/-- Bjorner--Brenti Corollary 1.4.5 -/
theorem card_of_isLeftInversion (w : W) :
  Nat.card {t : W // cs.IsLeftInversion w t} = cs.length w := by
  classical
  have ⟨ω, hω1, hω2⟩ := cs.exists_isReduced w
  subst hω2
  rw [hω1, Nat.card_congr (equiv_IsLeftInversion ω hω1),
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
      · have ⟨j, h2, h3⟩ := exchange_property ((not_isReduced_cons h k).mp hω)
        exists 0, j + 1
        refine ⟨Nat.zero_lt_succ j, ?_, ?_⟩
        · rw [length_cons]
          exact add_lt_add_left h2 1
        · rwa [eraseIdx_cons_succ, eraseIdx_zero, tail_cons, wordProd_cons]
      · have ⟨i, j, h2, h3, h4⟩ := ih h
        exists i + 1, j + 1
        refine ⟨add_lt_add_left h2 1, ?_, ?_⟩
        · rw [length_cons]
          exact add_lt_add_left h3 1
        · rw [eraseIdx_cons_succ, eraseIdx_cons_succ, wordProd_cons, wordProd_cons, h4]

/-- Bjorner--Brenti Corollary 1.4.8 (i) -/
theorem exists_reduced_subword (ω : List (B W)) :
  ∃ (ω' : List (B W)), ω' <+ ω ∧ cs.IsReduced ω' ∧ cs.wordProd ω = cs.wordProd ω' := by
  induction ω using Nat.strongRecMeasure length with
  | ind ω ih =>
      by_cases h : cs.IsReduced ω
      · exists ω
      · have ⟨i, j, _, _, h2⟩ := deletion_property h
        have ⟨ω', h3, h4, h5⟩ := ih ((ω.eraseIdx j).eraseIdx i) (by grind)
        exists ω'
        refine ⟨?_, h4, ?_⟩
        · calc
            ω' <+ (ω.eraseIdx j).eraseIdx i := h3
            _ <+ (ω.eraseIdx j) := eraseIdx_sublist _ _
            _ <+ ω := eraseIdx_sublist _ _
        · rw [h2, h5]

theorem exists_reduced_subword' {w : W} {ω : List (B W)} (h : w = cs.wordProd ω) :
  ∃ (ω' : ReducedWord w), ω'.val <+ ω := by
  rw [h]
  have ⟨ω', _, h2, h3⟩ := exists_reduced_subword ω
  exists ⟨ω', h2, h3⟩

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
    exact ⟨by lia, hi2⟩
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

end rightVariants

end Coxeter
