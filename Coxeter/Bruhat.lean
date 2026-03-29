import Mathlib.Order.Grade
import Coxeter.StrongExchange

/-!
# Bruhat order

This file defines the Bruhat order.

## Main definitions

* `Coxeter.le` : The Bruhat order
* `Coxeter.w₀` : The longest element

## Main statements

* `Coxeter.subword_property`
* `Coxeter.lifting_property`
* `Coxeter.exists_cover_of_lt`
* `Coxeter.length_mul_w₀`

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

private theorem length_le_of_le {u w : W} (h : u ≤ w) : cs.length u ≤ cs.length w := by
  induction h with
  | rfl => rfl
  | step _ _ _ _ h3 ih => exact le_of_lt (lt_of_le_of_lt ih h3)

def lt (u w : W) : Prop := u ≤ w ∧ u ≠ w

instance : LT W where
  lt := lt

theorem lt_iff_le_and_length_lt (u w : W) : u < w ↔ u ≤ w ∧ cs.length u < cs.length w := by
  change (u ≤ w ∧ u ≠ w) ↔ u ≤ w ∧ cs.length u < cs.length w
  rw [and_congr_right_iff]
  intro h
  cases h with
  | rfl => simp
  | step v w h1 h2 h3 =>
      constructor
      · intro
        exact lt_of_le_of_lt (length_le_of_le h1) h3
      · intro h h4
        rwa [h4, lt_self_iff_false] at h

private theorem length_lt_of_lt {u w : W} (h : u < w) : cs.length u < cs.length w := by
  rw [lt_iff_le_and_length_lt] at h
  exact h.2

instance : PartialOrder W where
  le_refl := le.rfl
  le_trans u v w huv hvw := by
    induction hvw with
    | rfl => tauto
    | step v w _ h1 h2 ih => exact le.step u v w ih h1 h2
  lt_iff_le_not_ge u w := by
    rw [lt_iff_le_and_length_lt, and_congr_right_iff]
    intro h
    constructor
    · intro h2 h3
      apply not_le_of_gt h2 (length_le_of_le h3)
    · intro h2
      apply length_lt_of_lt ⟨h, _⟩
      intro h3
      subst h3
      exact h2 h
  le_antisymm := by
    intro u w h1 h2
    by_contra! h3
    apply lt_irrefl (cs.length u)
    exact lt_of_lt_of_le (length_lt_of_lt ⟨h1, h3⟩) (length_le_of_le h2)

theorem monotone_length : Monotone (@cs W).length := by apply length_le_of_le

theorem strictMono_length : StrictMono (@cs W).length := by apply length_lt_of_lt

theorem eq_of_le_of_length_eq {u w : W} (h : u ≤ w) (h2 : cs.length u = cs.length w) : u = w := by
  apply eq_of_le_of_not_lt h
  intro h3
  apply strictMono_length at h3
  rwa [h2, lt_self_iff_false] at h3

instance : OrderBot W where
  bot := 1
  bot_le w := by
    have ⟨ω, hω1, hω2⟩ := cs.exists_reduced_word' w
    subst hω2
    induction ω with
    | nil => rw [wordProd_nil]
    | cons i is ih =>
        have h' : cs.IsReduced is := hω1.drop 1
        apply le.step 1 _ _ (ih h')
        · rw [wordProd_cons, mul_inv_cancel_right]
          apply cs.isReflection_simple
        · rw [hω1, h', length_cons, Nat.lt_succ_iff]

theorem lt_reflection_mul_iff {t : W} (ht : cs.IsReflection t) (w : W) :
  w < t * w ↔ cs.length w < cs.length (t * w) := by
  rw [lt_iff_le_and_length_lt, and_iff_right_iff_imp]
  apply le.step w w (t * w) (le.rfl _) _
  rwa [mul_inv_cancel_right]

theorem reflection_mul_lt_iff {t : W} (ht : cs.IsReflection t) (w : W) :
  t * w < w ↔ cs.length (t * w) < cs.length w := by
  have h := lt_reflection_mul_iff ht (t * w)
  rwa [←mul_assoc, ht.mul_self, one_mul] at h

theorem lt_mul_reflection_iff {t : W} (ht : cs.IsReflection t) (w : W) :
  w < w * t ↔ cs.length w < cs.length (w * t) := by
  have h : w * t = (w * t * w⁻¹) * w := by group
  rw [h]
  apply lt_reflection_mul_iff
  rwa [isReflection_conj_iff]

theorem mul_reflection_lt_iff {t : W} (ht : cs.IsReflection t) (w : W) :
  w * t < w ↔ cs.length (w * t) < cs.length w := by
  have h : w * t = (w * t * w⁻¹) * w := by group
  rw [h]
  apply reflection_mul_lt_iff
  rwa [isReflection_conj_iff]

theorem lt_simple_mul_iff (i : B W) (w : W) : w < cs.simple i * w ↔ ¬ cs.IsLeftDescent w i := by
  rw [lt_reflection_mul_iff (cs.isReflection_simple i) w, isLeftDescent_iff_not_isLeftDescent_mul,
    IsLeftDescent, simple_mul_simple_cancel_left, not_not]

theorem simple_mul_lt_iff (i : B W) (w : W) : cs.simple i * w < w ↔ cs.IsLeftDescent w i :=
  reflection_mul_lt_iff (cs.isReflection_simple i) w

theorem lt_mul_simple_iff (i : B W) (w : W) : w < w * cs.simple i ↔ ¬ cs.IsRightDescent w i := by
  rw [lt_mul_reflection_iff (cs.isReflection_simple i) w, isRightDescent_iff_not_isRightDescent_mul,
    IsRightDescent, simple_mul_simple_cancel_right, not_not]

theorem mul_simple_lt_iff (i : B W) (w : W) : w * cs.simple i < w ↔ cs.IsRightDescent w i :=
  mul_reflection_lt_iff (cs.isReflection_simple i) w

theorem mul_reflection_lt_or_gt (w : W) {t : W} (ht : cs.IsReflection t) :
  t * w < w ∨ t * w > w := by
  rw [gt_iff_lt, reflection_mul_lt_iff ht, lt_reflection_mul_iff ht]
  exact Nat.lt_or_gt_of_ne (ht.length_mul_right_ne w)

private theorem reduced_subword_extend_aux (α μ ω : List (B W))
  (hμ : cs.IsReduced (α ++ μ)) (hω : cs.IsReduced (α ++ ω)) (hsub : μ <+ ω) (hneq : μ ≠ ω) :
  ∃ (ν : List (B W)), ν <+ (α ++ ω) ∧ cs.wordProd ν > cs.wordProd (α ++ μ) ∧
    ν.length = (α ++ μ).length + 1 := by
  revert α μ
  induction ω using Nat.strongRecMeasure length with
  | ind ω ih =>
      intro α μ hμ hω hsub hne
      cases hsub with
      | slnil => contradiction
      | @cons μ ω i hsub =>
          let t := cs.wordProd α * cs.simple i * (cs.wordProd α)⁻¹
          have ht : cs.IsReflection t := by
            exists cs.wordProd α, i
          by_cases! h1 : cs.IsLeftInversion (cs.wordProd (α ++ μ)) t
          · rw [isLeftInversion_iff_mem_leftInvSeq hμ, leftInvSeq_append, mem_append, mem_map] at h1
            cases h1 with
            | inl h1 =>
                have h4 : cs.IsReduced (α ++ [i]) := by
                  rw [append_cons] at hω
                  exact isReduced_of_append_left hω
                replace h4 := h4.nodup_leftInvSeq
                rw [←concat_eq_append, leftInvSeq_concat, nodup_concat] at h4
                absurd h4.1
                exact h1
            | inr h1 =>
                have ⟨w, hw1, hw2⟩ := h1
                unfold t at hw2
                rw [MulAut.conj_apply, mul_left_inj, mul_right_inj] at hw2
                subst hw2
                rw [←isLeftInversion_iff_mem_leftInvSeq (isReduced_of_append_right hμ),
                  isLeftInversion_simple_iff_isLeftDescent] at hw1
                have ⟨j, hj1, hj2⟩ := exchange_property hw1
                rw [←eq_inv_mul_iff_mul_eq, inv_simple, ←wordProd_cons] at hj2
                have h : cs.IsReduced (α ++ i :: μ.eraseIdx j) := by
                  unfold CoxeterSystem.IsReduced at hμ ⊢
                  rw [wordProd_append, ←hj2, ←wordProd_append, hμ, length_append, length_append,
                    length_cons, length_eraseIdx_of_lt hj1]
                  lia
                rw [append_cons] at h hω
                have ⟨ν, hν1, hν2, hν3⟩ := ih ω (Nat.lt_succ_self _) (α ++ [i]) (μ.eraseIdx j) h hω
                  (Sublist.trans (eraseIdx_sublist _ _) hsub) ?_
                · rw [←append_cons] at hν1 hν2 hν3
                  rw [wordProd_append, ←hj2, ←wordProd_append] at hν2
                  rw [length_append, length_cons, length_eraseIdx_add_one hj1] at hν3
                  rw [length_append]
                  exists ν
                · apply_fun length
                  rw [length_eraseIdx_of_lt hj1]
                  replace hsub := hsub.length_le
                  lia
          · exists α ++ i :: μ
            simp only [append_sublist_append_left, cons_sublist_cons, hsub, gt_iff_lt,
              length_append, length_cons, add_assoc, and_true, true_and]
            rw [←ht.not_isLeftInversion_mul_right_iff, not_not, IsLeftInversion, ←mul_assoc,
              ht.mul_self, one_mul] at h1
            have h2 : cs.wordProd (α ++ i :: μ) = t * cs.wordProd (α ++ μ) := by
              rw [wordProd_append, wordProd_append, mul_inv_mul_mul_cancel,
                wordProd_cons, mul_assoc]
            rw [h2, lt_reflection_mul_iff ht]
            exact h1.2
      | @cons₂ μ ω i hsub =>
          rw [append_cons] at hμ hω
          simp only [ne_eq, cons.injEq, true_and] at hne
          have ⟨ν, hν1, hν2, hν3⟩ := ih ω (Nat.lt_succ_self _) (α ++ [i]) μ hμ hω hsub hne
          rw [←append_cons] at hν1 hν2 hν3
          exists ν

/-- Bjorner--Brenti Lemma 2.2.1 -/
theorem reduced_subword_extend {u w : W} (ω : ReducedWord w)
  (h1 : u ≠ w) (h2 : ∃ (μ : ReducedWord u), μ.val <+ ω.val) :
  ∃ (v : W), v > u ∧ cs.length v = cs.length u + 1 ∧ ∃ (ν : ReducedWord v), ν.val <+ ω.val := by
  have ⟨μ, hsub⟩ := h2
  have ⟨ν', hν1, hν2, hν3⟩ := reduced_subword_extend_aux [] μ.val ω.val μ.prop.1 ω.prop.1 hsub ?_
  on_goal 2 =>
    intro h
    rw [←μ.wordProd_eq, ←ω.wordProd_eq, h] at h1
    contradiction
  simp only [nil_append] at hν1 hν2 hν3
  rw [←μ.wordProd_eq, μ.prop.1]
  let v := cs.wordProd ν'
  exists v
  let ν : ReducedWord v := ⟨ν', ?_, rfl⟩
  · refine ⟨hν2, ?_, ν, hν1⟩
    rwa [←ν.length_eq]
  · apply eq_of_le_of_ge
    · apply length_wordProd_le
    · rw [hν3, μ.length_eq, ←μ.wordProd_eq]
      exact length_lt_of_lt hν2

theorem exists_reduced_subword_of_le {u w : W} (ω : ReducedWord w) (h : u ≤ w) :
  ∃ (μ : ReducedWord u), μ.val <+ ω.val := by
  induction h with
  | rfl => exists ω
  | step v w _ h1 h2 ih =>
      generalize h3 : w * v⁻¹ = t at h1
      rw [mul_inv_eq_iff_eq_mul] at h3
      have h4 : cs.IsLeftInversion (cs.wordProd ω) t := by
        refine ⟨h1, ?_⟩
        rw [ω.wordProd_eq]
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
  have h2 : μ.val.length ≤ ω.val.length := h.length_le
  generalize h3 : μ.val.length = k at h2
  revert u
  induction h2 using Nat.decreasingInduction with
  | self =>
      intro u μ h h2
      rw [←μ.wordProd_eq, ←ω.wordProd_eq, h.eq_of_length h2]
  | of_succ k h3 ih =>
      intro u μ h h2
      subst h2
      have hne : u ≠ w := by
        apply_fun cs.length
        rw [←μ.length_eq, ←ω.length_eq]
        exact ne_of_lt h3
      have ⟨v, hv1, hv2, ν, hν⟩ := reduced_subword_extend ω hne ⟨μ, h⟩
      rw [←ν.length_eq, ←μ.length_eq] at hv2
      exact le_of_lt (lt_of_lt_of_le hv1 (ih ν hν hv2))

/-- Bjorner--Brenti Theorem 2.2.2 -/
theorem subword_property (u : W) {w : W} (ω : ReducedWord w) :
  u ≤ w ↔ ∃ (μ : ReducedWord u), μ.val <+ ω.val := by
  constructor
  · apply exists_reduced_subword_of_le
  · intro ⟨μ, h⟩
    exact le_of_reduced_subword _ _ h

/-- Bjorner--Brenti Corollary 2.2.3 (i) iff (iii) -/
theorem subword_property' {u w : W} :
  u ≤ w ↔ ∃ (μ : ReducedWord u) (ω : ReducedWord w), μ.val <+ ω.val := by
  constructor
  · intro h
    have ω : ReducedWord w := Classical.ofNonempty
    have ⟨μ, hμ⟩ := exists_reduced_subword_of_le ω h
    exists μ, ω
  · intro ⟨μ, ω, h⟩
    exact le_of_reduced_subword _ _ h

private noncomputable def chooseReducedSubword {w : W} (ω : ReducedWord w) :
  Set.Iic w → {μ : List (B W) | μ <+ ω} := fun ⟨_, hx⟩ =>
    ⟨(exists_reduced_subword_of_le ω hx).choose, (exists_reduced_subword_of_le ω hx).choose_spec⟩

private theorem wordProd_chooseReducedSubword {w : W} (ω : ReducedWord w) (x : Set.Iic w) :
  cs.wordProd ((chooseReducedSubword ω x).val) = x :=
  (exists_reduced_subword_of_le ω x.prop).choose.prop.2.symm

private theorem chooseReducedSubword_inj {w : W} (ω : ReducedWord w) :
  Injective (chooseReducedSubword ω) := by
  intro x y h
  rw [Subtype.ext_iff, ←wordProd_chooseReducedSubword ω, h, wordProd_chooseReducedSubword ω]

theorem finite_Icc (u w : W) : Finite (Set.Icc u w) := by
  have ω : ReducedWord w := Classical.ofNonempty
  let f : Set.Icc u w → {μ : List (B W) | μ <+ ω} := @Set.restrict₂ _
    (fun _ => {μ : List (B W) | μ <+ ω}) _ _ Set.Icc_subset_Iic_self (chooseReducedSubword ω)
  haveI : Finite {x | x <+ ω.val} := by
    have h := ω.val.sublists.finite_toSet
    simp only [mem_sublists] at h
    exact h
  apply Finite.of_injective f
  intro x y h
  apply chooseReducedSubword_inj ω at h
  rwa [Subtype.mk.injEq, Subtype.val_inj] at h

noncomputable instance : LocallyFiniteOrder W := LocallyFiniteOrder.ofFiniteIcc finite_Icc

/-- Bjorner--Brenti Corollary 2.2.4 -/
theorem card_Icc_le (u w : W) : Finset.card (Finset.Icc u w) ≤ 2 ^ cs.length w := by
  classical
  have ω : ReducedWord w := Classical.ofNonempty
  let f : Finset.Icc u w → ω.val.sublists.toFinset :=
    fun x => ⟨chooseReducedSubword ω ⟨x.val, (Finset.mem_Icc.mp x.prop).2⟩, ?_⟩
  on_goal 2 =>
    rw [List.mem_toFinset, mem_sublists]
    exact (chooseReducedSubword ω ⟨x.val, (Finset.mem_Icc.mp x.prop).2⟩).prop
  have hf_inj : Injective f := by
    intro x y h
    rw [Subtype.mk.injEq, Subtype.val_inj] at h
    apply chooseReducedSubword_inj ω at h
    rwa [Subtype.mk.injEq, Subtype.val_inj] at h
  rw [←ω.length_eq]
  have hle := le_trans (Finset.card_le_card_of_injective hf_inj) (toFinset_card_le _)
  rwa [length_sublists] at hle

/-- Bjorner--Brenti Corollary 2.2.5 -/
theorem monotone_inv : Monotone (@Inv.inv W _) := by
  intro u w h
  rw [subword_property'] at h ⊢
  have ⟨μ, ω, h'⟩ := h
  exists μ.reverse, ω.reverse
  rwa [ReducedWord.reverse, ReducedWord.reverse, reverse_sublist]

theorem strictMono_inv : StrictMono (@Inv.inv W _) :=
  monotone_inv.strictMono_of_injective inv_injective

theorem length_cover {u w : W} (h : u ⋖ w) : cs.length w = cs.length u + 1 := by
  symm
  apply eq_of_le_of_not_lt (strictMono_length h.1)
  intro h2
  have ω : ReducedWord w := Classical.ofNonempty
  have ⟨v, h3, h4, ν, hν⟩ :=
    reduced_subword_extend ω (CovBy.ne h) (exists_reduced_subword_of_le ω h.1.1)
  apply not_covBy_of_lt_of_lt h3 _ h
  apply lt_of_le_of_ne (le_of_reduced_subword _ _ hν)
  intro heq
  rwa [←h4, heq, lt_self_iff_false] at h2

theorem cover_iff {u w : W} : u ⋖ w ↔ u ≤ w ∧ cs.length w = cs.length u + 1 := by
  constructor
  · intro h
    exact ⟨le_of_lt h.1, length_cover h⟩
  · intro h
    constructor
    · rw [lt_iff_le_and_length_lt, h.2]
      exact ⟨h.1, Nat.le_refl _⟩
    · intro z hz1 hz2
      apply_fun cs.length at hz1 hz2 using @strictMono_length W _
      lia

/-- Bjorner--Brenti Theorem 2.2.6 -/
theorem exists_cover_of_lt {u w : W} (h : u < w) : ∃ (v : W), u ⋖ v ∧ v ≤ w := by
  have ω : ReducedWord w := Classical.ofNonempty
  have ⟨v, h2, h3, ν, hν⟩ := reduced_subword_extend ω (ne_of_lt h)
    (exists_reduced_subword_of_le ω (le_of_lt h))
  exists v
  rw [cover_iff]
  exact ⟨⟨le_of_lt h2, h3⟩, le_of_reduced_subword ν ω hν⟩

noncomputable instance : GradeMinOrder ℕ W where
  grade := cs.length
  grade_strictMono := strictMono_length
  covBy_grade u w h := by
    rw [Nat.covBy_iff_add_one_eq, length_cover h]
  isMin_grade x hx := by
    rw [isMin_iff_eq_bot] at hx ⊢
    rw [hx]
    exact cs.length_one

/-- Bjorner--Brenti Proposition 2.2.7 -/
theorem lifting_property {u w : W} {i : B W}
  (h1 : u ≤ w) (h2 : cs.IsLeftDescent w i) (h3 : ¬ cs.IsLeftDescent u i) :
  u ≤ cs.simple i * w ∧ cs.simple i * u ≤ w := by
  have ⟨ω, hω1, hω2⟩ := cs.exists_reduced_word' (cs.simple i * w)
  have h4 : cs.IsReduced (i :: ω) := by
    rwa [IsReduced_cons hω1, ←hω2, ←isLeftDescent_iff_not_isLeftDescent_mul]
  rw [←eq_inv_mul_iff_mul_eq, inv_simple, ←wordProd_cons] at hω2
  have ⟨⟨μ, hμ1, hμ2⟩, hsub⟩ := exists_reduced_subword_of_le ⟨i :: ω, h4, hω2⟩ h1
  dsimp at hsub
  by_cases hu : u = 1
  · subst hu
    constructor
    · exact bot_le
    · rw [mul_one, hω2]
      apply le_of_reduced_subword ⟨[i], ⟨_, _⟩⟩ ⟨i :: ω, ⟨h4, rfl⟩⟩
      · exact Sublist.cons₂ _ (nil_sublist _)
      · apply isReduced_of_singleton
      · rw [wordProd_singleton]
  · match μ, hsub with
    | [], _ =>
        absurd hu
        rwa [wordProd_nil] at hμ2
    | j :: μ, Sublist.cons _ hsub =>
        constructor
        · apply le_of_reduced_subword ⟨j :: μ, hμ1, hμ2⟩ ⟨ω, hω1, _⟩ hsub
          rw [hω2, wordProd_cons, simple_mul_simple_cancel_left]
        · apply le_of_reduced_subword ⟨i :: j :: μ, _, _⟩ ⟨i :: ω, h4, hω2⟩
          · exact Sublist.cons₂ _ hsub
          · rwa [IsReduced_cons hμ1, ←hμ2]
          · rw [wordProd_cons, hμ2]
    | i :: μ, Sublist.cons₂ _ hsub =>
        absurd h3
        rw [←isLeftInversion_simple_iff_isLeftDescent, hμ2]
        apply cs.isLeftInversion_of_mem_leftInvSeq hμ1
        exact mem_cons_self

/-- Bjorner--Brenti Corollary 2.2.8 (i) -/
theorem local_configuration {i : B W} {t w : W}
  (h : cs.simple i ≠ t) (h2 : w ⋖ cs.simple i * w) (h3 : w ⋖ t * w) :
  cs.simple i * w ⋖ cs.simple i * t * w ∧ t * w ⋖ cs.simple i * t * w := by
  cases mul_reflection_lt_or_gt (t * w) (cs.isReflection_simple i) with
  | inl h4 =>
      absurd h
      rw [←mul_left_inj w]
      apply eq_of_le_of_length_eq
      · apply (lifting_property (le_of_lt h3.1) _ _).2
        · rwa [←simple_mul_lt_iff]
        · rw [←lt_simple_mul_iff]
          exact h2.1
      · rw [length_cover h2, length_cover h3]
  | inr h4 =>
      have h4' : cs.length (cs.simple i * (t * w)) = cs.length (t * w) + 1 := by
        rwa [gt_iff_lt, lt_simple_mul_iff, not_isLeftDescent_iff] at h4
      have h5 : cs.IsLeftDescent (cs.simple i * (t * w)) i := by
        rw [isLeftDescent_iff, simple_mul_simple_cancel_left, h4']
      have h6 : ¬ cs.IsLeftDescent w i := by
        rw [←lt_simple_mul_iff]
        exact h2.1
      have h7 := (lifting_property (le_of_lt (lt_trans h3.1 h4)) h5 h6).2
      rw [cover_iff, cover_iff, mul_assoc]
      refine ⟨⟨h7, ?_⟩, ⟨le_of_lt h4, h4'⟩⟩
      rw [h4', length_cover h2, length_cover h3]

/-- Bjorner--Brenti Corollary 2.2.8 (ii) -/
theorem local_configuration₂ {i i' : B W} {w : W}
  (h : w ⋖ cs.simple i * w) (h2 : w ⋖ w * cs.simple i') :
  (cs.simple i * w ⋖ cs.simple i * w * cs.simple i' ∧
    w * cs.simple i' ⋖ cs.simple i * w * cs.simple i') ∨
  w = cs.simple i * w * cs.simple i' := by
  by_cases h3 : cs.IsLeftDescent (w * cs.simple i') i
  · right
    rw [mul_assoc]
    have h4 := h.1
    rw [lt_simple_mul_iff] at h4
    have h5 := (lifting_property (le_of_lt h2.1) h3 h4).1
    apply eq_of_le_of_length_eq h5
    rw [isLeftDescent_iff] at h3
    rw [cover_iff] at h h2
    lia
  · left
    have h4 : w * cs.simple i' < cs.simple i * (w * cs.simple i') := by
      rwa [←lt_simple_mul_iff] at h3
    have h5 : cs.IsLeftDescent (cs.simple i * (w * cs.simple i')) i := by
      rwa [isLeftDescent_iff_not_isLeftDescent_mul, simple_mul_simple_cancel_left]
    have h6 : ¬ cs.IsLeftDescent w i := by
      rw [←lt_simple_mul_iff]
      exact h.1
    rw [not_isLeftDescent_iff, ←mul_assoc] at h3
    have h7 := lifting_property (le_of_lt (lt_trans h2.1 h4)) h5 h6
    rw [←mul_assoc] at h4
    rw [not_isLeftDescent_iff] at h6
    rw [simple_mul_simple_cancel_left, ←mul_assoc] at h7
    rw [cover_iff, cover_iff]
    refine ⟨⟨h7.2, ?_⟩, ⟨le_of_lt h4, h3⟩⟩
    rw [h3, h6, length_cover h2]

/-- Bjorner--Brenti Proposition 2.2.9 -/
instance : IsDirectedOrder W where
  directed u := by
    induction u using WellFoundedLT.induction with
    | ind u ih =>
        intro w
        by_cases h : u = 1
        · exists w
          constructor
          · rw [h]
            exact bot_le
          · apply le_refl
        · have ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h
          have hlt : cs.simple i * u < u := by
            rwa [reflection_mul_lt_iff (cs.isReflection_simple i)]
          have ⟨x, hx1, hx2⟩ := ih (cs.simple i * u) hlt w
          rw [isLeftDescent_iff_not_isLeftDescent_mul] at hi
          by_cases h2 : cs.IsLeftDescent x i
          · exists x
            have h3 := (lifting_property hx1 h2 hi).2
            rw [simple_mul_simple_cancel_left] at h3
            exact ⟨h3, hx2⟩
          · exists cs.simple i * x
            have h3 : x ≤ cs.simple i * x := le_of_lt ((lt_simple_mul_iff i x).mpr h2)
            rw [isLeftDescent_iff_not_isLeftDescent_mul, not_not] at h2
            have h4 := (lifting_property (le_trans hx1 h3) h2 hi).2
            rw [simple_mul_simple_cancel_left] at h4
            exact ⟨h4, le_trans hx2 h3⟩

section finite

/-! ### Bruhat order on finite Coxeter groups -/

theorem isTop_iff_all_isLeftDescent {x : W} : (∀ (i : B W), cs.IsLeftDescent x i) ↔ IsTop x := by
  constructor
  · intro h u
    induction u using WellFoundedLT.induction with
    | ind u ih =>
        by_cases h2 : u = 1
        · rw [h2]
          exact bot_le
        · have ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h2
          specialize ih _ ((simple_mul_lt_iff i u).mpr hi)
          rw [isLeftDescent_iff_not_isLeftDescent_mul] at hi
          have h3 := (lifting_property ih (h i) hi).2
          rwa [simple_mul_simple_cancel_left] at h3
  · intro h i
    rw [←simple_mul_lt_iff]
    apply lt_of_le_of_ne (h _)
    rw [ne_eq, mul_eq_right]
    apply simple_ne_one

instance [OrderTop W] : Finite W := by
  apply Finite.of_finite_univ (Set.Finite.ofFinset (Finset.Icc ⊥ ⊤) _)
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

noncomputable def w₀ : W := (Set.finite_univ.exists_maximal Set.univ_nonempty).choose

/-- Bjorner--Brenti Proposition 2.3.1 (i) -/
noncomputable instance : OrderTop W where
  top := w₀
  le_top := by
    apply IsMax.isTop
    intro w
    exact (Set.finite_univ.exists_maximal Set.univ_nonempty).choose_spec.2 (Set.mem_univ w)

/-- Bjorner--Brenti Proposition 2.3.1 (ii) continued -/
theorem all_isLeftDescent_iff (x : W) : (∀ (i : B W), cs.IsLeftDescent x i) ↔ x = w₀ := by
  rw [isTop_iff_all_isLeftDescent]
  constructor
  · intro h
    exact top_unique (h ⊤)
  · intro h w
    rw [h]
    exact le_top

theorem length_le_length_w₀ (w : W) : cs.length w ≤ cs.length (w₀ : W) := monotone_length le_top

theorem eq_w₀_of_length_ge {x : W} (h : cs.length x ≥ cs.length (w₀ : W)) : x = w₀ := by
  by_contra! h2
  replace h2 : x < w₀ := Ne.lt_top h2
  apply_fun cs.length at h2 using @strictMono_length W _
  exact not_le_of_gt h2 h

theorem eq_w₀_of_length_eq {x : W} (h : cs.length x = cs.length (w₀ : W)) : x = w₀ :=
  eq_w₀_of_length_ge (ge_of_eq h)

@[simp]
theorem inv_w₀ : (w₀⁻¹ : W) = w₀ := eq_w₀_of_length_eq (cs.length_inv w₀)

@[simp]
theorem w₀_mul_self : (w₀ : W) * w₀ = 1 := by
  rw [mul_eq_one_iff_eq_inv, inv_w₀]

/-- Bjorner--Brenti Proposition 2.3.2 (i) -/
@[simp]
theorem w₀_sq : (w₀ : W) ^ 2 = 1 := by
  rw [sq, w₀_mul_self]

/-- Bjorner--Brenti Proposition 2.3.2 (ii) -/
theorem length_mul_w₀ (w : W) : cs.length (w * w₀) = cs.length (w₀ : W) - cs.length w := by
  apply le_antisymm _ (cs.length_mul_ge_length_sub_length' w w₀)
  have hle : cs.length w ≤ cs.length w₀ := length_le_length_w₀ w
  generalize hk : cs.length w = k at hle
  revert w
  induction hle using Nat.decreasingInduction with
  | self =>
      intro w hw
      apply eq_w₀_of_length_eq at hw
      rw [hw, w₀_mul_self, length_one]
      apply Nat.zero_le
  | of_succ k hk ih =>
      intro w hw
      subst hw
      have ⟨i, hi⟩ : ∃ x, ¬cs.IsLeftDescent w x := by
        rw [←not_forall, all_isLeftDescent_iff]
        intro h
        rwa [h, lt_self_iff_false] at hk
      rw [not_isLeftDescent_iff] at hi
      specialize ih (cs.simple i * w) hi
      rw [mul_assoc] at ih
      trans cs.length (cs.simple i * (w * w₀)) + 1
      · have h := cs.length_mul_le (cs.simple i) (cs.simple i * (w * w₀))
        rwa [simple_mul_simple_cancel_left, length_simple, add_comm] at h
      · lia

/-- Bjorner--Brenti Proposition 2.3.2 (iii) -/
theorem isLeftInversion_mul_w₀_iff {t : W} (ht : cs.IsReflection t) (w : W) :
  cs.IsLeftInversion (w * w₀) t ↔ ¬ cs.IsLeftInversion w t := by
  rw [←ht.isLeftInversion_mul_right_iff]
  simp only [IsLeftInversion, ht, true_and]
  rw [←mul_assoc, ←mul_assoc, ht.mul_self, one_mul, length_mul_w₀, length_mul_w₀,
    tsub_lt_tsub_iff_left_of_le_of_le (length_le_length_w₀ _) (length_le_length_w₀ _)]

theorem isLeftInversion_w₀_iff (t : W) : cs.IsLeftInversion w₀ t ↔ cs.IsReflection t := by
  constructor
  · exact And.left
  · intro ht
    rw [←one_mul w₀, isLeftInversion_mul_w₀_iff ht]
    apply not_isLeftInversion_one

instance : Finite (ReflectionSet W) := Subtype.finite

/-- Bjorner--Brenti Proposition 2.3.2 (iv) -/
theorem length_w₀_eq_card_reflectionSet : cs.length (w₀ : W) = Nat.card (ReflectionSet W) := by
  rw [←card_of_isLeftInversion]
  exact Nat.card_congr (Equiv.subtypeEquivRight isLeftInversion_w₀_iff)

/-- Bjorner--Brenti Corollary 2.3.3 (i) -/
theorem length_w₀_mul (w : W) : cs.length (w₀ * w) = cs.length (w₀ : W) - cs.length w := by
  rw [←length_inv, mul_inv_rev, inv_w₀, length_mul_w₀, length_inv]

/-- Bjorner--Brenti Corollary 2.3.3 (ii) -/
theorem length_conj_w₀ (w : W) : cs.length (MulAut.conj w₀ w) = cs.length w := by
  rw [MulAut.conj_apply, inv_w₀, length_mul_w₀, length_w₀_mul]
  exact Nat.sub_sub_self (length_le_length_w₀ w)

/-- Bjorner--Brenti Proposition 2.3.4 (i) -/
theorem antitone_mul_w₀ : Antitone (Equiv.mulRight (w₀ : W)) := by
  intro u v h
  induction h with
  | rfl => rfl
  | step v w h1 h2 h3 ih =>
      apply le_trans (le_of_lt _) ih
      dsimp
      generalize ht : w * v⁻¹ = t at h2
      rw [←h2.inv, mul_inv_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq] at ht
      rw [←ht, mul_assoc, lt_reflection_mul_iff h2, ←mul_assoc, length_mul_w₀, length_mul_w₀, ht]
      have := length_le_length_w₀ w
      lia

theorem antitone_w₀_mul : Antitone (Equiv.mulLeft (w₀ : W)) := by
  intro u w h
  dsimp
  rw [←inv_inv (w₀ * w), ←inv_inv (w₀ * u)]
  apply monotone_inv
  rw [mul_inv_rev, mul_inv_rev, inv_w₀]
  exact antitone_mul_w₀ (monotone_inv h)

/-- Bjorner--Brenti Proposition 2.3.4 (ii) -/
theorem monotone_conj_w₀ : Monotone (MulAut.conj (w₀ : W)) := by
  intro u v h
  rw [MulAut.conj_apply, MulAut.conj_apply, inv_w₀]
  exact antitone_mul_w₀ (antitone_w₀_mul h)

end finite

end Coxeter
