module

public import Mathlib.Order.Grade
public import Coxeter.StrongExchange
public import Coxeter.Order.Directed

/-!
# Bruhat order

This file defines the Bruhat order.

## Main definitions

* `Coxeter.le` : The Bruhat order
* `Coxeter.w₀` : The longest element

## Main statements

* `Coxeter.subword_property`
* `Coxeter.lifting_property`
* `Coxeter.length_mul_w₀`

## References

* [bjorner2005] A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*
-/

@[expose] public section

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
  | step _ _ _ _ h3 ih => exact ih.trans h3.le

theorem eq_of_le_of_length_ge {u w : W} (h : u ≤ w) (h2 : cs.length u ≥ cs.length w) : u = w := by
  cases h with
  | rfl => rfl
  | step v w h1 h2' h3 =>
      apply length_le_of_le at h1
      lia

theorem eq_of_le_of_length_eq {u w : W} (h : u ≤ w) (h2 : cs.length u = cs.length w) : u = w :=
  eq_of_le_of_length_ge h (ge_of_eq h2)

def lt (u w : W) : Prop := u ≤ w ∧ u ≠ w

instance : LT W where
  lt := lt

theorem lt_iff_le_and_length_lt (u w : W) : u < w ↔ u ≤ w ∧ cs.length u < cs.length w := by
  change (u ≤ w ∧ ¬ u = w) ↔ u ≤ w ∧ cs.length u < cs.length w
  rw [and_congr_right_iff, not_iff_comm, not_lt]
  intro h
  refine ⟨eq_of_le_of_length_ge h, ?_⟩
  intro h2
  rw [h2]

instance : PartialOrder W where
  le_refl := le.rfl
  le_trans u v w huv hvw := by
    induction hvw with
    | rfl => tauto
    | step v w _ h1 h2 ih => exact le.step u v w ih h1 h2
  lt_iff_le_not_ge u w := by
    rw [lt_iff_le_and_length_lt, and_congr_right_iff, iff_not_comm, not_lt]
    intro h
    refine ⟨length_le_of_le, ?_⟩
    intro h2
    rw [eq_of_le_of_length_ge h h2]
    apply le.rfl
  le_antisymm u w h1 h2 := by
    exact eq_of_le_of_length_ge h1 (length_le_of_le h2)

theorem monotone_length : Monotone (@cs W).length := by apply length_le_of_le

theorem strictMono_length : StrictMono (@cs W).length := by
  intro u w h
  exact ((lt_iff_le_and_length_lt u w).mp h).2

theorem reflection_mul_lt_self_iff {t : W} (ht : cs.IsReflection t) (w : W) :
  t * w < w ↔ cs.IsLeftInversion w t := by
  unfold IsLeftInversion
  rw [lt_iff_le_and_length_lt]
  simp only [ht, true_and, and_iff_right_iff_imp]
  apply le.step (t * w) (t * w) w (le.rfl _) _
  rwa [mul_inv_rev, mul_inv_cancel_left, ht.inv]

theorem lt_reflection_mul_self_iff {t : W} (ht : cs.IsReflection t) (w : W) :
  w < t * w ↔ ¬ cs.IsLeftInversion w t := by
  have h := reflection_mul_lt_self_iff ht (t * w)
  rwa [←mul_assoc, ht.mul_self, one_mul, ht.isLeftInversion_mul_right_iff] at h

theorem mul_reflection_lt_self_iff {t : W} (ht : cs.IsReflection t) (w : W) :
  w * t < w ↔ cs.IsRightInversion w t := by
  have h := reflection_mul_lt_self_iff (ht.conj w) w
  rw [inv_mul_cancel_right] at h
  rw [h]
  simp [IsLeftInversion, IsRightInversion]

theorem lt_self_mul_reflection_iff {t : W} (ht : cs.IsReflection t) (w : W) :
  w < w * t ↔ ¬ cs.IsRightInversion w t := by
  have h := mul_reflection_lt_self_iff ht (w * t)
  rwa [mul_assoc, ht.mul_self, mul_one, ht.isRightInversion_mul_left_iff] at h

theorem simple_mul_lt_self_iff (i : B W) (w : W) : cs.simple i * w < w ↔ cs.IsLeftDescent w i := by
  rw [reflection_mul_lt_self_iff (cs.isReflection_simple i),
    cs.isLeftInversion_simple_iff_isLeftDescent]

theorem lt_simple_mul_self_iff (i : B W) (w : W) :
  w < cs.simple i * w ↔ ¬ cs.IsLeftDescent w i := by
  rw [lt_reflection_mul_self_iff (cs.isReflection_simple i),
    cs.isLeftInversion_simple_iff_isLeftDescent]

theorem mul_simple_lt_self_iff (i : B W) (w : W) : w * cs.simple i < w ↔ cs.IsRightDescent w i := by
  rw [mul_reflection_lt_self_iff (cs.isReflection_simple i),
    cs.isRightInversion_simple_iff_isRightDescent]

theorem lt_self_mul_simple_iff (i : B W) (w : W) :
  w < w * cs.simple i ↔ ¬ cs.IsRightDescent w i := by
  rw [lt_self_mul_reflection_iff (cs.isReflection_simple i),
    cs.isRightInversion_simple_iff_isRightDescent]

theorem reflection_mul_lt_or_gt_self (w : W) {t : W} (ht : cs.IsReflection t) :
  t * w < w ∨ t * w > w := by
  rw [reflection_mul_lt_self_iff ht, gt_iff_lt, lt_reflection_mul_self_iff ht]
  apply Classical.em

theorem mul_reflection_lt_or_gt_self (w : W) {t : W} (ht : cs.IsReflection t) :
  w * t < w ∨ w * t > w := by
  rw [mul_reflection_lt_self_iff ht, gt_iff_lt, lt_self_mul_reflection_iff ht]
  apply Classical.em

instance : OrderBot W where
  bot := 1
  bot_le w := by
    have ⟨ω, hω1, hω2⟩ := cs.exists_isReduced w
    subst hω2
    induction ω with
    | nil => rw [wordProd_nil]
    | cons i is ih =>
        have h' : cs.IsReduced is := hω1.drop 1
        apply le_trans (ih h') (le_of_lt _)
        rwa [wordProd_cons, lt_simple_mul_self_iff, ←isReduced_cons h']

private theorem reduced_subword_extend_aux (α μ ω : List (B W))
  (hμ : cs.IsReduced (α ++ μ)) (hω : cs.IsReduced (α ++ ω)) (hsub : μ <+ ω) (hneq : μ ≠ ω) :
  ∃ (ν : List (B W)), ν <+ (α ++ ω) ∧ cs.wordProd ν > cs.wordProd (α ++ μ) ∧
    ν.length = (α ++ μ).length + 1 := by
  induction ω using Nat.strongRecMeasure length generalizing α μ with | ind ω ih =>
  cases hsub with
  | slnil => contradiction
  | @cons μ ω i hsub =>
      let t := cs.wordProd α * cs.simple i * (cs.wordProd α)⁻¹
      have ht : cs.IsReflection t := (cs.isReflection_simple i).conj _
      by_cases! h1 : cs.IsLeftInversion (cs.wordProd (α ++ μ)) t
      · rw [isLeftInversion_iff_mem_leftInvSeq hμ, leftInvSeq_append, mem_append, mem_map] at h1
        cases h1 with
        | inl h1 =>
            absurd h1
            rw [append_cons] at hω
            apply isReduced_of_append_left at hω
            replace hω := hω.nodup_leftInvSeq
            rw [←concat_eq_append, leftInvSeq_concat, nodup_concat] at hω
            exact hω.1
        | inr h1 =>
            obtain ⟨w, hw1, hw2⟩ := h1
            rw [MulAut.conj_apply, mul_left_inj, mul_right_inj] at hw2
            subst hw2
            rw [←isLeftInversion_iff_mem_leftInvSeq (isReduced_of_append_right hμ),
              isLeftInversion_simple_iff_isLeftDescent] at hw1
            have ⟨j, hj1, hj2⟩ := exchange_property hw1
            rw [←eq_inv_mul_iff_mul_eq, inv_simple, ←wordProd_cons] at hj2
            have h : cs.IsReduced (α ++ i :: μ.eraseIdx j) := by
              unfold CoxeterSystem.IsReduced
              rw [wordProd_append, ←hj2, ←wordProd_append, hμ, length_append, length_append,
                length_cons, length_eraseIdx_of_lt hj1]
              lia
            rw [append_cons] at h hω
            have ⟨ν, hν1, hν2, hν3⟩ := ih ω (Nat.lt_succ_self _) (α ++ [i]) (μ.eraseIdx j) h hω
              (Sublist.trans (eraseIdx_sublist ..) hsub) ?_
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
        have h2 : t * cs.wordProd (α ++ μ) = cs.wordProd (α ++ i :: μ) := by
          rw [wordProd_append, wordProd_append, mul_inv_mul_mul_cancel, wordProd_cons, mul_assoc]
        refine ⟨by simpa, ?_, ?_⟩
        · rwa [←lt_reflection_mul_self_iff ht, h2] at h1
        · rw [length_append, length_append, length_cons, add_assoc]
  | @cons₂ μ ω i hsub =>
      rw [append_cons] at hμ hω
      simp only [ne_eq, cons.injEq, true_and] at hneq
      have ⟨ν, hν1, hν2, hν3⟩ := ih ω (Nat.lt_succ_self _) (α ++ [i]) μ hμ hω hsub hneq
      rw [←append_cons] at hν1 hν2 hν3
      exists ν

/-- Bjorner--Brenti Lemma 2.2.1 -/
theorem reduced_subword_extend {u w : W} (ω : ReducedWord w)
  (h1 : u ≠ w) (h2 : ∃ (μ : ReducedWord u), μ.val <+ ω.val) :
  ∃ (v : W), v > u ∧ cs.length v = cs.length u + 1 ∧ ∃ (ν : ReducedWord v), ν.val <+ ω.val := by
  obtain ⟨μ, hsub⟩ := h2
  have ⟨ν', hν1, hν2, hν3⟩ := reduced_subword_extend_aux [] μ.val ω.val μ.prop.1 ω.prop.1 hsub ?_
  on_goal 2 =>
    apply_fun cs.wordProd
    rwa [μ.wordProd_eq, ω.wordProd_eq]
  rw [nil_append] at hν1 hν2 hν3
  rw [←μ.wordProd_eq, μ.prop.1]
  let v := cs.wordProd ν'
  exists v
  let ν : ReducedWord v := ⟨ν', ?_, rfl⟩
  · refine ⟨hν2, ?_, ν, hν1⟩
    rwa [←ν.length_eq]
  · apply eq_of_le_of_ge (length_wordProd_le ..)
    rw [hν3, μ.length_eq, ←μ.wordProd_eq]
    exact strictMono_length hν2

theorem exists_reduced_subword_of_le {u w : W} (ω : ReducedWord w) (h : u ≤ w) :
  ∃ (μ : ReducedWord u), μ.val <+ ω.val := by
  induction h with
  | rfl => exists ω
  | step v w _ h1 h2 ih =>
      generalize ht : w * v⁻¹ = t at h1
      rw [←inv_inj, mul_inv_rev, inv_inv, h1.inv, mul_inv_eq_iff_eq_mul] at ht
      rw [ht] at h2
      have h3 : cs.IsLeftInversion (cs.wordProd ω) t := ⟨h1, by rwa [ω.wordProd_eq]⟩
      have ⟨i, _, h4⟩ := strong_exchange h3
      rw [ω.wordProd_eq, ←ht] at h4
      have ⟨ω', h6⟩ := exists_reduced_subword' h4
      have ⟨μ, h7⟩ := ih ω'
      exists μ
      calc
        μ <+ ω' := h7
        _ <+ ω.val.eraseIdx i := h6
        _ <+ ω := eraseIdx_sublist ..

theorem le_of_reduced_subword {u w : W} (μ : ReducedWord u) (ω : ReducedWord w)
  (h : μ.val <+ ω.val) : u ≤ w := by
  have hle : μ.val.length ≤ ω.val.length := h.length_le
  generalize hk : μ.val.length = k at hle
  induction hle using Nat.decreasingInduction generalizing u with
  | self =>
      rw [←μ.wordProd_eq, ←ω.wordProd_eq, h.eq_of_length hk]
  | of_succ k h2 ih =>
      subst hk
      have hne : u ≠ w := by
        apply_fun cs.length
        rw [←μ.length_eq, ←ω.length_eq]
        exact h2.ne
      have ⟨v, hv1, hv2, ν, hν⟩ := reduced_subword_extend ω hne ⟨μ, h⟩
      rw [←ν.length_eq, ←μ.length_eq] at hv2
      exact hv1.le.trans (ih ν hν hv2)

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

private noncomputable def chooseReducedSubword {w : W} (ω : ReducedWord w) (x : Set.Iic w) :
  {μ : List (B W) // μ <+ ω} := ⟨p.choose.val, p.choose_spec⟩
  where
    p := exists_reduced_subword_of_le ω x.prop

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
theorem card_Icc_le (u w : W) : (Finset.Icc u w).card ≤ 2 ^ cs.length w := by
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
  rw [←ω.length_eq, ←length_sublists]
  exact (Finset.card_le_card_of_injective hf_inj).trans (toFinset_card_le _)

/-- Bjorner--Brenti Corollary 2.2.5 -/
theorem monotone_inv : Monotone (@Inv.inv W _) := by
  intro u w h
  rw [subword_property'] at h ⊢
  obtain ⟨μ, ω, h⟩ := h
  exists μ.reverse, ω.reverse
  rwa [ReducedWord.reverse, ReducedWord.reverse, reverse_sublist]

theorem strictMono_inv : StrictMono (@Inv.inv W _) :=
  monotone_inv.strictMono_of_injective inv_injective

theorem length_cover {u w : W} (h : u ⋖ w) : cs.length u + 1 = cs.length w := by
  apply eq_of_le_of_not_lt (strictMono_length h.1)
  intro h2
  have ω : ReducedWord w := Classical.ofNonempty
  have ⟨v, h3, h4, ν, hν⟩ :=
    reduced_subword_extend ω h.ne (exists_reduced_subword_of_le ω h.1.1)
  apply not_covBy_of_lt_of_lt h3 _ h
  rw [lt_iff_le_and_length_lt]
  exact ⟨le_of_reduced_subword _ _ hν, by rwa [h4]⟩

noncomputable instance : GradeMinOrder ℕ W where
  grade := cs.length
  grade_strictMono := strictMono_length
  covBy_grade u w h := by
    rw [Nat.covBy_iff_add_one_eq, length_cover h]
  isMin_grade x hx := by
    rw [isMin_iff_eq_bot] at hx ⊢
    rw [hx]
    exact cs.length_one

instance : IsStronglyAtomic W := inferInstance

/-- Bjorner--Brenti Theorem 2.2.6 -/
theorem covBy_iff {u w : W} : u ⋖ w ↔ u ≤ w ∧ cs.length u + 1 = cs.length w := by
  rw [@covBy_iff_lt_covBy_grade ℕ, Nat.covBy_iff_add_one_eq, lt_iff_le_and_length_lt,
    show grade ℕ = cs.length by rfl]
  grind

theorem simple_mul_covBy_self_iff (i : B W) (w : W) :
  cs.simple i * w ⋖ w ↔ cs.IsLeftDescent w i := by
  rw [covBy_iff, ←cs.isLeftDescent_iff, ←simple_mul_lt_self_iff, and_iff_right_iff_imp]
  apply le_of_lt

theorem covBy_simple_mul_self_iff (i : B W) (w : W) :
  w ⋖ cs.simple i * w ↔ ¬ cs.IsLeftDescent w i := by
  rw [covBy_iff, Eq.comm, ←cs.not_isLeftDescent_iff, ←lt_simple_mul_self_iff, and_iff_right_iff_imp]
  apply le_of_lt

theorem mul_simple_covBy_self_iff (i : B W) (w : W) :
  w * cs.simple i ⋖ w ↔ cs.IsRightDescent w i := by
  rw [covBy_iff, ←cs.isRightDescent_iff, ←mul_simple_lt_self_iff, and_iff_right_iff_imp]
  apply le_of_lt

theorem covBy_self_mul_simple_iff (i : B W) (w : W) :
  w ⋖ w * cs.simple i ↔ ¬ cs.IsRightDescent w i := by
  rw [covBy_iff, Eq.comm, ←cs.not_isRightDescent_iff, ←lt_self_mul_simple_iff,
    and_iff_right_iff_imp]
  apply le_of_lt

/-- Bjorner--Brenti Proposition 2.2.7 -/
theorem lifting_property {u w : W} {i : B W}
  (h1 : u ≤ w) (h2 : cs.IsLeftDescent w i) (h3 : ¬ cs.IsLeftDescent u i) :
  u ≤ cs.simple i * w ∧ cs.simple i * u ≤ w := by
  have ⟨ω, hω1, hω2⟩ := cs.exists_isReduced (cs.simple i * w)
  have h4 : cs.IsReduced (i :: ω) := by
    rwa [isReduced_cons hω1, ←hω2, ←isLeftDescent_iff_not_isLeftDescent_mul]
  rw [←eq_inv_mul_iff_mul_eq, inv_simple, ←wordProd_cons] at hω2
  have ⟨⟨μ, hμ1, hμ2⟩, hsub⟩ := exists_reduced_subword_of_le ⟨i :: ω, h4, hω2⟩ h1
  dsimp at hsub
  match μ, hsub with
  | [], _ =>
      rw [hμ2, wordProd_nil, mul_one]
      refine ⟨bot_le, le_of_reduced_subword ⟨[i], ⟨isReduced_singleton i, ?_⟩⟩ ⟨i :: ω, ⟨h4, hω2⟩⟩
        (Sublist.cons₂ _ (nil_sublist _))⟩
      rw [wordProd_singleton]
  | j :: μ, Sublist.cons _ hsub =>
      refine ⟨le_of_reduced_subword ⟨j :: μ, hμ1, hμ2⟩ ⟨ω, hω1, ?_⟩ hsub,
        le_of_reduced_subword ⟨i :: j :: μ, ?_, ?_⟩ ⟨i :: ω, h4, hω2⟩ (Sublist.cons₂ _ hsub)⟩
      · rw [hω2, wordProd_cons, simple_mul_simple_cancel_left]
      · rwa [isReduced_cons hμ1, ←hμ2]
      · rw [wordProd_cons, hμ2]
  | i :: μ, Sublist.cons₂ _ hsub =>
      absurd hμ1
      rwa [not_isReduced_cons, isLeftDescent_iff_not_isLeftDescent_mul, ←wordProd_cons, ←hμ2]
      exact hμ1.drop 1

/-- Bjorner--Brenti Corollary 2.2.8 (i) -/
theorem local_configuration {i : B W} {t w : W}
  (h : cs.simple i ≠ t) (h2 : w ⋖ cs.simple i * w) (h3 : w ⋖ t * w) :
  cs.simple i * w ⋖ cs.simple i * t * w ∧ t * w ⋖ cs.simple i * t * w := by
  have h4 : ¬ cs.IsLeftDescent (t * w) i := by
    contrapose h
    rw [←mul_left_inj w]
    apply eq_of_le_of_length_eq
    · rw [covBy_simple_mul_self_iff] at h2
      exact (lifting_property h3.1.le h h2).2
    · rw [←length_cover h2, ←length_cover h3]
  have h5 : cs.length (cs.simple i * (t * w)) = cs.length (t * w) + 1 := by
    rwa [not_isLeftDescent_iff] at h4
  rw [←lt_simple_mul_self_iff] at h4
  have h6 : cs.simple i * w ≤ cs.simple i * (t * w) := by
    rw [covBy_simple_mul_self_iff] at h2
    rw [←cs.not_isLeftDescent_iff, cs.isLeftDescent_iff_not_isLeftDescent_mul, not_not] at h5
    exact (lifting_property ((h3.1.trans h4).le) h5 h2).2
  rw [covBy_iff, covBy_iff, mul_assoc]
  refine ⟨⟨h6, ?_⟩, ⟨h4.le, h5.symm⟩⟩
  rw [h5, ←length_cover h2, length_cover h3]

/-- Bjorner--Brenti Corollary 2.2.8 (ii) -/
theorem local_configuration₂ {i i' : B W} {w : W}
  (h : w ⋖ cs.simple i * w) (h2 : w ⋖ w * cs.simple i') :
  (cs.simple i * w ⋖ cs.simple i * w * cs.simple i' ∧
    w * cs.simple i' ⋖ cs.simple i * w * cs.simple i') ∨
  w = cs.simple i * w * cs.simple i' := by
  by_cases h3 : cs.IsLeftDescent (w * cs.simple i') i
  · right
    rw [mul_assoc]
    rw [covBy_simple_mul_self_iff] at h
    rw [covBy_iff] at h2
    have h5 := (lifting_property h2.1 h3 h).1
    apply eq_of_le_of_length_eq h5
    rw [isLeftDescent_iff] at h3
    lia
  · left
    have h4 : w * cs.simple i' < cs.simple i * (w * cs.simple i') := by
      rwa [←lt_simple_mul_self_iff] at h3
    have h5 : cs.IsLeftDescent (cs.simple i * (w * cs.simple i')) i := by
      rwa [isLeftDescent_iff_not_isLeftDescent_mul, simple_mul_simple_cancel_left]
    have h6 : ¬ cs.IsLeftDescent w i := by
      rw [←lt_simple_mul_self_iff]
      exact h.1
    rw [not_isLeftDescent_iff, ←mul_assoc] at h3
    have h7 := lifting_property ((h2.1.trans h4).le) h5 h6
    rw [←mul_assoc] at h4
    rw [not_isLeftDescent_iff] at h6
    rw [simple_mul_simple_cancel_left, ←mul_assoc] at h7
    rw [covBy_iff, covBy_iff]
    refine ⟨⟨h7.2, ?_⟩, ⟨h4.le, h3.symm⟩⟩
    rw [h3, h6, length_cover h2]

/-- Bjorner--Brenti Proposition 2.2.9 -/
instance : IsDirectedOrder W where
  directed u := by
    induction u using WellFoundedLT.induction with | ind u ih =>
    intro w
    by_cases h : u = 1
    · exists w
      rw [h]
      exact ⟨bot_le, le_refl _⟩
    · have ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h
      have hlt : cs.simple i * u < u := by
        rwa [simple_mul_lt_self_iff]
      have ⟨x, hx1, hx2⟩ := ih (cs.simple i * u) hlt w
      rw [isLeftDescent_iff_not_isLeftDescent_mul] at hi
      by_cases h2 : cs.IsLeftDescent x i
      · exists x
        have h3 := (lifting_property hx1 h2 hi).2
        rw [simple_mul_simple_cancel_left] at h3
        exact ⟨h3, hx2⟩
      · exists cs.simple i * x
        have h3 : x ≤ cs.simple i * x := ((lt_simple_mul_self_iff i x).mpr h2).le
        rw [isLeftDescent_iff_not_isLeftDescent_mul, not_not] at h2
        have h4 := (lifting_property (hx1.trans h3) h2 hi).2
        rw [simple_mul_simple_cancel_left] at h4
        exact ⟨h4, hx2.trans h3⟩

section finite

/-! ### Bruhat order on finite Coxeter groups -/

theorem isTop_iff_all_isLeftDescent {x : W} : (∀ (i : B W), cs.IsLeftDescent x i) ↔ IsTop x := by
  constructor
  · intro h u
    induction u using WellFoundedLT.induction with | ind u ih =>
    by_cases h2 : u = 1
    · subst h2
      exact bot_le
    · have ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h2
      specialize ih _ ((simple_mul_lt_self_iff i u).mpr hi)
      rw [isLeftDescent_iff_not_isLeftDescent_mul] at hi
      have h3 := (lifting_property ih (h i) hi).2
      rwa [simple_mul_simple_cancel_left] at h3
  · intro h i
    rw [←simple_mul_lt_self_iff]
    apply h.lt_of_ne
    rw [mul_ne_right]
    apply simple_ne_one

theorem finite_of_orderTop [OrderTop W] : Finite W := by
  apply Finite.of_finite_univ (Set.Finite.ofFinset (Finset.Icc ⊥ ⊤) _)
  simp

/-- Bjorner--Brenti Proposition 2.3.1 (ii) -/
theorem finite_of_exists_all_isLeftDescent {x : W} (h : ∀ (i : B W), cs.IsLeftDescent x i) :
  Finite W := by
  haveI : OrderTop W := {
    top := x
    le_top := isTop_iff_all_isLeftDescent.mp h
  }
  exact finite_of_orderTop

variable [Finite W]

/-- Bjorner--Brenti Proposition 2.3.1 (i) -/
noncomputable instance : OrderTop W := inferInstance

noncomputable def w₀ : W := ⊤

/-- Bjorner--Brenti Proposition 2.3.1 (ii) continued -/
theorem all_isLeftDescent_iff (x : W) : (∀ (i : B W), cs.IsLeftDescent x i) ↔ x = w₀ := by
  rw [isTop_iff_all_isLeftDescent]
  exact isTop_iff_eq_top

theorem length_le_length_w₀ (w : W) : cs.length w ≤ cs.length (w₀ : W) := monotone_length le_top

theorem eq_w₀_of_length_ge {x : W} (h : cs.length x ≥ cs.length (w₀ : W)) : x = w₀ :=
  eq_of_le_of_length_ge le_top h

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
  apply le_antisymm
  · have hle : cs.length w ≤ cs.length w₀ := length_le_length_w₀ w
    generalize hk : cs.length w = k at hle
    induction hle using Nat.decreasingInduction generalizing w with
    | self =>
        apply eq_w₀_of_length_eq at hk
        rw [hk, w₀_mul_self, length_one]
        apply Nat.zero_le
    | of_succ k hk_lt ih =>
        subst hk
        have ⟨i, hi⟩ : ∃ x, ¬cs.IsLeftDescent w x := by
          rw [←not_forall, all_isLeftDescent_iff]
          apply_fun cs.length
          exact hk_lt.ne
        rw [not_isLeftDescent_iff] at hi
        specialize ih (cs.simple i * w) hi
        rw [mul_assoc] at ih
        trans cs.length (cs.simple i * (w * w₀)) + 1
        · have h := cs.length_le_length_mul_add_left (cs.simple i) (w * w₀)
          rwa [length_simple] at h
        · lia
  · rw [Nat.sub_le_iff_le_add]
    apply cs.length_le_length_mul_add_left

/-- Bjorner--Brenti Proposition 2.3.2 (iii) -/
theorem isLeftInversion_mul_w₀_iff {t : W} (ht : cs.IsReflection t) (w : W) :
  cs.IsLeftInversion (w * w₀) t ↔ ¬ cs.IsLeftInversion w t := by
  rw [←ht.isLeftInversion_mul_right_iff]
  simp only [IsLeftInversion, ht, true_and]
  rw [←mul_assoc, ←mul_assoc, ht.mul_self, one_mul, length_mul_w₀, length_mul_w₀,
    tsub_lt_tsub_iff_left_of_le_of_le (length_le_length_w₀ _) (length_le_length_w₀ _)]

theorem isLeftInversion_w₀_iff (t : W) : cs.IsLeftInversion w₀ t ↔ cs.IsReflection t := by
  refine ⟨And.left, ?_⟩
  intro ht
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
      rw [←ht, mul_assoc, lt_reflection_mul_self_iff h2]
      simp only [IsLeftInversion, h2, true_and, not_lt]
      rw [←mul_assoc, length_mul_w₀, length_mul_w₀, ht]
      have := length_le_length_w₀ w
      lia

theorem strictAnti_mul_w₀ : StrictAnti (Equiv.mulRight (w₀ : W)) :=
  antitone_mul_w₀.strictAnti_of_injective (Equiv.injective _)

theorem antitone_w₀_mul : Antitone (Equiv.mulLeft (w₀ : W)) := by
  intro u w h
  dsimp
  rw [←inv_inv (w₀ * w), ←inv_inv (w₀ * u)]
  apply monotone_inv
  rw [mul_inv_rev, mul_inv_rev, inv_w₀]
  exact antitone_mul_w₀ (monotone_inv h)

theorem strictAnti_w₀_mul : StrictAnti (Equiv.mulLeft (w₀ : W)) :=
  antitone_w₀_mul.strictAnti_of_injective (Equiv.injective _)

/-- Bjorner--Brenti Proposition 2.3.4 (ii) -/
theorem monotone_conj_w₀ : Monotone (MulAut.conj (w₀ : W)) := by
  intro u v h
  rw [MulAut.conj_apply, MulAut.conj_apply, inv_w₀]
  exact antitone_mul_w₀ (antitone_w₀_mul h)

theorem strictMono_conj_w₀ : StrictMono (MulAut.conj (w₀ : W)) :=
  monotone_conj_w₀.strictMono_of_injective (MulEquiv.injective _)

end finite

end Coxeter
