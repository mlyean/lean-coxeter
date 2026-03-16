import Coxeter.Basic

/-!
# Permutation representation of Coxeter groups

This file defines the permutation representation of a Coxeter group.

## Main definitions

* `Coxeter.ReflectionSet`
* `Coxeter.RootSet`
* `Coxeter.permRep`
* `Coxeter.η`

## Main statements

* `Coxeter.eta_spec`
* `Coxeter.permRep_eq`
* `Coxeter.permRep_inj`

## References

* [bjorner2005] A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*

-/

namespace Coxeter

open Function List CoxeterSystem CoxeterGroup

def ReflectionSet (W : Type*) [CoxeterGroup W] : Type _ := {t : W // cs.IsReflection t}

def RootSet (W : Type*) [CoxeterGroup W] : Type _ := ReflectionSet W × ZMod 2

variable {W : Type*} [CoxeterGroup W]

/-- Induction principle for reflections -/
theorem ReflectionSet.induction {P : ReflectionSet W → Prop}
  (sh : ∀ (i : B W), P (⟨cs.simple i, cs.isReflection_simple i⟩))
  (ih : ∀ (t : ReflectionSet W) (i : B W),
    P t → P (⟨(cs.simple i) * t.val * (cs.simple i)⁻¹, t.prop.conj (cs.simple i)⟩)) :
  ∀ (t : ReflectionSet W), P t := by
  intro ⟨t, w, i, hi⟩
  subst hi
  apply cs.simple_induction_left w
  · simp only [one_mul, inv_one, mul_one]
    exact sh i
  · intro w j h
    apply Eq.subst _ (ih _ j h)
    group

noncomputable section construction

open Classical in
def etaAux (ω : List (B W)) (t : W) : ZMod 2 := count t (cs.leftInvSeq ω)

theorem etaAux_append (μ ω : List (B W)) (t : W) :
  etaAux (μ ++ ω) t = etaAux μ t + etaAux ω ((cs.wordProd μ)⁻¹ * t * cs.wordProd μ) := by
  classical
  unfold etaAux
  rw [leftInvSeq_append, count_append, Nat.cast_add, add_right_inj,
    count_eq_countP, count_eq_countP, countP_map]
  congr
  ext w
  simp only [comp_apply, MulAut.conj_apply, beq_eq_beq]
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq]

def permRepAux (ω : List (B W)) (r : RootSet W) : RootSet W :=
  ⟨⟨MulAut.conj (cs.wordProd ω) r.1.val, r.1.prop.conj _⟩, r.2 + etaAux ω.reverse r.1.val⟩

theorem permRepAux_nil : permRepAux ([] : List (B W)) = id := by
  unfold permRepAux etaAux
  simp
  rfl

theorem permRepAux_cons (i : B W) (ω : List (B W)) :
  permRepAux (i :: ω) = permRepAux [i] ∘ permRepAux ω := by
  classical
  ext ⟨t, ε⟩
  rw [comp_apply]
  unfold permRepAux
  dsimp
  congr 1
  · congr 1
    change MulAut.conj (cs.wordProd (i :: ω)) t.val
      = MulAut.conj (cs.wordProd [i]) (MulAut.conj (cs.wordProd ω) t.val)
    rw [wordProd_singleton, wordProd_cons, map_mul, MulAut.mul_apply]
  · rw [add_assoc, reverse_cons, reverse_singleton, add_right_inj, etaAux_append]
    simp only [wordProd_reverse, inv_inv]

theorem permRepAux_append (ω₁ ω₂ : List (B W)) :
  permRepAux (ω₁ ++ ω₂) = permRepAux ω₁ ∘ permRepAux ω₂ := by
  induction ω₁ with
  | nil =>
      rw [permRepAux_nil]
      simp
  | cons i is ih =>
      rw [cons_append, permRepAux_cons, ih]
      nth_rw 2 [permRepAux_cons]
      rfl

theorem permRepAux_alternatingWord (i i' : B W) :
  permRepAux (alternatingWord i i' (2 * M i i')) = id := by
  classical
  ext r
  unfold permRepAux
  apply Prod.ext
  · simp [prod_alternatingWord_eq_mul_pow]
  · unfold etaAux
    rw [id_eq, add_eq_left, reverse_alternatingWord, ZMod.natCast_eq_zero_iff]
    let p := M.M i i'
    suffices h : take p (cs.leftInvSeq (alternatingWord i' i (2 * p)))
      = drop p (cs.leftInvSeq (alternatingWord i' i (2 * p))) by
      rw [←take_append_drop p (cs.leftInvSeq (alternatingWord i' i (2 * p))), count_append,
        h, ←two_mul]
      apply dvd_mul_right
    rw [ext_get_iff]
    simp only [length_take, length_drop, length_leftInvSeq, length_alternatingWord]
    constructor
    · grind
    · intro n h _
      rw [lt_inf_iff] at h
      simp only [get_eq_getElem, getElem_take, getElem_drop]
      rw [cs.getElem_leftInvSeq_alternatingWord _ _ _ _ h.2,
        cs.getElem_leftInvSeq_alternatingWord _ _ _ _
          (by rw [two_mul]; exact add_lt_add_right h.1 p)]
      have h2 : 2 * (p + n) + 1 = (2 * p) + (2 * n + 1) := by linarith
      rw [h2]
      nth_rw 2 [alternatingWord_even_add]
      rw [wordProd_append, left_eq_mul, prod_alternatingWord_eq_mul_pow]
      unfold p
      simp

theorem permRepAux_singleton_involutive (i : B W) :
  Function.Involutive (permRepAux [i]) := by
  suffices h : permRepAux [i] ∘ permRepAux [i] = id from congr_fun h
  rw [←permRepAux_cons]
  have h := permRepAux_alternatingWord i i
  rwa [CoxeterMatrix.diagonal] at h

def permRepAux_equiv (i : B W) : Equiv.Perm (RootSet W) := {
  toFun := permRepAux [i]
  invFun := permRepAux [i]
  left_inv := permRepAux_singleton_involutive i
  right_inv := permRepAux_singleton_involutive i
}

theorem permRepAux_iterate (i i' : B W) (k : ℕ) :
  (permRepAux [i, i'])^[k] = permRepAux (alternatingWord i i' (2 * k)) := by
  induction k with
  | zero =>
      rw [iterate_zero, alternatingWord, permRepAux_nil]
  | succ k ih =>
      simp only [iterate_succ, alternatingWord, Nat.mul_eq, concat_eq_append, append_assoc,
        cons_append, nil_append]
      rw [permRepAux_append, ih]

theorem permRepAux_liftable : (@M W).IsLiftable permRepAux_equiv := by
  intro i i'
  ext r
  rw [Equiv.Perm.coe_one, Equiv.Perm.coe_pow, Equiv.Perm.coe_mul]
  change ((permRepAux [i]) ∘ (permRepAux [i']))^[M.M i i'] r = id r
  rw [←permRepAux_cons, permRepAux_iterate i i' (M.M i i'), permRepAux_alternatingWord]

/-- Bjorner--Brenti Theorem 1.3.2 (i): extension -/
def permRep : W →* Equiv.Perm (RootSet W) := cs.lift ⟨permRepAux_equiv, permRepAux_liftable⟩

open Classical in
def η (w t : W) : ZMod 2 := count t (cs.leftInvSeq (choose (cs.wordProd_surjective w)))

end construction

theorem permRep_wordProd_eq_permRepAux (ω : List (B W)) :
  permRep (cs.wordProd ω) = permRepAux ω := by
  induction ω with
  | nil =>
      rw [wordProd_nil, map_one, Equiv.Perm.coe_one, permRepAux_nil]
  | cons i is ih =>
      rw [permRepAux_cons, wordProd_cons, map_mul, Equiv.Perm.coe_mul, ih,
        permRep, lift_apply_simple]
      rfl

open Classical in
theorem eta_spec (ω : List (B W)) (t : W) :
  η (cs.wordProd ω) t = count t (cs.leftInvSeq ω) := by
  by_cases ht : cs.IsReflection t
  · have h : permRep (cs.wordProd (Classical.choose
      (cs.wordProd_surjective (cs.wordProd ω))).reverse) (⟨t, ht⟩, 0)
      = permRep (cs.wordProd ω.reverse) (⟨t, ht⟩, 0) := by
      congr 2
      rw [wordProd_reverse, wordProd_reverse, inv_inj]
      exact choose_spec (cs.wordProd_surjective (cs.wordProd ω))
    rw [permRep_wordProd_eq_permRepAux, permRep_wordProd_eq_permRepAux] at h
    have h2 := congr_arg Prod.snd h
    unfold permRepAux at h2
    simp only [etaAux, reverse_reverse, zero_add] at h2
    exact h2
  · unfold η
    congr 1
    trans 0
    on_goal 2 => symm
    all_goals
      rw [count_eq_zero]
      intro h
      exact ht (cs.isReflection_of_mem_leftInvSeq _ h)

@[simp]
theorem eta_simple (i : B W) : η (cs.simple i) (cs.simple i) = 1 := by
  classical
  rw [←cs.wordProd_singleton i, eta_spec, wordProd_singleton, leftInvSeq_singleton,
    count_singleton_self, Nat.cast_one]

@[simp]
theorem eta_conj (i : B W) (t : W) :
  η (cs.simple i) (cs.simple i * t * (cs.simple i)⁻¹) = η (cs.simple i) t := by
  classical
  nth_rw 1 4 [←wordProd_singleton]
  rw [eta_spec, eta_spec, leftInvSeq]
  dsimp
  rw [count_singleton, count_singleton]
  congr 2
  rw [beq_iff_eq, beq_iff_eq, eq_iff_iff, eq_mul_inv_iff_mul_eq, ←inv_mul_eq_iff_eq_mul,
    inv_mul_cancel_left]

theorem permRep_eq (w : W) (r : RootSet W) : permRep w r
  = ⟨⟨MulAut.conj w r.1.val, r.1.prop.conj _⟩, r.2 + η w⁻¹ r.1.val⟩ := by
  let ⟨ω, hω1, hω2⟩ := cs.exists_reduced_word w
  subst hω2
  rw [permRep_wordProd_eq_permRepAux, ←wordProd_reverse, eta_spec]
  rfl

theorem permRep_inv_eq (w : W) (r : RootSet W) : permRep w⁻¹ r
  = ⟨⟨MulAut.conj w⁻¹ r.1.val, r.1.prop.conj _⟩, r.2 + η w r.1.val⟩ := by
  rw [permRep_eq, inv_inv]

/-- Bjorner--Brenti Theorem 1.3.2 (i): injectivity -/
theorem permRep_inj : Function.Injective (@permRep W _) := by
  classical
  rw [injective_iff_map_eq_one]
  intro w hw
  let ⟨ω, hω1, hω2⟩ := cs.exists_reduced_word (w⁻¹)
  rw [inv_eq_iff_eq_inv] at hω2
  subst hω2
  rw [inv_inv] at hω1
  rw [inv_eq_one, ←cs.length_eq_zero_iff, ←hω1]
  cases ω with
  | nil => rfl
  | cons i is =>
    have h : count (cs.simple i) (cs.leftInvSeq (i :: is)) = 1 := by
      apply count_eq_one_of_mem
      · apply IsReduced.nodup_leftInvSeq
        exact hω1.symm
      · apply Mem.head
    have h2 := congr_arg Prod.snd (permRep_inv_eq (cs.wordProd (i :: is))
      ⟨⟨cs.simple i, cs.isReflection_simple i⟩, 0⟩)
    rw [hw, Equiv.Perm.coe_one, id_eq, zero_add, eta_spec, h] at h2
    dsimp at h2
    contradiction

/-- Bjorner--Brenti Theorem 1.3.2 (ii) -/
theorem permRep_reflection (t : ReflectionSet W) (ε : ZMod 2) :
  permRep t.val (t, ε) = (t, ε + 1) := by
  revert t ε
  apply ReflectionSet.induction
  · simp [permRep_eq]
  · intro t i ih ε
    calc
      permRep (cs.simple i * t.val * (cs.simple i)⁻¹)
        (⟨cs.simple i * t.val * (cs.simple i)⁻¹, t.prop.conj _⟩, ε)
        = permRep (cs.simple i) (permRep t.val (permRep (cs.simple i)⁻¹
          (⟨cs.simple i * t.val * (cs.simple i)⁻¹, t.prop.conj _⟩, ε))) := by simp
      _ = permRep (cs.simple i) (permRep t.val ((t, ε + η (cs.simple i) t.val))) := ?_
      _ = permRep (cs.simple i) ((t, ε + η (cs.simple i) t.val + 1)) := by rw [ih]
      _ = (⟨cs.simple i * t.val * (cs.simple i)⁻¹, _⟩, ε + 1) := ?_
    · rw [permRep_inv_eq, eta_conj]
      dsimp
      group
      rfl
    · rw [permRep_eq]
      dsimp
      congr 1
      rw [inv_simple]
      grind

theorem isLeftInversion_of_eta_eq_one {w t : W} (h : η w t = 1) : cs.IsLeftInversion w t := by
  classical
  let ⟨ω, hω1, hω2⟩ := cs.exists_reduced_word' w
  subst hω2
  rw [eta_spec] at h
  have h2 : 0 < count t (cs.leftInvSeq ω) := by
    rw [pos_iff_ne_zero]
    intro heq
    rw [heq] at h
    contradiction
  rw [count_pos_iff, mem_iff_get] at h2
  let ⟨i, hi⟩ := h2
  apply cs.isLeftInversion_of_mem_leftInvSeq hω1
  rw [←hi]
  apply List.getElem_mem

theorem not_isLeftInversion_of_eta_eq_zero {w t : W} (h : η w t = 0) :
  ¬ cs.IsLeftInversion w t := by
  intro h2
  have ht := h2.1
  rw [←ht.not_isLeftInversion_mul_right_iff] at h2
  apply h2
  apply isLeftInversion_of_eta_eq_one
  have h3 := congr_arg Prod.snd (permRep_inv_eq (t * w) (⟨t, ht⟩, 0))
  rwa [zero_add, mul_inv_rev, map_mul, Equiv.Perm.coe_mul, comp_apply, ht.inv,
    permRep_inv_eq, permRep_reflection ⟨t, ht⟩, h, zero_add, Eq.comm] at h3

theorem eta_eq_one_iff {t w : W} : η w t = 1 ↔ cs.IsLeftInversion w t := by
  generalize h : η w t = a
  match a with
  | 0 =>
      simp only [zero_ne_one, false_iff]
      apply not_isLeftInversion_of_eta_eq_zero h
  | 1 =>
      simp only [true_iff]
      apply isLeftInversion_of_eta_eq_one h

theorem eta_eq_zero_iff {t w : W} : η w t = 0 ↔ ¬ cs.IsLeftInversion w t := by
  trans ¬ η w t = 1
  · unfold ZMod
    grind
  · rw [not_iff_not, eta_eq_one_iff]

end Coxeter
