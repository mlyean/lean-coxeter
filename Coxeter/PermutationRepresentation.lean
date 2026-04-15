module

public import Coxeter.Basic

/-!
# Permutation representation of Coxeter groups

This file defines the permutation representation of a Coxeter group.

## Main definitions

* `Coxeter.ReflectionSet`
* `Coxeter.AbstractRootSet`
* `Coxeter.permRep`
* `Coxeter.η`

## Main statements

* `Coxeter.eta_spec`
* `Coxeter.permRep_eq`
* `Coxeter.permRep_inj`

## References

* [bjorner2005] A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*
-/

@[expose] public section

namespace Coxeter

open Function List CoxeterSystem CoxeterGroup

def ReflectionSet (W : Type*) [CoxeterGroup W] : Type _ := {t : W // cs.IsReflection t}

def AbstractRootSet (W : Type*) [CoxeterGroup W] : Type _ := ReflectionSet W × ZMod 2

variable {W : Type*} [CoxeterGroup W]

/-- Induction principle for reflections -/
theorem ReflectionSet.induction {motive : ReflectionSet W → Prop}
  (simple : ∀ (i : B W), motive (⟨cs.simple i, cs.isReflection_simple i⟩))
  (conj : ∀ (t : ReflectionSet W) (i : B W), motive t →
    motive (⟨cs.simple i * t.val * (cs.simple i)⁻¹, t.prop.conj (cs.simple i)⟩))
  (t : ReflectionSet W) : motive t := by
  obtain ⟨t, w, i, hi⟩ := t
  subst hi
  induction w using (@cs W).simple_induction_left with
  | one =>
      simp only [one_mul, inv_one, mul_one]
      exact simple i
  | mul_simple_left w j h =>
      apply Eq.subst _ (conj _ j h)
      group

noncomputable section construction

/-! ### Construction of the permutation representation -/

open Classical in
def etaAux (ω : List (B W)) (t : W) : ZMod 2 := count t (cs.leftInvSeq ω)

theorem etaAux_append (μ ω : List (B W)) (t : W) :
  etaAux (μ ++ ω) t = etaAux μ t + etaAux ω ((cs.wordProd μ)⁻¹ * t * cs.wordProd μ) := by
  unfold etaAux
  classical rw [leftInvSeq_append, count_append, Nat.cast_add, add_right_inj,
    count_eq_countP, count_eq_countP, countP_map]
  congr
  ext w
  simp only [comp_apply, MulAut.conj_apply, beq_eq_beq]
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq]

def permRepAux (ω : List (B W)) (r : AbstractRootSet W) : AbstractRootSet W :=
  ⟨⟨MulAut.conj (cs.wordProd ω) r.1.val, r.1.prop.conj _⟩, r.2 + etaAux ω.reverse r.1.val⟩

theorem permRepAux_nil : permRepAux ([] : List (B W)) = id := by
  unfold permRepAux etaAux
  simp
  rfl

theorem permRepAux_append (ω₁ ω₂ : List (B W)) :
  permRepAux (ω₁ ++ ω₂) = permRepAux ω₁ ∘ permRepAux ω₂ := by
  ext ⟨⟨t, _⟩, ε⟩
  rw [comp_apply]
  unfold permRepAux
  dsimp
  rw [add_assoc, reverse_append, etaAux_append, wordProd_reverse, inv_inv]
  congr 2
  rw [wordProd_append]
  group

theorem permRepAux_cons (i : B W) (ω : List (B W)) :
  permRepAux (i :: ω) = permRepAux [i] ∘ permRepAux ω := by
  rw [←singleton_append, permRepAux_append]

theorem permRepAux_alternatingWord (i i' : B W) :
  permRepAux (alternatingWord i i' (2 * M i i')) = id := by
  ext r
  unfold permRepAux
  apply Prod.ext
  · simp [prod_alternatingWord_eq_mul_pow]
  · unfold etaAux
    rw [id_eq, add_eq_left, reverse_alternatingWord, ZMod.natCast_eq_zero_iff]
    let p := M i i'
    suffices h : take p (cs.leftInvSeq (alternatingWord i' i (2 * p)))
      = drop p (cs.leftInvSeq (alternatingWord i' i (2 * p))) by
      classical rw [←take_append_drop p (cs.leftInvSeq (alternatingWord i' i (2 * p))),
        count_append, h, ←two_mul]
      apply dvd_mul_right
    rw [ext_get_iff]
    simp only [length_take, length_drop, length_leftInvSeq, length_alternatingWord]
    constructor
    · grind
    · intro n h _
      rw [lt_inf_iff] at h
      simp only [get_eq_getElem, getElem_take, getElem_drop]
      rw [cs.getElem_leftInvSeq_alternatingWord _ _ _ _ h.2,
        cs.getElem_leftInvSeq_alternatingWord _ _ _ _ (by lia),
        show 2 * (p + n) + 1 = (2 * p) + (2 * n + 1) by ring]
      nth_rw 2 [alternatingWord_even_add]
      rw [wordProd_append, left_eq_mul, prod_alternatingWord_eq_mul_pow]
      simp [p]

theorem permRepAux_singleton_involutive (i : B W) : Involutive (permRepAux [i]) := by
  suffices h : permRepAux [i] ∘ permRepAux [i] = id from congr_fun h
  rw [←permRepAux_cons]
  have h := permRepAux_alternatingWord i i
  rwa [CoxeterMatrix.diagonal] at h

def permRepAux_equiv (i : B W) : Equiv.Perm (AbstractRootSet W) := {
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
      rw [iterate_succ, ih, ←permRepAux_append, mul_add]
      simp [alternatingWord]

theorem permRepAux_liftable : (@M W).IsLiftable permRepAux_equiv := by
  intro i i'
  rw [←Equiv.coe_inj]
  change ((permRepAux [i]) ∘ (permRepAux [i']))^[M i i'] = id
  rw [←permRepAux_cons, permRepAux_iterate i i' (M i i'), permRepAux_alternatingWord]

/-- Bjorner--Brenti Theorem 1.3.2 (i): extension -/
def permRep : W →* Equiv.Perm (AbstractRootSet W) := cs.lift ⟨permRepAux_equiv, permRepAux_liftable⟩

open Classical in
def eta (w t : W) : ZMod 2 := count t (cs.leftInvSeq (cs.wordProd_surjective w).choose)

end construction

local notation "η" => eta

theorem permRep_wordProd_eq_permRepAux (ω : List (B W)) :
  permRep (cs.wordProd ω) = permRepAux ω := by
  induction ω with
  | nil =>
      rw [wordProd_nil, map_one, Equiv.Perm.coe_one, permRepAux_nil]
  | cons i is ih =>
      rw [permRepAux_cons, wordProd_cons, map_mul, Equiv.Perm.coe_mul, ih,
        permRep, lift_apply_simple]
      rfl

/-! ### Properties of $η$ -/

open Classical in
theorem eta_spec (ω : List (B W)) (t : W) : η (cs.wordProd ω) t = count t (cs.leftInvSeq ω) := by
  by_cases ht : cs.IsReflection t
  · have h : permRep (cs.wordProd ((cs.wordProd_surjective (cs.wordProd ω))).choose.reverse)
      (⟨t, ht⟩, 0) = permRep (cs.wordProd ω.reverse) (⟨t, ht⟩, 0) := by
      congr 2
      rw [wordProd_reverse, wordProd_reverse, inv_inj]
      exact (cs.wordProd_surjective (cs.wordProd ω)).choose_spec
    rw [permRep_wordProd_eq_permRepAux, permRep_wordProd_eq_permRepAux] at h
    apply_fun Prod.snd at h
    simp [permRepAux, etaAux] at h
    assumption
  · unfold eta
    rw [count_eq_zero.mpr, count_eq_zero.mpr]
    all_goals
      contrapose ht
      exact cs.isReflection_of_mem_leftInvSeq _ ht

theorem eta_mul (u w t : W) : η (u * w) t = η u t + η w (u⁻¹ * t * u) := by
  have ⟨μ, hμ⟩ := cs.wordProd_surjective u
  have ⟨ω, hω⟩ := cs.wordProd_surjective w
  subst hμ hω
  rw [←wordProd_append, eta_spec, eta_spec, eta_spec]
  apply etaAux_append

@[simp]
theorem eta_simple_self (i : B W) : η (cs.simple i) (cs.simple i) = 1 := by
  nth_rw 1 [←cs.wordProd_singleton i]
  classical rw [eta_spec, leftInvSeq_singleton, count_singleton_self, Nat.cast_one]

theorem eta_reflection_self {t : W} (ht : cs.IsReflection t) : η t t = 1 := by
  let t' : ReflectionSet W := ⟨t, ht⟩
  change η t'.val t'.val = 1
  induction t' using ReflectionSet.induction with
  | simple i =>
      apply eta_simple_self
  | conj t i ih =>
      dsimp
      have h1 := (eta_mul (cs.simple i) (cs.simple i * t.val * (cs.simple i)⁻¹) t.val)
      conv at h1 in cs.simple i * (cs.simple i * ↑t * (cs.simple i)⁻¹) =>
        rw [mul_assoc, inv_simple, simple_mul_simple_cancel_left]
      nth_rw 2 [inv_simple] at h1
      nth_rw 6 [←inv_simple] at h1
      have h2 := eta_mul t.val (cs.simple i) t.val
      rw [inv_mul_cancel, one_mul, ih] at h2
      rw [h2, add_comm, add_right_inj] at h1
      exact h1.symm

theorem isLeftInversion_of_eta_eq_one {w t : W} (h : η w t = 1) : cs.IsLeftInversion w t := by
  have ⟨ω, hω1, hω2⟩ := cs.exists_isReduced w
  subst hω2
  apply cs.isLeftInversion_of_mem_leftInvSeq hω1
  classical rw [eta_spec, hω1.nodup_leftInvSeq.count] at h
  simp at h
  assumption

theorem not_isLeftInversion_of_eta_eq_zero {w t : W} (h : η w t = 0) :
  ¬ cs.IsLeftInversion w t := by
  wlog ht : cs.IsReflection t
  · contrapose ht
    exact ht.1
  · rw [←ht.isLeftInversion_mul_right_iff]
    apply isLeftInversion_of_eta_eq_one
    rw [eta_mul]
    simp [eta_reflection_self ht, h]

theorem eta_eq_one_iff {t w : W} : η w t = 1 ↔ cs.IsLeftInversion w t := by
  match h : η w t with
  | 0 => simp [not_isLeftInversion_of_eta_eq_zero h]
  | 1 => simp [isLeftInversion_of_eta_eq_one h]

theorem eta_eq_zero_iff {t w : W} : η w t = 0 ↔ ¬ cs.IsLeftInversion w t := by
  rw [←eta_eq_one_iff]
  unfold ZMod
  grind

/-! ### Properties of the permutation representation -/

theorem permRep_eq (w : W) (r : AbstractRootSet W) : permRep w r
  = ⟨⟨MulAut.conj w r.1.val, r.1.prop.conj _⟩, r.2 + η w⁻¹ r.1.val⟩ := by
  have ⟨ω, hω1, hω2⟩ := cs.exists_isReduced w
  subst hω2
  rw [permRep_wordProd_eq_permRepAux, ←wordProd_reverse, eta_spec]
  rfl

theorem permRep_inv_eq (w : W) (r : AbstractRootSet W) :
  permRep w⁻¹ r = ⟨⟨MulAut.conj w⁻¹ r.1.val, r.1.prop.conj _⟩, r.2 + η w r.1.val⟩ := by
  rw [permRep_eq, inv_inv]

/-- Bjorner--Brenti Theorem 1.3.2 (i): injectivity -/
theorem permRep_inj : Injective (@permRep W _) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have ⟨ω, hω1, hω2⟩ := cs.exists_isReduced w⁻¹
  rw [inv_eq_iff_eq_inv] at hω2
  subst hω2
  rw [inv_eq_one, ←cs.length_eq_zero_iff, hω1]
  cases ω with
  | nil => rfl
  | cons i is =>
      have h := permRep_inv_eq (cs.wordProd (i :: is)) ⟨⟨cs.simple i, cs.isReflection_simple i⟩, 0⟩
      apply_fun Prod.snd at h
      classical rw [hw, Equiv.Perm.coe_one, id_eq, zero_add, eta_spec,
        count_eq_one_of_mem hω1.nodup_leftInvSeq (Mem.head _)] at h
      change 0 = 1 at h
      contradiction

/-- Bjorner--Brenti Theorem 1.3.2 (ii) -/
theorem permRep_reflection (t : ReflectionSet W) (ε : ZMod 2) :
  permRep t.val (t, ε) = (t, ε + 1) := by
  rw [permRep_eq, t.prop.inv]
  simp [eta_reflection_self t.prop]

end Coxeter
