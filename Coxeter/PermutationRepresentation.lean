import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Inversion
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

* `Coxeter.permRep_simple`
* `Coxeter.permRep_wordProd`
* `Coxeter.permRep_inj`

## References

* [bjorner2005] A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*

-/

namespace Coxeter

open Function List CoxeterSystem CoxeterGroup

def ReflectionSet (W : Type*) [CoxeterGroup W] := setOf (CoxeterSystem.IsReflection (@cs W _))

def RootSet (W : Type*) [CoxeterGroup W] := @ReflectionSet W _ × ZMod 2

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

noncomputable section

open Classical in
def etaAux (i : B W) (t : W) : ZMod 2 := if cs.simple i = t then 1 else 0

@[simp]
theorem etaAux_conj (i : B W) (t : W) :
  etaAux i ((cs.simple i) * t * (cs.simple i)⁻¹) = etaAux i t := by
  unfold etaAux
  congr 1
  rw [inv_simple, right_eq_mul, eq_iff_iff, mul_eq_one_iff_eq_inv', inv_simple]
  tauto

theorem etaAux_conj' (i : B W) (t : W) :
  etaAux i (MulAut.conj (cs.simple i) t) = etaAux i t := by
  rw [MulAut.conj_apply]
  apply etaAux_conj

section lemmas

private def permRepAux (i : B W) : RootSet W → RootSet W
  | (⟨t, h⟩, ε) => (⟨MulAut.conj (cs.simple i) t, h.conj _⟩ , ε + etaAux i t)

open Classical in
private theorem permRepAux_involutive (i : B W) : Function.Involutive (permRepAux i) := by
  intro ⟨t, ε⟩
  rw [permRepAux, permRepAux]
  apply Prod.ext
  · simp [mul_assoc]
  · rw [etaAux_conj']
    grind

open Classical in
private theorem foldl_permRepAux (ω : List (B W)) (r : RootSet W) :
  foldl (fun x i => permRepAux i x) r ω
    = ⟨⟨MulAut.conj ((cs.wordProd ω)⁻¹) r.1, r.1.property.conj _⟩,
        r.2 + count r.1.val (cs.leftInvSeq ω)⟩ := by
  revert r
  induction ω with
  | nil => simp
  | cons a as ih =>
      intro ⟨t, ε⟩
      rw [cs.wordProd_cons, foldl_cons, ih, permRepAux, leftInvSeq, count_cons]
      apply Prod.ext
      · simp
      · dsimp only [beq_iff_eq]
        rw [add_assoc]
        nth_rw 4 [add_comm]
        simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
          beq_iff_eq, etaAux, count, countP_map]
        congr
        ext
        nth_rw 2 [←inv_simple]
        rw [comp_apply, beq_eq_beq, map_inv, MulAut.inv_apply, MulEquiv.symm_apply_eq]

private def permRepAux_equiv (i : B W) : Equiv.Perm (RootSet W) := {
  toFun := permRepAux i
  invFun := permRepAux i
  left_inv := permRepAux_involutive i
  right_inv := permRepAux_involutive i
}

private theorem odd_div_2 (n : ℕ) : (2 * n + 1) / 2 = n := by grind

open Classical in
private theorem permRepAux_liftable : (@M W).IsLiftable permRepAux_equiv := by
  intros i i'
  ext r
  have h (k : ℕ) : ((permRepAux_equiv i * permRepAux_equiv i') ^ k) r
    = foldl (fun x i => permRepAux i x) r (alternatingWord i' i (2 * k)) := by
    induction k with
    | zero =>
        unfold alternatingWord
        rfl
    | succ k ih =>
        conv =>
          congr
          · rw [add_comm, pow_add, pow_one, Equiv.Perm.coe_mul, Function.comp, ih]
          · simp only [mul_add, alternatingWord_succ, concat_eq_append, foldl_append]
        rfl
  rw [h, foldl_permRepAux, prod_alternatingWord_eq_mul_pow]
  simp only [even_two, Even.mul_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    mul_div_cancel_left₀, simple_mul_simple_pow', mul_one, inv_one, map_one, MulAut.one_apply,
    Subtype.coe_eta, Equiv.Perm.coe_one, id_eq]
  symm
  apply Prod.snd_eq_iff.mp
  let p := M.M i i'
  rw [left_eq_add, ZMod.natCast_eq_zero_iff,
    ←take_append_drop p (cs.leftInvSeq (alternatingWord i' i (2 * p))), count_append]
  suffices h2 : take p (cs.leftInvSeq (alternatingWord i' i (2 * p)))
    = drop p (cs.leftInvSeq (alternatingWord i' i (2 * p))) by
    rw [h2, ←two_mul]
    apply dvd_mul_right
  rw [ext_get_iff]
  simp only [length_take, length_drop, length_leftInvSeq, length_alternatingWord]
  constructor
  · grind
  · intro n h3 _
    rw [lt_inf_iff] at h3
    simp only [get_eq_getElem, getElem_take, getElem_drop]
    rw [getElem_leftInvSeq_alternatingWord, getElem_leftInvSeq_alternatingWord,
      prod_alternatingWord_eq_mul_pow, prod_alternatingWord_eq_mul_pow]
    · simp only [Nat.not_even_bit1, reduceIte, odd_div_2, pow_add,
        simple_mul_simple_pow, one_mul, p]
    · grind
    · exact h3.2

end lemmas

/-- Bjorner--Brenti Theorem 1.3.2(i): extension -/
def permRep (W : Type*) [CoxeterGroup W] : W →* Equiv.Perm (RootSet W) :=
  cs.lift ⟨permRepAux_equiv, permRepAux_liftable⟩

@[simp]
theorem permRep_simple (i : B W) (r : RootSet W) : permRep W (cs.simple i) r
  = (⟨MulAut.conj (cs.simple i) r.1, r.1.prop.conj _⟩ , r.2 + etaAux i r.1) := by
  unfold permRep
  rw [lift_apply_simple]
  rfl

theorem permRep_inv_simple (i : B W) (r : RootSet W) : permRep W ((cs.simple i)⁻¹) r
  = (⟨MulAut.conj ((cs.simple i)⁻¹) r.1, r.1.prop.conj _⟩ , r.2 + etaAux i r.1) := by simp

/-- Bjorner--Brenti Theorem 1.3.2(i): uniqueness -/
theorem permRep_ext {φ : W →* Equiv.Perm (RootSet W)}
  (h : ∀ (i : B W), φ (cs.simple i) = permRep W (cs.simple i)) : φ = permRep W := cs.ext_simple h

open Classical in
theorem permRep_inv_wordProd (ω : List (B W)) (r : RootSet W) :
  permRep W ((cs.wordProd ω)⁻¹) r
  = ⟨⟨MulAut.conj ((cs.wordProd ω)⁻¹) r.1, r.1.property.conj _⟩,
    r.2 + count r.1.val (cs.leftInvSeq ω)⟩ := by
  revert r
  induction ω with
  | nil => simp
  | cons i is ih =>
      intro ⟨⟨t, h⟩, ε⟩
      dsimp
      rw [wordProd_cons, mul_inv_rev, map_mul, Equiv.Perm.mul_apply, permRep_inv_simple, ih]
      apply Prod.ext
      · simp [mul_assoc]
      · rw [add_assoc, add_right_inj ε, leftInvSeq, count_cons, etaAux, add_comm]
        simp only [inv_simple, MulAut.conj_apply, beq_iff_eq, Nat.cast_add, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero, add_left_inj]
        unfold count
        rw [countP_map]
        congr
        ext x
        rw [comp_apply, MulAut.conj_apply, inv_simple, beq_eq_beq, ←mul_inv_eq_iff_eq_mul,
          ←inv_mul_eq_iff_eq_mul, mul_assoc, inv_simple]

open Classical in
theorem permRep_wordProd (ω : List (B W)) (r : RootSet W) :
  permRep W (cs.wordProd ω) r
  = ⟨⟨MulAut.conj (cs.wordProd ω) r.1, r.1.property.conj _⟩,
    r.2 + count r.1.val (cs.rightInvSeq ω)⟩ := by
  have h := permRep_inv_wordProd (ω.reverse) r
  rw [wordProd_reverse, inv_inv, leftInvSeq_reverse, count_reverse] at h
  exact h

open Classical in
/-- Bjorner--Brenti Theorem 1.3.2(i): injectivity -/
theorem permRep_inj : Function.Injective (@permRep W _) := by
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
      have h2 := permRep_inv_wordProd (i :: is) (⟨⟨cs.simple i, cs.isReflection_simple i⟩, 0⟩)
      have h3 : count (cs.simple i) (cs.leftInvSeq (i :: is)) = 1 := by
        apply count_eq_one_of_mem
        · apply IsReduced.nodup_leftInvSeq
          exact hω1.symm
        · apply Mem.head
      rw [hw, h3] at h2
      have : (0 : ZMod 2) = 1 := congr_arg Prod.snd h2
      contradiction

/-- Bjorner--Brenti Theorem 1.3.2(ii) -/
theorem permRep_reflection (t : ReflectionSet W) (ε : ZMod 2) :
  permRep W t.val ⟨t, ε⟩ = ⟨t, ε + 1⟩ := by
  revert t ε
  apply ReflectionSet.induction
  · simp [permRep_simple, etaAux]
  · intro t i ih ε
    rw [map_mul, Equiv.Perm.mul_apply, permRep_inv_simple]
    dsimp
    group
    rw [map_mul, Equiv.Perm.mul_apply, ih, permRep_simple]
    apply Prod.ext
    · simp
    · simp [-inv_simple]
      grind

open Classical in
def η (w t : W) : ZMod 2 :=
  count t (cs.leftInvSeq (choose (cs.wordProd_surjective w)))

theorem permRep_inv_eq (w : W) (r : RootSet W) : permRep W w⁻¹ r
  = ⟨⟨MulAut.conj w⁻¹ r.1, r.1.prop.conj _⟩, r.2 + η w r.1⟩ := by
  unfold η
  have h := Exists.choose_spec (cs.wordProd_surjective w)
  rw [←h, permRep_inv_wordProd]
  grind

theorem permRep_eq (w : W) (r : RootSet W) : permRep W w r
  = ⟨⟨MulAut.conj w r.1, r.1.prop.conj _⟩, r.2 + η w⁻¹ r.1⟩ := by
  have h := permRep_inv_eq w⁻¹ r
  rw [inv_inv] at h
  exact h

open Classical in
theorem eta_spec (ω : List (B W)) (t : W) :
  η (cs.wordProd ω) t = count t (cs.leftInvSeq ω) := by
  cases Classical.em (cs.IsReflection t) with
  | inl ht =>
      have h := permRep_inv_eq (cs.wordProd ω) ⟨⟨t, ht⟩, 0⟩
      rw [permRep_inv_wordProd] at h
      simp only [map_inv, MulAut.inv_apply, MulAut.conj_symm_apply, zero_add] at h
      exact (congr_arg Prod.snd h).symm
  | inr ht =>
      unfold η
      congr 1
      trans 0
      · rw [count_eq_zero]
        intro h
        apply ht
        exact cs.isReflection_of_mem_leftInvSeq _ h
      · symm
        rw [count_eq_zero]
        intro h
        apply ht
        exact cs.isReflection_of_mem_leftInvSeq _ h

open Classical in
theorem eta_eq_one (w t : W) (h : η w t = 1) :
  cs.length (t * w) < cs.length w := by
  let ⟨ω, ⟨hω1, hω2⟩⟩ := cs.exists_reduced_word w
  subst hω2
  rw [eta_spec] at h
  have h2 : 0 < count t (cs.leftInvSeq ω) := by
    rw [pos_iff_ne_zero]
    intro heq
    rw [heq] at h
    contradiction
  rw [count_pos_iff, mem_iff_get] at h2
  let ⟨i, hi⟩ := h2
  rw [←hi, ←getD_eq_get _ 1, getD_leftInvSeq_mul_wordProd]
  calc
    cs.length (cs.wordProd (ω.eraseIdx i.val))
      ≤ (ω.eraseIdx i.val).length := cs.length_wordProd_le _
    _ = ω.length - 1 := ?_
    _ < ω.length := ?_
    _ = cs.length (cs.wordProd ω) := hω1
  · apply length_eraseIdx_of_lt
    rw [←cs.length_leftInvSeq]
    exact i.prop
  · apply Nat.sub_one_lt
    intro h3
    rw [length_eq_zero_iff] at h3
    subst h3
    simp at h

theorem eta_eq_zero (w t : W) (ht : cs.IsReflection t) (h : η w t = 0) :
  cs.length (t * w) > cs.length w := by
  suffices h2 : cs.length (t * (t * w)) < cs.length (t * w) by
    rw [←mul_assoc, ht.mul_self, one_mul] at h2
    exact h2
  apply eta_eq_one
  have h2 := permRep_inv_eq (t * w) ⟨⟨t, ht⟩, 0⟩
  have h3 := permRep_reflection ⟨t, ht⟩ 0
  replace h2 : (((permRep W) (t * w)⁻¹) (⟨t, ht⟩, 0)).2 = 0 + η (t * w) t := congr_arg Prod.snd h2
  rw [zero_add, mul_inv_rev, map_mul, Equiv.Perm.coe_mul, comp_apply, ht.inv,
    permRep_inv_eq, h3, h, zero_add] at h2
  exact h2.symm

theorem eta_eq_one_iff (w t : W) (ht : cs.IsReflection t) :
  η w t = 1 ↔ cs.length (t * w) < cs.length w := by
  constructor
  · apply eta_eq_one
  · intro h
    by_contra h2
    replace h2 : η w t = 0 := by
      rw [Fin.ext_iff] at *
      grind
    have := eta_eq_zero w t ht h2
    grind

theorem eta_eq_zero_iff (w t : W) (ht : cs.IsReflection t) :
  η w t = 0 ↔ cs.length (t * w) > cs.length w := by
  constructor
  · apply eta_eq_zero
    exact ht
  · intro h
    by_contra h2
    replace h2 : η w t = 1 := by
      rw [Fin.ext_iff] at *
      grind
    have := eta_eq_one w t h2
    grind

end

end Coxeter
