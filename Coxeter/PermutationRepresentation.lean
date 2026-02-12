import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Inversion

namespace CoxeterSystem

open Function List

variable {B : Type*}
variable {W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

def T := setOf cs.IsReflection

/-- Induction principle for reflections -/
theorem T.ind {P : cs.T → Prop}
  (sh : ∀ (i : B), P (⟨cs.simple i, cs.isReflection_simple i⟩))
  (ih : ∀ (t : cs.T) (i : B),
    P t → P (⟨(cs.simple i) * t.val * (cs.simple i)⁻¹, t.prop.conj (cs.simple i)⟩)) :
  ∀ (t : cs.T), P t := by
  intro t
  let ⟨w, ⟨i, hi⟩⟩ := t.prop
  let ⟨ω, hω⟩ := cs.wordProd_surjective w
  replace hi : t = ⟨w * cs.simple i * w⁻¹, (cs.isReflection_simple i).conj _⟩ := by
    ext
    exact hi
  subst hi hω
  induction ω with
  | nil =>
      rw [congr_arg P]
      · apply sh i
      · congr
        rw [wordProd_nil, one_mul, inv_one, mul_one]
  | cons j js ih2 =>
      simp only [wordProd_cons, mul_inv_rev, inv_simple]
      rw [congr_arg P]
      · exact ih ⟨cs.wordProd js * cs.simple i * (cs.wordProd js)⁻¹,
          (cs.isReflection_simple i).conj _⟩ j ih2
      · simp only [inv_simple, Subtype.mk.injEq]
        group

def R := cs.T × ZMod 2

noncomputable section

open Classical in
def η (i : B) (t : cs.T) : ZMod 2 := if cs.simple i = t.val then 1 else 0

def π (i : B) : cs.R → cs.R
  | (t, ε) => (⟨cs.simple i * t.val * cs.simple i,
                  by nth_rw 2 [←cs.inv_simple i]; apply t.prop.conj⟩
                , ε + cs.η i t)

open Classical in
theorem pi_involution (i : B) : (cs.π i) ∘ (cs.π i) = id := by
  ext ⟨t, ε⟩
  simp only [comp_apply, π, mul_assoc, simple_mul_simple_cancel_left,
    simple_mul_simple_self, mul_one, Subtype.coe_eta, id_eq]
  rw [←Prod.snd_eq_iff]
  cases decEq (cs.simple i) t.val with
  | isTrue h =>
      simp only [η, h, t.prop.mul_self, mul_one]
      grind
  | isFalse h =>
      simp only [η, h, ↓reduceIte, add_zero, left_eq_mul, add_eq_left, ite_eq_right_iff,
        one_ne_zero, imp_false]
      rw [mul_eq_one_iff_eq_inv, cs.inv_simple, Eq.comm]
      exact h

/- Unused lemma -/
open Classical in
theorem foldr_pi (ω : List B) (r : cs.R) :
  foldr cs.π r ω
    = ⟨⟨MulAut.conj (cs.wordProd ω) r.1, r.1.property.conj _⟩,
        r.2 + count r.1.val (cs.rightInvSeq ω)⟩ := by
  revert r
  induction ω with
  | nil => simp
  | cons a as ih =>
      intro r
      rw [cs.wordProd_cons, foldr_cons, ih]
      apply Prod.ext
      · simp [π]
      · simp only [π, MulAut.conj_apply, rightInvSeq]
        rw [add_assoc, add_right_inj r.2, count_cons]
        simp only [η, beq_iff_eq, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
          add_right_inj]
        congr 1
        nth_rw 2 [Eq.comm]
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, inv_mul_eq_iff_eq_mul, eq_iff_iff, Eq.comm]

open Classical in
theorem foldl_pi (ω : List B) (r : cs.R) :
  foldl (fun x i => cs.π i x) r ω
    = ⟨⟨MulAut.conj ((cs.wordProd ω)⁻¹) r.1, r.1.property.conj _⟩,
        r.2 + count r.1.val (cs.leftInvSeq ω)⟩ := by
  revert r
  induction ω with
  | nil => simp
  | cons a as ih =>
      intro ⟨t, ε⟩
      rw [cs.wordProd_cons, foldl_cons, ih]
      simp only [map_inv, π, MulAut.inv_apply, MulAut.conj_symm_apply, mul_inv_rev, inv_simple,
        map_mul, MulAut.mul_apply, MulAut.conj_apply]
      rw [←Prod.snd_eq_iff, leftInvSeq, count_cons, η, add_assoc, add_right_inj ε]
      nth_rw 2 [add_comm]
      simp only [beq_iff_eq, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        add_right_inj]
      congr 1
      unfold count
      rw [countP_map]
      apply countP_congr
      intro w _
      simp only [beq_iff_eq, comp_apply, MulAut.conj_apply, inv_simple]
      rw [←mul_inv_eq_iff_eq_mul, ←inv_mul_eq_iff_eq_mul, mul_assoc, inv_simple]

def π_equiv (i : B) : Equiv.Perm cs.R := {
  toFun := cs.π i
  invFun := cs.π i
  left_inv := congr_fun (cs.pi_involution i)
  right_inv := congr_fun (cs.pi_involution i)
}

private theorem odd_div_2 (n : ℕ) : (2 * n + 1) / 2 = n := by grind

open Classical in
private theorem pi_liftable : M.IsLiftable cs.π_equiv := by
  intros i i'
  ext r
  have h (k : ℕ) : ((cs.π_equiv i * cs.π_equiv i') ^ k) r
    = foldl (fun x i => cs.π i x) r (alternatingWord i' i (2 * k)) := by
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
  rw [h, foldl_pi, prod_alternatingWord_eq_mul_pow]
  simp only [even_two, Even.mul_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    mul_div_cancel_left₀, simple_mul_simple_pow', mul_one, inv_one, map_one, MulAut.one_apply,
    Subtype.coe_eta, Equiv.Perm.coe_one, id_eq]
  rw [Eq.comm, ←Prod.snd_eq_iff, Eq.comm]
  let p := M.M i i'
  rw [add_eq_left, ZMod.natCast_eq_zero_iff,
    ←take_append_drop p (cs.leftInvSeq (alternatingWord i' i (2 * p))), count_append]
  suffices h2 : take p (cs.leftInvSeq (alternatingWord i' i (2 * p)))
    = drop p (cs.leftInvSeq (alternatingWord i' i (2 * p))) by
    rw [h2, ←two_mul]
    apply dvd_mul_right
  rw [ext_get_iff]
  constructor
  · simp only [length_take, length_leftInvSeq, length_alternatingWord, length_drop,
      two_mul]
    grind
  · intro n h3 _
    simp only [length_take, length_leftInvSeq, length_alternatingWord, lt_inf_iff] at h3
    simp only [get_eq_getElem, getElem_take, getElem_drop]
    rw [getElem_leftInvSeq_alternatingWord, getElem_leftInvSeq_alternatingWord,
      prod_alternatingWord_eq_mul_pow, prod_alternatingWord_eq_mul_pow]
    · simp only [Nat.not_even_bit1, ↓reduceIte, odd_div_2, pow_add,
        simple_mul_simple_pow, one_mul, p]
    · grind
    · grind

/-- Bjorner--Brenti Theorem 1.3.2(i): extension -/
def π_lift : W →* Equiv.Perm cs.R := cs.lift ⟨cs.π_equiv, cs.pi_liftable⟩

@[simp]
theorem pi_lift_simple (i : B) : cs.π_lift (cs.simple i) = cs.π i := by
  ext
  simp [π_lift, π_equiv]

/-- Bjorner--Brenti Theorem 1.3.2(i): uniqueness -/
theorem pi_lift_ext {φ : W →* Equiv.Perm cs.R}
  (h : ∀ (i : B), φ (cs.simple i) = cs.π_lift (cs.simple i)) : φ = cs.π_lift := cs.ext_simple h

theorem pi_lift_wordProd (ω : List B) (r : cs.R) :
  cs.π_lift ((cs.wordProd ω)⁻¹) r = foldl (fun x i => cs.π i x) r ω := by
  revert r
  induction ω with
  | nil => simp
  | cons i is ih =>
      intro r
      rw [wordProd_cons, foldl, ←ih, mul_inv_rev, map_mul, Equiv.Perm.coe_mul, inv_simple,
        comp_apply, pi_lift_simple]

open Classical in
/-- Bjorner--Brenti Theorem 1.3.2(i): injectivity -/
theorem pi_lift_inj : Function.Injective cs.π_lift := by
  rw [injective_iff_map_eq_one]
  intro w hw
  let ⟨ω, ⟨hω1, hω2⟩⟩ := cs.exists_reduced_word (w⁻¹)
  rw [inv_eq_iff_eq_inv] at hω2
  subst hω2
  rw [inv_inv] at hω1
  rw [inv_eq_one, ←cs.length_eq_zero_iff, ←hω1]
  cases ω with
  | nil => rfl
  | cons i is =>
      have h2 := cs.pi_lift_wordProd (i :: is) (⟨⟨cs.simple i, cs.isReflection_simple i⟩, 0⟩)
      rw [hw, foldl_pi] at h2
      simp only [Equiv.Perm.coe_one, id_eq, map_inv, MulAut.inv_apply, MulAut.conj_symm_apply,
        zero_add] at h2
      have h3 : count (cs.simple i) (cs.leftInvSeq (i :: is)) = 1 := by
        apply count_eq_one_of_mem
        · apply IsReduced.nodup_leftInvSeq
          exact hω1.symm
        · apply Mem.head
      rw [h3] at h2
      have : (0 : ZMod 2) = 1 := congr_arg Prod.snd h2
      contradiction

/-- Bjorner--Brenti Theorem 1.3.2(ii) -/
theorem pi_lift_reflection (t : cs.T) (ε : ZMod 2) : cs.π_lift t ⟨t, ε⟩ = ⟨t, ε + 1⟩ := by
  revert t ε
  apply T.ind
  · simp [pi_lift_simple, π, η]
  · intro t i ih ε
    simp only [inv_simple, map_mul, Equiv.Perm.coe_mul, pi_lift_simple, comp_apply]
    conv in cs.π i (⟨cs.simple i * ↑t * cs.simple i, _⟩, ε) =>
      unfold π
      simp [mul_assoc]
    rw [ih]
    simp only [π]
    congr 1
    conv in cs.η i ⟨cs.simple i * (↑t * cs.simple i), _⟩ =>
      unfold η
      rw [left_eq_mul, mul_eq_one_iff_eq_inv, inv_simple, Eq.comm]
      change cs.η i t
    grind

open Classical in
def η2 (w : W) (t : cs.T) : ZMod 2 :=
  count t.val (cs.leftInvSeq (choose (cs.wordProd_surjective w)))

theorem pi_lift_eq' (w : W) (r : cs.R) : cs.π_lift w⁻¹ r
  = ⟨⟨MulAut.conj w⁻¹ r.1, r.1.prop.conj _⟩, r.2 + cs.η2 w r.1⟩ := by
  unfold η2
  have h := Exists.choose_spec (cs.wordProd_surjective w)
  rw [←h, pi_lift_wordProd, foldl_pi]
  grind

theorem pi_lift_eq (w : W) (r : cs.R) : cs.π_lift w r
  = ⟨⟨MulAut.conj w r.1, r.1.prop.conj _⟩, r.2 + cs.η2 w⁻¹ r.1⟩ := by
  have h := cs.pi_lift_eq' w⁻¹ r
  rw [inv_inv] at h
  exact h

open Classical in
theorem eta2_spec (ω : List B) (t : cs.T) :
  cs.η2 (cs.wordProd ω) t = count t.val (cs.leftInvSeq ω) := by
  have h := cs.pi_lift_eq' (cs.wordProd ω) ⟨t, 0⟩
  rw [pi_lift_wordProd, foldl_pi] at h
  simp only [map_inv, MulAut.inv_apply, MulAut.conj_symm_apply, zero_add] at h
  exact (congr_arg Prod.snd h).symm

open Classical in
theorem eta2_eq_one (w : W) (t : cs.T) (h : cs.η2 w t = 1) : cs.length (t * w) < cs.length w := by
  let ⟨ω, ⟨hω1, hω2⟩⟩ := cs.exists_reduced_word w
  subst hω2
  rw [eta2_spec] at h
  have h2 : 0 < count t.val (cs.leftInvSeq ω) := by
    rw [pos_iff_ne_zero]
    intro heq
    rw [heq] at h
    contradiction
  rw [count_pos_iff, mem_iff_get] at h2
  let ⟨i, hi⟩ := h2
  rw [←hi, ←getD_eq_get _ 1, getD_leftInvSeq_mul_wordProd]
  calc
    cs.length (cs.wordProd (ω.eraseIdx i.val))
      ≤ (ω.eraseIdx i.val).length := by apply length_wordProd_le
    _ = ω.length - 1 := ?_
    _ < ω.length := ?_
    _ = cs.length (cs.wordProd ω) := hω1
  · apply length_eraseIdx_of_lt
    rw [←cs.length_leftInvSeq]
    exact i.prop
  · apply Nat.sub_one_lt
    simp only [ne_eq, List.length_eq_zero_iff]
    intro h3
    subst h3
    simp at h

theorem eta2_eq_zero (w : W) (t : cs.T) (h : cs.η2 w t = 0) : cs.length (t * w) > cs.length w := by
  suffices h2 : cs.length (t * (t * w)) < cs.length (t * w) by
    rw [←mul_assoc, t.prop.mul_self, one_mul] at h2
    exact h2
  apply eta2_eq_one
  have h2 := cs.pi_lift_eq' (t * w) ⟨t, 0⟩
  rw [mul_inv_rev, map_mul, Equiv.Perm.coe_mul, comp_apply, t.prop.inv,
    pi_lift_eq', pi_lift_reflection, h] at h2
  simp only [map_inv, MulAut.inv_apply, MulAut.conj_symm_apply, zero_add, add_zero, map_mul,
    MulAut.mul_apply, MulAut.conj_apply, mul_inv_cancel_right] at h2
  exact (congr_arg Prod.snd h2).symm

private theorem zmod2_eq_one_iff (n : ZMod 2) : n = 1 ↔ ¬ n = 0 := by
  rw [Fin.ext_iff, Fin.ext_iff]
  grind

theorem eta2_eq_one_iff (w : W) (t : cs.T) : cs.η2 w t = 1 ↔ cs.length (t * w) < cs.length w := by
  constructor
  · apply eta2_eq_one
  · intro h
    rw [zmod2_eq_one_iff]
    intro h2
    have := cs.eta2_eq_zero w t h2
    grind

open Classical in
/-- Bjorner--Brenti Corollary 1.4.4 (a) implies (c) -/
theorem mem_leftInvSeq_of_isLeftInversion
  {ω : List B} {t : W} (ht : cs.IsReflection t) (h : cs.IsLeftInversion (cs.wordProd ω) t) :
  t ∈ cs.leftInvSeq ω := by
  have hrw := cs.eta2_eq_one_iff (cs.wordProd ω) ⟨t, ht⟩
  dsimp at hrw
  rw [IsLeftInversion, ←hrw, eta2_spec] at h
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

end

end CoxeterSystem
