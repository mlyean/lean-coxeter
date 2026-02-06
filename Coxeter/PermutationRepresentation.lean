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
  (hs : ∀ (i : B), P (⟨cs.simple i, cs.isReflection_simple i⟩))
  (hind : ∀ (t : cs.T) (i : B),
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
      · apply hs i
      · congr
        rw [wordProd_nil, one_mul, inv_one, mul_one]
  | cons j js ih =>
      simp only [wordProd_cons, mul_inv_rev, inv_simple]
      rw [congr_arg P]
      · apply hind ⟨cs.wordProd js * cs.simple i * (cs.wordProd js)⁻¹,
          (cs.isReflection_simple i).conj _⟩ j
        exact ih
      · simp only [inv_simple, Subtype.mk.injEq]
        group

def R := cs.T × ZMod 2

open Classical in
noncomputable def η (i : B) (t : cs.T) : ZMod 2 := if cs.simple i = t.val then 1 else 0

noncomputable def π (i : B) : cs.R → cs.R
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

noncomputable def π_equiv (i : B) : Equiv.Perm cs.R := {
  toFun := cs.π i
  invFun := cs.π i
  left_inv := congr_fun (cs.pi_involution i)
  right_inv := congr_fun (cs.pi_involution i)
}

private theorem odd_div_2 (n : ℕ) : (2 * n + 1) / 2 = n := by grind

open Classical in
/-- Bjorner--Brenti Theorem 1.3.2(i): extension -/
theorem pi_liftable : M.IsLiftable cs.π_equiv := by
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

noncomputable def π_lift : W →* Equiv.Perm cs.R := cs.lift ⟨cs.π_equiv, cs.pi_liftable⟩

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
        comp_apply, π_lift, cs.lift_apply_simple, π_equiv]
      rfl

open Classical in
/-- Bjorner--Brenti Theorem 1.3.2(i): injectivity -/
theorem pi_inj : Function.Injective cs.π_lift := by
  rw [injective_iff_map_eq_one]
  intro w hw
  let ⟨ω, ⟨hω1, hω2⟩⟩ := cs.exists_reduced_word (w⁻¹)
  rw [inv_eq_iff_eq_inv] at hω2
  subst hω2
  rw [inv_inv] at hω1
  rw [inv_eq_one, ←cs.length_eq_zero_iff, ←hω1]
  apply Classical.by_contradiction
  intro h
  cases ω with
  | nil => contradiction
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
theorem pi_reflection (t : cs.T) (ε : ZMod 2) : cs.π_lift t ⟨t, ε⟩ = ⟨t, ε + 1⟩ := by
  revert t ε
  apply T.ind
  · simp [π_lift, π_equiv, π, η]
  · intro t i ih ε
    simp only [inv_simple, map_mul, Equiv.Perm.coe_mul, pi_lift_simple, comp_apply]
    conv in cs.π i (⟨cs.simple i * ↑t * cs.simple i, _⟩, ε) =>
      unfold π
      simp [mul_assoc]
    rw [ih]
    simp only [π]
    congr 1
    have h : cs.η i ⟨cs.simple i * (↑t * cs.simple i),
      by rw [←mul_assoc]; nth_rw 2 [←inv_simple]; exact (t.prop.conj _)⟩
      = cs.η i t := by
      unfold η
      congr 1
      simp only [left_eq_mul, eq_iff_iff]
      rw [mul_eq_one_iff_eq_inv, Eq.comm, inv_simple]
    rw [h]
    grind

end CoxeterSystem
