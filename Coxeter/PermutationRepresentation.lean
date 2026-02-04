import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Inversion

namespace CoxeterSystem

open Function List

variable {B : Type*}
variable {W : Type*} [Group W] [hdeceq : DecidableEq W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

def T := setOf cs.IsReflection

def R := cs.T × ZMod 2

def η (i : B) (t : cs.T) : ZMod 2 := if cs.simple i = t.val then 1 else 0

def π (i : B) : cs.R → cs.R
  | (t, ε) => (⟨cs.simple i * t.val * cs.simple i,
                  by nth_rw 2 [←cs.inv_simple i]; apply t.prop.conj⟩
                , ε + cs.η i t)

theorem pi_involution (i : B) : (cs.π i) ∘ (cs.π i) = id := by
  ext ⟨t, ε⟩
  simp only [comp_apply, π, mul_assoc, simple_mul_simple_cancel_left,
    simple_mul_simple_self, mul_one, Subtype.coe_eta, id_eq]
  apply Prod.ext (Eq.refl t)
  match hdeceq (cs.simple i) t.val with
  | isTrue h =>
      simp only [η, h, t.prop.mul_self, mul_one]
      grind
  | isFalse h =>
      have h2 : ¬ t.val * cs.simple i = 1 := by
        rw [mul_eq_one_iff_eq_inv, cs.inv_simple, Eq.comm]
        exact h
      simp only [η, h, ↓reduceIte, add_zero, left_eq_mul, h2]

/- Unused lemma -/
theorem pi_foldr (ω : List B) (r : cs.R) :
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

theorem pi_foldl (ω : List B) (r : cs.R) :
  foldl (fun x i => cs.π i x) r ω
    = ⟨⟨MulAut.conj ((cs.wordProd ω)⁻¹) r.1, r.1.property.conj _⟩,
        r.2 + count r.1.val (cs.leftInvSeq ω)⟩ := by
  revert r
  induction ω with
  | nil => simp
  | cons a as ih =>
      intro ⟨t, ε⟩
      rw [cs.wordProd_cons, foldl_cons, ih]
      apply Prod.ext
      · simp [π]
      · simp only [π]
        rw [leftInvSeq, count_cons, η, add_assoc, add_right_inj ε]
        nth_rw 2 [add_comm]
        simp only [beq_iff_eq, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
          add_right_inj]
        congr 1
        unfold count
        rw [countP_map]
        congr
        funext w
        simp only [comp_apply, MulAut.conj_apply, inv_simple, beq_eq_beq]
        rw [←mul_inv_eq_iff_eq_mul, ←inv_mul_eq_iff_eq_mul, mul_assoc]
        simp only [inv_simple]

def π_equiv (i : B) : Equiv.Perm cs.R := {
  toFun := cs.π i
  invFun := cs.π i
  left_inv := congr_fun (cs.pi_involution i)
  right_inv := congr_fun (cs.pi_involution i)
}

theorem odd_div_2 (n : ℕ) : (2 * n + 1) / 2 = n := by grind

/-- Part of Bjorner--Brenti Theorem 1.3.2(i) -/
theorem pi_liftable : M.IsLiftable cs.π_equiv := by
  intros i i'
  ext r
  have h : ∀ (k : ℕ), ((cs.π_equiv i * cs.π_equiv i') ^ k) r
    = foldl (fun x i => cs.π i x) r (alternatingWord i' i (2 * k)) := by
    intro k
    induction k with
    | zero =>
        unfold alternatingWord;
        rfl
    | succ k ih =>
        rw [mul_add, alternatingWord_succ, alternatingWord_succ]
        rw [add_comm, pow_add]
        simp only [pow_one, Equiv.Perm.coe_mul, comp_apply, concat_eq_append,
          append_assoc, cons_append, nil_append, foldl_append, foldl_cons,
          foldl_nil]
        rw [ih]
        simp only [π_equiv, Equiv.coe_fn_mk]
  rw [h, pi_foldl, prod_alternatingWord_eq_mul_pow]
  simp only [even_two, Even.mul_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    mul_div_cancel_left₀, simple_mul_simple_pow', mul_one, inv_one, map_one, MulAut.one_apply,
    Subtype.coe_eta, Equiv.Perm.coe_one, id_eq]
  apply Prod.ext
  · rfl
  · rw [add_eq_left, ZMod.natCast_eq_zero_iff]
    let p := M.M i i'
    have h1 : ∀ (j : ℕ) (hj : j < p),
      (cs.leftInvSeq (alternatingWord i' i (2 * p)))[j]'
      (by rw [length_leftInvSeq, length_alternatingWord]; grind)
      = (cs.leftInvSeq (alternatingWord i' i (2 * p)))[p + j]'
      (by rw [length_leftInvSeq, length_alternatingWord]; grind) := by
      intro j hj
      rw [getElem_leftInvSeq_alternatingWord, getElem_leftInvSeq_alternatingWord,
        prod_alternatingWord_eq_mul_pow, prod_alternatingWord_eq_mul_pow]
      · simp only [Nat.not_even_bit1, ↓reduceIte, odd_div_2, mul_right_inj]
        rw [pow_add]
        simp [p]
      · grind
      · grind
    have h2 : take p (cs.leftInvSeq (alternatingWord i' i (2 * p)))
      = drop p (cs.leftInvSeq (alternatingWord i' i (2 * p))) := by
      rw [ext_get_iff]
      apply And.intro
      · simp only [length_take, length_leftInvSeq, length_alternatingWord, length_drop,
          two_mul]
        rw [min_eq_left]
        · rw [Nat.add_sub_self_right]
        · apply Nat.le_add_left
      · intro n h3 _
        have h4 : (take p (cs.leftInvSeq (alternatingWord i' i (2 * p)))).length = p := by
          rw [length_take, length_leftInvSeq, length_alternatingWord, min_eq_left_iff, two_mul]
          apply Nat.le_add_left
        simp only [get_eq_getElem, getElem_take, getElem_drop]
        apply h1
        rw [←h4]
        exact h3
    rw [←take_append_drop p (cs.leftInvSeq (alternatingWord i' i (2 * p))),
      count_append, h2, ←two_mul]
    apply dvd_mul_right

def π_lift : W →* Equiv.Perm cs.R := cs.lift.toFun ⟨cs.π_equiv, cs.pi_liftable⟩

end CoxeterSystem
