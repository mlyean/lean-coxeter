import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Inversion

namespace CoxeterSystem

variable {B : Type*}
variable {W : Type*} [Group W] [hdeceq : DecidableEq W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

def T := setOf cs.IsReflection

def R := cs.T × ZMod 2

def η (i : B) (t : cs.T) : ZMod 2 := if cs.simple i = t.val then 1 else 0

def π (i : B) : cs.R → cs.R
  | (t, ε) => (⟨cs.simple i * t.val * cs.simple i, aux t⟩, ε + cs.η i t)
  where
    aux t :=  by
      nth_rw 2 [←cs.inv_simple i]
      exact CoxeterSystem.IsReflection.conj t.prop _

theorem pi_involution (i : B) : (cs.π i) ∘ (cs.π i) = id := by
  ext ⟨t, ε⟩
  simp only [Function.comp_apply, π, mul_assoc, simple_mul_simple_cancel_left,
    simple_mul_simple_self, mul_one, Subtype.coe_eta, id_eq]
  apply Prod.ext (Eq.refl t)
  match hdeceq (cs.simple i) t.val with
  | isTrue h =>
      simp only [η, h, t.prop.mul_self]
      grind
  | isFalse h =>
      have h2 : ¬ t.val * cs.simple i = 1 := by
        rw [mul_eq_one_iff_eq_inv, cs.inv_simple, Eq.comm]
        exact h
      simp [h, h2, η]

theorem pi_foldr (ω : List B) (r : cs.R) :
  List.foldr cs.π r ω
    = ⟨⟨MulAut.conj (cs.wordProd ω) r.1, r.1.property.conj _⟩,
        r.2 + List.count r.1.val (cs.rightInvSeq ω)⟩ := by
  revert r
  induction ω with
  | nil => simp
  | cons a as ih =>
      intro r
      rw [cs.wordProd_cons, List.foldr_cons, ih]
      apply Prod.ext
      · simp [π]
      · simp only [π, MulAut.conj_apply, rightInvSeq]
        rw [add_assoc, add_right_inj r.2, List.count_cons]
        simp only [η, beq_iff_eq, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
          add_right_inj]
        congr 1
        nth_rw 2 [Eq.comm]
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, inv_mul_eq_iff_eq_mul, eq_iff_iff, Eq.comm]

def π_equiv (i : B) : Equiv.Perm cs.R := {
  toFun := cs.π i
  invFun := cs.π i
  left_inv := congr_fun (cs.pi_involution i)
  right_inv := congr_fun (cs.pi_involution i)
}

@[simp]
def alternate : ℕ → B → B → List B
  | 0, _, _ => []
  | k + 1, i, i' => i :: i' :: alternate k i i'

theorem wordProd_alternate (k : ℕ) (i i' : B) :
  cs.wordProd (alternate k i i') = (cs.simple i * cs.simple i') ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [alternate, wordProd_cons]
      rw [add_comm, pow_add]
      simp [ih, mul_assoc]

theorem order_alternate (i i' : B) : (cs.wordProd (alternate (M.M i i') i i')) = 1 := by
  rw [wordProd_alternate]
  apply simple_mul_simple_pow

/-- Part of Bjorner--Brenti Theorem 1.3.2(i) -/
theorem pi_liftable : M.IsLiftable cs.π_equiv := by
  intros i i'
  ext r
  have h : ∀ (k : ℕ), ((cs.π_equiv i * cs.π_equiv i') ^ k) r
    = List.foldr cs.π r (alternate k i i') := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        simp only [alternate, List.foldr_cons]
        rw [add_comm, pow_add, pow_one, ←ih]
        rfl
  rw [h, pi_foldr, order_alternate]
  simp only [map_one, MulAut.one_apply, Subtype.coe_eta, Equiv.Perm.coe_one, id_eq]
  apply Prod.ext
  · rfl
  · rw [add_eq_left, ZMod.natCast_eq_zero_iff]
    sorry

end CoxeterSystem
