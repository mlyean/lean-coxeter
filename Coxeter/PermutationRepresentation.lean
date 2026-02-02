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

def π_equiv (i : B) : Equiv.Perm cs.R := {
  toFun := cs.π i
  invFun := cs.π i
  left_inv := congr_fun (cs.pi_involution i)
  right_inv := congr_fun (cs.pi_involution i)
}

/-- Bjorner--Brenti Theorem 1.3.2(i) -/
theorem pi_liftable : M.IsLiftable cs.π_equiv := by
  intros i i'
  sorry

end CoxeterSystem
