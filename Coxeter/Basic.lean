module

public import Mathlib.GroupTheory.Coxeter.Inversion

/-!
# Coxeter groups

We build upon the the theory of Coxeter systems currently available in `mathlib`.

## Main definitions

* `Coxeter.CoxeterGroup`
* `Coxeter.ReducedWord`
-/

@[expose] public section

namespace Coxeter

class CoxeterGroup (W : Type*) extends Group W where
  B : Type*
  M : CoxeterMatrix B
  cs : CoxeterSystem M W

end Coxeter

namespace List

variable {α : Type*}

theorem drop_eraseIdx (l : List α) (i j : ℕ) :
  (drop i l).eraseIdx j = drop i (l.eraseIdx (i + j)) := by
  revert l
  induction i with
  | zero => simp
  | succ i ih =>
      intro l
      cases l with
      | nil => simp
      | cons =>
          rw [add_right_comm]
          apply ih

theorem reverse_eraseIdx {l : List α} {i : ℕ} (hi : i < l.length) :
  l.reverse.eraseIdx i = (l.eraseIdx (l.length - i - 1)).reverse := by
  rw [←Nat.sub_ne_zero_iff_lt] at hi
  rw [eraseIdx_eq_take_drop_succ, eraseIdx_eq_take_drop_succ, take_reverse, drop_reverse,
    ←reverse_append, Nat.sub_one_add_one hi, Nat.sub_add_eq]

end List

namespace Coxeter

open List CoxeterSystem CoxeterGroup

variable {W : Type*} [CoxeterGroup W]

section

@[simp]
theorem isReduced_nil : cs.IsReduced ([] : List (B W)) := by
  unfold CoxeterSystem.IsReduced
  rw [wordProd_nil, length_one, length_nil]

@[simp]
theorem isReduced_singleton (i : B W) : cs.IsReduced [i] := by
  unfold CoxeterSystem.IsReduced
  rw [wordProd_singleton, length_simple, length_cons, length_nil, zero_add]

theorem isReduced_cons {ω : List (B W)} (hω : cs.IsReduced ω) (i : B W) :
  cs.IsReduced (i :: ω) ↔ ¬ cs.IsLeftDescent (cs.wordProd ω) i := by
  unfold CoxeterSystem.IsReduced
  rw [not_isLeftDescent_iff, wordProd_cons, length_cons, hω]

theorem not_isReduced_cons {ω : List (B W)} (hω : cs.IsReduced ω) (i : B W) :
  ¬ cs.IsReduced (i :: ω) ↔ cs.IsLeftDescent (cs.wordProd ω) i :=
  Iff.not_left (isReduced_cons hω i)

theorem isReduced_of_append_left {μ ω : List (B W)} (h : cs.IsReduced (μ ++ ω)) : cs.IsReduced μ :=
  take_left.subst (h.take (μ.length))

theorem isReduced_of_append_right {μ ω : List (B W)} (h : cs.IsReduced (μ ++ ω)) : cs.IsReduced ω :=
  drop_left.subst (h.drop (μ.length))

theorem tail_leftInvSeq (i : B W) (ω : List (B W)) :
  tail (cs.leftInvSeq (i :: ω)) = map (MulAut.conj (cs.simple i)) (cs.leftInvSeq ω) := rfl

theorem leftInvSeq_append (μ ω : List (B W)) :
  cs.leftInvSeq (μ ++ ω)
  = cs.leftInvSeq μ ++ map (MulAut.conj (cs.wordProd μ)) (cs.leftInvSeq ω) := by
  induction μ with
  | nil => simp
  | cons i μ ih =>
      simp [leftInvSeq, ih, wordProd_cons]

theorem tail_alternatingWord (i j : (B W)) (p : ℕ) :
  tail (alternatingWord i j (p + 1)) = alternatingWord i j p := by
  rw [alternatingWord_succ']
  rfl

theorem drop_alternatingWord (i j : (B W)) (p q : ℕ) :
  drop p (alternatingWord i j (p + q)) = alternatingWord i j q := by
  revert q
  induction p with
  | zero => simp
  | succ p ih =>
      intro q
      rw [←tail_drop, add_assoc]
      nth_rw 2 [add_comm]
      rw [ih (q + 1)]
      apply tail_alternatingWord

theorem alternatingWord_even_add (i i' : B W) (k m : ℕ) :
  alternatingWord i i' (2 * k + m) = alternatingWord i i' m ++ alternatingWord i i' (2 * k) := by
  revert i i'
  induction m with
  | zero => simp [alternatingWord]
  | succ n ih =>
      intro i i'
      rw [←add_assoc, alternatingWord_succ, alternatingWord_succ, ih]
      simp only [concat_eq_append, append_assoc, cons_append, nil_append, append_cancel_left_eq]
      rw [←concat_eq_append, ←alternatingWord_succ, alternatingWord_succ']
      simp

theorem reverse_alternatingWord (i i' : B W) (k : ℕ) :
  (alternatingWord i i' (2 * k)).reverse = alternatingWord i' i (2 * k) := by
  induction k with
  | zero =>
      simp [alternatingWord]
  | succ k ih =>
      simp only [alternatingWord, Nat.mul_eq, concat_eq_append, append_assoc, cons_append,
        nil_append, reverse_append, reverse_cons, reverse_nil]
      rw [ih]
      trans alternatingWord i' i (2 * k + 2)
      · rw [alternatingWord_succ', alternatingWord_succ']
        simp
      · simp [alternatingWord]

@[simp]
theorem simple_ne_one (i : B W) : cs.simple i ≠ 1 := by
  apply_fun cs.length
  simp

theorem not_isLeftInversion_one (t : W) : ¬ cs.IsLeftInversion 1 t := by
  intro ⟨_, h⟩
  rw [length_one] at h
  exact Nat.not_lt_zero _ h

theorem not_isRightInversion_one (t : W) : ¬ cs.IsRightInversion 1 t := by
  intro ⟨_, h⟩
  rw [length_one] at h
  exact Nat.not_lt_zero _ h

end

section

/-! ### Reduced words -/

def ReducedWord (w : W) := {ω : List (B W) // cs.IsReduced ω ∧ w = cs.wordProd ω}

instance {w : W} : CoeOut (ReducedWord w) (List (B W)) where
  coe := Subtype.val

instance {w : W} : Nonempty (ReducedWord w) :=
  ⟨(Classical.indefiniteDescription _ (cs.exists_isReduced w))⟩

namespace ReducedWord

@[simp]
def reverse {w : W} (ω : ReducedWord w) : ReducedWord w⁻¹ :=
  ⟨ω.val.reverse, ω.prop.1.reverse, (congr_arg Inv.inv ω.prop.2).trans (cs.wordProd_reverse _).symm⟩

theorem length_eq {w : W} (ω : ReducedWord w) : ω.val.length = cs.length w := by
  rw [←ω.2.1, ←ω.2.2]

theorem wordProd_eq {w : W} (ω : ReducedWord w) : cs.wordProd ω = w := ω.2.2.symm

end ReducedWord

end

section opposite

/-! ### Opposite group -/

open MulOpposite

def cs_op : CoxeterSystem (@M W _) Wᵐᵒᵖ where
  mulEquiv := MulEquiv.trans (MulEquiv.inv' W).symm cs.mulEquiv

instance : CoxeterGroup Wᵐᵒᵖ where
  B := B W
  M := M
  cs := cs_op

theorem simple_op (i : B W) : (@cs Wᵐᵒᵖ).simple i = op (cs.simple i) := by
  change (op (cs.simple i))⁻¹ = op (cs.simple i)
  rw [←op_inv, inv_simple]

theorem wordProd_op (ω : List (B W)) :
  (@cs Wᵐᵒᵖ).wordProd ω = op (cs.wordProd ω.reverse) := by
  induction ω with
  | nil => rfl
  | cons i is hi =>
      rw [wordProd_cons, reverse_cons, wordProd_append, op_mul, hi, wordProd_singleton, simple_op]

theorem length_op (w : W) : cs.length (op w) = cs.length w := by
  apply eq_of_le_of_ge
  · have ⟨ω, hω1, hω2⟩ := cs.exists_isReduced w
    rw [hω2, hω1]
    nth_rw 1 [←reverse_reverse ω, ←wordProd_op, ←length_reverse]
    apply cs.length_wordProd_le
  · have ⟨ω, hω1, hω2⟩ := cs.exists_isReduced (op w)
    rw [hω2, hω1]
    rw [wordProd_op, op_inj] at hω2
    rw [hω2, wordProd_reverse, length_inv]
    apply cs.length_wordProd_le

theorem isLeftDescent_op_iff (w : W) (i : B W) :
  cs.IsLeftDescent (op w) i ↔ cs.IsRightDescent w i := by
  unfold IsLeftDescent IsRightDescent
  rw [simple_op, ←op_mul, length_op, length_op]

theorem isReflection_op_iff (t : W) :
  cs.IsReflection (op t) ↔ cs.IsReflection t := by
  unfold IsReflection
  constructor
  · intro ⟨w, i, hi⟩
    cases w with
    | h w =>
        rw [simple_op, ←op_inv, ←op_mul, ←op_mul, ←mul_assoc, op_inj] at hi
        exists w⁻¹, i
        rw [inv_inv]
        exact hi
  · intro ⟨w, i, hi⟩
    exists op w⁻¹, i
    rw [simple_op, ←op_inv, ←op_mul, ←op_mul, inv_inv, ←mul_assoc, hi]

theorem isLeftInversion_op_iff (w t : W) :
  cs.IsLeftInversion (op w) (op t) ↔ cs.IsRightInversion w t := by
  unfold IsLeftInversion IsRightInversion
  rw [isReflection_op_iff, ←op_mul, length_op, length_op]

theorem leftInvSeq_op (ω : List (B W)) : (@cs Wᵐᵒᵖ).leftInvSeq ω = map op (cs.leftInvSeq ω) := by
  induction ω with
  | nil => rfl
  | cons i is ih =>
      dsimp [leftInvSeq]
      rw [ih, simple_op, map_map, map_map]
      congr 2
      ext w
      dsimp
      rw [←op_inv, ←op_mul, ←op_mul, ←op_mul, ←op_mul, op_inj, ←mul_assoc, inv_simple]

end opposite

end Coxeter
