module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace List

variable {α : Type*}

theorem drop_eraseIdx (l : List α) (i j : ℕ) :
  (drop i l).eraseIdx j = drop i (l.eraseIdx (i + j)) := by
  induction i generalizing l with
  | zero => simp
  | succ i ih =>
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

theorem finite_sublist (l : List α) : {l' : List α | l' <+ l}.Finite := by
  have h := l.sublists.finite_toSet
  simp only [mem_sublists] at h
  assumption

end List
