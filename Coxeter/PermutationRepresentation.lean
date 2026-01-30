import Mathlib.GroupTheory.Coxeter.Length

variable {B : Type*}
variable {W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

def word_t (ω : List B) (i : Fin ω.length) : W :=
  cs.wordProd (List.take i ω) * cs.simple (List.get ω i) * (cs.wordProd (List.take i ω))⁻¹

/- t_i is a reflection -/
theorem word_t_mul_word_t (ω : List B) (i : Fin ω.length) : word_t cs ω i * word_t cs ω i = 1 := by
  simp [word_t]

theorem left_mul_t (ω : List B) (i : Fin ω.length) :
  (word_t cs ω i) * cs.wordProd ω = cs.wordProd (ω.eraseIdx i) := by
  nth_rw 2 [←List.take_append_drop i ω]
  rw [word_t, cs.wordProd_append]
  simp only [List.get_eq_getElem, mul_assoc, inv_mul_cancel_left]
  rw [List.drop_eq_getElem_cons, cs.wordProd_cons]
  · simp [←cs.wordProd_append]
    congr
    simp [List.eraseIdx_eq_take_drop_succ]
  exact Fin.is_lt i

/- Bjorner--Brenti Lemma 1.3.1 -/
theorem word_t_neq (ω : List B) (hω : cs.IsReduced ω) (i j : Fin ω.length) (hij : i < j) :
  word_t cs ω i ≠ word_t cs ω j := by
  intro heq
  have h : cs.wordProd ω = cs.wordProd ((ω.eraseIdx j).eraseIdx i) := by
    calc
      cs.wordProd ω = word_t cs ω i * word_t cs ω j * cs.wordProd ω := ?_
      _ = word_t cs ω i * cs.wordProd (ω.eraseIdx j) := by rw [mul_assoc, left_mul_t]
      _ = cs.wordProd ((ω.eraseIdx j).eraseIdx i) := ?_
    · rw [heq, word_t_mul_word_t, one_mul]
    · have hi : i < (ω.eraseIdx j).length := by
        calc
          ↑i < ↑j := hij
          _ ≤ ω.length - 1 := Nat.le_sub_one_of_lt (Fin.is_lt j)
          _ = (ω.eraseIdx j).length := by rw [List.length_eraseIdx_of_lt (Fin.is_lt j)]
      rw [←left_mul_t cs (ω.eraseIdx j) (Fin.mk i hi)]
      simp only [word_t, List.get_eq_getElem, mul_left_inj]
      rw [List.take_eraseIdx_eq_take_of_le, List.getElem_eraseIdx_of_lt]
      · exact hij
      · exact le_of_lt hij
  apply (lt_self_iff_false ω.length).mp
  calc
    ω.length = cs.length (cs.wordProd ω) := by rw [hω]
    _ = cs.length (cs.wordProd ((ω.eraseIdx j).eraseIdx i)) := by rw [h]
    _ ≤ ((ω.eraseIdx j).eraseIdx i).length := by apply cs.length_wordProd_le
    _ ≤ (ω.eraseIdx j).length := by apply List.length_eraseIdx_le
    _ < ω.length := ?_
  · rw [List.length_eraseIdx_of_lt]
    · apply Nat.sub_one_lt
      exact Nat.ne_zero_of_lt (Fin.is_lt j)
    · exact Fin.is_lt j
