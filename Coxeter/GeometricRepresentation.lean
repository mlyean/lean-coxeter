import Coxeter.Basic
import Coxeter.LinearAlgebra.BilinearForm
import Coxeter.LinearAlgebra.TwoDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

/-!
# Geometric representation of Coxeter groups

This file attempts to define the geometric representation of a Coxeter group.

## References

* [bourbaki2007] N. Bourbaki, *Groupes et algèbres de Lie*

-/

namespace Coxeter

open CoxeterGroup Real Function Finsupp

noncomputable section

abbrev V (W : Type*) [CoxeterGroup W] := B W →₀ ℝ

variable {W : Type*} [CoxeterGroup W]

def stdBasis : Module.Basis (B W) ℝ (V W) := Finsupp.basisSingleOne

def bilAux (i i' : B W) : ℝ := - cos (π / M i i')

def bil : LinearMap.BilinForm ℝ (V W) := Matrix.toBilin stdBasis bilAux

theorem bil_isSymm : (@bil W _).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_iff_basis stdBasis]
  intro i i'
  unfold bil
  rw [Matrix.toBilin_single, Matrix.toBilin_single]
  unfold bilAux
  rw [M.symmetric i i']

@[simp high]
theorem bil_diag (i : B W) : bil (stdBasis i) (stdBasis i) = 1 := by
  unfold bil
  rw [Matrix.toBilin_single]
  unfold bilAux
  simp

@[simp low]
theorem bil_eq (i i' : B W) :
  bil (stdBasis i) (stdBasis i') = - cos (π / M.M i i') := by
  unfold bil
  rw [Matrix.toBilin_single]
  unfold bilAux
  simp

theorem bil_off_diag_le (i i' : B W) (h : i ≠ i') : bil (stdBasis i) (stdBasis i') ≤ 0 := by
  unfold bil
  rw [Matrix.toBilin_single]
  unfold bilAux
  rw [Left.neg_nonpos_iff]
  apply Real.cos_nonneg_of_mem_Icc
  have := M.off_diagonal i i' h
  rw [Set.mem_Icc]
  have := pi_pos
  constructor
  · trans 0
    · grind
    · positivity
  · cases Nat.eq_zero_or_pos (M.M i i') with
    | inl h =>
        rw [h]
        simp only [CharP.cast_eq_zero, div_zero]
        positivity
    | inr h =>
        apply div_le_div_of_nonneg_left
        · grind
        · norm_num
        · norm_num
          grind

def sigmaAux (i : B W) : V W →ₗ[ℝ] V W where
  toFun x := x - (2 * bil (stdBasis i) x) • stdBasis i
  map_add' := by
    intro x y
    match_scalars
    · rfl
    · rfl
    · simp
      ring
  map_smul' := by
    intro r x
    match_scalars
    · rfl
    · simp
      ring

theorem sigmaAux_apply (i : B W) (x : V W) :
  sigmaAux i x = x - (2 * bil (stdBasis i) x) • stdBasis i := rfl

theorem sigmaAux_involutive (i : B W) : Involutive (sigmaAux i) := by
  intro x
  unfold sigmaAux
  simp only [LinearMap.coe_mk, AddHom.coe_mk, map_sub, map_smul]
  match_scalars
  · rfl
  · simp [bil_diag]
    ring

def sigmaAux' (i : B W) : LinearMap.GeneralLinearGroup ℝ (V W) where
  val := sigmaAux i
  inv := sigmaAux i
  val_inv := by
    ext x y
    simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, Module.End.mul_apply,
      Module.End.one_apply]
    rw [sigmaAux_involutive i]
  inv_val := by
    ext x y
    simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, Module.End.mul_apply,
      Module.End.one_apply]
    rw [sigmaAux_involutive i]

theorem sigmaAux'_involutive (i : B W) : (sigmaAux' i) ^ 2 = 1 := by
  exact Units.val_eq_one.mp (sigmaAux' i).val_inv

def E (i i' : B W) : Submodule ℝ (V W) := supported ℝ _ {i, i'}

theorem mem_E_iff (i i' : B W) (v : V W)
  : v ∈ E i i' ↔ ∃ (x y : ℝ), v = x • stdBasis i + y • stdBasis i' := by
  unfold E stdBasis
  simp only [coe_basisSingleOne, smul_single, smul_eq_mul, mul_one]
  constructor
  · intro h
    by_cases h2 : i = i'
    · subst h2
      exists v i, 0
      simp only [single_zero, add_zero]
      ext j
      by_cases h3 : j = i
      · subst h3
        simp
      · simp only [ne_eq, h3, not_false_eq_true, single_eq_of_ne]
        rw [mem_supported'] at h
        apply h
        simp [h3]
    · exists v i, v i'
      ext j
      by_cases h3 : j = i
      · subst h3
        simp [h2]
      · by_cases h4 : j = i'
        · subst h4
          simp [h2]
        · simp only [coe_add, Pi.add_apply, ne_eq, h3, not_false_eq_true,
            single_eq_of_ne, h4, add_zero]
          rw [mem_supported'] at h
          apply h
          simp [h3, h4]
  · intro ⟨x, y, h⟩
    rw [h]
    apply add_mem
    all_goals
    apply single_mem_supported
    simp

theorem bil_restrict_E_diag (i i' : B W) (x y : ℝ) :
  bil (x • stdBasis i + y • stdBasis i') (x • stdBasis i + y • stdBasis i')
  = (x - y * cos (π / M.M i i')) ^ 2 + (y * sin (π / M.M i i')) ^ 2 := by
  calc
    bil (x • stdBasis i + y • stdBasis i') (x • stdBasis i + y • stdBasis i')
      = x ^ 2 - 2 * x * y * cos (π / M.M i i') + y ^ 2 := ?_
    _ = (x - y * cos (π / M.M i i')) ^ 2 + (y * sin (π / M.M i i')) ^ 2 := ?_
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    unfold bil
    simp only [Matrix.toBilin_single stdBasis]
    unfold bilAux
    rw [M.symmetric i i']
    simp
    ring
  · conv =>
      lhs
      congr
      · skip
      · rw [←one_mul (y ^ 2), ←Real.sin_sq_add_cos_sq (π / M.M i i')]
    ring

theorem bil_restrict_E_isSymm (i i' : B W) : (bil.restrict (E i i')).IsSymm := by
  apply LinearMap.BilinForm.IsSymm.restrict
  exact bil_isSymm

theorem bil_restrict_E_nonneg (i i' : B W) : (bil.restrict (E i i')).IsNonneg := by
  rw [LinearMap.BilinForm.isNonneg_def]
  intro z
  have ⟨x, y, h⟩ := (mem_E_iff i i' z).mp z.prop
  simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
  rw [h, bil_restrict_E_diag]
  positivity

/-- Bourbaki Ch V, §4, Proposition 1 -/
theorem bil_restrict_E_isPosSemidef (i i' : B W) : (bil.restrict (E i i')).IsPosSemidef := by
  rw [LinearMap.BilinForm.isPosSemidef_def]
  constructor
  · apply bil_restrict_E_isSymm
  · apply bil_restrict_E_nonneg

/-- Bourbaki Ch V, §4, Proposition 1 (continued) -/
theorem bil_restrict_E_nondegenerate_iff (i i' : B W) (h : i ≠ i') :
  (bil.restrict (E i i')).Nondegenerate ↔ M.M i i' ≠ 0 := by
  unfold LinearMap.BilinForm.Nondegenerate
  rw [LinearMap.BilinForm.nondegenerate_iff']
  · generalize h2 : M.M i i' = m
    match m with
    | 0 =>
        simp only [ne_eq,  not_true_eq_false, iff_false]
        push_neg
        exists ⟨cos (π / M.M i i') • stdBasis i + 1 • stdBasis i', ?_⟩
        · rw [mem_E_iff]
          exists cos (π / M.M i i'), 1
          simp
        · constructor
          · simp only [one_smul, ne_eq, Submodule.mk_eq_zero]
            rw [←ne_eq, Finsupp.ne_iff]
            exists i'
            simp [stdBasis, h]
          · have := bil_restrict_E_diag i i' (cos (π / M.M i i')) 1
            simp only [ne_eq, one_smul, map_add, map_smul, LinearMap.add_apply,
              LinearMap.smul_apply, smul_eq_mul, one_mul, sub_self, OfNat.ofNat_ne_zero,
              not_false_eq_true, zero_pow, zero_add, LinearMap.BilinForm.restrict_apply,
              LinearMap.domRestrict_apply, ge_iff_le] at *
            rw [this, h2]
            simp
    | 1 =>
        have := M.off_diagonal i i' h
        contradiction
    | k+2 =>
        simp only [ne_eq, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
          Subtype.forall, Submodule.mk_eq_zero, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false,
          not_false_eq_true, iff_true]
        intro z hz1 hz2
        apply lt_of_le_of_ne
        · exact (bil_restrict_E_nonneg i i').nonneg ⟨z, hz1⟩
        · have ⟨x, y, h⟩ := (mem_E_iff i i' z).mp hz1
          rw [h, bil_restrict_E_diag]
          intro h3
          symm at h3
          rw [sq, sq, mul_self_add_mul_self_eq_zero] at h3
          replace ⟨h3, h4⟩ := h3
          have : sin (π / ↑(M.M i i')) ≠ 0 := by
            rw [h2]
            apply ne_of_gt
            apply Real.sin_pos_of_mem_Ioo
            simp only [Nat.cast_add, Nat.cast_ofNat, Set.mem_Ioo]
            constructor
            · positivity
            · field_simp
              linarith
          simp only [mul_eq_zero, this, or_false] at h4
          rw [h4] at h3
          simp only [zero_mul, sub_zero] at h3
          rw [h3, h4] at h
          simp at h
          contradiction
  · exact (bil_restrict_E_nonneg i i').nonneg
  · rw [←LinearMap.BilinForm.isSymm_iff]
    exact bil_restrict_E_isSymm i i'

theorem sigmaAux_E_perp_left (i i' : B W) :
  ∀ z ∈ (E i i').orthogonalBilin bil, sigmaAux i z = z := by
  intro z hz
  simp only [sigmaAux, LinearMap.coe_mk, AddHom.coe_mk, sub_eq_self, smul_eq_zero, mul_eq_zero,
    OfNat.ofNat_ne_zero, false_or]
  left
  apply hz (stdBasis i)
  rw [mem_E_iff]
  exists 1, 0
  simp

theorem sigmaAux_E_perp_right (i i' : B W) :
  ∀ z ∈ (E i i').orthogonalBilin bil, sigmaAux i' z = z := by
  intro z hz
  simp only [sigmaAux, LinearMap.coe_mk, AddHom.coe_mk, sub_eq_self, smul_eq_zero, mul_eq_zero,
    OfNat.ofNat_ne_zero, false_or]
  left
  apply hz (stdBasis i')
  rw [mem_E_iff]
  exists 0, 1
  simp

theorem sigmaAux_E_left (i i' : B W) : ∀ z ∈ E i i', sigmaAux i z ∈ E i i' := by
  intro z hz
  rw [mem_E_iff] at hz
  have ⟨x, y, h⟩ := hz
  rw [h]
  simp only [map_add, map_smul]
  apply add_mem
  · simp only [sigmaAux, LinearMap.coe_mk, AddHom.coe_mk, bil_diag, mul_one]
    rw [mem_E_iff]
    exists -x, 0
    match_scalars
    · ring
    · simp
  · simp only [sigmaAux, LinearMap.coe_mk, AddHom.coe_mk]
    rw [mem_E_iff]
    exists -2 * y * bil (stdBasis i) (stdBasis i'), y
    match_scalars
    · rfl
    · ring

theorem sigmaAux_E_right (i i' : B W) : ∀ z ∈ E i i', sigmaAux i' z ∈ E i i' := by
  intro z hz
  rw [mem_E_iff] at hz
  have ⟨x, y, h⟩ := hz
  rw [h]
  simp only [map_add, map_smul]
  apply add_mem
  · simp only [sigmaAux, LinearMap.coe_mk, AddHom.coe_mk]
    rw [mem_E_iff]
    exists x, -2 * x * bil (stdBasis i') (stdBasis i)
    match_scalars
    · rfl
    · ring
  · simp only [sigmaAux, LinearMap.coe_mk, AddHom.coe_mk, bil_diag, mul_one]
    rw [mem_E_iff]
    exists 0, -y
    match_scalars
    · ring
    · simp

theorem sigmaAux_E_2 (i i' : B W) : ∀ z ∈ E i i', (sigmaAux i * sigmaAux i') z ∈ E i i' := by
  intro z hz
  apply sigmaAux_E_left i i'
  apply sigmaAux_E_right i i'
  exact hz

section finite_order

variable {i i' : B W}
variable [h : Fact (M i i' ≥ 2)]

theorem i_ne_i' : i ≠ i' := by
  intro heq
  subst heq
  replace h := h.out
  simp at h

open Classical in
def eAux : ({i, i'} : Set (B W)) → Fin 2 := fun x => if x.val = i then 0 else 1

def eInvAux : Fin 2 → ({i, i'} : Set (B W))
| 0 => ⟨i, by tauto⟩
| 1 => ⟨i', by tauto⟩

def e : ({i, i'} : Set (B W)) ≃ Fin 2 where
  toFun := eAux
  invFun := eInvAux
  left_inv := by
    intro x
    have : x = i ∨ x = i' := by grind
    cases this with
    | inl h1 =>
        simp only [eAux, eInvAux, h1, ↓reduceIte, Fin.isValue]
        ext
        rw [h1]
    | inr h1 =>
        have : i ≠ i' := i_ne_i'
        simp only [eAux, eInvAux, Fin.isValue]
        rw [h1]
        symm at this
        simp only [this, ↓reduceIte, Fin.isValue]
        ext
        rw [h1]
  right_inv := by
    intro x
    match x with
    | 0 => simp [eAux, eInvAux]
    | 1 =>
        simp only [eInvAux, eAux, Fin.isValue, ite_eq_right_iff, zero_ne_one, imp_false, ne_eq]
        rw [←ne_eq]
        symm
        apply i_ne_i'

def stdBasisE : Module.Basis (Fin 2) ℝ (E i i') :=
  (Finsupp.basisSingleOne.map (supportedEquivFinsupp {i, i'}).symm).reindex e

@[simp]
theorem stdBasisE_0 : (@stdBasisE _ _ i i' _ 0).val = stdBasis i := by
  unfold stdBasisE
  calc
    (((Finsupp.basisSingleOne.map (supportedEquivFinsupp {i, i'}).symm).reindex e) 0).val
    = ((Finsupp.basisSingleOne.map (supportedEquivFinsupp {i, i'}).symm) (e.symm 0)).val := ?_
    _ = stdBasis i := ?_
  · rw [Module.Basis.reindex_apply]
  · rw [Module.Basis.map_apply]
    unfold stdBasis e eInvAux
    simp

@[simp]
theorem stdBasisE_1 : (@stdBasisE _ _ i i' _ 1) = stdBasis i' := by
  unfold stdBasisE
  calc
    (((Finsupp.basisSingleOne.map (supportedEquivFinsupp {i, i'}).symm).reindex e) 1).val
    = ((Finsupp.basisSingleOne.map (supportedEquivFinsupp {i, i'}).symm) (e.symm 1)).val := ?_
    _ = stdBasis i' := ?_
  · rw [Module.Basis.reindex_apply]
  · rw [Module.Basis.map_apply]
    unfold stdBasis e eInvAux
    simp

instance findimE : FiniteDimensional ℝ (E i i') := stdBasisE.finiteDimensional_of_finite

theorem dimE_eq_two : Module.finrank ℝ (E i i') = 2 := by
  rw [Module.finrank_eq_card_basis stdBasisE]
  simp

theorem E_sup_orthogonal : E i i' ⊔ (E i i').orthogonalBilin bil = ⊤ := by
  apply sup_orthogonal_eq_top
  · exact bil_isSymm
  · exact bil_restrict_E_nonneg i i'
  · rw [bil_restrict_E_nondegenerate_iff i i' i_ne_i']
    replace h := h.out
    grind

theorem order_sigmaAux_2_eq_order_restrict (m : ℕ) :
  (sigmaAux i * sigmaAux i') ^ m = 1
  ↔ (sigmaAux i * sigmaAux i').restrict (sigmaAux_E_2 i i') ^ m = 1 := by
  constructor
  · intro h2
    rw [Module.End.pow_restrict]
    conv =>
      lhs
      congr
      rw [h2]
    rfl
  · intro h2
    apply LinearMap.ext
    intro z
    simp only [Module.End.one_apply]
    have h3 := @E_sup_orthogonal _ _ i i'
    rw [Submodule.sup_eq_top_iff] at h3
    have ⟨u, hu, v, hv, hz⟩ := h3 z
    rw [hz]
    simp only [map_add]
    congr
    · have := LinearMap.congr_fun h2 ⟨u, hu⟩
      rw [Module.End.pow_restrict, LinearMap.restrict_apply] at this
      simp_all only [ge_iff_le, Submodule.mem_orthogonalBilin_iff, Module.End.one_apply,
        Subtype.mk.injEq]
    · clear h2
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ]
          change ((sigmaAux i * sigmaAux i') ^ m) (sigmaAux i (sigmaAux i' v)) = v
          rw [sigmaAux_E_perp_right i i' v hv, sigmaAux_E_perp_left i i' v hv, ih]

noncomputable instance : PreInnerProductSpace.Core ℝ (E i i') where
  inner x y := bil.restrict (E i i') x y
  conj_inner_symm := by
    intro x y
    simp only [conj_trivial]
    apply bil_isSymm.eq
  re_inner_nonneg := by
    simp only [RCLike.re_to_real]
    exact (bil_restrict_E_nonneg i i').nonneg
  add_left := by simp
  smul_left := by simp

noncomputable instance : InnerProductSpace.Core ℝ (E i i') where
  definite := by
    replace h := h.out
    intro x h2
    change bil.restrict (E i i') x x = 0 at h2
    have : (bil.restrict (E i i')).Nondegenerate := by
      rw [bil_restrict_E_nondegenerate_iff]
      · grind
      · intro h3
        subst h3
        simp at h
    unfold LinearMap.BilinForm.Nondegenerate at this
    rw [LinearMap.BilinForm.nondegenerate_iff] at this
    · specialize this x
      rw [this] at h2
      exact h2
    · exact (bil_restrict_E_nonneg i i').nonneg
    · rw [←LinearMap.BilinForm.isSymm_iff]
      exact bil_restrict_E_isSymm i i'

noncomputable instance : NormedAddCommGroup (E i i') :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (E i i') _ _ _ inferInstance

noncomputable instance : InnerProductSpace ℝ (E i i') :=
  InnerProductSpace.ofCore inferInstance

@[simp]
theorem norm_stdBasisE_0 : ‖@stdBasisE _ _ _ _ h 0‖ = 1 := by
  rw [@norm_eq_sqrt_re_inner ℝ (E i i')]
  change √(RCLike.re (bil.restrict (E i i') (stdBasisE 0) (stdBasisE 0))) = 1
  rw [LinearMap.BilinForm.restrict_apply]
  simp

@[simp]
theorem norm_stdBasisE_1 : ‖@stdBasisE _ _ _ _ h 1‖ = 1 := by
  rw [@norm_eq_sqrt_re_inner ℝ (E i i')]
  change √(RCLike.re (bil.restrict (E i i') (stdBasisE 1) (stdBasisE 1))) = 1
  rw [LinearMap.BilinForm.restrict_apply]
  simp

@[simp]
theorem inner_stdBasisE_0_1 :
  inner ℝ (@stdBasisE _ _ _ _ h 0) (@stdBasisE _ _ _ _ h 1) = -cos (π / M.M i i') := by
  change bil.restrict (E i i') (@stdBasisE _ _ _ _ h 0) (@stdBasisE _ _ _ _ h 1)
    = -cos (π / ↑(M.M i i'))
  simp

def o : Orientation ℝ (E i i') (Fin 2) := stdBasisE.orientation

instance : Fact (Module.finrank ℝ (E i i') = 2) where
  out := dimE_eq_two

theorem oangle_stdBasisE :
  (@o _ _ _ _ h).oangle (stdBasisE 0) (stdBasisE 1) = (Real.pi - Real.pi / M.M i i' : ℝ) ∨
  (@o _ _ _ _ h).oangle (stdBasisE 0) (stdBasisE 1) = -(Real.pi - Real.pi / M.M i i' : ℝ) := by
  have h2 := (@o _ _ _ _ h).inner_eq_norm_mul_norm_mul_cos_oangle (stdBasisE 0) (stdBasisE 1)
  symm at h2
  simp only [Fin.isValue, inner_stdBasisE_0_1, norm_stdBasisE_0, norm_stdBasisE_1, mul_one,
    one_mul] at h2
  rwa [←Real.cos_pi_sub, Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg] at h2

omit h in
theorem restrict_sigmaAux_mul :
  (sigmaAux i * sigmaAux i').restrict (sigmaAux_E_2 i i')
  = (sigmaAux i).restrict (sigmaAux_E_left i i')
    ∘ₗ (sigmaAux i').restrict (sigmaAux_E_right i i') := by
  trivial

theorem sigmaAux_i_restrict_eq_reflect : (sigmaAux i).restrict (sigmaAux_E_left i i') =
  reflect (@norm_stdBasisE_0 _ _ _ _ h) := by
  ext x : 1
  rw [LinearMap.restrict_apply]
  simp only [Fin.isValue, LinearEquiv.coe_coe]
  rw [reflect_apply]
  rw [←Subtype.coe_inj]
  simp only [Fin.isValue, AddSubgroupClass.coe_sub, SetLike.val_smul, stdBasisE_0]
  rw [sigmaAux_apply]
  congr 3
  change (bil (stdBasis i)) ↑x = bil.restrict (E i i') (stdBasisE 0) x
  rw [LinearMap.BilinForm.restrict_apply, stdBasisE_0]
  simp

theorem sigmaAux_i'_restrict_eq_reflect : (sigmaAux i').restrict (sigmaAux_E_right i i') =
  reflect (@norm_stdBasisE_1 _ _ _ _ h) := by
  ext x : 1
  rw [LinearMap.restrict_apply]
  simp only [Fin.isValue, LinearEquiv.coe_coe]
  rw [reflect_apply]
  rw [←Subtype.coe_inj]
  simp only [Fin.isValue, AddSubgroupClass.coe_sub, SetLike.val_smul, stdBasisE_1]
  rw [sigmaAux_apply]
  congr 3
  change (bil (stdBasis i')) ↑x = bil.restrict (E i i') (stdBasisE 1) x
  rw [LinearMap.BilinForm.restrict_apply, stdBasisE_1]
  simp

theorem sigmaAux_2_restrict_eq_rotate :
  (sigmaAux i * sigmaAux i').restrict (sigmaAux_E_2 i i')
  = (o.rotation (2 * Real.pi / M i i' : ℝ)).toLinearMap ∨
  (sigmaAux i * sigmaAux i').restrict (sigmaAux_E_2 i i')
  = (o.rotation (2 * Real.pi / (-M i i') : ℝ)).toLinearMap := by
  rw [restrict_sigmaAux_mul, sigmaAux_i_restrict_eq_reflect, sigmaAux_i'_restrict_eq_reflect]
  simp only [Fin.isValue, LinearEquiv.comp_coe, LinearEquiv.toLinearMap_inj]
  rw [reflect_reflect o]
  cases @oangle_stdBasisE _ _ _ _ h with
  | inl h2 =>
      left
      rw [Orientation.oangle_rev, h2]
      conv =>
        lhs
        congr
        congr
        · skip
        · rw [Real.Angle.coe_sub, smul_neg, smul_sub, neg_sub, ←Real.Angle.coe_nsmul]
          simp
      ext
      simp only [SemilinearEquivClass.semilinearEquiv_apply, LinearIsometryEquiv.coe_toLinearEquiv]
      congr 5
      ring
  | inr h2 =>
      right
      rw [Orientation.oangle_rev, h2]
      conv =>
        lhs
        congr
        congr
        · skip
        · rw [neg_neg]
          rw [Real.Angle.coe_sub]
          rw [smul_sub]
          simp
          rw [←Real.Angle.coe_nsmul, ←Real.Angle.coe_neg]
      ext
      simp only [SemilinearEquivClass.semilinearEquiv_apply, LinearIsometryEquiv.coe_toLinearEquiv]
      congr 5
      ring

end finite_order

end

end Coxeter
