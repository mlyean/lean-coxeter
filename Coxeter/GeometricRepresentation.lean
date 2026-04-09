module

public import Coxeter.Basic
public import Coxeter.LinearAlgebra.BilinearForm
public import Coxeter.LinearAlgebra.TwoDim

/-!
# Geometric representation of Coxeter groups

This file defines the geometric representation of a Coxeter group.

## Main definitions

* `Coxeter.geomRep` : The geometric representation

## Main statements

* `Coxeter.orderOf_simple_mul_simple` : $s_i s_{i'}$ has the expected order
* `Coxeter.simple_inj`

## TODO

* Pin down the orientation in `Coxeter.oangle_stdBasisE`

## References

* [bourbaki2007] N. Bourbaki, *Groupes et algèbres de Lie*
-/

@[expose] public section

namespace Coxeter

open CoxeterGroup Real Function Finsupp

noncomputable section

abbrev V (W : Type*) [CoxeterGroup W] := B W →₀ ℝ

variable {W : Type*} [CoxeterGroup W]

def stdBasis : Module.Basis (B W) ℝ (V W) := Finsupp.basisSingleOne

def bil : LinearMap.BilinForm ℝ (V W) := Matrix.toBilin stdBasis (fun i i' => -cos (π / M i i'))

theorem bil_isSymm : (@bil W _).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_iff_basis stdBasis]
  intro i i'
  unfold bil
  rw [Matrix.toBilin_single, Matrix.toBilin_single, M.symmetric i i']

@[simp]
theorem bil_eq (i i' : B W) : bil (stdBasis i) (stdBasis i') = -cos (π / M i i') := by
  unfold bil
  rw [Matrix.toBilin_single]

@[simp]
theorem bil_diag (i : B W) : bil (stdBasis i) (stdBasis i) = 1 := by
  rw [bil_eq]
  simp

theorem bil_off_diag_le (i i' : B W) (h : i ≠ i') : bil (stdBasis i) (stdBasis i') ≤ 0 := by
  rw [bil_eq, neg_nonpos]
  apply cos_nonneg_of_neg_pi_div_two_le_of_le
  · trans 0
    · rw [neg_nonpos]
      positivity
    · positivity
  · cases Nat.eq_zero_or_pos (M i i') with
    | inl h2 =>
        rw [h2]
        norm_num
        positivity
    | inr h2 =>
        apply div_le_div_of_nonneg_left
        · positivity
        · norm_num
        · norm_num
          have := M.off_diagonal i i' h
          lia

def geomRepAux (i : B W) : V W ≃ₗ[ℝ] V W where
  toFun x := x - (2 * bil (stdBasis i) x) • stdBasis i
  invFun x := x - (2 * bil (stdBasis i) x) • stdBasis i
  map_add' := by
    intro x y
    rw [map_add]
    match_scalars <;> ring
  map_smul' := by
    intro r x
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    match_scalars <;> ring
  left_inv := by
    intro x
    simp only [map_sub, map_smul, bil_diag, smul_eq_mul, mul_one]
    match_scalars <;> ring
  right_inv := by
    intro x
    simp only [map_sub, map_smul, bil_diag, smul_eq_mul, mul_one]
    match_scalars <;> ring

theorem geomRepAux_apply (i : B W) (x : V W) :
  geomRepAux i x = x - (2 * bil (stdBasis i) x) • stdBasis i := rfl

theorem geomRepAux_involutive (i : B W) : Involutive (geomRepAux i) := (geomRepAux i).left_inv

@[simp]
theorem geomRepAux_stdBasis (i : B W) :
  geomRepAux i (stdBasis i) = -stdBasis i := by
  rw [geomRepAux_apply, bil_diag]
  match_scalars
  norm_num

def E (i i' : B W) : Submodule ℝ (V W) := supported ℝ _ {i, i'}

theorem E_eq_span (i i' : B W) : E i i' = Submodule.span ℝ {stdBasis i, stdBasis i'} := by
  unfold E stdBasis
  rw [supported_eq_span_single, Set.image_pair]
  rfl

theorem mem_E_iff (i i' : B W) (v : V W)
  : v ∈ E i i' ↔ ∃ (x y : ℝ), v = x • stdBasis i + y • stdBasis i' := by
  rw [E_eq_span, Submodule.mem_span_pair]
  tauto

theorem E_symm (i i' : B W) : E i i' = E i' i := by
  unfold E
  rw [Set.pair_comm]

theorem bil_restrict_E_diag (i i' : B W) (x y : ℝ) :
  bil (x • stdBasis i + y • stdBasis i') (x • stdBasis i + y • stdBasis i')
  = (x - y * cos (π / M i i')) ^ 2 + (y * sin (π / M i i')) ^ 2 := by
  calc
    bil (x • stdBasis i + y • stdBasis i') (x • stdBasis i + y • stdBasis i')
      = x ^ 2 - 2 * x * y * cos (π / M i i') + y ^ 2 := ?_
    _ = (x - y * cos (π / M i i')) ^ 2 + (y * sin (π / M i i')) ^ 2 := ?_
  · simp [M.symmetric i' i]
    ring
  · conv in y ^ 2 =>
      rw [←one_mul (y ^ 2), ←sin_sq_add_cos_sq (π / M i i')]
    ring

theorem bil_restrict_E_isSymm (i i' : B W) : (bil.restrict (E i i')).IsSymm := by
  apply LinearMap.BilinForm.IsSymm.restrict bil_isSymm

theorem bil_restrict_E_nonneg (i i' : B W) : (bil.restrict (E i i')).IsNonneg := by
  rw [LinearMap.BilinForm.isNonneg_def]
  intro ⟨z, hz⟩
  rw [mem_E_iff] at hz
  obtain ⟨x, y, h⟩ := hz
  simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
  rw [h, bil_restrict_E_diag]
  positivity

/-- Bourbaki Ch V, §4, Proposition 1 -/
theorem bil_restrict_E_isPosSemidef (i i' : B W) : (bil.restrict (E i i')).IsPosSemidef := by
  rw [LinearMap.BilinForm.isPosSemidef_def]
  exact ⟨bil_restrict_E_isSymm i i', bil_restrict_E_nonneg i i'⟩

/-- Bourbaki Ch V, §4, Proposition 1 (continued) -/
theorem bil_restrict_E_nondegenerate_iff (i i' : B W) (h : i ≠ i') :
  (bil.restrict (E i i')).Nondegenerate ↔ M i i' ≠ 0 := by
  unfold LinearMap.BilinForm.Nondegenerate
  rw [LinearMap.BilinForm.nondegenerate_iff']
  · have h2 : M i i' = 0 ∨ M i i' = 1 ∨ M i i' ≥ 2 := by lia
    match h2 with
    | Or.inl h2 =>
        rw [h2]
        simp only [ne_eq,  not_true_eq_false, iff_false]
        push Not
        exists ⟨cos (π / M i i') • stdBasis i + 1 • stdBasis i', ?_⟩
        · rw [mem_E_iff]
          exists cos (π / M i i'), 1
          simp
        · simp only [h2, CharP.cast_eq_zero, div_zero, cos_zero, one_smul, ne_eq,
            Submodule.mk_eq_zero, LinearMap.BilinForm.restrict_apply, map_add,
            LinearMap.domRestrict_apply, LinearMap.add_apply, bil_diag, bil_eq, add_neg_cancel,
            M.symmetric i' i, neg_add_cancel, add_zero, Std.le_refl, and_true]
          rw [←ne_eq, Finsupp.ne_iff]
          exists i'
          simp [stdBasis, h]
    | Or.inr (Or.inl h2) =>
        absurd h2
        exact M.off_diagonal i i' h
    | Or.inr (Or.inr h2) =>
        have : M i i' ≠ 0 := by lia
        simp only [ne_eq, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
          Subtype.forall, Submodule.mk_eq_zero, this, not_false_eq_true, iff_true]
        intro z hz1 hz2
        apply lt_of_le_of_ne
        · exact (bil_restrict_E_nonneg i i').nonneg ⟨z, hz1⟩
        · rw [mem_E_iff] at hz1
          obtain ⟨x, y, h⟩ := hz1
          rw [h, bil_restrict_E_diag]
          intro h3
          symm at h3
          rw [sq, sq, mul_self_add_mul_self_eq_zero] at h3
          replace ⟨h3, h4⟩ := h3
          have h5 : sin (π / M i i') ≠ 0 := by
            apply ne_of_gt
            apply sin_pos_of_pos_of_lt_pi
            · positivity
            · apply div_lt_self
              · positivity
              · norm_num
                exact h2
          rw [mul_eq_zero_iff_right h5] at h4
          subst h4
          rw [zero_mul, sub_zero] at h3
          subst h3
          rw [zero_smul, zero_smul, add_zero] at h
          contradiction
  · exact (bil_restrict_E_nonneg i i').nonneg
  · rw [←LinearMap.BilinForm.isSymm_iff]
    exact bil_restrict_E_isSymm i i'

theorem geomRepAux_E_perp_left (i i' : B W) :
  ∀ z ∈ (E i i').orthogonalBilin bil, geomRepAux i z = z := by
  intro z hz
  rw [geomRepAux_apply, sub_eq_self, hz (stdBasis i), mul_zero, zero_smul]
  rw [mem_E_iff]
  exists 1, 0
  simp

theorem geomRepAux_E_perp_right (i i' : B W) :
  ∀ z ∈ (E i i').orthogonalBilin bil, geomRepAux i' z = z := by
  rw [E_symm]
  apply geomRepAux_E_perp_left

theorem geomRepAux_E_left (i i' : B W) : Set.MapsTo (geomRepAux i) (E i i') (E i i') := by
  suffices h : Submodule.map (geomRepAux i).toLinearMap (E i i') ≤ E i i'
    from Set.mapsTo_iff_image_subset.mpr h
  nth_rw 1 [E_eq_span, LinearMap.map_span_le]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, LinearEquiv.coe_coe, forall_eq_or_imp,
    geomRepAux_stdBasis, neg_mem_iff, forall_eq]
  constructor
  · rw [mem_E_iff]
    exists 1, 0
    simp
  · rw [geomRepAux_apply, mem_E_iff]
    simp only [bil_eq, mul_neg, neg_smul, sub_neg_eq_add]
    exists 2 * cos (π / M i i'), 1
    match_scalars <;> ring

theorem geomRepAux_E_right (i i' : B W) : Set.MapsTo (geomRepAux i') (E i i') (E i i') := by
  rw [E_symm]
  apply geomRepAux_E_left

theorem geomRepAux_E_2 (i i' : B W)
  : Set.MapsTo (geomRepAux i * geomRepAux i') (E i i') (E i i') := by
  change Set.MapsTo (geomRepAux i ∘ geomRepAux i') (E i i') (E i i')
  exact (geomRepAux_E_left i i').comp (geomRepAux_E_right i i')

theorem restrict_geomRepAux_mul (i i' : B W) :
  (geomRepAux i * geomRepAux i').restrict (geomRepAux_E_2 i i')
  = (geomRepAux i).restrict (geomRepAux_E_left i i')
    ∘ₗ (geomRepAux i').restrict (geomRepAux_E_right i i') := by rfl

section infinite_order

variable (i i' : B W)

theorem geomRepAux_2_add_of_order_zero (h : M i i' = 0) (n : ℕ) :
  ((geomRepAux i * geomRepAux i') ^ n) (stdBasis i)
  = (2 * n) • (stdBasis i + stdBasis i') + stdBasis i := by
  generalize hu : stdBasis i + stdBasis i' = u
  have h1 : bil (stdBasis i) u = 0 := by
    rw [←hu]
    simp only [map_add, bil_diag, bil_eq]
    rw [h]
    simp
  have h2 : bil (stdBasis i') u = 0 := by
    rw [←hu]
    simp only [map_add, bil_eq]
    rw [M.symmetric i' i, h]
    simp
  have h3 : (geomRepAux i * geomRepAux i') u = u := by
    rw [LinearEquiv.mul_apply]
    nth_rw 2 [geomRepAux_apply]
    rw [h2, mul_zero, zero_smul, sub_zero, geomRepAux_apply, h1, mul_zero, zero_smul, sub_zero]
  have h4 : (geomRepAux i * geomRepAux i') (stdBasis i) = 2 • u + stdBasis i := by
    rw [LinearEquiv.mul_apply, ←hu]
    simp only [geomRepAux_apply, bil_eq, mul_neg, neg_smul, sub_neg_eq_add, map_add,
      map_smul, smul_add]
    rw [M.symmetric i' i, h]
    simp only [CoxeterMatrix.diagonal, Nat.cast_one, div_one, cos_pi, mul_neg, mul_one, neg_smul,
      CharP.cast_eq_zero, div_zero, cos_zero]
    match_scalars <;> ring
  suffices ((geomRepAux i * geomRepAux i') ^ n) (stdBasis i) = (2 * n) • u + stdBasis i ∧
    ((geomRepAux i * geomRepAux i') ^ n) u = u by
    exact this.1
  induction n with
  | zero => simp
  | succ n ih =>
      constructor
      · rw [pow_succ, LinearEquiv.mul_apply, h4, map_add, ih.1, map_nsmul, ih.2]
        match_scalars <;> ring
      · rw [pow_succ, LinearEquiv.mul_apply, h3, ih.2]

end infinite_order

section finite_order

variable (i i' : B W) [Fact (M i i' ≥ 2)]

theorem i_ne_i' : i ≠ i' := by
  have h := (inferInstance : Fact (M i i' ≥ 2)).out
  intro heq
  subst heq
  simp at h

open Classical in
def e : ({i, i'} : Set (B W)) ≃ Fin 2 where
  toFun := fun x => if x.val = i then 0 else 1
  invFun
  | 0 => ⟨i, by tauto⟩
  | 1 => ⟨i', by tauto⟩
  left_inv x := by grind
  right_inv
  | 0 => by simp
  | 1 => by
      simp only [ite_eq_right_iff, zero_ne_one, imp_false]
      rw [←ne_eq]
      symm
      apply i_ne_i'

def stdBasisE : Module.Basis (Fin 2) ℝ (E i i') :=
  (Finsupp.basisSingleOne.map (supportedEquivFinsupp {i, i'}).symm).reindex (e i i')

@[simp]
theorem stdBasisE_0 : stdBasisE i i' 0 = stdBasis i := by
  calc
    (((Finsupp.basisSingleOne.map (supportedEquivFinsupp {i, i'}).symm).reindex (e i i')) 0).val
    = ((Finsupp.basisSingleOne.map (supportedEquivFinsupp {i, i'}).symm) ((e i i').symm 0)).val
      := by rw [Module.Basis.reindex_apply]
    _ = stdBasis i := ?_
  rw [Module.Basis.map_apply]
  unfold stdBasis e
  simp

@[simp]
theorem stdBasisE_1 : stdBasisE i i' 1 = stdBasis i' := by
  calc
    (((Finsupp.basisSingleOne.map (supportedEquivFinsupp {i, i'}).symm).reindex (e i i')) 1).val
    = ((Finsupp.basisSingleOne.map (supportedEquivFinsupp {i, i'}).symm) ((e i i').symm 1)).val
      := by rw [Module.Basis.reindex_apply]
    _ = stdBasis i' := ?_
  rw [Module.Basis.map_apply]
  unfold stdBasis e
  simp

instance : FiniteDimensional ℝ (E i i') := (stdBasisE i i').finiteDimensional_of_finite

theorem finrank_E_eq_two : Module.finrank ℝ (E i i') = 2 := by
  rw [Module.finrank_eq_card_basis (stdBasisE i i')]
  simp

instance : Fact (Module.finrank ℝ (E i i') = 2) where
  out := finrank_E_eq_two i i'

theorem E_sup_orthogonal :
  E i i' ⊔ (E i i').orthogonalBilin bil = ⊤ := by
  apply sup_orthogonal_eq_top _ bil_isSymm (bil_restrict_E_nonneg i i')
  rw [bil_restrict_E_nondegenerate_iff i i' (i_ne_i' i i')]
  have := (inferInstance : Fact (M i i' ≥ 2)).out
  lia

theorem order_geomRepAux_2_eq_order_restrict (m : ℕ) :
  (geomRepAux i * geomRepAux i') ^ m = 1
  ↔ (geomRepAux i * geomRepAux i').restrict (geomRepAux_E_2 i i') ^ m = 1 := by
  rw [Module.End.pow_restrict]
  constructor
  · intro h2
    ext ⟨x, hx⟩ : 1
    rw [LinearMap.restrict_apply]
    simp only [LinearEquiv.coe_toLinearMap_mul, Module.End.one_apply, Subtype.mk.injEq]
    rw [Module.End.pow_apply]
    have := LinearEquiv.congr_fun h2 x
    rwa [LinearEquiv.pow_apply] at this
  · intro h2
    apply LinearEquiv.ext
    intro z
    simp only [LinearEquiv.coe_one, id_eq]
    have h3 := E_sup_orthogonal i i'
    rw [Submodule.sup_eq_top_iff] at h3
    have ⟨u, hu, v, hv, hz⟩ := h3 z
    rw [hz]
    simp only [map_add]
    congr
    · have := LinearMap.congr_fun h2 ⟨u, hu⟩
      rw [LinearMap.restrict_apply] at this
      simp only [LinearEquiv.coe_toLinearMap_mul, Module.End.one_apply, Subtype.mk.injEq] at this
      rw [Module.End.pow_apply] at this
      rwa [LinearEquiv.pow_apply]
    · clear h2
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ]
          change ((geomRepAux i * geomRepAux i') ^ m) (geomRepAux i (geomRepAux i' v)) = v
          rw [geomRepAux_E_perp_right i i' v hv, geomRepAux_E_perp_left i i' v hv, ih]

instance : PreInnerProductSpace.Core ℝ (E i i') where
  inner x y := bil.restrict (E i i') x y
  conj_inner_symm x y := by
    simp only [conj_trivial]
    apply bil_isSymm.eq
  re_inner_nonneg := by
    simp only [RCLike.re_to_real]
    exact (bil_restrict_E_nonneg i i').nonneg
  add_left := by simp
  smul_left := by simp

instance : InnerProductSpace.Core ℝ (E i i') where
  definite x h := by
    have h2 := (inferInstance : Fact (M i i' ≥ 2)).out
    change bil.restrict (E i i') x x = 0 at h
    have h3 : (bil.restrict (E i i')).Nondegenerate := by
      rw [bil_restrict_E_nondegenerate_iff]
      · lia
      · intro h3
        simp [h3] at h2
    unfold LinearMap.BilinForm.Nondegenerate at h3
    rw [LinearMap.BilinForm.nondegenerate_iff] at h3
    · specialize h3 x
      rwa [h3] at h
    · exact (bil_restrict_E_nonneg i i').nonneg
    · rw [←LinearMap.BilinForm.isSymm_iff]
      exact bil_restrict_E_isSymm i i'

instance : NormedAddCommGroup (E i i') :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (E i i') _ _ _ inferInstance

instance : InnerProductSpace ℝ (E i i') := InnerProductSpace.ofCore inferInstance

open scoped RealInnerProductSpace

@[simp]
theorem norm_stdBasisE_0 : ‖stdBasisE i i' 0‖ = 1 := by
  rw [@norm_eq_sqrt_re_inner ℝ (E i i')]
  change √((bil.restrict (E i i') (stdBasisE i i' 0) (stdBasisE i i' 0))) = 1
  rw [LinearMap.BilinForm.restrict_apply]
  simp

@[simp]
theorem norm_stdBasisE_1 : ‖stdBasisE i i' 1‖ = 1 := by
  rw [@norm_eq_sqrt_re_inner ℝ (E i i')]
  change √((bil.restrict (E i i') (stdBasisE i i' 1) (stdBasisE i i' 1))) = 1
  rw [LinearMap.BilinForm.restrict_apply]
  simp

@[simp]
theorem inner_stdBasisE_0_1 : ⟪stdBasisE i i' 0, stdBasisE i i' 1⟫ = -cos (π / M i i') := by
  simp [inner]

theorem oangle_stdBasisE : ∃ (o : Orientation ℝ (E i i') (Fin 2)),
  o.oangle (stdBasisE i i' 0) (stdBasisE i i' 1) = Angle.coe (π - π / M i i') := by
  let o := (stdBasisE i i').orientation
  have h2 := o.inner_eq_norm_mul_norm_mul_cos_oangle (stdBasisE i i' 0) (stdBasisE i i' 1)
  symm at h2
  simp only [Fin.isValue, inner_stdBasisE_0_1, norm_stdBasisE_0, norm_stdBasisE_1, mul_one,
    one_mul] at h2
  rw [←cos_pi_sub, Angle.cos_eq_real_cos_iff_eq_or_eq_neg] at h2
  cases h2 with
  | inl h2 =>
      exists o
  | inr h2 =>
      exists -o
      rw [Orientation.oangle_neg_orientation_eq_neg, h2, neg_neg]

theorem geomRepAux_i_restrict_eq_reflect :
  (geomRepAux i).restrict (geomRepAux_E_left i i') = reflect (norm_stdBasisE_0 i i') := by
  ext x : 1
  rw [LinearMap.restrict_apply]
  simp only [LinearEquiv.coe_coe]
  rw [reflect_apply, ←Subtype.coe_inj]
  simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, stdBasisE_0]
  rw [geomRepAux_apply]
  congr 3
  change (bil (stdBasis i)) x.val = bil.restrict (E i i') (stdBasisE i i' 0) x
  rw [LinearMap.BilinForm.restrict_apply, stdBasisE_0]
  rfl

theorem geomRepAux_i'_restrict_eq_reflect :
  (geomRepAux i').restrict (geomRepAux_E_right i i') = reflect (norm_stdBasisE_1 i i') := by
  ext x : 1
  rw [LinearMap.restrict_apply]
  simp only [LinearEquiv.coe_coe]
  rw [reflect_apply, ←Subtype.coe_inj]
  simp only [Fin.isValue, AddSubgroupClass.coe_sub, SetLike.val_smul, stdBasisE_1]
  rw [geomRepAux_apply]
  congr 3
  change bil (stdBasis i') x.val = bil.restrict (E i i') (stdBasisE i i' 1) x
  rw [LinearMap.BilinForm.restrict_apply, stdBasisE_1]
  rfl

theorem geomRepAux_2_restrict_eq_rotate : ∃ (o : Orientation ℝ (E i i') (Fin 2)),
  (geomRepAux i * geomRepAux i').restrict (geomRepAux_E_2 i i')
  = (o.rotation (2 * π / M i i' : ℝ)).toLinearMap := by
  have h := (inferInstance : Fact (M i i' ≥ 2)).out
  have ⟨o, ho⟩ := oangle_stdBasisE i i'
  exists o
  rw [restrict_geomRepAux_mul, geomRepAux_i_restrict_eq_reflect, geomRepAux_i'_restrict_eq_reflect]
  simp only [Fin.isValue, LinearEquiv.comp_coe, LinearEquiv.toLinearMap_inj]
  rw [reflect_reflect o, Orientation.oangle_rev, ho, ←mul_div]
  conv in 2 • -Angle.coe (π - π / M i i') =>
    rw [Angle.coe_sub, smul_neg, smul_sub, neg_sub, ←Angle.coe_nsmul]
    simp
  rfl

theorem order_geomRepAux_2_eq :
  orderOf (geomRepAux i * geomRepAux i') = M i i' := by
  have h := (inferInstance : Fact (M i i' ≥ 2)).out
  have ⟨o, ho⟩ := geomRepAux_2_restrict_eq_rotate i i'
  have h2 := order_rotation_two_pi_div o (M i i') (by lia)
  rw [orderOf_eq_iff (by lia)] at h2 ⊢
  have rot_pow : ∀ (m : ℕ) (x : E i i'), (o.rotation (Angle.coe (2 * π / M i i')) ^ m) x
    = (⇑(o.rotation (Angle.coe (2 * π / M i i'))))^[m] x := by
    intro m x
    induction m with
    | zero => simp
    | succ m ih =>
        rw [add_comm, pow_add, iterate_add, comp_apply, ←ih]
        rfl
  constructor
  · rw [order_geomRepAux_2_eq_order_restrict, ho]
    ext x : 1
    rw [Module.End.one_apply, Module.End.pow_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, ←rot_pow, h2.1]
    rfl
  · intro m hm1 hm2 h3
    apply h2.2 m hm1 hm2
    rw [order_geomRepAux_2_eq_order_restrict, ho] at h3
    ext x : 1
    have : ((o.rotation (Angle.coe (2 * π / M i i'))).toLinearEquiv.toLinearMap ^ m) x = x := by
      simp_all only [ge_iff_le, LinearEquiv.coe_toLinearMap_mul, ne_eq, Module.End.one_apply]
    rw [Module.End.pow_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] at this
    nth_rw 2 [←this]
    apply rot_pow

end finite_order

theorem geomRepAux_liftable : (@M W).IsLiftable geomRepAux := by
  intro i i'
  have h : M i i' = 0 ∨ M i i' = 1 ∨ M i i' ≥ 2 := by lia
  match h with
  | Or.inl h =>
      rw [h]
      rfl
  | Or.inr (Or.inl h) =>
      rw [h]
      have heq : i = i' := by
        by_contra! h2
        exact M.off_diagonal i i' h2 h
      subst heq
      ext : 1
      apply geomRepAux_involutive i
  | Or.inr (Or.inr h) =>
      haveI : Fact (M i i' ≥ 2) := { out := h }
      rw [←order_geomRepAux_2_eq i i']
      apply pow_orderOf_eq_one

/-- The geometric representation -/
def geomRep : W →* (V W ≃ₗ[ℝ] V W) := cs.lift ⟨geomRepAux, geomRepAux_liftable⟩

theorem geomRep_simple (i : B W) : geomRep (cs.simple i) = geomRepAux i := by
  apply cs.lift_apply_simple

theorem geomRep_simple_apply (i : B W) (x : V W) :
  geomRep (cs.simple i) x = x - (2 * bil (stdBasis i) x) • stdBasis i := by
  rw [geomRep_simple]
  rfl

theorem orderOf_simple_mul_simple (i i' : B W) : orderOf (cs.simple i * cs.simple i') = M i i' := by
  have h : M i i' = 0 ∨ M i i' = 1 ∨ M i i' ≥ 2 := by lia
  match h with
  | Or.inl h =>
      rw [h, orderOf_eq_zero_iff']
      intro n hn
      apply_fun geomRep
      rw [map_pow, map_mul, map_one, geomRep_simple, geomRep_simple]
      intro h2
      have h3 := LinearEquiv.congr_fun h2 (stdBasis i)
      rw [geomRepAux_2_add_of_order_zero i i' h n] at h3
      simp only [smul_add, LinearEquiv.coe_one, id_eq, add_eq_right] at h3
      have h4 : i ≠ i' := by
        intro heq
        rw [heq] at h
        simp at h
      unfold stdBasis at h3
      simp only [coe_basisSingleOne, smul_single, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat,
        mul_one] at h3
      rw [Finsupp.ext_iff] at h3
      specialize h3 i
      simp [h4] at h3
      lia
  | Or.inr (Or.inl h) =>
      have h2 : i = i' := by
        by_contra! h2
        exact M.off_diagonal i i' h2 h
      rw [h2]
      simp
  | Or.inr (Or.inr h) =>
      haveI : Fact (M i i' ≥ 2) := { out := h }
      apply Nat.dvd_antisymm
      · apply orderOf_dvd_of_pow_eq_one
        simp
      · have h2 := orderOf_map_dvd geomRep (cs.simple i * cs.simple i')
        rwa [map_mul, geomRep_simple, geomRep_simple, order_geomRepAux_2_eq i i'] at h2

theorem simple_inj : Injective ((@cs W).simple) := by
  intro i i' h
  by_contra! h2
  apply M.off_diagonal i i' h2
  have : orderOf (cs.simple i * cs.simple i') = 1 := by
    rw [h]
    simp
  rwa [orderOf_simple_mul_simple] at this

end

end Coxeter
