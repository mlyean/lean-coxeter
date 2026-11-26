module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Bilinear lattices

A *bilinear lattice* is `(G, χ, S)`:
- a finitely generated abelian group `G`
- a nondegenerate biadditive `χ : G × G → ℤ`
  (`ker χ = 0`, not necessarily unimodular)
- `S ∈ Aut G` with
  `χ x y = -χ y (S x)`

Morphisms are group homomorphisms `f` with
- `χ' (f x) (f y) = χ x y`
- `f ∘ S = S' ∘ f`

Freeness of `G` and uniqueness of `S` follow from nondegeneracy.

A *bilinear lattice with a distinguished submonoid, subject to the power condition*
(`BilinearLattice.WithMonoidQuasiUnipotent`) additionally carries a submonoid `P ⊆ G`, and `S`
satisfies the power condition
`∃ m ≥ 1, (S ^ m - 1) ^ 2 = 0`.
Neither `m` nor a basis is chosen.
Morphisms additionally must satisfy `f(P) ⊆ P'`.

The power condition says that `S` is
*quasi-unipotent of index at most `2`*:
some positive power
`S ^ m` is unipotent,
and `S ^ m - 1` is square-zero.
This is recorded by `Module.End.IsQuasiUnipotentOfIndex S 2`.

## Main definitions

* `Module.End.IsQuasiUnipotentOfIndex f k`: `(f ^ m - 1) ^ k = 0` for some `m ≥ 1`.
* `Coxeter.BilinearLattice`: the objects `(G, χ, S)`; freeness of `G` is derived, not assumed.
* `Coxeter.BilinearLattice.Hom`: the morphisms, with the `Category` instance.
* `Coxeter.BilinearLattice.Hom.injective`: nondegeneracy forces morphisms to be injective.
* `Coxeter.BilinearLattice.prod`: the orthogonal direct sum `(G ⊕ G', χ ⊥ χ', S ⊕ S')`, giving
  the `SymmetricCategory` instance with zero unit.
* `Coxeter.BilinearLattice.WithMonoidQuasiUnipotent`: the objects `(G, P, χ, S)` with the power
  condition, with the same structure (`P ⊕ P'` on direct sums).
* `Coxeter.BilinearLattice.S_eq_self_of_isRadical`: `S` fixes the radical of `χ + χᵀ`.
* `Coxeter.BilinearLattice.IsPsdQuasiUnipotent`: deferred data, positive semidefinite implies
  quasi-unipotent of index at most `2`.
* `Coxeter.BilinearLattice.ofUnimodular`: the bilinear lattice of a Gram matrix with unit
  determinant, with `S = -C⁻¹ Cᵀ`; `positiveCone` is `ℕⁿ ⊆ ℤⁿ`.
* Faithful forgetful functors `BilinearLattice.forget : BilinearLattice ⥤ ModuleCat ℤ`,
  `WithMonoidQuasiUnipotent.forget : WithMonoidQuasiUnipotent ⥤ BilinearLattice`, and their
  composite `WithMonoidQuasiUnipotent.forgetModuleCat`.
-/

@[expose] public section

universe u

namespace Module.End

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- `f` is *quasi-unipotent of index at most `k`*
if `(f ^ m - 1) ^ k = 0` for some `m ≥ 1` -/
def IsQuasiUnipotentOfIndex (f : Module.End R M) (k : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (f ^ m - 1) ^ k = 0

/-- If `f ^ m - 1` is square-zero then so is `f ^ (m * k) - 1`. -/
lemma pow_mul_sub_one_sq_eq_zero {f : Module.End R M} {m : ℕ} (hf : (f ^ m - 1) ^ 2 = 0)
    (k : ℕ) : (f ^ (m * k) - 1) ^ 2 = 0 := by
  set g := ∑ i ∈ Finset.range k, (f ^ m) ^ i
  calc (f ^ (m * k) - 1) ^ 2 = (g * (f ^ m - 1)) * ((f ^ m - 1) * g) := by
        rw [geom_sum_mul, mul_geom_sum, pow_mul, sq]
    _ = g * (f ^ m - 1) ^ 2 * g := by rw [sq]; simp only [mul_assoc]
    _ = 0 := by rw [hf, mul_zero, zero_mul]

/-- A witness that `f` has infinite order: if `f ^ h` fixes `δ ≠ 0` and translates `v` by `δ`,
then `f ^ (h * k)` translates `v` by `k • δ`, so no power of `f` is `1` (in a torsion-free
module). Hence `f` is not quasi-unipotent of index `1`. -/
theorem not_isQuasiUnipotentOfIndex_one_of_pow_apply [IsAddTorsionFree M] (f : Module.End R M)
    {h : ℕ} (v δ : M) (hδ : (f ^ h) δ = δ) (hv : (f ^ h) v = v + δ) (hδ0 : δ ≠ 0) :
    ¬ IsQuasiUnipotentOfIndex f 1 := by
  rintro ⟨m, hm, h1⟩
  rw [pow_one, sub_eq_zero] at h1
  have hδk : ∀ k : ℕ, ((f ^ h) ^ k) δ = δ := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_apply_eq_self]
    | succ k ih => rw [pow_succ, mul_apply_eq_comp, hδ, ih]
  have hvk : ∀ k : ℕ, ((f ^ h) ^ k) v = v + k • δ := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_apply_eq_self, zero_smul, add_zero]
    | succ k ih => rw [pow_succ, mul_apply_eq_comp, hv, map_add, ih, hδk, succ_nsmul, add_assoc]
  have hvm := hvk m
  rw [← pow_mul, mul_comm, pow_mul, h1, one_pow, one_apply_eq_self, left_eq_add] at hvm
  exact hδ0 ((nsmul_eq_zero_iff_right hm.ne').mp hvm)

/-- An endomorphism of finite order is quasi-unipotent of every positive index. -/
theorem isQuasiUnipotentOfIndex_of_pow_eq_one {f : Module.End R M} {m k : ℕ} (hm : 0 < m)
    (hf : f ^ m = 1) (hk : 0 < k) : IsQuasiUnipotentOfIndex f k :=
  ⟨m, hm, by rw [hf, sub_self, zero_pow hk.ne']⟩

/-- Quasi-unipotence of index at most `2`
is preserved by squaring. -/
theorem IsQuasiUnipotentOfIndex.squaring
    {f : Module.End R M}
    (hf : IsQuasiUnipotentOfIndex f 2)
    : IsQuasiUnipotentOfIndex (f^2) 2 := by
  obtain ⟨m, hm, hf⟩ := hf
  refine ⟨m, hm, ?_⟩
  have hf := pow_mul_sub_one_sq_eq_zero hf 2
  rw [mul_comm, pow_mul] at hf
  exact hf

/-- Quasi-unipotence of index at most `2` is preserved by direct sums. -/
theorem IsQuasiUnipotentOfIndex.prodMap {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
    {f : Module.End R M} {g : Module.End R M₂} (hf : IsQuasiUnipotentOfIndex f 2)
    (hg : IsQuasiUnipotentOfIndex g 2) : IsQuasiUnipotentOfIndex (f.prodMap g) 2 := by
  obtain ⟨m, hm, hf⟩ := hf
  obtain ⟨n, hn, hg⟩ := hg
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have hf := pow_mul_sub_one_sq_eq_zero hf n
  have hg := pow_mul_sub_one_sq_eq_zero hg m
  rw [mul_comm] at hg
  let φ := LinearMap.prodMapRingHom R M M₂
  change (φ (f, g) ^ (m * n) - 1) ^ 2 = 0
  rw [← map_pow, ← map_one φ, ← map_sub, ← map_pow]
  convert map_zero φ
  exact Prod.ext (by simpa using hf) (by simpa using hg)

section CommRing

open Polynomial

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- To show `f` is quasi-unipotent of index at most `k`,
it suffices to find a polynomial
`p` which
- annihilates `f`
- `p ∣ (X ^ m - 1) ^ k` for some `m ≥ 1`. -/
theorem isQuasiUnipotentOfIndex_of_aeval {f : Module.End R M} {k m : ℕ} (hm : 0 < m)
    {p : R[X]} (hp : aeval f p = 0) (hdvd : p ∣ (X ^ m - 1) ^ k) :
    IsQuasiUnipotentOfIndex f k := by
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨m, hm, ?_⟩
  simpa [hp] using congrArg (aeval f) hq

/-- Cayley–Hamilton version:
on a finite free module,
`f` is quasi-unipotent of index at most `k`
if its characteristic polynomial divides
`(X ^ m - 1) ^ k` for some `m ≥ 1`. -/
theorem isQuasiUnipotentOfIndex_of_charpoly_dvd [Module.Free R M] [Module.Finite R M]
    {f : Module.End R M} {k m : ℕ} (hm : 0 < m) (hdvd : f.charpoly ∣ (X ^ m - 1) ^ k) :
    IsQuasiUnipotentOfIndex f k :=
  isQuasiUnipotentOfIndex_of_aeval hm (LinearMap.aeval_self_charpoly f) hdvd

end CommRing

end Module.End

namespace Coxeter

open CategoryTheory

/-- A bilinear lattice:
a finitely generated abelian group `G` with
- a nondegenerate (not necessarily unimodular) `ℤ`-bilinear form `χ`
- an automorphism `S`
satisfying `χ x y = -χ y (S x)`.

Freeness of `G` is not a field:
nondegeneracy forces `G` to be torsion-free -/
structure BilinearLattice where
  /-- The underlying abelian group `G`. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [finite : Module.Finite ℤ carrier]
  /-- The bilinear form `χ`. -/
  χ : LinearMap.BilinForm ℤ carrier
  nondegenerate : χ.Nondegenerate
  /-- The automorphism `S`. -/
  S : carrier ≃ₗ[ℤ] carrier
  χ_S : ∀ x y, χ x y = -χ y (S x)

namespace BilinearLattice

attribute [instance] addCommGroup finite

instance : CoeSort BilinearLattice.{u} (Type u) := ⟨carrier⟩

/-- Nondegeneracy of `χ`
makes the underlying group torsion-free. -/
instance instIsTorsionFree (A : BilinearLattice.{u}) : Module.IsTorsionFree ℤ A where
  isSMulRegular r hr a b hab := by
    rw [← sub_eq_zero]
    refine A.nondegenerate.1 _ fun y ↦ ?_
    have hab : r • a = r • b := hab
    have h : r * A.χ (a - b) y = 0 := by
      rw [← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, smul_sub, hab, sub_self, map_zero,
        LinearMap.zero_apply]
    exact (mul_eq_zero.1 h).resolve_left (isRegular_iff_ne_zero.1 hr)

/-- The underlying group is free, following from above -/
instance (A : BilinearLattice.{u}) : Module.Free ℤ A :=
  Module.free_of_finite_type_torsion_free'

/-- `S` is determined by `χ`
any `T` with `χ x y = -χ y (T x)` equals `S`. -/
theorem eq_S (A : BilinearLattice.{u}) {T : A →ₗ[ℤ] A} (hT : ∀ x y, A.χ x y = -A.χ y (T x)) :
    T = A.S := by
  ext x
  refine sub_eq_zero.1 (A.nondegenerate.2 _ fun y ↦ ?_)
  rw [map_sub, sub_eq_zero, ← neg_inj, ← hT]
  exact A.χ_S x y

/-- A morphism of bilinear lattices:
a group homomorphism `f` with
`χ' (f x) (f y) = χ x y`. -/
@[ext]
structure Hom (A B : BilinearLattice.{u}) where
  /-- The underlying group homomorphism. -/
  toLinearMap : A →ₗ[ℤ] B
  map_χ : ∀ x y, B.χ (toLinearMap x) (toLinearMap y) = A.χ x y

namespace Hom

variable {A B C : BilinearLattice.{u}}

/-- The identity morphism. -/
def id (A : BilinearLattice.{u}) : Hom A A where
  toLinearMap := LinearMap.id
  map_χ _ _ := rfl

/-- Composition of morphisms. -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  map_χ x y := by simp [g.map_χ, f.map_χ]

/-- Nondegeneracy of `χ`
makes every morphism injective. -/
theorem injective (f : Hom A B) : Function.Injective f.toLinearMap := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine A.nondegenerate.1 x fun y ↦ ?_
  rw [← f.map_χ, hx, map_zero, LinearMap.zero_apply]

end Hom

instance : Category BilinearLattice.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
theorem hom_ext {A B : BilinearLattice.{u}} {f g : A ⟶ B}
    (h : f.toLinearMap = g.toLinearMap) : f = g :=
  Hom.ext h

@[simp]
theorem id_toLinearMap (A : BilinearLattice.{u}) :
    (𝟙 A : A ⟶ A).toLinearMap = LinearMap.id :=
  rfl

@[simp]
theorem comp_toLinearMap {A B C : BilinearLattice.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap :=
  rfl

/-- The forgetful functor to `ℤ`-modules,
forgetting `χ` and `S`. -/
@[simps]
def forget : BilinearLattice.{u} ⥤ ModuleCat.{u} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.toLinearMap

instance : forget.Faithful where
  map_injective h := hom_ext (congrArg ModuleCat.Hom.hom h)

/-- Nondegeneracy of `χ` makes
every morphism a monomorphism. -/
instance {A B : BilinearLattice.{u}} (f : A ⟶ B) : Mono f where
  right_cancellation g h w := by
    ext x
    exact Hom.injective f (congrArg (fun k ↦ k.toLinearMap x) w)

/-- Build an isomorphism from
a linear equivalence compatible with `χ` and `S`. -/
@[simps]
def isoMk {A B : BilinearLattice.{u}} (e : A ≃ₗ[ℤ] B) (hχ : ∀ x y, B.χ (e x) (e y) = A.χ x y)
    : A ≅ B where
  hom := ⟨e, hχ⟩
  inv :=
    { toLinearMap := e.symm
      map_χ x y := by rw [← hχ]; simp
    }
  hom_inv_id := hom_ext (LinearMap.ext e.symm_apply_apply)
  inv_hom_id := hom_ext (LinearMap.ext e.apply_symm_apply)

/-! ### Orthogonal direct sum -/

/-- The orthogonal direct sum
`(G ⊕ G', χ ⊥ χ', S ⊕ S')`. -/
def prod (A B : BilinearLattice.{u}) : BilinearLattice.{u} where
  carrier := A × B
  addCommGroup := inferInstanceAs (AddCommGroup (A × B))
  finite := inferInstanceAs (Module.Finite ℤ (A × B))
  χ := A.χ.compl₁₂ (LinearMap.fst ℤ A B) (LinearMap.fst ℤ A B) +
    B.χ.compl₁₂ (LinearMap.snd ℤ A B) (LinearMap.snd ℤ A B)
  nondegenerate := by
    refine ⟨fun x hx ↦ Prod.ext ?_ ?_, fun y hy ↦ Prod.ext ?_ ?_⟩
    · exact A.nondegenerate.1 _ fun y ↦ by simpa using hx (y, 0)
    · exact B.nondegenerate.1 _ fun y ↦ by simpa using hx (0, y)
    · exact A.nondegenerate.2 _ fun x ↦ by simpa using hy (x, 0)
    · exact B.nondegenerate.2 _ fun x ↦ by simpa using hy (0, x)
  S := A.S.prodCongr B.S
  χ_S x y := by
    change A.χ x.1 y.1 + B.χ x.2 y.2 = -(A.χ y.1 (A.S x.1) + B.χ y.2 (B.S x.2))
    rw [A.χ_S, B.χ_S, neg_add]

/-- The zero bilinear lattice, the unit for `prod`. -/
def zero : BilinearLattice.{u} where
  carrier := PUnit
  addCommGroup := inferInstanceAs (AddCommGroup PUnit)
  finite := inferInstanceAs (Module.Finite ℤ PUnit)
  χ := 0
  nondegenerate := ⟨fun _ _ ↦ Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩
  S := LinearEquiv.refl ℤ PUnit
  χ_S _ _ := by simp

/-- The direct sum of two morphisms. -/
def prodMap {A A' B B' : BilinearLattice.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    prod A B ⟶ prod A' B' where
  toLinearMap := f.toLinearMap.prodMap g.toLinearMap
  map_χ x y := by
    change A'.χ (f.toLinearMap x.1) (f.toLinearMap y.1) +
      B'.χ (g.toLinearMap x.2) (g.toLinearMap y.2) = A.χ x.1 y.1 + B.χ x.2 y.2
    rw [f.map_χ, g.map_χ]

instance : MonoidalCategoryStruct BilinearLattice.{u} where
  tensorObj := prod
  whiskerLeft A _ _ g := prodMap (𝟙 A) g
  whiskerRight f B := prodMap f (𝟙 B)
  tensorHom := prodMap
  tensorUnit := zero
  associator A B C := isoMk (LinearEquiv.prodAssoc ℤ A B C)
    (fun _ _ ↦ (add_assoc _ _ _).symm)
  leftUnitor _ := isoMk (LinearEquiv.uniqueProd (M₂ := PUnit))
    (fun _ _ ↦ (zero_add _).symm)
  rightUnitor _ := isoMk (LinearEquiv.prodUnique (M₂ := PUnit))
    (fun _ _ ↦ (add_zero _).symm)

instance : MonoidalCategory BilinearLattice.{u} :=
  .ofTensorHom
    (id_tensorHom_id := fun _ _ ↦ rfl)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := fun _ _ ↦ rfl)
    (tensorHom_comp_tensorHom := fun _ _ _ _ ↦ rfl)
    (associator_naturality := fun _ _ _ ↦ rfl)
    (leftUnitor_naturality := fun _ ↦ rfl)
    (rightUnitor_naturality := fun _ ↦ rfl)
    (pentagon := fun _ _ _ _ ↦ rfl)
    (triangle := fun _ _ ↦ rfl)

/-- The braiding swaps the two summands. -/
instance : SymmetricCategory BilinearLattice.{u} where
  braiding A B := isoMk (LinearEquiv.prodComm ℤ A B) (fun _ _ ↦ add_comm _ _)
  braiding_naturality_right _ _ _ _ := rfl
  braiding_naturality_left _ _ := rfl
  hexagon_forward _ _ _ := rfl
  hexagon_reverse _ _ _ := rfl
  symmetry _ _ := rfl

/-! ### Bilinear lattices with a distinguished submonoid -/

/-- A bilinear lattice with
a distinguished submonoid `P`,
subject to the power condition:
`S` is quasi-unipotent of index at most `2`. -/
structure BilinearLatticeWithMonoidQuasiUnipotent extends BilinearLattice.{u} where
  /-- The distinguished submonoid `P`. -/
  P : AddSubmonoid carrier
  isQuasiUnipotent : Module.End.IsQuasiUnipotentOfIndex (S : Module.End ℤ carrier) 2

namespace WithMonoidQuasiUnipotent

instance : CoeSort BilinearLatticeWithMonoidQuasiUnipotent (Type u) := ⟨fun A ↦ A.carrier⟩

/-- A morphism of bilinear lattices with distinguished submonoids:
a morphism of bilinear lattices `f` with `f(P) ⊆ P'`. -/
structure Hom (A B : BilinearLatticeWithMonoidQuasiUnipotent) extends
    BilinearLattice.Hom A.toBilinearLattice B.toBilinearLattice where
  map_P : ∀ x ∈ A.P, toLinearMap x ∈ B.P

theorem Hom.ext {A B : BilinearLatticeWithMonoidQuasiUnipotent} {f g : Hom A B}
    (h : f.toLinearMap = g.toLinearMap) :
    f = g := by
  obtain ⟨f, _⟩ := f
  obtain ⟨g, _⟩ := g
  congr
  exact BilinearLattice.Hom.ext h

instance : Category BilinearLatticeWithMonoidQuasiUnipotent where
  Hom := Hom
  id A := ⟨BilinearLattice.Hom.id _, fun _ hx ↦ hx⟩
  comp f g := ⟨f.toHom.comp g.toHom, fun x hx ↦ g.map_P _ (f.map_P x hx)⟩

@[ext]
theorem hom_ext {A B : BilinearLatticeWithMonoidQuasiUnipotent} {f g : A ⟶ B}
    (h : f.toLinearMap = g.toLinearMap) :
    f = g :=
  Hom.ext h

@[simp]
theorem id_toLinearMap (A : BilinearLatticeWithMonoidQuasiUnipotent) :
    (𝟙 A : A ⟶ A).toLinearMap = LinearMap.id :=
  rfl

@[simp]
theorem comp_toLinearMap {A B C : BilinearLatticeWithMonoidQuasiUnipotent} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap :=
  rfl

/-- The forgetful functor to bilinear lattices
forgetting `P` and the power condition. -/
@[simps]
def forget : BilinearLatticeWithMonoidQuasiUnipotent ⥤ BilinearLattice.{u} where
  obj A := A.toBilinearLattice
  map f := f.toHom

instance : forget.Faithful where
  map_injective h := hom_ext (congrArg BilinearLattice.Hom.toLinearMap h)

/-- The forgetful functor to `ℤ`-modules
as the composite through `BilinearLattice`. -/
abbrev forgetModuleCat : BilinearLatticeWithMonoidQuasiUnipotent ⥤ ModuleCat.{u} ℤ :=
  forget ⋙ BilinearLattice.forget

/-- Nondegeneracy of `χ`
makes every morphism a monomorphism. -/
instance {A B : BilinearLatticeWithMonoidQuasiUnipotent} (f : A ⟶ B) : Mono f where
  right_cancellation _ _ w := hom_ext <| LinearMap.ext fun x ↦
    BilinearLattice.Hom.injective f.toHom (congrArg (fun k ↦ k.toLinearMap x) w)

/-- Build an isomorphism from
a linear equivalence compatible with `P`, `χ` and `S`. -/
def isoMk {A B : BilinearLatticeWithMonoidQuasiUnipotent}
  (e : A ≃ₗ[ℤ] B)
  (hP : ∀ x, e x ∈ B.P ↔ x ∈ A.P)
  (hχ : ∀ x y, B.χ (e x) (e y) = A.χ x y)
  : A ≅ B where
  hom := ⟨(BilinearLattice.isoMk e hχ).hom, fun x hx ↦ (hP x).2 hx⟩
  inv := ⟨(BilinearLattice.isoMk e hχ).inv, fun y hy ↦ (hP _).1 (by simpa using hy)⟩
  hom_inv_id := hom_ext (LinearMap.ext e.symm_apply_apply)
  inv_hom_id := hom_ext (LinearMap.ext e.apply_symm_apply)

/-- The orthogonal direct sum
`(G ⊕ G', P ⊕ P', χ ⊥ χ', S ⊕ S')`. -/
def prod (A B : BilinearLatticeWithMonoidQuasiUnipotent) :
  BilinearLatticeWithMonoidQuasiUnipotent where
  toBilinearLattice := A.toBilinearLattice.prod B.toBilinearLattice
  P := A.P.prod B.P
  isQuasiUnipotent := A.isQuasiUnipotent.prodMap B.isQuasiUnipotent

/-- The zero bilinear lattice, the unit for `prod`. -/
def zero : BilinearLatticeWithMonoidQuasiUnipotent where
  toBilinearLattice := BilinearLattice.zero
  P := ⊤
  isQuasiUnipotent := ⟨1, one_pos, LinearMap.ext fun _ ↦ Subsingleton.elim (α := PUnit) _ _⟩

/-- The direct sum of two morphisms. -/
def prodMap {A A' B B' : BilinearLatticeWithMonoidQuasiUnipotent} (f : A ⟶ A') (g : B ⟶ B') :
    prod A B ⟶ prod A' B' :=
  ⟨BilinearLattice.prodMap f.toHom g.toHom, fun _ hx ↦ ⟨f.map_P _ hx.1, g.map_P _ hx.2⟩⟩

instance : MonoidalCategoryStruct BilinearLatticeWithMonoidQuasiUnipotent where
  tensorObj := prod
  whiskerLeft A _ _ g := prodMap (𝟙 A) g
  whiskerRight f B := prodMap f (𝟙 B)
  tensorHom := prodMap
  tensorUnit := zero
  associator A B C := isoMk (LinearEquiv.prodAssoc ℤ A B C)
    (fun _ ↦ and_assoc.symm) (fun _ _ ↦ (add_assoc _ _ _).symm)
  leftUnitor _ := isoMk (LinearEquiv.uniqueProd (M₂ := PUnit))
    (fun _ ↦ Iff.of_eq (true_and _).symm) (fun _ _ ↦ (zero_add _).symm)
  rightUnitor _ := isoMk (LinearEquiv.prodUnique (M₂ := PUnit))
    (fun _ ↦ Iff.of_eq (and_true _).symm) (fun _ _ ↦ (add_zero _).symm)

instance : MonoidalCategory BilinearLatticeWithMonoidQuasiUnipotent :=
  .ofTensorHom
    (id_tensorHom_id := fun _ _ ↦ rfl)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := fun _ _ ↦ rfl)
    (tensorHom_comp_tensorHom := fun _ _ _ _ ↦ rfl)
    (associator_naturality := fun _ _ _ ↦ rfl)
    (leftUnitor_naturality := fun _ ↦ rfl)
    (rightUnitor_naturality := fun _ ↦ rfl)
    (pentagon := fun _ _ _ _ ↦ rfl)
    (triangle := fun _ _ ↦ rfl)

/-- The braiding swaps the two summands. -/
instance : SymmetricCategory BilinearLatticeWithMonoidQuasiUnipotent where
  braiding A B := isoMk (LinearEquiv.prodComm ℤ A B)
    (fun _ ↦ and_comm) (fun _ _ ↦ add_comm _ _)
  braiding_naturality_right _ _ _ _ := rfl
  braiding_naturality_left _ _ := rfl
  hexagon_forward _ _ _ := rfl
  hexagon_reverse _ _ _ := rfl
  symmetry _ _ := rfl

end WithMonoidQuasiUnipotent


/-! ### Isometry and the radical -/

/-- `S` is an isometry of `χ`. -/
theorem χ_S_S (A : BilinearLattice.{u}) (x y : A) :
  A.χ (A.S x) (A.S y) = A.χ x y := by
  rw [A.χ_S x y, A.χ_S y (A.S x), neg_neg]

/-- `r` lies in the radical of
the symmetrization `χ x y + χ y x`. -/
def IsRadical (A : BilinearLattice.{u}) (r : A) : Prop :=
  ∀ y, A.χ r y + A.χ y r = 0

/-- `S` fixes the radical
of the symmetrized form pointwise. -/
theorem S_eq_self_of_isRadical (A : BilinearLattice.{u}) {r : A} (hr : A.IsRadical r) :
    A.S r = r := by
  refine sub_eq_zero.1 (A.nondegenerate.2 _ fun x ↦ ?_)
  rw [map_sub, sub_eq_zero, ← neg_inj, ← A.χ_S r x]
  linarith [hr x]

/-- Deferred data:
when the symmetrized form is positive semidefinite
`S` is quasi-unipotent of index at most `2`
and of index `1` (finite order) when
it is positive definite.

These hold for every bilinear lattice:
- `S` preserves the symmetrized form `q` (`χ_S_S`)
- `S` fixes its radical `R` (`S_eq_self_of_isRadical`)

Using the positive semidefiniteness,
on `G / R` the form `q` is positive definite, so its
isometry group is finite and some `S ^ m` is the identity there
Therefore `S ^ m - 1` maps `G` into `R` and kills `R`.

The finiteness of the isometry group of a positive definite lattice is the
heavy step, so the result is supplied as an instance rather than proved here. -/
class IsPsdQuasiUnipotent (A : BilinearLattice.{u}) : Prop where
  quasiUnipotent_of_nonneg :
    (∀ x, 0 ≤ A.χ x x) → Module.End.IsQuasiUnipotentOfIndex (A.S : Module.End ℤ A) 2
  quasiUnipotent_of_pos :
    (∀ x, x ≠ 0 → 0 < A.χ x x) → Module.End.IsQuasiUnipotentOfIndex (A.S : Module.End ℤ A) 1

/-! ### Bilinear lattices from Gram matrices -/

section Matrix

open Matrix

variable {n : ℕ}

/-- The bilinear lattice on `Fin n → ℤ`
with Gram matrix `C`, where `det C` is a unit.
Its Coxeter transformation is `S = -C⁻¹ Cᵀ`. -/
@[implicit_reducible]
noncomputable def ofUnimodular (C : Matrix (Fin n) (Fin n) ℤ) (hC : IsUnit C.det) :
    BilinearLattice.{0} where
  carrier := Fin n → ℤ
  addCommGroup := inferInstanceAs (AddCommGroup (Fin n → ℤ))
  finite := inferInstanceAs (Module.Finite ℤ (Fin n → ℤ))
  χ := Matrix.toLinearMap₂' ℤ C
  nondegenerate := (LinearMap.nondegenerate_toLinearMap₂'_iff_det_ne_zero).2 hC.ne_zero
  S := (-(C⁻¹ * Cᵀ)).toLinearEquiv' <| invertibleOfRightInverse _ (-(Cᵀ⁻¹ * C)) <| by
    have hCt : IsUnit Cᵀ.det := by rwa [det_transpose]
    rw [neg_mul_neg, Matrix.mul_assoc, ← Matrix.mul_assoc Cᵀ, mul_nonsing_inv _ hCt,
      Matrix.one_mul, nonsing_inv_mul _ hC]
  χ_S x y := by
    rw [toLinearMap₂'_apply', toLinearMap₂'_apply']
    change _ = -(y ⬝ᵥ (C *ᵥ ((-(C⁻¹ * Cᵀ)) *ᵥ x)))
    rw [mulVec_mulVec, Matrix.mul_neg, ← Matrix.mul_assoc, mul_nonsing_inv _ hC, Matrix.one_mul,
      neg_mulVec, dotProduct_neg, neg_neg, dotProduct_mulVec y, vecMul_transpose,
      dotProduct_comm]

theorem ofUnimodular_χ_apply
  (C : Matrix (Fin n) (Fin n) ℤ)
  (hC : IsUnit C.det) (x y : Fin n → ℤ) :
  (ofUnimodular C hC).χ x y = x ⬝ᵥ (C *ᵥ y) :=
  toLinearMap₂'_apply' C x y

/-- The Coxeter transformation of `ofUnimodular C hC` is characterized by `C (S x) = -Cᵀ x`. -/
theorem ofUnimodular_S_eq_iff
  (C : Matrix (Fin n) (Fin n) ℤ)
  (hC : IsUnit C.det) (x z : Fin n → ℤ) :
  (ofUnimodular C hC).S x = z ↔ C *ᵥ z = -(Cᵀ *ᵥ x) := by
  change (-(C⁻¹ * Cᵀ)) *ᵥ x = z ↔ _
  constructor
  · rintro rfl
    rw [mulVec_mulVec, Matrix.mul_neg, ← Matrix.mul_assoc, mul_nonsing_inv _ hC, Matrix.one_mul,
      neg_mulVec]
  · intro h
    rw [neg_mulVec, ← mulVec_mulVec, ← mulVec_neg, ← h, mulVec_mulVec, nonsing_inv_mul _ hC,
      one_mulVec]

/-- If `C * Q = -Cᵀ` then `Q` is the matrix of the Coxeter transformation of
`ofUnimodular C hC`, so `S ^ m = 1` as soon as `Q ^ m = 1`. -/
theorem ofUnimodular_S_pow_eq_one
  (C : Matrix (Fin n) (Fin n) ℤ)
  (hC : IsUnit C.det) (Q : Matrix (Fin n) (Fin n) ℤ) (hQ : C * Q = -Cᵀ) {m : ℕ}
  (hm : Q ^ m = 1) :
  ((ofUnimodular C hC).S : Module.End ℤ (ofUnimodular C hC)) ^ m = 1 := by
  have hS : ((ofUnimodular C hC).S : Module.End ℤ (ofUnimodular C hC)) = Matrix.toLin' Q :=
    LinearMap.ext fun (x : Fin n → ℤ) ↦
      (ofUnimodular_S_eq_iff C hC x (Q *ᵥ x)).2 (by rw [mulVec_mulVec, hQ, neg_mulVec])
  have h := Matrix.toLin'_pow Q m
  rw [hm, Matrix.toLin'_one] at h
  rw [hS]
  exact h.symm

/-- If `C * Q = -Cᵀ`
then the Coxeter transformation `S`
of `ofUnimodular C hC` is `Q`, viewed as an
endomorphism through the algebra equivalence
`Matrix.toLinAlgEquiv'`. -/
theorem ofUnimodular_S_eq_toLinAlgEquiv'
  (C : Matrix (Fin n) (Fin n) ℤ)
  (hC : IsUnit C.det) (Q : Matrix (Fin n) (Fin n) ℤ) (hQ : C * Q = -Cᵀ) :
  ((ofUnimodular C hC).S : Module.End ℤ (ofUnimodular C hC)) = Matrix.toLinAlgEquiv' Q :=
  LinearMap.ext fun (x : Fin n → ℤ) ↦
    ((ofUnimodular_S_eq_iff C hC x (Q *ᵥ x)).2 (by rw [mulVec_mulVec, hQ, neg_mulVec])).trans
      (Matrix.toLinAlgEquiv'_apply Q x).symm

/-- If `C * Q = -Cᵀ` and `Q ^ m - 1` is square-zero for some `m > 0`,
then the Coxeter transformation of `ofUnimodular C hC` is quasi-unipotent of index `2`. -/
theorem ofUnimodular_isQuasiUnipotentOfIndex_two
  (C : Matrix (Fin n) (Fin n) ℤ)
  (hC : IsUnit C.det) (Q : Matrix (Fin n) (Fin n) ℤ) (hQ : C * Q = -Cᵀ) {m : ℕ} (hm : 0 < m)
  (h : (Q ^ m - 1) ^ 2 = 0) :
  Module.End.IsQuasiUnipotentOfIndex
    ((ofUnimodular C hC).S : Module.End ℤ (ofUnimodular C hC)) 2 := by
  refine ⟨m, hm, ?_⟩
  have key : (Matrix.toLinAlgEquiv' Q ^ m - 1) ^ 2 = (0 : Module.End ℤ (Fin n → ℤ)) := by
    rw [← map_pow, ← map_one Matrix.toLinAlgEquiv', ← map_sub, ← map_pow, h, map_zero]
  rw [ofUnimodular_S_eq_toLinAlgEquiv' C hC Q hQ]
  exact key

/-- A witness that the Coxeter transformation has infinite order:
if `Q ^ h` fixes `δ ≠ 0` and
translates `v` by `δ`, then `Q ^ (h * k)` translates `v` by `k • δ`.
So no power of `Q` is `1`.
Hence the Coxeter transformation of `ofUnimodular C hC` is not quasi-unipotent of index `1`. -/
theorem ofUnimodular_not_isQuasiUnipotentOfIndex_one
  (C : Matrix (Fin n) (Fin n) ℤ)
  (hC : IsUnit C.det) (Q : Matrix (Fin n) (Fin n) ℤ) (hQ : C * Q = -Cᵀ) {h : ℕ}
  (v δ : Fin n → ℤ) (hδ : Q ^ h *ᵥ δ = δ) (hv : Q ^ h *ᵥ v = v + δ) (hδ0 : δ ≠ 0) :
  ¬ Module.End.IsQuasiUnipotentOfIndex
    ((ofUnimodular C hC).S : Module.End ℤ (ofUnimodular C hC)) 1 := by
  rintro ⟨m, hm, h1⟩
  rw [pow_one, sub_eq_zero, ofUnimodular_S_eq_toLinAlgEquiv' C hC Q hQ] at h1
  have h1' : Matrix.toLinAlgEquiv' Q ^ m = (1 : Module.End ℤ (Fin n → ℤ)) := h1
  rw [← map_pow, ← map_one Matrix.toLinAlgEquiv'] at h1'
  have hQm : Q ^ m = 1 := Matrix.toLinAlgEquiv'.injective h1'
  have hδk : ∀ k : ℕ, (Q ^ h) ^ k *ᵥ δ = δ := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_mulVec]
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hδ, ih]
  have hvk : ∀ k : ℕ, (Q ^ h) ^ k *ᵥ v = v + (k : ℤ) • δ := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_mulVec, Nat.cast_zero, zero_smul, add_zero]
    | succ k ih =>
        rw [pow_succ, ← mulVec_mulVec, hv, mulVec_add, ih, hδk, Nat.cast_succ, add_smul, one_smul,
          add_assoc]
  have hvm := hvk m
  rw [← pow_mul, mul_comm, pow_mul, hQm, one_pow, one_mulVec, left_eq_add] at hvm
  rcases smul_eq_zero.mp hvm with h0 | h0
  · exact absurd (Int.ofNat_eq_zero.mp h0) hm.ne'
  · exact hδ0 h0

/-- The cone of dimension vectors `ℕⁿ ⊆ ℤⁿ`. -/
def positiveCone (n : ℕ) : AddSubmonoid (Fin n → ℤ) where
  carrier := {x | ∀ i, 0 ≤ x i}
  add_mem' hx hy i := add_nonneg (hx i) (hy i)
  zero_mem' _ := le_rfl

/-- The bilinear lattice on `Fin n → ℤ`
with Gram matrix `C`, where `det C` is a unit
and that it is positive semidefinite.
Its Coxeter transformation is `S = -C⁻¹ Cᵀ`.
This gives an object of `BilinearLatticeWithMonoidQuasiUnipotent`
with distinguished submonoid `ℕⁿ ⊆ ℤⁿ` and
quasi-unipotence of index at most `2`
from the positive semidefinite condition. -/
noncomputable def ofUnimodularWithMonoidQuasiUnipotent
  (C : Matrix (Fin n) (Fin n) ℤ)
  (hC : IsUnit C.det)
  (hC2 : ∀ x, 0 ≤ x ⬝ᵥ (C *ᵥ x))
  [hA : IsPsdQuasiUnipotent (ofUnimodular C hC)]
:
    BilinearLatticeWithMonoidQuasiUnipotent where
  toBilinearLattice := ofUnimodular C hC
  P := positiveCone n
  isQuasiUnipotent := hA.quasiUnipotent_of_nonneg fun (x : Fin n → ℤ) ↦ by
    simp only [ofUnimodular_χ_apply, hC2]

end Matrix

end BilinearLattice

end Coxeter
