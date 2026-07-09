module

public import Coxeter.GeometricRepresentation
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Components of a Coxeter system

`Coxeter.IsComponentOf cg1 cg` records that `cg1` is identified with one connected component of
`cg`'s Coxeter diagram: a bijection between `cg1`'s generators and the generators lying in that
component, together with a group homomorphism sending simple reflections to simple reflections
accordingly.

This is *data*, not a theorem: none of the fields are derived from more primitive facts about
Coxeter groups (e.g. `toHom` is not asserted or proved to be injective).

## Main definitions

* `Coxeter.IsComponentOf`
-/

@[expose] public section

namespace Coxeter

/-- The graph on generators with an edge between `i ≠ i'` whenever `M i i' ≠ 2` (the two simple
reflections don't commute) — the *Coxeter diagram*, as a `SimpleGraph`. -/
def coxeterGraphMatrix {B1 : Type*} (M1 : CoxeterMatrix B1) :
  SimpleGraph B1 := SimpleGraph.fromRel (M1 · · ≠ 2)

/-- `cg1 IsComponentOf cg`: data identifying `cg1` with one connected component of `cg`'s Coxeter
diagram — a bijection between `cg1`'s generators and the generators lying in that component,
together with a group homomorphism `W1 →* W` sending each simple reflection of `cg1` to the
simple reflection of `cg` at the corresponding generator. -/
structure IsComponentOf {W1 : Type*} (cg1 : CoxeterGroup W1) {W : Type*} (cg : CoxeterGroup W)
    where
  /-- The connected component of `cg`'s Coxeter diagram that `cg1` is identified with. -/
  component : (coxeterGraphMatrix cg.M).ConnectedComponent
  /-- The identification of `cg1`'s generators with the generators lying in `component`. -/
  reindex : cg1.B ≃ component.supp
  /-- The group homomorphism realizing `W1` inside `W`. -/
  toHom : W1 →* W
  /-- `toHom` sends each simple reflection of `cg1` to the simple reflection of `cg` at the
  corresponding (via `reindex`) generator. -/
  map_simple : ∀ i : cg1.B, toHom (cg1.cs.simple i) = cg.cs.simple (reindex i : cg.B)

/-- The Coxeter matrix on the generators of `cg` lying in a single connected component `c` of
`cg`'s Coxeter diagram, obtained by restricting `cg.M`. -/
def componentMatrix {W : Type*} (cg : CoxeterGroup W)
    (c : (coxeterGraphMatrix cg.M).ConnectedComponent) : CoxeterMatrix c.supp where
  M a b := cg.M a.1 b.1
  isSymm := Matrix.IsSymm.ext_iff.mpr (fun a b => cg.M.symmetric b.1 a.1)
  diagonal a := cg.M.diagonal a.1
  off_diagonal a b hab := cg.M.off_diagonal a.1 b.1 (fun h => hab (Subtype.ext h))

/-- The Coxeter group of `componentMatrix cg c`, presented as the quotient of the free group on
that component's generators by the relevant relations coming from `cg.M`. -/
@[reducible] noncomputable def componentCoxeterGroup {W : Type*} (cg : CoxeterGroup W)
    (c : (coxeterGraphMatrix cg.M).ConnectedComponent) :
    CoxeterGroup (componentMatrix cg c).Group where
  B := c.supp
  M := componentMatrix cg c
  cs := (componentMatrix cg c).toCoxeterSystem

/-- `componentCoxeterGroup cg c` is a component of `cg`, in the sense of `IsComponentOf`: its
generators literally *are* `c.supp` (so `reindex` is the identity), and the group homomorphism is
the one induced by the universal property of the presented group, sending each generator to the
simple reflection of `cg` at the corresponding point of `c` — so `toHom` and `map_simple` are both
immediate from the construction, via `CoxeterSystem.lift_apply_simple`. -/
noncomputable def ofComponent {W : Type*} (cg : CoxeterGroup W)
    (c : (coxeterGraphMatrix cg.M).ConnectedComponent) :
    IsComponentOf (componentCoxeterGroup cg c) cg where
  component := c
  reindex := Equiv.refl _
  toHom := (componentMatrix cg c).toCoxeterSystem.lift
    ⟨fun a => cg.cs.simple a.1, fun a b => cg.cs.simple_mul_simple_pow a.1 b.1⟩
  map_simple a := (componentMatrix cg c).toCoxeterSystem.lift_apply_simple
    (fun a b => cg.cs.simple_mul_simple_pow a.1 b.1) a

/-- Every connected component of `cg`'s Coxeter diagram, each paired with the witness that its
associated Coxeter group is a component of `cg`. Assumes finitely many components. -/
noncomputable def allComponents {W : Type*} (cg : CoxeterGroup W)
    [Finite (coxeterGraphMatrix cg.M).ConnectedComponent] :
    List (Σ c : (coxeterGraphMatrix cg.M).ConnectedComponent,
      IsComponentOf (componentCoxeterGroup cg c) cg) :=
  haveI := Fintype.ofFinite (coxeterGraphMatrix cg.M).ConnectedComponent
  Finset.univ.toList.map (fun c => ⟨c, ofComponent cg c⟩)

/-- The generating set of `cg` is, as a type, the disjoint union of its connected components. -/
def blockEquiv {W : Type*} (cg : CoxeterGroup W) :
    (Σ c : (coxeterGraphMatrix cg.M).ConnectedComponent, c.supp) ≃ cg.B :=
  Equiv.sigmaFiberEquiv (coxeterGraphMatrix cg.M).connectedComponentMk

/-- `cg.M` is *block diagonal* along the partition of generators into connected components: two
generators from different components always commute (`M i i' = 2`), since a diagram edge would put
them in the same component. -/
theorem M_eq_two_of_connectedComponentMk_ne {W : Type*} (cg : CoxeterGroup W) {i i' : cg.B}
    (h : (coxeterGraphMatrix cg.M).connectedComponentMk i ≠
      (coxeterGraphMatrix cg.M).connectedComponentMk i') :
    cg.M i i' = 2 := by
  have hii' : i ≠ i' := fun heq =>
    h (congrArg (coxeterGraphMatrix cg.M).connectedComponentMk heq)
  have hadj : ¬ (coxeterGraphMatrix cg.M).Adj i i' :=
    fun hadj => h (SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable)
  have hadj' : ¬ (i ≠ i' ∧ (cg.M i i' ≠ 2 ∨ cg.M i' i ≠ 2)) := hadj
  push Not at hadj'
  exact (hadj' hii').1

/-- Generators within the same component agree with `componentMatrix`, definitionally: the "block"
of `cg.M` on component `c` is exactly `componentMatrix cg c`. -/
theorem M_eq_componentMatrix {W : Type*} (cg : CoxeterGroup W)
    (c : (coxeterGraphMatrix cg.M).ConnectedComponent) (i i' : c.supp) :
    cg.M i.1 i'.1 = componentMatrix cg c i i' := rfl

/-- `bil` is manifestly built entrywise from `cos (π / M i i')` (see `bil`'s definition via
`Matrix.toBilin`), so — for exactly the same reason as `M_eq_two_of_connectedComponentMk_ne` — it
vanishes on pairs of standard basis vectors from different connected components. This is the
"direct sum" structure of `bil` across components: cross-component terms never contribute. -/
theorem bil_stdBasis_eq_zero_of_connectedComponentMk_ne {W : Type*} (cg : CoxeterGroup W)
    {i i' : cg.B}
    (h : (coxeterGraphMatrix cg.M).connectedComponentMk i ≠
      (coxeterGraphMatrix cg.M).connectedComponentMk i') :
    (@bil W cg) (stdBasis i) (stdBasis i') = 0 := by
  unfold bil
  rw [Matrix.toBilin_single, M_eq_two_of_connectedComponentMk_ne cg h]
  norm_num

/-- The other half of the "direct sum" structure of `bil`, alongside
`bil_stdBasis_eq_zero_of_connectedComponentMk_ne`: on a single connected component, `bil` agrees
exactly with that component's own `bil` — again immediate from `bil`'s entrywise definition via
`M`, this time using `M_eq_componentMatrix` instead of `M_eq_two_of_connectedComponentMk_ne`. -/
theorem bil_stdBasis_eq_of_mem_component {W : Type*} (cg : CoxeterGroup W)
    (c : (coxeterGraphMatrix cg.M).ConnectedComponent) (i i' : c.supp) :
    (@bil W cg) (stdBasis i.1) (stdBasis i'.1) =
    (@bil _ (componentCoxeterGroup cg c))
      (@stdBasis _ (componentCoxeterGroup cg c) i)
        (@stdBasis _ (componentCoxeterGroup cg c) i') := by
  unfold bil
  repeat rw [Matrix.toBilin_single]
  rfl

open Classical in
/-- `bil` is *block diagonal*, on the level of the underlying symmetric matrix: transported along
`blockEquiv` (reindexing `stdBasis` by the disjoint-union-of-components identification), the
matrix of `bil` at `⟨c, i⟩, ⟨c', i'⟩` is `0` when `c ≠ c'`
(`bil_stdBasis_eq_zero_of_connectedComponentMk_ne`), and is the matrix of component `c`'s own
`bil` when `c = c'` (`bil_stdBasis_eq_of_mem_component`). -/
theorem bil_toMatrix_blockEquiv_apply {W : Type*} (cg : CoxeterGroup W)
    (c c' : (coxeterGraphMatrix cg.M).ConnectedComponent) (i : c.supp) (i' : c'.supp) :
    (LinearMap.BilinForm.toMatrix (stdBasis.reindex (blockEquiv cg).symm)) (@bil W cg)
        ⟨c, i⟩ ⟨c', i'⟩ =
      if h : c = c' then
        (LinearMap.BilinForm.toMatrix (@stdBasis _ (componentCoxeterGroup cg c)))
          (@bil _ (componentCoxeterGroup cg c)) i (h ▸ i')
      else 0 := by
  have key : (LinearMap.BilinForm.toMatrix (stdBasis.reindex (blockEquiv cg).symm)) (@bil W cg)
      ⟨c, i⟩ ⟨c', i'⟩ = (@bil W cg) (stdBasis i.1) (stdBasis i'.1) := by
    unfold LinearMap.BilinForm.toMatrix
    simp only [Module.Basis.reindex_apply, blockEquiv]
    simp only [Equiv.symm_symm, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    have keyL := Equiv.sigmaFiberEquiv_apply
      (f:=(coxeterGraphMatrix cg.M).connectedComponentMk)
      (x:=⟨c, i⟩)
    have keyR := Equiv.sigmaFiberEquiv_apply
      (f:=(coxeterGraphMatrix cg.M).connectedComponentMk)
      (x:=⟨c', i'⟩)
    erw [keyL, keyR]
  rw [key]
  by_cases h : c = c'
  · subst h
    rw [dif_pos rfl]
    exact bil_stdBasis_eq_of_mem_component cg c i i'
  · rw [dif_neg h]
    exact bil_stdBasis_eq_zero_of_connectedComponentMk_ne cg (by rw [i.2, i'.2]; exact h)

open Classical in
/-- `bil` **is** a direct sum: the matrix of `bil` (in the `blockEquiv`-reindexed basis) is
exactly `Matrix.blockDiagonal'` of the components' own `bil` matrices — mathlib's standard
"block diagonal matrix" construction, built entrywise from `bil_toMatrix_blockEquiv_apply`. -/
theorem bil_toMatrix_blockEquiv_eq_blockDiagonal' {W : Type*} (cg : CoxeterGroup W) :
    LinearMap.BilinForm.toMatrix (stdBasis.reindex (blockEquiv cg).symm) (@bil W cg) =
      Matrix.blockDiagonal' (fun c : (coxeterGraphMatrix cg.M).ConnectedComponent =>
        LinearMap.BilinForm.toMatrix (@stdBasis _ (componentCoxeterGroup cg c))
          (@bil _ (componentCoxeterGroup cg c))) := by
  funext ⟨c, i⟩ ⟨c', i'⟩
  rw [bil_toMatrix_blockEquiv_apply cg c c' i i', Matrix.blockDiagonal'_apply']
  by_cases h : c = c'
  · subst h
    rw [dif_pos rfl, dif_pos rfl]
    congr!
  · rw [dif_neg h, dif_neg h]

/-- `P` *assembles* across connected components: whenever `cg` has finitely many components and
`P` holds of the Coxeter group of each individual component, `P` already holds of `cg` itself.

`P` is required to apply to `CoxeterGroup.{v, v}`, i.e. Coxeter groups whose underlying group and
generating set live in the *same* universe `v` — this is forced by `componentCoxeterGroup`, whose
underlying group `(componentMatrix cg c).Group` always lives in the universe of `cg.B`, not of
`W`, so `cg` itself must already have `W` and `B` in that common universe for `P` to apply to both
`cg` and all of its components uniformly. -/
def Assembles (P : ∀ {W : Type v}, CoxeterGroup.{v, v} W → Prop) : Prop :=
  ∀ {W : Type v} (cg : CoxeterGroup.{v, v} W)
    [Finite (coxeterGraphMatrix cg.M).ConnectedComponent],
    (∀ c : (coxeterGraphMatrix cg.M).ConnectedComponent, P (componentCoxeterGroup cg c)) → P cg

lemma assembles_combination
  (P Q : ∀ {W : Type v}, CoxeterGroup.{v, v} W → Prop) :
  Assembles P -> Assembles Q -> Assembles (fun x => P x ∧ Q x) := by
  intro assembles_P assembles_Q W cg finiteness on_components_PQ
  have on_componentsP' : ∀ c : (coxeterGraphMatrix cg.M).ConnectedComponent,
    P (componentCoxeterGroup cg c) := by
    intro c
    have key := on_components_PQ c
    simp at key
    exact key.left
  have on_componentsQ' : ∀ c : (coxeterGraphMatrix cg.M).ConnectedComponent,
    Q (componentCoxeterGroup cg c) := by
    intro c
    have key := on_components_PQ c
    simp at key
    exact key.right
  have p_part := assembles_P cg on_componentsP'
  have q_part := assembles_Q cg on_componentsQ'
  exact And.intro p_part q_part

end Coxeter
