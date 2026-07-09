module

public import Coxeter.GeometricRepresentation
public import Coxeter.Component
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Special features of Coxeter systems

This file collects propositions singling out special classes of Coxeter systems.
`IsRightAngled`/`IsCrystallographic` are readable directly off the entries of a Coxeter matrix with
only minimal arithmetic (they don't need a group at all, only `CoxeterMatrix ι`);
`IsFiniteCoxeter`/`IsPolyFiniteWeyl`/`IsAffineCoxeter`/`IsPolyAffineWeyl` instead bundle the genuine
(semi)definiteness of the associated bilinear form `bil`, since that classification isn't
entrywise-arithmetic in nature.
None of these require the Coxeter diagram to be connected
(irreducible);
The `Poly` prefix on `IsPolyFiniteWeyl`/`IsPolyAffineWeyl` signals that they allow a
*product* of several irreducible finite/affine Weyl groups, not just a single irreducible one.

Each definition's docstring below also records how it interacts with the connected components of
the Coxeter diagram (writing `component_cg` for the sub-Coxeter-system obtained by restricting to
one component): whether *descent* holds (`cg.IsX → component_cg.IsX` for every component), and
whether *assembly* holds (`component_cg.IsX` for every component `⟹ cg.IsX`). This matters because
generators in different components automatically have `M i i' = 2`, hence
`bil (stdBasis i) (stdBasis i') = -cos (π / 2) = 0`: the diagram's components correspond to an
orthogonal direct sum decomposition of `bil`.

## Main definitions

* `Coxeter.IsRightAngled`
* `Coxeter.IsCrystallographic`
* `Coxeter.IsIrreducible`
* `Coxeter.IsFiniteCoxeter`
* `Coxeter.IsPolyFiniteWeyl`
* `Coxeter.IsIrreducibleFiniteWeyl`
* `Coxeter.IsAffineCoxeter`
* `Coxeter.IsIrreducibleAffineCoxeter`
* `Coxeter.IsPolyAffineWeyl`
* `Coxeter.IsIrreducibleAffineWeyl`
-/

@[expose] public section

namespace Coxeter

open Finsupp CoxeterGroup CoxeterSystem

variable {W : Type*} {cg : CoxeterGroup W}

/-- A Coxeter matrix is *right-angled* if every pair of distinct generators either commutes
(`M i i' = 2`) or generates an infinite dihedral subgroup (`M i i' = 0`) — i.e. no relation of
order `3` or more ever occurs between two distinct generators.

- Descent: holds. This is a `∀` over pairs of generators, so it restricts to any subset for free.
- Assembly: holds. `assembles_rightAngled` -/
def IsRightAngled : Prop := ∀ i i' : B W, i ≠ i' → M i i' = 2 ∨ M i i' = 0

/-
Generators in different components already have `M i i' = 2`, which satisfies
the disjunction for free, so `cg.IsRightAngled` holds iff every component does.
-/
lemma assembles_rightAngled :
  Assembles
    fun [W1 : Type*] (cg1 : CoxeterGroup W1) => @IsRightAngled W1 cg1
  := by
  unfold Assembles
  intro W1 cg1 finitely_many_comp on_components
  unfold IsRightAngled
  set cg1_graph := coxeterGraphMatrix cg1.M
  intro i i' hii'
  by_cases same_comp : cg1_graph.Reachable i i'
  · set c := cg1_graph.connectedComponentMk i
    have hi : i ∈ c.supp := rfl
    have hi' : i' ∈ c.supp := (SimpleGraph.ConnectedComponent.sound same_comp).symm
    have hne : (⟨i, hi⟩ : c.supp) ≠ ⟨i', hi'⟩ := fun h => hii' (congrArg Subtype.val h)
    exact on_components c ⟨i, hi⟩ ⟨i', hi'⟩ hne
  · exact Or.inl (M_eq_two_of_connectedComponentMk_ne cg1
      (fun heq => same_comp (SimpleGraph.ConnectedComponent.eq.mp heq)))

/-- A Coxeter matrix is *crystallographic* if every pair of distinct generators either generates an
infinite dihedral subgroup (`M i i' = 0`) or one of order `2 * M i i'` for `M i i' ∈ {2, 3, 4, 6}`
— the restriction on dihedral angles forced by requiring the reflections to preserve a lattice.

- Descent: holds, for the same reason as `IsRightAngled` — a `∀` over pairs restricts freely.
- Assembly: holds. `assembles_crystallographic` -/
def IsCrystallographic : Prop :=
  ∀ i i' : cg.B, i ≠ i' →
    cg.M i i' = 0 ∨ cg.M i i' = 2 ∨
    cg.M i i' = 3 ∨ cg.M i i' = 4 ∨ cg.M i i' = 6

/-
Cross-component entries are `2 ∈ {0, 2, 3, 4, 6}` for free, so
`cg.IsCrystallographic` holds iff every component does.
-/
lemma assembles_crystallographic :
  Assembles
    fun [W1 : Type*] (cg1 : CoxeterGroup W1) => @IsCrystallographic W1 cg1
  := by
  unfold Assembles
  intro W1 cg1 finitely_many_comp on_components
  unfold IsCrystallographic
  set cg1_graph := coxeterGraphMatrix cg1.M
  intro i i' hii'
  by_cases same_comp : cg1_graph.Reachable i i'
  · set c := cg1_graph.connectedComponentMk i
    have hi : i ∈ c.supp := rfl
    have hi' : i' ∈ c.supp := (SimpleGraph.ConnectedComponent.sound same_comp).symm
    have hne : (⟨i, hi⟩ : c.supp) ≠ ⟨i', hi'⟩ := fun h => hii' (congrArg Subtype.val h)
    exact on_components c ⟨i, hi⟩ ⟨i', hi'⟩ hne
  · exact Or.inr (Or.inl (M_eq_two_of_connectedComponentMk_ne cg1
      (fun heq => same_comp (SimpleGraph.ConnectedComponent.eq.mp heq))))

/-- `W` *has a generalized Cartan matrix* realizing its Coxeter matrix: there is an explicit
positive length-rescaling `scale : cg.B → ℝ` of the simple roots making every simple reflection
integral with respect to the rescaled basis. Concretely, for every `i ≠ i'`,
`2 * scale i' * cos (π / M i i')` must be an natural multiple of `scale i` — this is exactly the
condition for the reflection `geomRepAux i` to send the rescaled root `scale i' • stdBasis i'`
back into the `ℤ`-span of the rescaled roots `{scale j • stdBasis j}`. The witness `n : ℕ` for the
pair `(i, i')` is always nonnegative by construction — this is exactly right, since (see
`Coxeter.CartanMatrix`, notably `HasGeneralizedCartanMatrix.cartanMatrix`) it is the *negation*
`-n` of the generalized Cartan matrix entry `a_{i i'}` in the Kac–Moody sense (whose off-diagonal
entries are `≤ 0`).

This already forces `IsCrystallographic` (`HasGeneralizedCartanMatrix.isCrystallographic` in
`Coxeter.CartanMatrix`): the two witnesses for `(i, i')` and `(i', i)` multiply to
`4 * cos (π / M i i') ^ 2`, a natural number, which pins `M i i' ∈ {0, 2, 3, 4, 6}`.

- Descent: holds — restricting a global `scale` to a component's generators still satisfies that
  component's own condition.
- Assembly: holds. `assembles_hasGeneralizedCartanMatrix`: cross-component pairs already satisfy
  the condition for free (`cos (π/2) = 0`, witnessed by `n = 0`), so gluing each component's own
  scale function together gives a scale on the whole diagram. -/
def HasGeneralizedCartanMatrix : Prop :=
  ∃ scale : cg.B → ℝ, (∀ i, 0 < scale i) ∧
    ∀ i i' : cg.B, i ≠ i' → ∃ n : ℕ, 2 * scale i' * Real.cos (Real.pi / cg.M i i') = n * scale i

/-- Dividing `HasGeneralizedCartanMatrix`'s defining condition at `(i, i')` by the same condition
at the reversed pair `(i', i)` pins the ratio `n / m` of the two integer witnesses to be exactly the
*square* of the scale ratio `scale i' / scale i` — equivalently, in the cleared-denominator form
proved here, `n * scale i ^ 2 = m * scale i' ^ 2`. (This is the same pair of equations used in
`Coxeter.CartanMatrix.generalizedCartanMatrix_mul_eq` to get the *product* `n * m = 4 cos²(π/M)`;
here we instead eliminate `cos` to compare `scale i` against `scale i'` directly, with no positivity
hypothesis needed.) Consequently, two scales agreeing on `n` and `m` at a pair `(i, i')` must have
the same ratio `scale i' / scale i`, since positive reals with equal squares are equal. -/
lemma scale_ratio_sq_eq_of_generalizedCartanMatrix_cond
    (scale : cg.B → ℝ) (i i' : cg.B)
    (n : ℕ) (hn : 2 * scale i' * Real.cos (Real.pi / cg.M i i') = n * scale i)
    (m : ℕ) (hm : 2 * scale i * Real.cos (Real.pi / cg.M i i') = m * scale i') :
    (n : ℝ) * scale i ^ 2 = m * scale i' ^ 2 := by
  linear_combination scale i' * hm - scale i * hn

/-- Rescaling `scale` by a factor `t` that depends only on the connected component of each
generator preserves `HasGeneralizedCartanMatrix`'s pairwise condition. Within a component, `i` and
`i'` get multiplied by the *same* factor (`t` agrees on a component), so it cancels and the same
witness `n` still works; across components the condition holds via `n = 0` regardless of any
rescaling, since `M i i' = 2` gives `cos (π / M i i') = 0` there. -/
lemma hasGeneralizedCartanMatrix_cond_of_rescale
    (scale : cg.B → ℝ) (t : (coxeterGraphMatrix cg.M).ConnectedComponent → ℝ)
    (hcond : ∀ i i' : cg.B, i ≠ i' →
      ∃ n : ℕ, 2 * scale i' * Real.cos (Real.pi / cg.M i i') = n * scale i) :
    ∀ i i' : cg.B, i ≠ i' →
      ∃ n : ℕ,
        2 * (t ((coxeterGraphMatrix cg.M).connectedComponentMk i') * scale i') *
            Real.cos (Real.pi / cg.M i i') =
        n * (t ((coxeterGraphMatrix cg.M).connectedComponentMk i) * scale i) := by
  intro i i' hii'
  by_cases same_comp : (coxeterGraphMatrix cg.M).Reachable i i'
  · obtain ⟨n, hn⟩ := hcond i i' hii'
    have ht : t ((coxeterGraphMatrix cg.M).connectedComponentMk i) =
        t ((coxeterGraphMatrix cg.M).connectedComponentMk i') :=
      congrArg t (SimpleGraph.ConnectedComponent.sound same_comp)
    refine ⟨n, ?_⟩
    rw [ht]
    linear_combination t ((coxeterGraphMatrix cg.M).connectedComponentMk i') * hn
  · refine ⟨0, ?_⟩
    rw [M_eq_two_of_connectedComponentMk_ne cg
      (fun heq => same_comp (SimpleGraph.ConnectedComponent.eq.mp heq))]
    simp

/-- Renormalize an a priori `HasGeneralizedCartanMatrix` witness `a_priori_scale` so that, on each
connected component `c`, the chosen representative `(component_reps c).1` gets exactly the
*prescribed* scale `(component_reps c).2`, rather than whatever value `a_priori_scale` happened to
give it. `HasGeneralizedCartanMatrix`'s defining condition only pins the *ratio* `scale i / scale
i'` between generators sharing a component (and says nothing at all about cross-component ratios,
where `n = 0` works regardless), so multiplying every generator of one component by a single
positive constant is always still a valid witness — and the constant needed to hit the prescribed
target `(component_reps c).2` at the representative is
`(component_reps c).2 / a_priori_scale (component_reps c).1`. -/
noncomputable def scale_fixing
  (a_priori_scale : cg.B → ℝ)
  (a_priori_scale_proof :
    (∀ i, 0 < a_priori_scale i) ∧
    ∀ i i' : cg.B, i ≠ i' →
      ∃ n : ℕ,
        2 * a_priori_scale i' * Real.cos (Real.pi / cg.M i i') =
        n * a_priori_scale i
  )
  (component_reps : (coxeterGraphMatrix cg.M).ConnectedComponent -> cg.B × ℝ)
  (component_reps_pos : ∀ c, 0 < (component_reps c).2)
  (component_reps_mem : ∀ c,
    (coxeterGraphMatrix cg.M).connectedComponentMk (component_reps c).1 = c)
  : {new_scale: cg.B → ℝ //
    (∀ i, 0 < new_scale i) ∧
    (∀ i i' : cg.B, i ≠ i' →
      ∃ n : ℕ,
        2 * new_scale i' * Real.cos (Real.pi / cg.M i i') =
        n * new_scale i
    ) ∧
    (∀ c : (coxeterGraphMatrix cg.M).ConnectedComponent,
      new_scale (component_reps c).1 = (component_reps c).2)
  } := by
  let cg1_graph := coxeterGraphMatrix cg.M
  let rep : cg1_graph.ConnectedComponent → cg.B := fun c => (component_reps c).1
  let target : cg1_graph.ConnectedComponent → ℝ := fun c => (component_reps c).2
  let t : cg1_graph.ConnectedComponent → ℝ := fun c => target c / a_priori_scale (rep c)
  let new_scale_candidate : cg.B → ℝ :=
    fun i => t (cg1_graph.connectedComponentMk i) * a_priori_scale i
  refine ⟨new_scale_candidate, fun i => ?_, ?_, fun c => ?_⟩
  · exact mul_pos (div_pos (component_reps_pos _) (a_priori_scale_proof.1 _))
      (a_priori_scale_proof.1 i)
  · exact hasGeneralizedCartanMatrix_cond_of_rescale a_priori_scale t a_priori_scale_proof.2
  · change t (cg1_graph.connectedComponentMk (rep c)) * a_priori_scale (rep c) = target c
    rw [component_reps_mem c]
    exact div_mul_cancel₀ _ (a_priori_scale_proof.1 (rep c)).ne'

/-
Cross-component pairs already satisfy the condition for free (`cos (π/2) = 0`, witnessed by
`n = 0` regardless of scale), so gluing each component's own scale function together (indexed by
`coxeterGraphMatrix.connectedComponentMk`) gives a scale on all of `cg1.B` satisfying the condition
on every pair — hence `cg1.HasGeneralizedCartanMatrix` holds iff every component does.
-/
lemma assembles_hasGeneralizedCartanMatrix :
  Assembles
    fun [W1 : Type*] (cg1 : CoxeterGroup W1) => @HasGeneralizedCartanMatrix W1 cg1
  := by
  unfold Assembles
  intro W1 cg1 finitely_many_comp on_components
  choose scale_c hscale_c_pos hscale_c_cond using on_components
  set cg1_graph := coxeterGraphMatrix cg1.M
  refine ⟨fun i => scale_c (cg1_graph.connectedComponentMk i) ⟨i, rfl⟩,
    fun i => hscale_c_pos _ _, ?_⟩
  intro i i' hii'
  dsimp only
  by_cases same_comp : cg1_graph.Reachable i i'
  · have heq : cg1_graph.connectedComponentMk i = cg1_graph.connectedComponentMk i' :=
      SimpleGraph.ConnectedComponent.sound same_comp
    have hi : i ∈ (cg1_graph.connectedComponentMk i).supp := rfl
    have hi' : i' ∈ (cg1_graph.connectedComponentMk i).supp := heq.symm
    have hne : (⟨i, hi⟩ : (cg1_graph.connectedComponentMk i).supp) ≠ ⟨i', hi'⟩ :=
      fun h => hii' (congrArg Subtype.val h)
    obtain ⟨n, hn⟩ := hscale_c_cond (cg1_graph.connectedComponentMk i) ⟨i, hi⟩ ⟨i', hi'⟩ hne
    refine ⟨n, ?_⟩
    have transport : ∀ {c c' : cg1_graph.ConnectedComponent} (h : c = c') {x : cg1.B}
        (hx : x ∈ c.supp), scale_c c ⟨x, hx⟩ = scale_c c' ⟨x, h ▸ hx⟩ := by
      rintro c c' rfl x hx
      rfl
    rw [transport heq hi'] at hn
    rw [M_eq_componentMatrix cg1 (cg1_graph.connectedComponentMk i) ⟨i, hi⟩ ⟨i', hi'⟩]
    exact hn
  · refine ⟨0, ?_⟩
    rw [M_eq_two_of_connectedComponentMk_ne cg1
      (fun heq => same_comp (SimpleGraph.ConnectedComponent.eq.mp heq))]
    simp

/-- A Coxeter matrix is *irreducible* if its Coxeter diagram (`coxeterGraphMatrix`) is connected. -/
def IsIrreducibleMatrix {B1 : Type*} (M1 : CoxeterMatrix B1) : Prop :=
  (coxeterGraphMatrix M1).Connected

/-- - Descent: holds, but vacuously — a connected component is connected by definition, so
    `component_cg.IsIrreducible` holds unconditionally, whether or not `cg.IsIrreducible` does.
  - Assembly: fails. "Every component is connected" is always true and carries no information
    about whether there is only *one* component, so it cannot imply `cg.IsIrreducible`. -/
def IsIrreducible : Prop :=
  IsIrreducibleMatrix (M1 := cg.M)

/-- The Coxeter matrix obtained from `M` by deleting one generator `i₀` — restricting the matrix to
the remaining generators is again a valid Coxeter matrix (symmetric, diagonal `1`, off-diagonal
`≠ 1`), inherited directly from `M`. -/
def deleteGenerator (i₀ : B W) :
    CoxeterMatrix {j : B W // j ≠ i₀} where
  M a b := M a.1 b.1
  isSymm := Matrix.IsSymm.ext_iff.mpr (fun a b => M.symmetric b.1 a.1)
  diagonal a := M.diagonal a.1
  off_diagonal a b hab := M.off_diagonal a.1 b.1 (fun h => hab (Subtype.ext h))

/-- `W` is of *finite type*: either finite, or `bil` is positive semidefinite and nondegenerate
(i.e. positive definite — `IsPosDef` isn't a separate notion in Mathlib for bilinear forms). Stated
as an *or*, not an *iff*: the classical equivalence `W` finite ↔ `bil` positive definite isn't
proved here, so satisfying either disjunct is the obligation, not both.

- Descent: holds, via either disjunct — a direct factor of a finite group is finite, and a block
  of a positive-definite form is positive-definite.
- Assembly: holds, symmetrically — a finite product of finite groups is finite, and an orthogonal
  sum of positive-definite blocks is positive-definite (assuming finitely many components; an
  infinite product of nontrivial finite groups is infinite). -/
def IsFiniteCoxeter : Prop :=
  Finite W ∨ (
    (@bil W _).IsPosSemidef ∧ (@bil W _).Nondegenerate
  )

/-- `W` is a *product of finite Weyl groups*:
`IsFiniteCoxeter` together with `IsCrystallographic`.

- Descent: holds — conjunction of two properties that each descend.
- Assembly: holds — conjunction of two properties that each assemble. -/
def IsPolyFiniteWeyl : Prop :=
  @IsFiniteCoxeter W cg ∧
  @IsCrystallographic W cg

/-- `W` is an *irreducible finite Weyl group*: `IsPolyFiniteWeyl` together with `IsIrreducible`
(the Coxeter diagram is connected) — the genuine, single (not a product) case.

- Descent: holds, but vacuously, via the `IsIrreducible` conjunct.
- Assembly: fails, via the `IsIrreducible` conjunct — if there are ≥2 components each individually
  an irreducible finite Weyl group, their union is reducible, so it isn't `IsIrreducibleFiniteWeyl`
  even though the `IsPolyFiniteWeyl` part would assemble fine. -/
def IsIrreducibleFiniteWeyl : Prop :=
  @IsPolyFiniteWeyl W cg ∧ @IsIrreducible W cg

/-- A Coxeter system is of *affine type*:
`bil` is positive semidefinite but not nondegenerate —
This covers the properly-degenerate case.
That is the only restriction on how large the degenerate (radical) directions are.
It is at least 1, but can be more.

- Descent: fails. `bil` positive semidefinite does descend to each block, but degeneracy of the
  whole form doesn't: `cg` can be degenerate because of just one "bad" component while a
  finite-type sibling component stays nondegenerate on its own, failing `IsAffineCoxeter` there.
- Assembly: holds, given at least one component — see `assembles_affineCoxeter`. If every
  component's block is positive semidefinite and degenerate, the orthogonal sum is positive
  semidefinite (sum of psd) and degenerate (its kernel contains each block's nonzero kernel). -/
def IsAffineCoxeter : Prop :=
  (@bil W _).IsPosSemidef ∧ ¬ (@bil W _).Nondegenerate

/-- `W` is an *irreducible affine Coxeter group*: `IsAffineCoxeter` together with
`IsIrreducible`. This is the broad affine-Coxeter predicate and does not require
crystallographic entries or a finite Weyl part. Use `IsIrreducibleAffineWeyl` for the stronger
root-system/Weyl refinement. -/
def IsIrreducibleAffineCoxeter : Prop :=
  @IsAffineCoxeter W cg ∧ @IsIrreducible W cg

/-- `IsAffineCoxeter`, or `cg` has no generators at all. Plain `IsAffineCoxeter` isn't an instance
of `Assembles`: on the empty diagram (zero components), `V W` is the trivial module, on which `bil`
is vacuously `Nondegenerate`, so `IsAffineCoxeter` is false there while `∀ c, IsAffineCoxeter
(component c)` is vacuously true. Weakening to this "or empty" version fixes it: the extra disjunct
is only ever needed exactly when `cg` itself has no generators, and is never needed for an
individual component, since a connected component's own sub-diagram always has itself as an
inhabitant (`SimpleGraph.ConnectedComponent.nonempty_supp`) — so it's never vacuously empty. -/
def IsAffineCoxeterOrEmpty : Prop := IsEmpty (B W) ∨ @IsAffineCoxeter W cg

/-- `bil` being positive semidefinite assembles across connected components unconditionally — no
"or empty" wrapper needed, since `bil` on the trivial module (no generators) is vacuously positive
semidefinite anyway, matching the vacuous truth of `∀ c, ...` over an empty component index.
Follows directly from `Component.lean`'s block-diagonal decomposition
(`bil_toMatrix_blockEquiv_eq_blockDiagonal'`) fed into
`LinearMap.BilinForm.isPosSemidef_of_toMatrix_eq_blockDiagonal'`. -/
lemma assembles_possemidef :
  Assembles fun [W1 : Type*] (cg1 : CoxeterGroup W1) => (@bil W1 cg1).IsPosSemidef := by
  unfold Assembles
  intro W1 cg1 finitely_many_comp on_components
  classical
  exact LinearMap.BilinForm.isPosSemidef_of_toMatrix_eq_blockDiagonal'
    (stdBasis.reindex (blockEquiv cg1).symm) (@bil W1 cg1)
    (fun c => @bil _ (componentCoxeterGroup cg1 c))
    (bil_toMatrix_blockEquiv_eq_blockDiagonal' cg1) on_components

/-
The empty-diagram case is immediate (`Or.inl empty`). Otherwise, `IsPosSemidef` comes straight from
`assembles_possemidef`, while `¬ Nondegenerate` needs the "or empty" case split: an arbitrary
component is degenerate (`on_arbitrary`), which after converting the one-sided `¬ SeparatingRight`
fact to `¬ SeparatingLeft` (using that each component's `bil` is symmetric) transfers, via
`LinearMap.BilinForm.not_separatingLeft_of_toMatrix_eq_blockDiagonal'`, to
`¬ SeparatingLeft (@bil W1 cg1)`, hence `¬ Nondegenerate`.
-/
lemma assembles_affineCoxeter :
  Assembles
    fun [W1 : Type*] (cg1 : CoxeterGroup W1) => @IsAffineCoxeterOrEmpty W1 cg1
  := by
  unfold Assembles
  intro W1 cg1 finitely_many_comp on_components
  unfold IsAffineCoxeterOrEmpty
  by_cases empty : IsEmpty (B W1)
  · exact Or.inl empty
  · refine Or.inr ?obligation
    unfold IsAffineCoxeter
    set bil_c := fun c : (coxeterGraphMatrix cg1.M).ConnectedComponent =>
      @bil _ (componentCoxeterGroup cg1 c) with bil_c_def
    have on_components' : ∀ c : (coxeterGraphMatrix cg1.M).ConnectedComponent,
        (bil_c c).IsPosSemidef ∧ ¬ (bil_c c).Nondegenerate := by
      intro c
      rcases on_components c with hempty | haffine
      · obtain ⟨v, hv⟩ := c.nonempty_supp
        exact hempty.elim ⟨v, hv⟩
      · exact haffine
    have arbitrary_component : (coxeterGraphMatrix cg1.M).ConnectedComponent := by
      have arbitrary_gen : B W1 := Classical.arbitrary (B W1)
        (h:=not_isEmpty_iff.mp empty)
      exact (coxeterGraphMatrix cg1.M).connectedComponentMk arbitrary_gen
    have on_arbitrary := on_components' arbitrary_component
    unfold IsAffineCoxeterOrEmpty at on_arbitrary
    have on_arbitrary := on_arbitrary.right
    unfold LinearMap.BilinForm.Nondegenerate at on_arbitrary
    unfold LinearMap.Nondegenerate at on_arbitrary
    rw [not_and] at on_arbitrary
    have on_components'' : ∀ c : (coxeterGraphMatrix cg1.M).ConnectedComponent,
        (bil_c c).IsPosSemidef := by
      intro c
      exact (on_components' c).left
    classical
    have hsep_left_ne : ¬ (bil_c arbitrary_component).SeparatingLeft := by
      intro hleft
      apply on_arbitrary hleft
      intro y hy
      apply hleft
      intro z
      rw [bil_c_def, (@bil_isSymm _ (componentCoxeterGroup cg1 arbitrary_component)).eq]
      exact hy z
    have hpsd_whole : (@bil W1 cg1).IsPosSemidef := assembles_possemidef cg1 on_components''
    have hdeg_whole : ¬ (@bil W1 cg1).SeparatingLeft :=
      LinearMap.BilinForm.not_separatingLeft_of_toMatrix_eq_blockDiagonal'
        (stdBasis.reindex (blockEquiv cg1).symm) (@bil W1 cg1) bil_c
        (bil_toMatrix_blockEquiv_eq_blockDiagonal' cg1) hsep_left_ne
    exact ⟨hpsd_whole, fun hnd => hdeg_whole hnd.1⟩

/-- A particular kind of affine Coxeter system
(`IsAffineCoxeter`), characterized the classical way.
Deleting a single node from the Coxeter diagram recovers a finite part.
Concretely:
- `bil` is positive semidefinite
- the whole matrix `IsCrystallographic`
  (the entire diagram, including the null generator, preserves a lattice)
- there is some generator `i₀` and some `δ` supported away from `i₀`
  (`δ i₀ = 0`) such that `bil`'s radical (kernel) is spanned by `stdBasis i₀ + δ`
  as exactly the single "null"/imaginary-root direction
  (the diagonal entry `bil (stdBasis i₀) (stdBasis i₀) = 1` rules out the kernel
  being spanned by `stdBasis i₀` alone)
- Deleting `i₀` (`deleteGenerator i₀`) then recovers the
  finite part.
We do not have the classification result available. So we cannot
go from `IsAffineCoxeter` to disjoint union of connected `IsAffineCoxeter`
and from there to disjoint union of several possibilities all of which have nullity at
most 1. The block structure on connected components (`Component.lean`'s
`bil_toMatrix_blockEquiv_eq_blockDiagonal'`) is now available, but writing `δ` in terms of
`B_a^-1 B_{i0, a_j}` (where `a` indexes the components upon removing `i0` and `a_j` indexes the
nodes within that component) is still not done.

- Descent: fails, worse than `IsAffineCoxeter`. The `∃ i₀, δ` clause pins the *total* nullity of
  `bil` to exactly `1`; since the kernel of an orthogonal direct sum is the direct sum of the
  kernels, `cg` satisfying this has exactly one component with nullity `1` and every other
  component nondegenerate, so `IsPolyAffineWeyl` fails on those nondegenerate components.
- Assembly: fails, in the opposite direction. If *every* component individually had nullity `1`,
  the total nullity would be the number of components, not `1`, unless there is only one
  component. The real per-component statement is a *mixed* one — exactly one component is
  `IsIrreducibleAffineWeyl` and the rest are `IsIrreducibleFiniteWeyl` — not "the same property on
  every component". -/
def IsPolyAffineWeyl : Prop :=
  (@bil W _).IsPosSemidef ∧
  @IsCrystallographic W cg ∧
  ∃ i₀ : B W, ∃ δ ∈ supported ℝ ℝ ({i₀}ᶜ : Set (B W)),
    LinearMap.ker (@bil W _) = Submodule.span ℝ {stdBasis i₀ + δ}

/-- `W` is an *irreducible affine Weyl group*: `IsPolyAffineWeyl` together with `IsIrreducible`
(the Coxeter diagram is connected) — the genuine, single (not a product) case.

- Descent: holds, but vacuously, via the `IsIrreducible` conjunct.
- Assembly: fails, via the `IsIrreducible` conjunct, compounded by the nullity-counting failure of
  `IsPolyAffineWeyl` (several irreducible affine components would sum to nullity `> 1`). -/
def IsIrreducibleAffineWeyl : Prop :=
  @IsPolyAffineWeyl W cg ∧ @IsIrreducible W cg

end Coxeter
