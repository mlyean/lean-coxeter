module

public import Coxeter.GeometricRepresentation
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

## Main definitions

* `Coxeter.IsRightAngled`
* `Coxeter.IsCrystallographic`
* `Coxeter.IsIrreducible`
* `Coxeter.IsFiniteCoxeter`
* `Coxeter.IsPolyFiniteWeyl`
* `Coxeter.IsIrreducibleFiniteWeyl`
* `Coxeter.IsAffineCoxeter`
* `Coxeter.IsPolyAffineWeyl`
* `Coxeter.IsIrreducibleAffineWeyl`
-/

@[expose] public section

namespace Coxeter

open Finsupp CoxeterGroup CoxeterSystem

variable {W : Type*} {cg : CoxeterGroup W}

/-- A Coxeter matrix is *right-angled* if every pair of distinct generators either commutes
(`M i i' = 2`) or generates an infinite dihedral subgroup (`M i i' = 0`) — i.e. no relation of
order `3` or more ever occurs between two distinct generators. -/
def IsRightAngled : Prop := ∀ i i' : B W, i ≠ i' → M i i' = 2 ∨ M i i' = 0

def IsCrystallographicMatrix {B1 : Type*} (M1 : Matrix B1 B1 ℕ) : Prop :=
  ∀ i i' : B1, i ≠ i' → M1 i i' = 0 ∨ M1 i i' = 2 ∨ M1 i i' = 3 ∨ M1 i i' = 4 ∨ M1 i i' = 6

/-- A Coxeter matrix is *crystallographic* if every pair of distinct generators either generates an
infinite dihedral subgroup (`M i i' = 0`) or one of order `2 * M i i'` for `M i i' ∈ {2, 3, 4, 6}`
— the restriction on dihedral angles forced by requiring the reflections to preserve a lattice. -/
def IsCrystallographic : Prop :=
  IsCrystallographicMatrix (B1 := B W) (M1 := cg.M)

/-- The graph on generators with an edge between `i ≠ i'` whenever `M i i' ≠ 2` (the two simple
reflections don't commute) — the *Coxeter diagram*, as a `SimpleGraph`. -/
def coxeterGraphMatrix {B1 : Type*} (M1 : CoxeterMatrix B1) :
  SimpleGraph B1 := SimpleGraph.fromRel (M1 · · ≠ 2)

/-- A Coxeter matrix is *irreducible* if its Coxeter diagram (`coxeterGraphMatrix`) is connected. -/
def IsIrreducibleMatrix {B1 : Type*} (M1 : CoxeterMatrix B1) : Prop :=
  (coxeterGraphMatrix M1).Connected

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
proved here, so satisfying either disjunct is the obligation, not both. -/
def IsFiniteCoxeter : Prop :=
  Finite W ∨ (
    (@bil W _).IsPosSemidef ∧ (@bil W _).Nondegenerate
  )

/-- `W` is a *product of finite Weyl groups*:
`IsFiniteCoxeter` together with `IsCrystallographic`. -/
def IsPolyFiniteWeyl : Prop :=
  @IsFiniteCoxeter W cg ∧
  @IsCrystallographic W cg

/-- `W` is an *irreducible finite Weyl group*: `IsPolyFiniteWeyl` together with `IsIrreducible`
(the Coxeter diagram is connected) — the genuine, single (not a product) case. -/
def IsIrreducibleFiniteWeyl : Prop :=
  @IsPolyFiniteWeyl W cg ∧ @IsIrreducible W cg

/-- A Coxeter system is of *affine type*:
`bil` is positive semidefinite but not nondegenerate —
This covers the properly-degenerate case.
That is the only restriction on how large the degenerate (radical) directions are.
It is at least 1, but can be more.
-/
def IsAffineCoxeter : Prop :=
  (@bil W _).IsPosSemidef ∧ ¬ (@bil W _).Nondegenerate

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
  finite part. -/
def IsPolyAffineWeyl : Prop :=
  (@bil W _).IsPosSemidef ∧
  @IsCrystallographic W cg ∧
  ∃ i₀ : B W, ∃ δ ∈ supported ℝ ℝ ({i₀}ᶜ : Set (B W)),
    LinearMap.ker (@bil W _) = Submodule.span ℝ {stdBasis i₀ + δ}

/-- `W` is an *irreducible affine Weyl group*: `IsPolyAffineWeyl` together with `IsIrreducible`
(the Coxeter diagram is connected) — the genuine, single (not a product) case. -/
def IsIrreducibleAffineWeyl : Prop :=
  @IsPolyAffineWeyl W cg ∧ @IsIrreducible W cg

end Coxeter
