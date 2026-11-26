# FiniteOrAffine: open `axiom`/`proof_wanted`/`sorry` stubs

Everything in this directory that is not yet a real proof, grouped by file; each item names the
declaration and what's needed to close it.

## Finite types

### Exceptional.lean
- `proof_wanted typeE6_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeE6Group`
- `proof_wanted typeE7_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeE7Group`
- `proof_wanted typeE8_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeE8Group`
- `proof_wanted typeF4_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeF4Group`
- `proof_wanted typeG2_isIrreducibleFiniteWeyl : @IsIrreducibleFiniteWeyl _ typeG2Group`
  — each needs `IsIrreducible` (diagram connectivity, checkable by `fin_cases`/`decide` since
  these are small fixed-rank matrices) plus `IsPolyFiniteWeyl` (`IsFiniteCoxeter ∧
  IsCrystallographic`; crystallographic is already proved for all five). `IsFiniteCoxeter` needs
  positive-definiteness of `bil` — these are fixed, small finite matrices (rank ≤ 8), so in
  principle decidable/computable rather than needing a general SOS argument.
- `proof_wanted typeH3_isIrreducible : @IsIrreducible _ typeH3Group`
- `proof_wanted typeH4_isIrreducible : @IsIrreducible _ typeH4Group` — diagram connectivity,
  should be straightforward (`fin_cases`/`decide` on the fixed rank-3/4 matrix).
- `proof_wanted typeH3_isFiniteCoxeter : @IsFiniteCoxeter _ typeH3Group`
- `proof_wanted typeH4_isFiniteCoxeter : @IsFiniteCoxeter _ typeH4Group` — `H₃`/`H₄` are
  *non-crystallographic* (golden-ratio entries, `cos(π/5)`), so this needs its own
  positive-definiteness argument; not crystallographic, so no `IsPolyFiniteWeyl`/Weyl statement
  applies to these two, only `IsIrreducible ∧ IsFiniteCoxeter` (there's no
  `typeH3_isIrreducibleFiniteWeyl` target, consistent with `H₃`/`H₄` not being Weyl groups).

## Affine types

The `axiom` matrices below (`B̃`, `C̃`) block every downstream `proof_wanted` in their file. Matrix
definitions should mirror `TypeD.lean`'s `typeDMatrix`-style construction (explicit `Matrix.of`
with the standard affine Dynkin diagram shape) or reuse mathlib's affine matrices if/when
available.

For the `IsIrreducibleAffineCoxeter`/`IsIrreducibleAffineWeyl` goals: irreducibility is
connectivity of the diagram (as in `typeD_isIrreducible`), and the affine condition is positive
semidefinite but degenerate `bil`, with radical spanned by the null root.

### AffineTypeA.lean
- `proof_wanted affineTypeA_isIrreducibleAffineCoxeter (n : ℕ) [NeZero n] : @IsIrreducibleAffineCoxeter _ (affineTypeAGroup n)`
- `proof_wanted affineTypeA_isIrreducibleAffineWeyl (n : ℕ) [NeZero n] : @IsIrreducibleAffineWeyl _ (affineTypeAGroup n)`
  — the diagram is a cycle; the null root is `(1, …, 1)`.

### AffineTypeB.lean
- `axiom affineTypeBMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1))`
- `proof_wanted affineTypeB_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineCoxeter _ (affineTypeBGroup n hn)`
- `proof_wanted affineTypeB_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineWeyl _ (affineTypeBGroup n hn)`

### AffineTypeC.lean
- `axiom affineTypeCMatrix (n : ℕ) : CoxeterMatrix (Fin (n + 1))`
- `proof_wanted affineTypeC_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineCoxeter _ (affineTypeCGroup n hn)`
- `proof_wanted affineTypeC_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineWeyl _ (affineTypeCGroup n hn)`
- `proof_wanted affineTypeC_two_identifies_affineTypeB_two : HEq (@CoxeterGroup.cs _ (affineTypeCGroup 2 _)) (@CoxeterGroup.cs _ (affineTypeBGroup 2 _))`
  — the accidental `C₂-hat = B₂-hat` identification; blocked on both `affineTypeCMatrix` and
  `affineTypeBMatrix` being defined, same shape as `typeBC_one_identifies_typeA_one` once they
  are.

### AffineTypeD.lean
- `proof_wanted affineTypeD_isIrreducibleAffineCoxeter (n : ℕ) [NeZero n] : @IsIrreducibleAffineCoxeter _ (affineTypeDGroup n)`
- `proof_wanted affineTypeD_isIrreducibleAffineWeyl (n : ℕ) [NeZero n] : @IsIrreducibleAffineWeyl _ (affineTypeDGroup n)`
  — the null root is `(1, 2, …, 2, 1, 1, 1)` (`1` at nodes `0`, `n - 2`, `n - 1`, `n`). The
  statements use `[NeZero n]`, but `affineTypeDMatrix n` is only `D̃ₙ` for `n ≥ 4`; the
  hypothesis likely needs strengthening to `4 ≤ n`.

### AffineExceptional.lean
- `proof_wanted affineTypeE6_isIrreducibleAffineCoxeter : @IsIrreducibleAffineCoxeter _ affineTypeE6Group`
- `proof_wanted affineTypeE7_isIrreducibleAffineCoxeter : @IsIrreducibleAffineCoxeter _ affineTypeE7Group`
- `proof_wanted affineTypeE8_isIrreducibleAffineCoxeter : @IsIrreducibleAffineCoxeter _ affineTypeE8Group`
- `proof_wanted affineTypeF4_isIrreducibleAffineCoxeter : @IsIrreducibleAffineCoxeter _ affineTypeF4Group`
- `proof_wanted affineTypeG2_isIrreducibleAffineCoxeter : @IsIrreducibleAffineCoxeter _ affineTypeG2Group`
- `proof_wanted affineTypeE6_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeE6Group`
- `proof_wanted affineTypeE7_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeE7Group`
- `proof_wanted affineTypeE8_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeE8Group`
- `proof_wanted affineTypeF4_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeF4Group`
- `proof_wanted affineTypeG2_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeG2Group`
  — all five matrices are fixed, so connectivity is a finite check. For `Ẽ₆`–`Ẽ₈` the null root
  is (a multiple of) the `δ` in the quasi-unipotence proofs. `F̃₄`/`G̃₂` are not simply laced, so
  `bil` has irrational entries (`cos (π / 4)`, `cos (π / 6)`) and they have no Euler lattice here
  (they need valued quivers).

## Suggested order of attack

1. `Exceptional.lean`'s `IsIrreducible` goals for `H₃`/`H₄` — connectivity only, cheap.
2. `Exceptional.lean`'s five `IsIrreducibleFiniteWeyl` goals and two `H₃`/`H₄` `IsFiniteCoxeter`
   goals — fixed small rank, so brute-force/`decide`-style positive-definiteness may be more
   tractable than a general argument; the rank-2 machinery in `Coxeter.GeometricRepresentation`
   (`bil_restrict_E_diag`/`bil_restrict_E_isPosSemidef`/`bil_restrict_E_nondegenerate_iff`)
   generalizes to any pair of generators, not just rank-2 whole diagrams, and may help.
3. The `Ãₙ`, `D̃ₙ`, `Ẽ₆`–`Ẽ₈`, `F̃₄`, `G̃₂` `IsIrreducibleAffineCoxeter`/`IsIrreducibleAffineWeyl`
   goals, whose matrices are already defined.
4. Define the remaining affine matrices (`B̃`, `C̃`), then their goals.
