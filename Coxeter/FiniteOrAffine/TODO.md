# FiniteOrAffine: open `proof_wanted` stubs

Everything in this directory that is not yet a real proof, grouped by file; each item names the
declaration and what's needed to close it.

## Affine types

For the `IsIrreducibleAffineCoxeter` goals use `isAffineCoxeter_of_nonneg_of_radical` (nonnegative
`bil` plus a nonzero null vector orthogonal to every `stdBasis i`) and
`isIrreducibleMatrix_of_exists_rank_lt` for connectivity, as in `AffineExceptional.lean`. For a
general `n` the nonnegativity needs a sum-of-squares identity in `n` (as `sos_identity_fork` does
for finite `Dₙ`) rather than a fixed `LDLᵀ` decomposition.

The `IsIrreducibleAffineWeyl` goals additionally need `IsPolyAffineWeyl`: crystallographic entries
and `LinearMap.ker bil = Submodule.span ℝ {stdBasis i₀ + δ}` with `δ i₀ = 0`, i.e. the radical is
exactly the line through the null root. From an `LDLᵀ` decomposition with a single zero pivot
(the last one), `bil x x = 0` forces every other linear form to vanish, which pins `x` to a
multiple of the null root.

### AffineTypeA.lean
- `proof_wanted affineTypeA_isIrreducibleAffineCoxeter (n : ℕ) [NeZero n] : @IsIrreducibleAffineCoxeter _ (affineTypeAGroup n)`
- `proof_wanted affineTypeA_isIrreducibleAffineWeyl (n : ℕ) [NeZero n] : @IsIrreducibleAffineWeyl _ (affineTypeAGroup n)`
  — the diagram is a cycle; the null root is `(1, …, 1)`.

### AffineTypeB.lean
- `proof_wanted affineTypeB_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineCoxeter _ (affineTypeBGroup n hn)`
- `proof_wanted affineTypeB_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineWeyl _ (affineTypeBGroup n hn)`

### AffineTypeC.lean
- `proof_wanted affineTypeC_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineCoxeter _ (affineTypeCGroup n hn)`
- `proof_wanted affineTypeC_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineWeyl _ (affineTypeCGroup n hn)`

### AffineTypeD.lean
- `proof_wanted affineTypeD_isIrreducibleAffineCoxeter (n : ℕ) [NeZero n] : @IsIrreducibleAffineCoxeter _ (affineTypeDGroup n)`
- `proof_wanted affineTypeD_isIrreducibleAffineWeyl (n : ℕ) [NeZero n] : @IsIrreducibleAffineWeyl _ (affineTypeDGroup n)`
  — the null root is `(1, 2, …, 2, 1, 1, 1)` (`1` at nodes `0`, `n - 2`, `n - 1`, `n`). The
  statements use `[NeZero n]`, but `affineTypeDMatrix n` is only `D̃ₙ` for `n ≥ 4`; the
  hypothesis likely needs strengthening to `4 ≤ n`.

### AffineExceptional.lean
- `proof_wanted affineTypeE6_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeE6Group`
- `proof_wanted affineTypeE7_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeE7Group`
- `proof_wanted affineTypeE8_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeE8Group`
- `proof_wanted affineTypeF4_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeF4Group`
- `proof_wanted affineTypeG2_isIrreducibleAffineWeyl : @IsIrreducibleAffineWeyl _ affineTypeG2Group`
  — fixed matrices: positive semidefiniteness, the null roots `affineType*Null` and irreducibility
  are already available (`affineType*_isIrreducibleAffineCoxeter`), and the entries are
  crystallographic by a finite check. What remains is the kernel equality, from the existing
  `LDLᵀ` decompositions (the last pivot is the only zero one). The null roots have `1` at the extra
  node, so `i₀` can be taken to be the extra node.

## Suggested order of attack

1. The `AffineExceptional.lean` `IsIrreducibleAffineWeyl` goals — fixed matrices, with the
   decompositions already in place.
2. The `Ãₙ`, `B̃ₙ`, `C̃ₙ`, `D̃ₙ` `IsIrreducibleAffineCoxeter` goals — need general-`n`
   sum-of-squares identities.
3. Their `IsIrreducibleAffineWeyl` goals.
