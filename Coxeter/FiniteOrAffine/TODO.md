# FiniteOrAffine: open `proof_wanted` stubs

Everything in this directory that is not yet a real proof, grouped by file; each item names the
declaration and what's needed to close it.

## Affine types

For the `IsIrreducibleAffineCoxeter` goals use `isAffineCoxeter_of_nonneg_of_radical` (nonnegative
`bil` plus a nonzero null vector orthogonal to every `stdBasis i`) and
`isIrreducibleMatrix_of_exists_rank_lt` for connectivity, as in `AffineExceptional.lean`. For a
general `n` the nonnegativity needs a sum-of-squares identity in `n` (as `sos_identity_fork` does
for finite `Dₙ`) rather than a fixed `LDLᵀ` decomposition.

The `IsIrreducibleAffineWeyl` goals additionally need `IsPolyAffineWeyl`; use
`isPolyAffineWeyl_of_isotropic` (crystallographic entries, a null root `v` with `v i₀ = 1`, and
every `x` with `bil x x = 0` a multiple of `v`), as in `AffineExceptional.lean`: in a
sum-of-squares decomposition with a single zero coefficient, `bil x x = 0` forces every other
linear form to vanish, which pins `x` to a multiple of the null root.

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

## Suggested order of attack

1. The `B̃ₙ`, `C̃ₙ`, `D̃ₙ` `IsIrreducibleAffineCoxeter` goals — need general-`n` sum-of-squares
   identities (see `affineTypeA_bil_eq` for the cycle).
2. Their `IsIrreducibleAffineWeyl` goals, via `isPolyAffineWeyl_of_isotropic`.
