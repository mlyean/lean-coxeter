# FiniteOrAffine: open `proof_wanted` stubs

Everything in this directory that is not yet a real proof, grouped by file; each item names the
declaration and what's needed to close it.

## Affine types

Use `isIrreducibleAffineCoxeter_of_null` and `isIrreducibleAffineWeyl_of_null` (as in
`AffineTypeD.lean`): they need only irreducibility (`isIrreducibleMatrix_of_exists_lt`),
crystallographic entries, and a null vector `δ` with positive coordinates and
`bil δ (stdBasis j) = 0` for every `j` — a local check at each node.

### AffineTypeB.lean
- `proof_wanted affineTypeB_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineCoxeter _ (affineTypeBGroup n hn)`
- `proof_wanted affineTypeB_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineWeyl _ (affineTypeBGroup n hn)`

### AffineTypeC.lean
- `proof_wanted affineTypeC_isIrreducibleAffineCoxeter (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineCoxeter _ (affineTypeCGroup n hn)`
- `proof_wanted affineTypeC_isIrreducibleAffineWeyl (n : ℕ) (hn : 2 ≤ n) : @IsIrreducibleAffineWeyl _ (affineTypeCGroup n hn)`

## Suggested order of attack

1. The `B̃ₙ`, `C̃ₙ` goals, via `isIrreducibleAffineCoxeter_of_null` /
   `isIrreducibleAffineWeyl_of_null` as for `D̃ₙ`: only irreducibility, crystallographic entries,
   and a positive null vector orthogonal to every `stdBasis j` are needed.
