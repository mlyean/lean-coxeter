module

public import Coxeter.BilinearLatticeDynkins
public import Coxeter.SpecialFeatures

/-!
# Exceptional affine Coxeter groups

This file defines the affine Coxeter matrices of types `Ẽ₆`, `Ẽ₇`, `Ẽ₈` and their Euler lattices,
and reserves names for `F̃₄`, `G̃₂`, whose matrices are still stubs. The classification proofs are
intentionally left as stubs.
-/

@[expose] public section

namespace Coxeter

set_option backward.isDefEq.respectTransparency false in
/-- The Coxeter matrix of affine type `Ẽ₆`: mathlib's `CoxeterMatrix.E₆` with one extra node.
```
                o
                |
                o
                |
    o --- o --- o --- o --- o
```
(the extra node `6` is attached to node `1`). -/
def affineTypeE6Matrix : CoxeterMatrix (Fin 7) where
  M := !![1, 2, 3, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 3;
          3, 2, 1, 3, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2;
          2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 3, 1, 2;
          2, 3, 2, 2, 2, 2, 1]

set_option backward.isDefEq.respectTransparency false in
/-- The Coxeter matrix of affine type `Ẽ₇`: mathlib's `CoxeterMatrix.E₇` with one extra node.
```
                      o
                      |
    o --- o --- o --- o --- o --- o --- o
```
(the extra node `7` is attached to node `0`). -/
def affineTypeE7Matrix : CoxeterMatrix (Fin 8) where
  M := !![1, 2, 3, 2, 2, 2, 2, 3;
          2, 1, 2, 3, 2, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2, 2;
          2, 2, 2, 3, 1, 3, 2, 2;
          2, 2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 2, 3, 1, 2;
          3, 2, 2, 2, 2, 2, 2, 1]

set_option backward.isDefEq.respectTransparency false in
/-- The Coxeter matrix of affine type `Ẽ₈`: mathlib's `CoxeterMatrix.E₈` with one extra node.
```
                o
                |
    o --- o --- o --- o --- o --- o --- o --- o
```
(the extra node `8` is attached to node `7`). -/
def affineTypeE8Matrix : CoxeterMatrix (Fin 9) where
  M := !![1, 2, 3, 2, 2, 2, 2, 2, 2;
          2, 1, 2, 3, 2, 2, 2, 2, 2;
          3, 2, 1, 3, 2, 2, 2, 2, 2;
          2, 3, 3, 1, 3, 2, 2, 2, 2;
          2, 2, 2, 3, 1, 3, 2, 2, 2;
          2, 2, 2, 2, 3, 1, 3, 2, 2;
          2, 2, 2, 2, 2, 3, 1, 3, 2;
          2, 2, 2, 2, 2, 2, 3, 1, 3;
          2, 2, 2, 2, 2, 2, 2, 3, 1]

axiom affineTypeF4Matrix : CoxeterMatrix (Fin 5)
axiom affineTypeG2Matrix : CoxeterMatrix (Fin 3)

@[reducible] noncomputable def affineTypeE6Group : CoxeterGroup affineTypeE6Matrix.Group where
  B := Fin 7
  M := affineTypeE6Matrix
  cs := affineTypeE6Matrix.toCoxeterSystem

@[reducible] noncomputable def affineTypeE7Group : CoxeterGroup affineTypeE7Matrix.Group where
  B := Fin 8
  M := affineTypeE7Matrix
  cs := affineTypeE7Matrix.toCoxeterSystem

@[reducible] noncomputable def affineTypeE8Group : CoxeterGroup affineTypeE8Matrix.Group where
  B := Fin 9
  M := affineTypeE8Matrix
  cs := affineTypeE8Matrix.toCoxeterSystem

@[reducible] noncomputable def affineTypeF4Group : CoxeterGroup affineTypeF4Matrix.Group where
  B := Fin 5
  M := affineTypeF4Matrix
  cs := affineTypeF4Matrix.toCoxeterSystem

@[reducible] noncomputable def affineTypeG2Group : CoxeterGroup affineTypeG2Matrix.Group where
  B := Fin 3
  M := affineTypeG2Matrix
  cs := affineTypeG2Matrix.toCoxeterSystem

proof_wanted affineTypeE6_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeE6Group
proof_wanted affineTypeE7_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeE7Group
proof_wanted affineTypeE8_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeE8Group
proof_wanted affineTypeF4_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeF4Group
proof_wanted affineTypeG2_isIrreducibleAffineCoxeter :
    @IsIrreducibleAffineCoxeter _ affineTypeG2Group

proof_wanted affineTypeE6_isIrreducibleAffineWeyl :
    @IsIrreducibleAffineWeyl _ affineTypeE6Group
proof_wanted affineTypeE7_isIrreducibleAffineWeyl :
    @IsIrreducibleAffineWeyl _ affineTypeE7Group
proof_wanted affineTypeE8_isIrreducibleAffineWeyl :
    @IsIrreducibleAffineWeyl _ affineTypeE8Group
proof_wanted affineTypeF4_isIrreducibleAffineWeyl :
    @IsIrreducibleAffineWeyl _ affineTypeF4Group
proof_wanted affineTypeG2_isIrreducibleAffineWeyl :
    @IsIrreducibleAffineWeyl _ affineTypeG2Group


/-! ### Euler lattices of `Ẽ₆`, `Ẽ₇`, `Ẽ₈` -/

section EulerLattice

/-- The Euler lattice of type `Ẽ₆` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev affineTypeE6BilinearLattice : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice affineTypeE6Matrix

theorem affineTypeE6_isSimplyLaced : BilinearLattice.IsSimplyLaced affineTypeE6Matrix := by
  unfold BilinearLattice.IsSimplyLaced
  intro i j; fin_cases i <;> fin_cases j <;> decide

/-- The Coxeter transformation of `affineTypeE6BilinearLattice` as an integer matrix. `Q ^ 6 - 1`
is square-zero but nonzero. -/
private def affineTypeE6CoxeterTransformation : Matrix (Fin 7) (Fin 7) ℤ :=
  !![0, 1, 0, 0, 0, -1, 0;
     0, 1, 1, 0, 0, -1, -1;
     1, 1, 0, 0, 0, -1, 0;
     0, 1, 1, 0, 0, -1, 0;
     0, 0, 0, 1, 0, -1, 0;
     0, 0, 0, 0, 1, -1, 0;
     0, 1, 0, 0, 0, 0, -1]

/-- `S` is quasi-unipotent of index exactly `2`. -/
theorem affineTypeE6BilinearLattice_isQuasiUnipotent :
    Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE6BilinearLattice.S : Module.End ℤ affineTypeE6BilinearLattice) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE6BilinearLattice.S : Module.End ℤ affineTypeE6BilinearLattice) 1 :=
  ⟨BilinearLattice.ofUnimodular_isQuasiUnipotentOfIndex_two _ _
      affineTypeE6CoxeterTransformation (by decide) (m := 6) (by norm_num) (by decide),
    BilinearLattice.ofUnimodular_not_isQuasiUnipotentOfIndex_one _ _
      affineTypeE6CoxeterTransformation (by decide) (h := 6)
      ![1, 0, 0, 0, 0, 0, 0] ![1, 2, 2, 3, 2, 1, 1] (by decide) (by decide) (by decide)⟩

/-- The Euler lattice of type `Ẽ₇` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev affineTypeE7BilinearLattice : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice affineTypeE7Matrix

theorem affineTypeE7_isSimplyLaced : BilinearLattice.IsSimplyLaced affineTypeE7Matrix := by
  unfold BilinearLattice.IsSimplyLaced
  intro i j; fin_cases i <;> fin_cases j <;> decide

/-- The Coxeter transformation of `affineTypeE7BilinearLattice` as an integer matrix. `Q ^ 12 - 1`
is square-zero but nonzero. -/
private def affineTypeE7CoxeterTransformation : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 1, 0, 0, 0, 0, -1, -1;
     0, 0, 1, 0, 0, 0, -1, 0;
     1, 1, 0, 0, 0, 0, -1, 0;
     0, 1, 1, 0, 0, 0, -1, 0;
     0, 0, 0, 1, 0, 0, -1, 0;
     0, 0, 0, 0, 1, 0, -1, 0;
     0, 0, 0, 0, 0, 1, -1, 0;
     1, 0, 0, 0, 0, 0, 0, -1]

/-- `S` is quasi-unipotent of index exactly `2`. -/
theorem affineTypeE7BilinearLattice_isQuasiUnipotent :
    Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE7BilinearLattice.S : Module.End ℤ affineTypeE7BilinearLattice) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE7BilinearLattice.S : Module.End ℤ affineTypeE7BilinearLattice) 1 :=
  ⟨BilinearLattice.ofUnimodular_isQuasiUnipotentOfIndex_two _ _
      affineTypeE7CoxeterTransformation (by decide) (m := 12) (by norm_num) (by decide),
    BilinearLattice.ofUnimodular_not_isQuasiUnipotentOfIndex_one _ _
      affineTypeE7CoxeterTransformation (by decide) (h := 12)
      ![1, 0, 0, 0, 0, 0, 0, 0] ![4, 4, 6, 8, 6, 4, 2, 2] (by decide) (by decide) (by decide)⟩

/-- The Euler lattice of type `Ẽ₈` (see `Coxeter.BilinearLatticeDynkins`). -/
noncomputable abbrev affineTypeE8BilinearLattice : BilinearLattice.{0} :=
  BilinearLattice.eulerLattice affineTypeE8Matrix

theorem affineTypeE8_isSimplyLaced : BilinearLattice.IsSimplyLaced affineTypeE8Matrix := by
  unfold BilinearLattice.IsSimplyLaced
  intro i j; fin_cases i <;> fin_cases j <;> decide

/-- The Coxeter transformation of `affineTypeE8BilinearLattice` as an integer matrix. `Q ^ 30 - 1`
is square-zero but nonzero. -/
private def affineTypeE8CoxeterTransformation : Matrix (Fin 9) (Fin 9) ℤ :=
  !![0, 1, 0, 0, 0, 0, 0, 0, -1;
     0, 0, 1, 0, 0, 0, 0, 0, -1;
     1, 1, 0, 0, 0, 0, 0, 0, -1;
     0, 1, 1, 0, 0, 0, 0, 0, -1;
     0, 0, 0, 1, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 1, 0, 0, 0, -1;
     0, 0, 0, 0, 0, 1, 0, 0, -1;
     0, 0, 0, 0, 0, 0, 1, 0, -1;
     0, 0, 0, 0, 0, 0, 0, 1, -1]

set_option maxRecDepth 100000 in
/-- `S` is quasi-unipotent of index exactly `2`. -/
theorem affineTypeE8BilinearLattice_isQuasiUnipotent :
    Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE8BilinearLattice.S : Module.End ℤ affineTypeE8BilinearLattice) 2 ∧
    ¬ Module.End.IsQuasiUnipotentOfIndex
      (affineTypeE8BilinearLattice.S : Module.End ℤ affineTypeE8BilinearLattice) 1 :=
  ⟨BilinearLattice.ofUnimodular_isQuasiUnipotentOfIndex_two _ _
      affineTypeE8CoxeterTransformation (by decide) (m := 30) (by norm_num) (by decide),
    BilinearLattice.ofUnimodular_not_isQuasiUnipotentOfIndex_one _ _
      affineTypeE8CoxeterTransformation (by decide) (h := 30)
      ![1, 0, 0, 0, 0, 0, 0, 0, 0] ![4, 6, 8, 12, 10, 8, 6, 4, 2]
      (by decide) (by decide) (by decide)⟩

noncomputable abbrev affineTypeE6BilinearLatticeWithMonoidQuasiUnipotent :
    BilinearLattice.BilinearLatticeWithMonoidQuasiUnipotent.{0} :=
  BilinearLattice.eulerLatticeWithMonoidQuasiUnipotent
    (M := affineTypeE6Matrix)
    (hS := affineTypeE6BilinearLattice_isQuasiUnipotent.1)

noncomputable abbrev affineTypeE7BilinearLatticeWithMonoidQuasiUnipotent :
    BilinearLattice.BilinearLatticeWithMonoidQuasiUnipotent.{0} :=
  BilinearLattice.eulerLatticeWithMonoidQuasiUnipotent
    (M := affineTypeE7Matrix)
    (hS := affineTypeE7BilinearLattice_isQuasiUnipotent.1)

noncomputable abbrev affineTypeE8BilinearLatticeWithMonoidQuasiUnipotent :
    BilinearLattice.BilinearLatticeWithMonoidQuasiUnipotent.{0} :=
  BilinearLattice.eulerLatticeWithMonoidQuasiUnipotent
    (M := affineTypeE8Matrix)
    (hS := affineTypeE8BilinearLattice_isQuasiUnipotent.1)

end EulerLattice

end Coxeter
