module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Associated graded ring of a filtered algebra

Given a `CommRing R`, a `Ring A` that is an `R`-algebra,
and an increasing, unital, submultiplicative `ℕ`-indexed filtration
`F : ℕ → Submodule R A` (bundled as `Coxeter.Filtration`),
this file constructs the graded pieces
`F.piece n := F.carrier n ⧸ F.carrier (n - 1)` (with `F.carrier (-1) := ⊥`)
and the bilinear multiplication `F.mulPiece` they inherit from `A`.

`F.AssociatedGraded := ⨁ n, F.piece n` is a full associative, unital `Ring` and `R`-algebra,
all proved: the graded-monoid unitality/associativity laws
(`piece_one_mul`/`piece_mul_one`/`piece_mul_assoc`)
are established by transporting `A`'s own unitality/associativity
across `Nat.zero_add`/`Nat.add_zero`/`Nat.add_assoc`
(`mkPiece_heq`, `coe_carrier_cast`);
the `R`-algebra structure needs no such reindexing,
since scalar multiplication doesn't change degree
(`smul_mul_left`, `mul_smul_right`).

## Main definitions

* `Coxeter.Filtration`
* `Coxeter.Filtration.piece`, `Coxeter.Filtration.mulPiece`
* `Coxeter.Filtration.AssociatedGraded`
-/

@[expose] public section

open DirectSum

namespace Coxeter

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- An increasing, unital, submultiplicative `ℕ`-indexed filtration of an `R`-algebra `A`:
`1 ∈ F.carrier 0`,
`F.carrier` is monotone,
and `F.carrier m * F.carrier n ⊆ F.carrier (m + n)`. -/
structure Filtration (R A : Type*) [CommRing R] [Ring A] [Algebra R A] where
  /-- The `n`-th filtration piece `F n`. -/
  carrier : ℕ → Submodule R A
  mono : Monotone carrier
  one_mem : (1 : A) ∈ carrier 0
  mul_mem : ∀ {m n : ℕ} {x y : A}, x ∈ carrier m → y ∈ carrier n → x * y ∈ carrier (m + n)

namespace Filtration

variable (F : Filtration R A)

/-- `F.below n = F.carrier (n - 1)` (and `F.below 0 = ⊥`):
the filtration piece one degree below `n`,
against which the degree-`n` graded piece `F.piece n` is taken. -/
def below : ℕ → Submodule R A
  | 0 => ⊥
  | n + 1 => F.carrier n

private theorem below_le (n : ℕ) : F.below n ≤ F.carrier n := by
  cases n with
  | zero => exact bot_le
  | succ n => exact F.mono n.le_succ

private theorem mul_mem_below_left {m n : ℕ} {x y : A} (hx : x ∈ F.below m) (hy : y ∈ F.carrier n) :
    x * y ∈ F.below (m + n) := by
  cases m with
  | zero =>
      have : x = 0 := hx
      simp [this]
  | succ m =>
      rw [Nat.succ_add]
      exact F.mul_mem hx hy

private theorem mul_mem_below_right {m n : ℕ} {x y : A}
    (hx : x ∈ F.carrier m) (hy : y ∈ F.below n) :
    x * y ∈ F.below (m + n) := by
  cases n with
  | zero =>
      have : y = 0 := hy
      simp [this]
  | succ n => exact F.mul_mem hx hy

/-- The `n`-th associated graded piece `F.carrier n ⧸ F.below n`. -/
def piece (n : ℕ) : Type _ :=
  F.carrier n ⧸ (F.below n).comap (F.carrier n).subtype

instance piece.addCommGroup (n : ℕ) : AddCommGroup (F.piece n) :=
  inferInstanceAs (AddCommGroup (F.carrier n ⧸ (F.below n).comap (F.carrier n).subtype))

instance piece.module (n : ℕ) : Module R (F.piece n) :=
  inferInstanceAs (Module R (F.carrier n ⧸ (F.below n).comap (F.carrier n).subtype))

/-- The quotient map `F.carrier n → F.piece n`. -/
def mkPiece (n : ℕ) : F.carrier n →ₗ[R] F.piece n :=
  Submodule.mkQ _

/-- The raw multiplication `F.carrier m × F.carrier n → F.piece (m + n)`,
before descending to the quotients `F.piece m`, `F.piece n`. -/
def mulRaw (m n : ℕ) : F.carrier m →ₗ[R] F.carrier n →ₗ[R] F.piece (m + n) :=
  LinearMap.mk₂ R
    (fun x y => F.mkPiece (m + n) ⟨(x : A) * (y : A), F.mul_mem x.2 y.2⟩)
    (fun x₁ x₂ y => by
      simp only [← map_add]
      congr 1
      exact Subtype.ext (add_mul ..))
    (fun c x y => by
      simp only [← map_smul]
      congr 1
      exact Subtype.ext (smul_mul_assoc c (x : A) (y : A)))
    (fun x y₁ y₂ => by
      simp only [← map_add]
      congr 1
      exact Subtype.ext (mul_add ..))
    (fun c x y => by
      simp only [← map_smul]
      congr 1
      exact Subtype.ext (mul_smul_comm c (x : A) (y : A)))

theorem mulRaw_ker_left (m n : ℕ) :
    (F.below m).comap (F.carrier m).subtype ≤ (F.mulRaw m n).ker := by
  intro x hx
  ext y
  exact (Submodule.Quotient.mk_eq_zero _).mpr (F.mul_mem_below_left hx y.2)

theorem mulRaw_ker_right (m n : ℕ) :
    (F.below n).comap (F.carrier n).subtype ≤ (F.mulRaw m n).flip.ker := by
  intro y hy
  ext x
  exact (Submodule.Quotient.mk_eq_zero _).mpr (F.mul_mem_below_right x.2 hy)

/-- The induced multiplication `F.piece m × F.piece n → F.piece (m + n)`. -/
def mulPiece (m n : ℕ) : F.piece m →ₗ[R] F.piece n →ₗ[R] F.piece (m + n) :=
  (F.mulRaw m n).liftQ₂ _ _ (F.mulRaw_ker_left m n) (F.mulRaw_ker_right m n)

@[simp]
private theorem mulPiece_mk (m n : ℕ) (x : F.carrier m) (y : F.carrier n) :
    F.mulPiece m n (F.mkPiece m x) (F.mkPiece n y)
      = F.mkPiece (m + n) ⟨(x : A) * (y : A), F.mul_mem x.2 y.2⟩ :=
  rfl

/-- The distinguished element `1 ∈ F.piece 0`. -/
def onePiece : F.piece 0 := F.mkPiece 0 ⟨1, F.one_mem⟩

instance : GradedMonoid.GMul F.piece where
  mul {i j} a b := F.mulPiece i j a b

instance : GradedMonoid.GOne F.piece where
  one := F.onePiece

instance : DirectSum.GNonUnitalNonAssocSemiring F.piece where
  mul_zero a := map_zero (F.mulPiece _ _ a)
  zero_mul b := LinearMap.map_zero₂ (F.mulPiece _ _) b
  mul_add a b c := map_add (F.mulPiece _ _ a) b c
  add_mul a b c := LinearMap.map_add₂ (F.mulPiece _ _) a b c

/-- The associated graded `R`-module `⨁ n, F.piece n`.
An `abbrev`, not a bare `def` (unlike `Coxeter.NilHeckeAlgebra`):
its ring structure genuinely *is* the direct sum's own,
so `DirectSum`'s lemmas (`of_mul_of`, `of_smul`, ...) apply to it directly. -/
abbrev AssociatedGraded : Type _ := ⨁ n, F.piece n

noncomputable instance : AddCommGroup F.AssociatedGraded :=
  inferInstanceAs (AddCommGroup (⨁ n, F.piece n))

noncomputable instance : Module R F.AssociatedGraded :=
  inferInstanceAs (Module R (⨁ n, F.piece n))

/-- The multiplication on `F.AssociatedGraded` induced degreewise by `mulPiece`:
distributive (`NonUnitalNonAssocSemiring`). -/
noncomputable instance : NonUnitalNonAssocSemiring F.AssociatedGraded :=
  inferInstanceAs (NonUnitalNonAssocSemiring (⨁ n, F.piece n))

instance : One F.AssociatedGraded where
  one := DirectSum.of _ _ (F.onePiece)

theorem natCast_mem (n : ℕ) : (n : A) ∈ F.carrier 0 := by
  induction n with
  | zero => simp [(F.carrier 0).zero_mem]
  | succ n ih => simpa [Nat.cast_succ] using (F.carrier 0).add_mem ih F.one_mem

theorem intCast_mem (z : ℤ) : (z : A) ∈ F.carrier 0 := by
  cases z with
  | ofNat n => simpa using F.natCast_mem n
  | negSucc n => simpa using (F.carrier 0).neg_mem (F.natCast_mem (n + 1))

private theorem mkPiece_surjective (n : ℕ) : Function.Surjective (F.mkPiece n) :=
  Submodule.mkQ_surjective _

/-- Transporting `F.mkPiece m x` across a proof `m = n`
(reinterpreting `x : F.carrier m` as an element of `F.carrier n`)
lands `HEq`-equal to `F.mkPiece n` of the transported element:
the basic tool for comparing graded pieces
at propositionally-but-not-definitionally-equal indices. -/
private theorem mkPiece_heq {m n : ℕ} (h : m = n) (x : F.carrier m) :
    HEq (F.mkPiece m x) (F.mkPiece n (h ▸ x)) := by
  subst h
  rfl

/-- Transporting a carrier element along a proof of index equality
doesn't change its underlying value in `A`. -/
private theorem coe_carrier_cast {m n : ℕ} (h : m = n) (x : F.carrier m) :
    ((h ▸ x : F.carrier n) : A) = (x : A) := by
  subst h
  rfl

/-- The obligation that `1 * a = a` in the graded monoid `F.piece`,
i.e. `A`'s own left unitality
transported across the reindexing `Nat.zero_add`. -/
theorem piece_one_mul (a : GradedMonoid F.piece) :
    (1 : GradedMonoid F.piece) * a = a := by
  obtain ⟨i, a⟩ := a
  obtain ⟨a, rfl⟩ := F.mkPiece_surjective i a
  refine Sigma.ext (zero_add i) ?_
  refine HEq.trans (heq_of_eq (F.mulPiece_mk 0 i ⟨1, F.one_mem⟩ a)) ?_
  refine HEq.trans (F.mkPiece_heq (zero_add i) ⟨(1 : A) * (a : A), F.mul_mem F.one_mem a.2⟩) ?_
  apply heq_of_eq
  congr 1
  exact Subtype.ext (by rw [F.coe_carrier_cast]; exact one_mul (a : A))

/-- The obligation that `a * 1 = a` in the graded monoid `F.piece`,
i.e. `A`'s own right unitality
transported across the reindexing `Nat.add_zero`. -/
theorem piece_mul_one (a : GradedMonoid F.piece) :
    a * (1 : GradedMonoid F.piece) = a := by
  obtain ⟨i, a⟩ := a
  change GradedMonoid.mk (i + 0) (F.mulPiece i 0 a F.onePiece) = GradedMonoid.mk i a
  congr 1
  obtain ⟨a, rfl⟩ := F.mkPiece_surjective i a
  rw [onePiece, mulPiece_mk]
  congr 1
  exact Subtype.ext (mul_one (a : A))

/-- The obligation that multiplication in the graded monoid `F.piece` is associative,
i.e. `A`'s own associativity
transported across the reindexing `Nat.add_assoc`. -/
theorem piece_mul_assoc (a b c : GradedMonoid F.piece) :
    a * b * c = a * (b * c) := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  obtain ⟨k, c⟩ := c
  obtain ⟨a, rfl⟩ := F.mkPiece_surjective i a
  obtain ⟨b, rfl⟩ := F.mkPiece_surjective j b
  obtain ⟨c, rfl⟩ := F.mkPiece_surjective k c
  refine Sigma.ext (add_assoc i j k) ?_
  refine HEq.trans (heq_of_eq (?_ : F.mulPiece (i + j) k
      (F.mulPiece i j (F.mkPiece i a) (F.mkPiece j b)) (F.mkPiece k c)
      = F.mkPiece (i + j + k) ⟨((a : A) * (b : A)) * (c : A),
          F.mul_mem (F.mul_mem a.2 b.2) c.2⟩)) ?_
  · rw [mulPiece_mk, mulPiece_mk]
  refine HEq.trans (F.mkPiece_heq (add_assoc i j k)
    ⟨((a : A) * (b : A)) * (c : A), F.mul_mem (F.mul_mem a.2 b.2) c.2⟩) ?_
  refine heq_of_eq (?_ : F.mkPiece (i + (j + k)) _
      = F.mulPiece i (j + k) (F.mkPiece i a) (F.mulPiece j k (F.mkPiece j b) (F.mkPiece k c)))
  rw [mulPiece_mk, mulPiece_mk]
  congr 1
  exact Subtype.ext (by rw [F.coe_carrier_cast]; exact mul_assoc (a : A) (b : A) (c : A))

instance : GradedMonoid.GMonoid F.piece where
  one_mul := F.piece_one_mul
  mul_one := F.piece_mul_one
  mul_assoc := F.piece_mul_assoc

/-- Everything a `DirectSum.GSemiring` needs beyond `GNonUnitalNonAssocSemiring`/`GMonoid`
(the natural-number cast into `F.piece 0`) is genuinely provable:
`F.carrier 0` is a submodule containing `1`,
hence closed under the `ℕ`-fold sums that define `Nat.cast`. -/
instance : DirectSum.GSemiring F.piece :=
  { (inferInstance : DirectSum.GNonUnitalNonAssocSemiring F.piece),
    (inferInstance : GradedMonoid.GMonoid F.piece) with
    natCast := fun n => F.mkPiece 0 ⟨(n : A), F.natCast_mem n⟩
    natCast_zero := by
      change F.mkPiece 0 ⟨((0 : ℕ) : A), F.natCast_mem 0⟩ = 0
      rw [← map_zero (F.mkPiece 0)]
      congr 1
      exact Subtype.ext (by norm_num)
    natCast_succ := fun n => by
      change F.mkPiece 0 ⟨((n + 1 : ℕ) : A), F.natCast_mem (n + 1)⟩
        = F.mkPiece 0 ⟨((n : ℕ) : A), F.natCast_mem n⟩ + F.onePiece
      rw [onePiece, ← map_add]
      congr 1
      exact Subtype.ext (by push_cast; ring_nf) }

/-- Likewise, the integer cast into `F.piece 0` is genuinely provable:
`F.carrier 0` is a submodule,
hence also closed under negation. -/
instance : DirectSum.GRing F.piece :=
  { (inferInstance : DirectSum.GSemiring F.piece) with
    intCast := fun z => F.mkPiece 0 ⟨(z : A), F.intCast_mem z⟩
    intCast_ofNat := fun n => by
      change F.mkPiece 0 ⟨((n : ℤ) : A), F.intCast_mem n⟩
        = F.mkPiece 0 ⟨((n : ℕ) : A), F.natCast_mem n⟩
      congr 1
      exact Subtype.ext (by push_cast; ring_nf)
    intCast_negSucc_ofNat := fun n => by
      change F.mkPiece 0 ⟨((Int.negSucc n : ℤ) : A), F.intCast_mem (Int.negSucc n)⟩
        = -F.mkPiece 0 ⟨(((n + 1 : ℕ)) : A), F.natCast_mem (n + 1)⟩
      rw [← map_neg]
      congr 1
      exact Subtype.ext (by push_cast [Int.negSucc_eq]; ring_nf) }

/-- `F.AssociatedGraded` as an associative, unital `Ring`,
assembled from the `DirectSum.GRing` instance above. -/
noncomputable instance : Ring F.AssociatedGraded :=
  inferInstanceAs (Ring (⨁ n, F.piece n))

/-- `GMul.mul` on `F.piece` unfolds to `F.mulPiece`,
so `mulPiece`'s linearity can be invoked by name below. -/
private theorem gmul_eq_mulPiece {i j : ℕ} (a : F.piece i) (b : F.piece j) :
    GradedMonoid.GMul.mul a b = F.mulPiece i j a b :=
  rfl

/-- Left `R`-linearity of the graded multiplication, restated for `GMul.mul`. -/
private theorem piece_smul_mul_left (r : R) {i j : ℕ} (a : F.piece i) (b : F.piece j) :
    r • GradedMonoid.GMul.mul a b = GradedMonoid.GMul.mul (r • a) b := by
  rw [gmul_eq_mulPiece, gmul_eq_mulPiece, LinearMap.map_smul₂]

/-- Right `R`-linearity of the graded multiplication, restated for `GMul.mul`. -/
private theorem piece_smul_mul_right (r : R) {i j : ℕ} (a : F.piece i) (b : F.piece j) :
    r • GradedMonoid.GMul.mul a b = GradedMonoid.GMul.mul a (r • b) := by
  rw [gmul_eq_mulPiece, gmul_eq_mulPiece, map_smul]

/-- `(r • x) * y = r • (x * y)` on `F.AssociatedGraded`,
via `DirectSum.induction_on` reducing to `piece_smul_mul_left` on pure tensors. -/
theorem smul_mul_left (r : R) (x y : F.AssociatedGraded) : r • x * y = r • (x * y) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [zero_mul, smul_zero]
  | of i a =>
      induction y using DirectSum.induction_on with
      | zero => simp only [mul_zero, smul_zero]
      | of j b =>
          rw [DirectSum.of_mul_of, ← DirectSum.of_smul, ← DirectSum.of_smul,
            DirectSum.of_mul_of]
          exact congrArg (DirectSum.of F.piece (i + j)) (F.piece_smul_mul_left r a b).symm
      | add y y' hy hy' => simp [mul_add, smul_add, hy, hy']
  | add x x' hx hx' => simp [add_mul, smul_add, hx, hx']

/-- `x * (r • y) = r • (x * y)` on `F.AssociatedGraded`,
via `DirectSum.induction_on` reducing to `piece_smul_mul_right` on pure tensors. -/
theorem mul_smul_right (r : R) (x y : F.AssociatedGraded) : x * r • y = r • (x * y) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [zero_mul, smul_zero]
  | of i a =>
      induction y using DirectSum.induction_on with
      | zero => simp only [mul_zero, smul_zero]
      | of j b =>
          rw [DirectSum.of_mul_of, ← DirectSum.of_smul, ← DirectSum.of_smul,
            DirectSum.of_mul_of]
          exact congrArg (DirectSum.of F.piece (i + j)) (F.piece_smul_mul_right r a b).symm
      | add y y' hy hy' => simp [mul_add, smul_add, hy, hy']
  | add x x' hx hx' => simp [add_mul, smul_add, hx, hx']

/-- `F.AssociatedGraded` as an `R`-algebra, via `Algebra.ofModule`:
no `Nat`-reindexing is involved here, unlike `Ring`,
since scalar multiplication doesn't change degree. -/
noncomputable instance : Algebra R F.AssociatedGraded :=
  Algebra.ofModule F.smul_mul_left F.mul_smul_right

end Filtration

end Coxeter
