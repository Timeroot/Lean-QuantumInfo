/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.TraceNorm.Distance
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Finite-dimensional Schatten `p`-norm kernels

This module introduces the PSD matrix power-trace expression, the associated
spectral Schatten `p`-norm expression, and the finite-dimensional PSD trace
Holder upper bounds used by the one-shot Renyi proof route.

The reverse-Holder and support-domination side of the route is handled by
separate negative-power infrastructure.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix Polynomial

namespace QIT

universe u v

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

omit [DecidableEq a] in
theorem partialTraceB_leftKroneckerOne_mul
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : CMatrix a) :
    partialTraceB (a := a) (b := b) (Matrix.kronecker U (1 : CMatrix b) * X) =
      U * partialTraceB (a := a) (b := b) X := by
  ext i i'
  simp [partialTraceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]

omit [DecidableEq a] in
theorem partialTraceB_mul_leftKroneckerOne
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : CMatrix a) :
    partialTraceB (a := a) (b := b) (X * Matrix.kronecker U (1 : CMatrix b)) =
      partialTraceB (a := a) (b := b) X * U := by
  ext i i'
  simp [partialTraceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem partialTraceB_left_unitary_conj
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : Matrix.unitaryGroup a ℂ) :
    partialTraceB (a := a) (b := b)
        (star (Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)) * X *
          Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)) =
      star (U : CMatrix a) * partialTraceB (a := a) (b := b) X *
        (U : CMatrix a) := by
  have hstar :
      star (Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)) =
        Matrix.kronecker (star (U : CMatrix a)) (1 : CMatrix b) := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.conjTranspose_kronecker (U : CMatrix a) (1 : CMatrix b)
  rw [hstar]
  calc
    partialTraceB (a := a) (b := b)
        ((Matrix.kronecker (star (U : CMatrix a)) (1 : CMatrix b) * X) *
          Matrix.kronecker (U : CMatrix a) (1 : CMatrix b))
        =
          partialTraceB (a := a) (b := b)
            (Matrix.kronecker (star (U : CMatrix a)) (1 : CMatrix b) * X) *
            (U : CMatrix a) := by
            rw [partialTraceB_mul_leftKroneckerOne]
    _ = (star (U : CMatrix a) * partialTraceB (a := a) (b := b) X) *
          (U : CMatrix a) := by
            rw [partialTraceB_leftKroneckerOne_mul]
    _ = star (U : CMatrix a) * partialTraceB (a := a) (b := b) X *
          (U : CMatrix a) := by
            rw [Matrix.mul_assoc]

theorem partialTraceB_right_unitary_conj
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (V : Matrix.unitaryGroup b ℂ) :
    partialTraceB (a := a) (b := b)
        (star (Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)) * X *
          Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)) =
      partialTraceB (a := a) (b := b) X := by
  classical
  ext i i'
  have hstar :
      star (Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)) =
        Matrix.kronecker (1 : CMatrix a) (star (V : CMatrix b)) := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.conjTranspose_kronecker (1 : CMatrix a) (V : CMatrix b)
  rw [hstar]
  simp [partialTraceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum, mul_left_comm, mul_comm]
  have hunit : (V : CMatrix b) * star (V : CMatrix b) = 1 :=
    Unitary.coe_mul_star_self V
  have hrow : ∀ x₁ x₂ : b,
      (∑ x, (V : CMatrix b) x₁ x * star ((V : CMatrix b) x₂ x)) =
        if x₁ = x₂ then 1 else 0 := by
    intro x₁ x₂
    have h := congrFun (congrFun hunit x₁) x₂
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] using h
  calc
    ∑ x, ∑ x_1, ∑ x_2,
        X (i, x_2) (i', x_1) *
          ((V : CMatrix b) x_1 x * star ((V : CMatrix b) x_2 x))
        =
      ∑ x_1, ∑ x_2, ∑ x,
        X (i, x_2) (i', x_1) *
          ((V : CMatrix b) x_1 x * star ((V : CMatrix b) x_2 x)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x_1 _ => ?_
        rw [Finset.sum_comm]
    _ =
      ∑ x_1, ∑ x_2,
        X (i, x_2) (i', x_1) *
          (∑ x, (V : CMatrix b) x_1 x * star ((V : CMatrix b) x_2 x)) := by
        simp [Finset.mul_sum]
    _ = ∑ x_1, ∑ x_2,
        X (i, x_2) (i', x_1) * (if x_1 = x_2 then 1 else 0) := by
        simp_rw [hrow]
    _ = ∑ j, X (i, j) (i', j) := by
        simp

theorem partialTraceA_rightKroneckerOne_mul
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (V : CMatrix b) :
    partialTraceA (a := a) (b := b) (Matrix.kronecker (1 : CMatrix a) V * X) =
      V * partialTraceA (a := a) (b := b) X := by
  ext j j'
  simp [partialTraceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem partialTraceA_mul_rightKroneckerOne
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (V : CMatrix b) :
    partialTraceA (a := a) (b := b) (X * Matrix.kronecker (1 : CMatrix a) V) =
      partialTraceA (a := a) (b := b) X * V := by
  ext j j'
  simp [partialTraceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem partialTraceA_right_unitary_conj
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (V : Matrix.unitaryGroup b ℂ) :
    partialTraceA (a := a) (b := b)
        (star (Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)) * X *
          Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)) =
      star (V : CMatrix b) * partialTraceA (a := a) (b := b) X *
        (V : CMatrix b) := by
  have hstar :
      star (Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)) =
        Matrix.kronecker (1 : CMatrix a) (star (V : CMatrix b)) := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.conjTranspose_kronecker (1 : CMatrix a) (V : CMatrix b)
  rw [hstar]
  calc
    partialTraceA (a := a) (b := b)
        ((Matrix.kronecker (1 : CMatrix a) (star (V : CMatrix b)) * X) *
          Matrix.kronecker (1 : CMatrix a) (V : CMatrix b))
        =
          partialTraceA (a := a) (b := b)
            (Matrix.kronecker (1 : CMatrix a) (star (V : CMatrix b)) * X) *
            (V : CMatrix b) := by
            rw [partialTraceA_mul_rightKroneckerOne]
    _ = (star (V : CMatrix b) * partialTraceA (a := a) (b := b) X) *
          (V : CMatrix b) := by
            rw [partialTraceA_rightKroneckerOne_mul]
    _ = star (V : CMatrix b) * partialTraceA (a := a) (b := b) X *
          (V : CMatrix b) := by
            rw [Matrix.mul_assoc]

theorem partialTraceA_left_unitary_conj
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : Matrix.unitaryGroup a ℂ) :
    partialTraceA (a := a) (b := b)
        (star (Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)) * X *
          Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)) =
      partialTraceA (a := a) (b := b) X := by
  classical
  ext j j'
  have hstar :
      star (Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)) =
        Matrix.kronecker (star (U : CMatrix a)) (1 : CMatrix b) := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.conjTranspose_kronecker (U : CMatrix a) (1 : CMatrix b)
  rw [hstar]
  simp [partialTraceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum, mul_left_comm, mul_comm]
  have hunit : (U : CMatrix a) * star (U : CMatrix a) = 1 :=
    Unitary.coe_mul_star_self U
  have hrow : ∀ x₁ x₂ : a,
      (∑ x, (U : CMatrix a) x₁ x * star ((U : CMatrix a) x₂ x)) =
        if x₁ = x₂ then 1 else 0 := by
    intro x₁ x₂
    have h := congrFun (congrFun hunit x₁) x₂
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] using h
  calc
    ∑ x, ∑ x_1, ∑ x_2,
        X (x_2, j) (x_1, j') *
          ((U : CMatrix a) x_1 x * star ((U : CMatrix a) x_2 x))
        =
      ∑ x_1, ∑ x_2, ∑ x,
        X (x_2, j) (x_1, j') *
          ((U : CMatrix a) x_1 x * star ((U : CMatrix a) x_2 x)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x_1 _ => ?_
        rw [Finset.sum_comm]
    _ =
      ∑ x_1, ∑ x_2,
        X (x_2, j) (x_1, j') *
          (∑ x, (U : CMatrix a) x_1 x * star ((U : CMatrix a) x_2 x)) := by
        simp [Finset.mul_sum]
    _ = ∑ x_1, ∑ x_2,
        X (x_2, j) (x_1, j') * (if x_1 = x_2 then 1 else 0) := by
        simp_rw [hrow]
    _ = ∑ i, X (i, j) (i, j') := by
        simp

theorem partialTraceB_local_unitary_conj
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : Matrix.unitaryGroup a ℂ)
    (V : Matrix.unitaryGroup b ℂ) :
    partialTraceB (a := a) (b := b)
        (star (Matrix.kronecker (U : CMatrix a) (V : CMatrix b)) * X *
          Matrix.kronecker (U : CMatrix a) (V : CMatrix b)) =
      star (U : CMatrix a) * partialTraceB (a := a) (b := b) X *
        (U : CMatrix a) := by
  let K : CMatrix (Prod a b) := Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)
  let L : CMatrix (Prod a b) := Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)
  have hfactor :
      Matrix.kronecker (U : CMatrix a) (V : CMatrix b) = K * L := by
    simpa using
      (Matrix.mul_kronecker_mul (U : CMatrix a) (1 : CMatrix a)
        (1 : CMatrix b) (V : CMatrix b))
  rw [hfactor]
  have houter :
      partialTraceB (a := a) (b := b) (star (K * L) * X * (K * L)) =
        partialTraceB (a := a) (b := b) (star K * X * K) := by
    rw [star_mul]
    simpa [K, L, Matrix.mul_assoc] using
      partialTraceB_right_unitary_conj (a := a) (b := b) (star K * X * K) V
  rw [houter]
  simpa [K] using partialTraceB_left_unitary_conj (a := a) (b := b) X U

theorem partialTraceA_local_unitary_conj
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : Matrix.unitaryGroup a ℂ)
    (V : Matrix.unitaryGroup b ℂ) :
    partialTraceA (a := a) (b := b)
        (star (Matrix.kronecker (U : CMatrix a) (V : CMatrix b)) * X *
          Matrix.kronecker (U : CMatrix a) (V : CMatrix b)) =
      star (V : CMatrix b) * partialTraceA (a := a) (b := b) X *
        (V : CMatrix b) := by
  let K : CMatrix (Prod a b) := Matrix.kronecker (U : CMatrix a) (1 : CMatrix b)
  let L : CMatrix (Prod a b) := Matrix.kronecker (1 : CMatrix a) (V : CMatrix b)
  have hfactor :
      Matrix.kronecker (U : CMatrix a) (V : CMatrix b) = K * L := by
    simpa using
      (Matrix.mul_kronecker_mul (U : CMatrix a) (1 : CMatrix a)
        (1 : CMatrix b) (V : CMatrix b))
  rw [hfactor]
  have houter :
      partialTraceA (a := a) (b := b) (star (K * L) * X * (K * L)) =
        star (V : CMatrix b) *
          partialTraceA (a := a) (b := b) (star K * X * K) *
            (V : CMatrix b) := by
    rw [star_mul]
    simpa [K, L, Matrix.mul_assoc] using
      partialTraceA_right_unitary_conj (a := a) (b := b) (star K * X * K) V
  rw [houter]
  rw [partialTraceA_left_unitary_conj (a := a) (b := b) X U]

theorem kronecker_mem_unitaryGroup
    {b : Type v} [Fintype b] [DecidableEq b]
    (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ) :
    Matrix.kronecker (U : CMatrix a) (V : CMatrix b) ∈
      Matrix.unitaryGroup (Prod a b) ℂ := by
  exact kronecker_mem_unitary U.2 V.2

namespace Matrix

/-- Support domination for finite matrices, represented as kernel inclusion:
`M` is supported by `N` when every vector killed by `N` is also killed by
`M`.  For PSD matrices this is the finite-dimensional `M << N` condition
used in the reverse-Holder variational formula. -/
def Supports (M N : CMatrix a) : Prop :=
  ∀ v : a → ℂ, N.mulVec v = 0 → M.mulVec v = 0

omit [DecidableEq a] in
theorem Supports.refl (M : CMatrix a) : Supports M M :=
  fun _ h => h

omit [DecidableEq a] in
/-- The zero matrix is supported by every right-hand matrix. -/
theorem Supports.zero_left (N : CMatrix a) :
    Supports (0 : CMatrix a) N := by
  intro v _hv
  simp

omit [DecidableEq a] in
/-- Support domination is transitive. -/
theorem Supports.trans {M N P : CMatrix a}
    (hMN : Supports M N) (hNP : Supports N P) :
    Supports M P := by
  intro v hv
  exact hMN v (hNP v hv)

/-- A positive-definite right-hand matrix supports every matrix: its kernel is
zero. -/
theorem Supports.of_right_posDef (M N : CMatrix a) (hN : N.PosDef) :
    Supports M N := by
  intro v hv
  have hvzero : N.mulVec v = N.mulVec 0 := by
    simpa using hv
  have hv0 : v = 0 :=
    (Matrix.mulVec_injective_of_isUnit hN.isUnit) hvzero
  simp [hv0]

omit [DecidableEq a] in
/-- Support domination is closed under adding supported left-hand matrices. -/
theorem Supports.add_left {M P N : CMatrix a}
    (hM : Supports M N) (hP : Supports P N) :
    Supports (M + P) N := by
  intro v hv
  simp [Matrix.add_mulVec, hM v hv, hP v hv]

omit [DecidableEq a] in
/-- Support domination is closed under scalar multiplication on the left. -/
theorem Supports.smul_left {M N : CMatrix a} (c : ℂ)
    (hM : Supports M N) :
    Supports (c • M) N := by
  intro v hv
  simp [Matrix.smul_mulVec, hM v hv]

omit [DecidableEq a] in
/-- If multiplying on the right by `N` fixes `M`, then the right kernel of
`N` is contained in the right kernel of `M`. -/
theorem Supports.of_mul_right_eq_self {M N : CMatrix a}
    (h : M * N = M) :
    Supports M N := by
  intro v hv
  have hmul := congrArg (fun A : CMatrix a => Matrix.mulVec A v) h.symm
  calc
    Matrix.mulVec M v = Matrix.mulVec (M * N) v := by
      simpa using hmul
    _ = Matrix.mulVec M (Matrix.mulVec N v) := by
      rw [Matrix.mulVec_mulVec]
    _ = 0 := by
      simp [hv]

omit [DecidableEq a] in
/-- A PSD summand is supported by the PSD sum. -/
theorem Supports.left_of_posSemidef_add {M N : CMatrix a}
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    Supports M (M + N) := by
  intro v hv
  let qM : ℂ := dotProduct (star v) (Matrix.mulVec M v)
  let qN : ℂ := dotProduct (star v) (Matrix.mulVec N v)
  let f : Bool → ℂ := fun b => cond b qM qN
  have hsum_zero : ∑ b : Bool, f b = 0 := by
    have h := congrArg (fun w => dotProduct (star v) w) hv
    simp [f, qM, qN, Matrix.add_mulVec, dotProduct_add] at h ⊢
    exact h
  have hnonneg : ∀ b ∈ (Finset.univ : Finset Bool), 0 ≤ f b := by
    intro b _hb
    cases b <;> simp [f, qM, qN, hM.dotProduct_mulVec_nonneg,
      hN.dotProduct_mulVec_nonneg]
  have hqM_zero : qM = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero true
      (Finset.mem_univ true)
  exact (hM.dotProduct_mulVec_zero_iff v).mp hqM_zero

omit [DecidableEq a] in
/-- A PSD summand is supported by the PSD sum, right-hand version. -/
theorem Supports.right_of_posSemidef_add {M N : CMatrix a}
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    Supports N (M + N) := by
  simpa [add_comm] using
    (Supports.left_of_posSemidef_add (M := N) (N := M) hN hM)

omit [DecidableEq a] in
/-- A PSD matrix is supported by any sum containing a positive scalar multiple
of itself as a PSD summand. -/
theorem Supports.of_pos_smul_right_add {M N : CMatrix a}
    (hM : M.PosSemidef) (hN : N.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    Supports M (N + ε • M) := by
  have hscaled :
      Supports ((ε : ℝ) • M) (N + ε • M) := by
    simpa using
      (Supports.right_of_posSemidef_add
        (M := N) (N := ((ε : ℝ) • M)) hN
        (Matrix.PosSemidef.smul hM (le_of_lt hε)))
  intro v hv
  have hscaled_zero := hscaled v hv
  have hεC : ε ≠ 0 := ne_of_gt hε
  have hmul :
      ε • Matrix.mulVec M v = 0 := by
    simpa [Matrix.smul_mulVec] using hscaled_zero
  exact smul_eq_zero.mp hmul |>.resolve_left hεC

/-- Entrywise support domination for real diagonal matrices. -/
theorem Supports.diagonal_of_real_zero_imp_zero {d e : a → ℝ}
    (h : ∀ i, e i = 0 → d i = 0) :
    Supports
      (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix a)
      (Matrix.diagonal fun i => ((e i : ℝ) : ℂ) : CMatrix a) := by
  intro v hv
  ext i
  have hi := congrFun hv i
  by_cases he : e i = 0
  · simp [Matrix.mulVec, dotProduct, Matrix.diagonal, h i he]
  · have heC : ((e i : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast he
    have hvi : v i = 0 := by
      simpa [Matrix.mulVec, dotProduct, Matrix.diagonal, heC] using hi
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal, hvi]

variable {r : Type v} [Fintype r] [DecidableEq r]

/-- Rectangular isometry conjugation only adds zero eigenvalues.

This charpoly identity is the finite-dimensional spectral bridge needed when a
positive matrix is embedded as `V A Vᴴ` with `Vᴴ V = I`.  Downstream
power-trace invariance lemmas can combine it with the Hermitian eigenvalue
API; the proof itself is just Mathlib's rectangular `AB`/`BA` characteristic
polynomial identity. -/
theorem charpoly_isometry_conj
    (V : Matrix r a ℂ) (A : CMatrix a)
    (hV : Matrix.conjTranspose V * V = (1 : CMatrix a)) :
    Polynomial.X ^ Fintype.card a *
        (V * A * Matrix.conjTranspose V).charpoly =
      Polynomial.X ^ Fintype.card r * A.charpoly := by
  have h :=
    Matrix.charpoly_mul_comm' (A := V * A) (B := Matrix.conjTranspose V)
  have hleft : (V * A) * Matrix.conjTranspose V =
      V * A * Matrix.conjTranspose V := by
    simp [Matrix.mul_assoc]
  have hright : Matrix.conjTranspose V * (V * A) = A := by
    calc
      Matrix.conjTranspose V * (V * A) =
          (Matrix.conjTranspose V * V) * A := by
            rw [Matrix.mul_assoc]
      _ = (1 : CMatrix a) * A := by rw [hV]
      _ = A := by simp
  rw [hleft, hright] at h
  exact h

/-- The zero roots contributed by powers of `X` do not affect sums of positive
real powers of real parts. -/
theorem roots_X_pow_map_re_rpow_sum_zero (n : ℕ) {p : ℝ} (hp : 0 < p) :
    ((Polynomial.X ^ n : ℂ[X]).roots.map (fun z : ℂ => z.re ^ p)).sum = 0 := by
  rw [Polynomial.roots_X_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton]
  have hz : Complex.re 0 ^ p = (0 : ℝ) := by
    simpa using Real.zero_rpow (ne_of_gt hp)
  rw [hz]
  simp

/-- If two characteristic-polynomial identities differ only by powers of `X`,
then the positive real-power sums over their nonzero roots agree.

This is the root-level handoff for rectangular isometry embeddings: the
extra roots produced by `V A Vᴴ` are zeros, and positive powers kill them. -/
theorem roots_re_rpow_sum_eq_of_X_pow_mul_eq
    {P Q : ℂ[X]} {m n : ℕ} {p : ℝ} (hp : 0 < p)
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : Polynomial.X ^ m * P = Polynomial.X ^ n * Q) :
    (P.roots.map (fun z : ℂ => z.re ^ p)).sum =
      (Q.roots.map (fun z : ℂ => z.re ^ p)).sum := by
  have hXm : (Polynomial.X ^ m : ℂ[X]) ≠ 0 := by simp
  have hXn : (Polynomial.X ^ n : ℂ[X]) ≠ 0 := by simp
  have hleft_ne : (Polynomial.X ^ m : ℂ[X]) * P ≠ 0 := mul_ne_zero hXm hP
  have hright_ne : (Polynomial.X ^ n : ℂ[X]) * Q ≠ 0 := mul_ne_zero hXn hQ
  have hroots := congrArg Polynomial.roots h
  rw [Polynomial.roots_mul hleft_ne, Polynomial.roots_mul hright_ne] at hroots
  have hsum :=
    congrArg (fun s : Multiset ℂ => (s.map (fun z : ℂ => z.re ^ p)).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add] at hsum
  rw [roots_X_pow_map_re_rpow_sum_zero m hp,
    roots_X_pow_map_re_rpow_sum_zero n hp] at hsum
  simpa using hsum

/-- Rectangular isometry conjugation as a non-unital star algebra homomorphism.

This is the right algebraic object for non-unital continuous functional
calculus: `X ↦ V X Vᴴ` preserves products and stars whenever `Vᴴ V = I`, but
it does not preserve the unit unless `V` is square unitary. -/
noncomputable def isometryConjNonUnitalStarAlgHom
    (V : Matrix r a ℂ) (hV : Matrix.conjTranspose V * V = (1 : CMatrix a)) :
    CMatrix a →⋆ₙₐ[ℂ] CMatrix r where
  toFun A := V * A * Matrix.conjTranspose V
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_mul' A B := by
    calc
      V * (A * B) * Matrix.conjTranspose V =
          V * A * (Matrix.conjTranspose V * V) * B * Matrix.conjTranspose V := by
            rw [hV]
            simp [Matrix.mul_assoc]
      _ = (V * A * Matrix.conjTranspose V) *
            (V * B * Matrix.conjTranspose V) := by
            simp [Matrix.mul_assoc]
  map_smul' c A := by
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  map_star' A := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Support domination is invariant under simultaneous unitary conjugation. -/
theorem Supports.unitary_conj {M N : CMatrix a} (h : Supports M N)
    (U : Matrix.unitaryGroup a ℂ) :
    Supports
      ((U : CMatrix a) * M * star (U : CMatrix a))
      ((U : CMatrix a) * N * star (U : CMatrix a)) := by
  intro v hv
  have hleft := congrArg (fun w => star (U : CMatrix a) *ᵥ w) hv
  have hN : N *ᵥ (star (U : CMatrix a) *ᵥ v) = 0 := by
    have hUU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
      Unitary.coe_star_mul_self U
    have hmat : star (U : CMatrix a) * ((U : CMatrix a) * N * star (U : CMatrix a)) =
        N * star (U : CMatrix a) := by
      calc
        star (U : CMatrix a) * ((U : CMatrix a) * N * star (U : CMatrix a))
            = (star (U : CMatrix a) * ((U : CMatrix a) * N)) *
                star (U : CMatrix a) := by noncomm_ring
        _ = ((star (U : CMatrix a) * (U : CMatrix a)) * N) *
                star (U : CMatrix a) := by rw [← Matrix.mul_assoc]
        _ = N * star (U : CMatrix a) := by rw [hUU, Matrix.one_mul]
    simpa [Matrix.mulVec_mulVec, hmat] using hleft
  have hM : M *ᵥ (star (U : CMatrix a) *ᵥ v) = 0 :=
    h (star (U : CMatrix a) *ᵥ v) hN
  have hright := congrArg (fun w => (U : CMatrix a) *ᵥ w) hM
  have hUU : (U : CMatrix a) * star (U : CMatrix a) = 1 :=
    Unitary.coe_mul_star_self U
  have hmat : (U : CMatrix a) * (M * star (U : CMatrix a)) =
      (U : CMatrix a) * M * star (U : CMatrix a) := by
    rw [Matrix.mul_assoc]
  simpa [Matrix.mulVec_mulVec, hmat, hUU] using hright

end Matrix

/-- Each row of a finite unitary matrix has squared entry norms summing to one. -/
theorem unitary_row_normSq_sum (U : Matrix.unitaryGroup a ℂ) (i : a) :
    ∑ j, Complex.normSq ((U : CMatrix a) i j) = 1 := by
  have hunit : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
    exact Unitary.coe_mul_star_self U
  have hij := congrFun (congrFun hunit i) i
  have hre := congrArg Complex.re hij
  simpa [Matrix.mul_apply, Matrix.one_apply, Complex.normSq_eq_conj_mul_self,
    mul_comm] using hre

/-- Each column of a finite unitary matrix has squared entry norms summing to one. -/
theorem unitary_col_normSq_sum (U : Matrix.unitaryGroup a ℂ) (j : a) :
    ∑ i, Complex.normSq ((U : CMatrix a) i j) = 1 := by
  have hunit : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
    exact Unitary.coe_star_mul_self U
  have hij := congrFun (congrFun hunit j) j
  have hre := congrArg Complex.re hij
  simpa [Matrix.mul_apply, Matrix.one_apply, Complex.normSq_eq_conj_mul_self,
    mul_comm] using hre

/-- A PSD matrix diagonal entry is the convex spectral average determined by
the corresponding eigenvector-unitary row. -/
theorem posSemidef_diagonal_re_eq_eigenvalue_weighted_sum
    {B : CMatrix a} (hB : B.PosSemidef) (i : a) :
    (B i i).re =
      ∑ j, hB.isHermitian.eigenvalues j *
        Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hB.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun j => ((hB.isHermitian.eigenvalues j : ℝ) : ℂ))
  have hBdiag : B = (U : CMatrix a) * D * (U⁻¹ : Matrix.unitaryGroup a ℂ) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hB.isHermitian.spectral_theorem
  have hentry := congrFun (congrFun hBdiag i) i
  have hre := congrArg Complex.re hentry
  simpa [U, D, Matrix.mul_apply, Matrix.diagonal, Complex.normSq_eq_conj_mul_self,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hre

/-- Diagonal entries of a PSD matrix are nonnegative in real part. -/
theorem posSemidef_diagonal_re_nonneg {B : CMatrix a} (hB : B.PosSemidef) (i : a) :
    0 ≤ (B i i).re := by
  rw [posSemidef_diagonal_re_eq_eigenvalue_weighted_sum hB i]
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (hB.eigenvalues_nonneg j) (Complex.normSq_nonneg _)

/-- A PSD matrix with a zero diagonal entry has the corresponding row and
column equal to zero. This is the finite-dimensional kernel fact used when a
supported input is moved into the spectral basis of a singular reference. -/
theorem posSemidef_zero_diag_zero_row_col
    {A : CMatrix a} (hA : A.PosSemidef) {i : a} (hii : A i i = 0) (j : a) :
    A i j = 0 ∧ A j i = 0 := by
  classical
  set e : a → ℂ := Pi.single i 1 with he
  have hei : e i = (1 : ℂ) := by
    rw [he, Pi.single_apply, if_pos rfl]
  have hek : ∀ k, k ≠ i → e k = 0 := fun k hk => by
    rw [he, Pi.single_apply, if_neg hk]
  have hmulVec : Matrix.mulVec A e = fun k => A k i := by
    ext k
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
    · simp [hei]
    · intro m _ hm
      simp [hek m hm]
    · simp [hei]
  have hform : dotProduct (star e) (Matrix.mulVec A e) = A i i := by
    rw [hmulVec, dotProduct, Finset.sum_eq_single i]
    · simp [hei]
    · intro k _ hk
      simp [hek k hk]
    · simp [hei]
  have hcol : Matrix.mulVec A e = 0 :=
    (hA.dotProduct_mulVec_zero_iff e).mp (by rw [hform, hii])
  have hji : A j i = 0 := by
    have h1 : (fun k => A k i) j = 0 := by
      rw [← hmulVec, hcol]
      simp
    exact h1
  refine ⟨?_, hji⟩
  have hherm : star A = A := hA.isHermitian.eq
  have hij : A i j = star (A j i) := by
    rw [show A i j = star A i j from by rw [hherm], Matrix.star_apply A i j]
  rw [hij, hji, star_zero]

/-- Real zero diagonal form of `posSemidef_zero_diag_zero_row_col`. -/
theorem posSemidef_zero_diag_re_zero_row_col
    {A : CMatrix a} (hA : A.PosSemidef) {i : a}
    (hii : (A i i).re = 0) (j : a) :
    A i j = 0 ∧ A j i = 0 := by
  have hdiag_nonneg : 0 ≤ A i i := Matrix.PosSemidef.diag_nonneg hA (i := i)
  have hdiag_im : (A i i).im = 0 := (Complex.nonneg_iff.mp hdiag_nonneg).2.symm
  have hdiag : A i i = 0 := by
    apply Complex.ext
    · simpa using hii
    · simpa using hdiag_im
  exact posSemidef_zero_diag_zero_row_col hA hdiag j

/-- Trace pairing with a PSD left factor, expanded in that factor's eigenbasis. -/
theorem posSemidef_trace_mul_eq_eigenvalue_conjugate_diag_sum
    {M B : CMatrix a} (hM : M.PosSemidef) :
    ((M * B).trace).re =
      ∑ i, hM.isHermitian.eigenvalues i *
        ((star (hM.isHermitian.eigenvectorUnitary : CMatrix a) * B *
          (hM.isHermitian.eigenvectorUnitary : CMatrix a)) i i).re := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hM.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun i => ((hM.isHermitian.eigenvalues i : ℝ) : ℂ))
  let B' : CMatrix a := star (U : CMatrix a) * B * (U : CMatrix a)
  have hMdiag : M = (U : CMatrix a) * D * (U⁻¹ : Matrix.unitaryGroup a ℂ) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hM.isHermitian.spectral_theorem
  have htrace :
      (M * B).trace = (D * B').trace := by
    calc
      (M * B).trace =
          (((U : CMatrix a) * D * (U⁻¹ : Matrix.unitaryGroup a ℂ)) * B).trace := by
            rw [hMdiag]
      _ = (((U : CMatrix a) * (D * (star (U : CMatrix a) * B)))).trace := by
            rw [Matrix.mul_assoc]
            simp [Matrix.mul_assoc]
      _ = ((D * (star (U : CMatrix a) * B)) * (U : CMatrix a)).trace := by
            exact Matrix.trace_mul_comm (U : CMatrix a)
              (D * (star (U : CMatrix a) * B))
      _ = (D * B').trace := by
            simp [B', Matrix.mul_assoc]
  have hdiag :
      (D * B').trace =
        ∑ i, ((hM.isHermitian.eigenvalues i : ℝ) : ℂ) * B' i i := by
    simp [D, Matrix.trace, Matrix.diagonal_mul]
  have hre := congrArg Complex.re (htrace.trans hdiag)
  simpa [U, B', Complex.mul_re] using hre

/-- Jensen bound for PSD diagonal entries: the `q`-power of a diagonal entry is
bounded by the matching convex combination of spectral `q`-powers. -/
theorem posSemidef_diagonal_re_rpow_le_eigenvalue_weighted_rpow
    {B : CMatrix a} (hB : B.PosSemidef) {q : ℝ} (hq : 1 ≤ q) (i : a) :
    (B i i).re ^ q ≤
      ∑ j, Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
        hB.isHermitian.eigenvalues j ^ q := by
  classical
  let w : a → ℝ := fun j =>
    Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j)
  let evals : a → ℝ := fun j => hB.isHermitian.eigenvalues j
  have hw_nonneg : ∀ j ∈ (Finset.univ : Finset a), 0 ≤ w j := by
    intro j _
    exact Complex.normSq_nonneg _
  have hw_sum : ∑ j ∈ (Finset.univ : Finset a), w j = 1 := by
    simpa [w] using unitary_row_normSq_sum hB.isHermitian.eigenvectorUnitary i
  have hevals_mem : ∀ j ∈ (Finset.univ : Finset a), evals j ∈ Set.Ici (0 : ℝ) := by
    intro j _
    exact hB.eigenvalues_nonneg j
  have hjensen :=
    (convexOn_rpow hq).map_sum_le
      (t := (Finset.univ : Finset a)) (w := w) (p := evals)
      hw_nonneg hw_sum hevals_mem
  have hdiag :
      (B i i).re = ∑ j ∈ (Finset.univ : Finset a), w j * evals j := by
    simpa [w, evals, mul_comm] using
      posSemidef_diagonal_re_eq_eigenvalue_weighted_sum hB i
  rw [hdiag]
  simpa [w, evals, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hjensen

/-- Concave Jensen bound for PSD diagonal entries in the range `0 ≤ p ≤ 1`:
the spectral `p`-power average of a diagonal entry is bounded by the
`p`-power of that diagonal entry. -/
theorem eigenvalue_weighted_rpow_le_posSemidef_diagonal_re_rpow
    {B : CMatrix a} (hB : B.PosSemidef) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : a) :
    (∑ j, Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
        hB.isHermitian.eigenvalues j ^ p) ≤
      (B i i).re ^ p := by
  classical
  let w : a → ℝ := fun j =>
    Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j)
  let evals : a → ℝ := fun j => hB.isHermitian.eigenvalues j
  have hw_nonneg : ∀ j ∈ (Finset.univ : Finset a), 0 ≤ w j := by
    intro j _
    exact Complex.normSq_nonneg _
  have hw_sum : ∑ j ∈ (Finset.univ : Finset a), w j = 1 := by
    simpa [w] using unitary_row_normSq_sum hB.isHermitian.eigenvectorUnitary i
  have hevals_mem : ∀ j ∈ (Finset.univ : Finset a), evals j ∈ Set.Ici (0 : ℝ) := by
    intro j _
    exact hB.eigenvalues_nonneg j
  have hjensen :=
    (Real.concaveOn_rpow hp0 hp1).le_map_sum
      (t := (Finset.univ : Finset a)) (w := w) (p := evals)
      hw_nonneg hw_sum hevals_mem
  have hdiag :
      (B i i).re = ∑ j ∈ (Finset.univ : Finset a), w j * evals j := by
    simpa [w, evals, mul_comm] using
      posSemidef_diagonal_re_eq_eigenvalue_weighted_sum hB i
  rw [hdiag]
  simpa [w, evals, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hjensen

/-- Real powers of positive semidefinite matrices are positive semidefinite. -/
theorem cMatrix_rpow_posSemidef {s : ℝ} {A : CMatrix a}
    (_hA : A.PosSemidef) :
    (CFC.rpow A s).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := A) (y := s))

/-- Power-of-power reduction for PSD matrices and nonnegative exponents. -/
theorem cMatrix_rpow_rpow_of_nonneg {A : CMatrix a} (hA : A.PosSemidef)
    {r t s : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) (hrt : r * t = s) :
    CFC.rpow (CFC.rpow A r) t = CFC.rpow A s := by
  rw [show CFC.rpow (CFC.rpow A r) t = CFC.rpow A (r * t) by
    exact CFC.rpow_rpow_of_exponent_nonneg A r t hr ht
      (Matrix.nonneg_iff_posSemidef.mpr hA)]
  rw [hrt]

/-- The real spectrum of a real diagonal complex matrix is its diagonal range. -/
theorem spectrum_real_diagonal_ofReal
    (d : a → ℝ) :
    spectrum ℝ (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) = Set.range d := by
  ext r
  rw [← spectrum.algebraMap_mem_iff ℂ]
  change (r : ℂ) ∈ spectrum ℂ (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) ↔
    r ∈ Set.range d
  rw [spectrum_diagonal]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, Complex.ofReal_injective hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

/-- Polynomial functional calculus is entrywise on real diagonal matrices. -/
theorem aeval_diagonal_ofReal
    (d : a → ℝ) (p : Polynomial ℝ) :
    aeval (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) p =
      Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) := by
  let dC : a → ℂ := fun i => (d i : ℂ)
  change aeval (Matrix.diagonal dC) p =
    Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ))
  rw [show Matrix.diagonal dC = Matrix.diagonalAlgHom (R := ℝ) dC by rfl]
  rw [Polynomial.aeval_algHom (Matrix.diagonalAlgHom (R := ℝ)) dC]
  rw [Polynomial.aeval_pi]
  ext i j
  by_cases h : i = j
  · subst j
    simpa [Matrix.diagonal, dC, Polynomial.aeval_def] using
      (Polynomial.eval₂_at_apply (p := p) (algebraMap ℝ ℂ) (d i))
  · simp [Matrix.diagonal, h]

/-- Continuous functional calculus is entrywise on real diagonal matrices. -/
theorem cfc_diagonal_ofReal
    (d : a → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) =
      Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  obtain ⟨p, hp⟩ :=
    (Polynomial.exists_eval_eq_iff d (fun i => f (d i))).mpr (by
      intro i j hij
      simp [hij])
  calc
    cfc f (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) =
        cfc p.eval (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) := by
      apply cfc_congr
      intro x hx
      rw [spectrum_real_diagonal_ofReal d] at hx
      rcases hx with ⟨i, rfl⟩
      exact (hp i).symm
    _ = aeval (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) p := by
      exact cfc_polynomial (q := p)
        (a := (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a))
        (ha := by
          rw [isSelfAdjoint_iff, star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
          ext i j
          by_cases h : i = j
          · subst j
            simp
          · simp [Matrix.diagonal, h])
    _ = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
      rw [aeval_diagonal_ofReal d p]
      ext i j
      by_cases h : i = j
      · subst j
        simp [hp i]
      · simp [Matrix.diagonal, h]

/-- Real powers of nonnegative real diagonal matrices are entrywise powers. -/
theorem cMatrix_rpow_diagonal_ofReal
    (d : a → ℝ) (hd : ∀ i, 0 ≤ d i) (s : ℝ) :
    CFC.rpow (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) s =
      Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) := by
  change ((Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) ^ s) =
    Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ))
  have hnonneg : 0 ≤ (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a) :=
    Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.PosSemidef.diagonal (d := fun i => (d i : ℂ)) (by
        intro i
        change (0 : ℂ) ≤ (d i : ℂ)
        exact_mod_cast hd i))
  rw [CFC.rpow_eq_cfc_real (a := (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a))
    (y := s) hnonneg]
  exact cfc_diagonal_ofReal d (fun x => x ^ s)

/-- The real spectrum of a unitary conjugate of a real diagonal complex matrix
is still the diagonal range. -/
theorem spectrum_real_unitary_conj_diagonal_ofReal
    (U : Matrix.unitaryGroup a ℂ) (d : a → ℝ) :
    spectrum ℝ
      ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) = Set.range d := by
  let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
  have hspec :
      spectrum ℝ
        ((Unitary.conjStarAlgAut ℂ (CMatrix a) U) D) =
          spectrum ℝ D := by
    exact AlgEquiv.spectrum_eq
      ((Unitary.conjStarAlgAut ℂ (CMatrix a) U).restrictScalars ℝ) D
  calc
    spectrum ℝ
      ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) =
        spectrum ℝ ((Unitary.conjStarAlgAut ℂ (CMatrix a) U) D) := by
          simp [D, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
    _ = spectrum ℝ D := hspec
    _ = Set.range d := spectrum_real_diagonal_ofReal d

/-- Polynomial functional calculus is transported by a fixed unitary
conjugation on real diagonal matrices. -/
theorem aeval_unitary_conj_diagonal_ofReal
    (U : Matrix.unitaryGroup a ℂ) (d : a → ℝ) (p : Polynomial ℝ) :
    aeval ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) p =
      (U : CMatrix a) *
        Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
  let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
  have hmap :
      (Unitary.conjStarAlgAut ℂ (CMatrix a) U)
        (aeval D p) =
        aeval ((Unitary.conjStarAlgAut ℂ (CMatrix a) U) D) p := by
    simpa using
      (Polynomial.aeval_algHom_apply
        ((Unitary.conjStarAlgAut ℂ (CMatrix a) U).restrictScalars ℝ)
          D p).symm
  have hdiag := aeval_diagonal_ofReal d p
  calc
    aeval ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) p =
        aeval ((Unitary.conjStarAlgAut ℂ (CMatrix a) U) D) p := by
          simp [D, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
    _ = (Unitary.conjStarAlgAut ℂ (CMatrix a) U) (aeval D p) := hmap.symm
    _ = (Unitary.conjStarAlgAut ℂ (CMatrix a) U)
          (Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ))) := by
          rw [hdiag]
    _ = (U : CMatrix a) *
        Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
          simp [Unitary.conjStarAlgAut_apply]

/-- Continuous functional calculus, in finite-dimensional matrix form, is
entrywise on a real diagonal matrix after a fixed unitary conjugation.  The
proof uses polynomial interpolation on the finite spectrum, so it is valid for
functions such as negative real powers at zero-spectrum points. -/
theorem cfc_unitary_conj_diagonal_ofReal
    (U : Matrix.unitaryGroup a ℂ) (d : a → ℝ) (f : ℝ → ℝ) :
    cfc f ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) =
      (U : CMatrix a) *
        Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
  classical
  obtain ⟨p, hp⟩ :=
    (Polynomial.exists_eval_eq_iff d (fun i => f (d i))).mpr (by
      intro i j hij
      simp [hij])
  calc
    cfc f ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) =
        cfc p.eval ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
          star (U : CMatrix a)) := by
      apply cfc_congr
      intro x hx
      rw [spectrum_real_unitary_conj_diagonal_ofReal U d] at hx
      rcases hx with ⟨i, rfl⟩
      exact (hp i).symm
    _ = aeval ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
          star (U : CMatrix a)) p := by
      exact cfc_polynomial (q := p)
        (a := ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
          star (U : CMatrix a)))
        (ha := by
          let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
          have hDself : star D = D := by
            ext i j
            by_cases h : i = j
            · subst j
              simp [D, Matrix.diagonal]
            · have hji : j ≠ i := Ne.symm h
              simp [D, Matrix.diagonal, h, hji]
          rw [isSelfAdjoint_iff]
          change star ((U : CMatrix a) * D * star (U : CMatrix a)) =
            (U : CMatrix a) * D * star (U : CMatrix a)
          calc
            star ((U : CMatrix a) * D * star (U : CMatrix a))
                = star (star (U : CMatrix a)) * star D * star (U : CMatrix a) := by
                  simp [star_mul, Matrix.mul_assoc]
            _ = (U : CMatrix a) * D * star (U : CMatrix a) := by
                  rw [hDself]
                  simp)
    _ = (U : CMatrix a) *
        Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
      rw [aeval_unitary_conj_diagonal_ofReal U d p]
      ext i j
      simp [hp]

/-- Real powers of a unitary conjugate of a nonnegative real diagonal matrix
are computed in the same diagonalizing basis for every real exponent. -/
theorem cMatrix_rpow_unitary_conj_diagonal_ofReal
    (U : Matrix.unitaryGroup a ℂ) (d : a → ℝ) (hd : ∀ i, 0 ≤ d i) (s : ℝ) :
    CFC.rpow ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) s =
      (U : CMatrix a) *
        Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
  change (((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) ^ s) =
      (U : CMatrix a) *
        Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) *
        star (U : CMatrix a)
  have hdiag : (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a).PosSemidef :=
    Matrix.PosSemidef.diagonal (d := fun i => (d i : ℂ)) (by
      intro i
      change (0 : ℂ) ≤ (d i : ℂ)
      exact_mod_cast hd i)
  have hnonneg :
      0 ≤ ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) :=
    Matrix.nonneg_iff_posSemidef.mpr
      (hdiag.mul_mul_conjTranspose_same (U : CMatrix a))
  rw [CFC.rpow_eq_cfc_real
    (a := ((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
      star (U : CMatrix a))) (y := s) hnonneg]
  exact cfc_unitary_conj_diagonal_ofReal U d (fun x => x ^ s)

/-- Trace of a unitary conjugate of a real diagonal matrix. -/
theorem trace_unitary_conj_diagonal_ofReal_re
    (U : Matrix.unitaryGroup a ℂ) (d : a → ℝ) :
    (((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)).trace).re = ∑ i, d i := by
  let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
  have hUU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  have htrace :
      (((U : CMatrix a) * D * star (U : CMatrix a)).trace) =
        D.trace := by
    calc
      (((U : CMatrix a) * D * star (U : CMatrix a)).trace)
          = (star (U : CMatrix a) * ((U : CMatrix a) * D)).trace := by
              exact Matrix.trace_mul_comm ((U : CMatrix a) * D) (star (U : CMatrix a))
      _ = D.trace := by
              rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  rw [htrace]
  simp [D, Matrix.trace_diagonal]

/-- Trace pairing of two real diagonal matrices conjugated by the same unitary. -/
theorem trace_mul_unitary_conj_diagonal_ofReal_re
    (U : Matrix.unitaryGroup a ℂ) (d e : a → ℝ) :
    ((((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) *
      ((U : CMatrix a) * (Matrix.diagonal fun i => (e i : ℂ)) *
        star (U : CMatrix a))).trace).re = ∑ i, d i * e i := by
  let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
  let E : CMatrix a := Matrix.diagonal fun i => (e i : ℂ)
  have hUU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  have hprod :
      ((U : CMatrix a) * D * star (U : CMatrix a)) *
        ((U : CMatrix a) * E * star (U : CMatrix a)) =
          (U : CMatrix a) * (D * E) * star (U : CMatrix a) := by
    calc
      ((U : CMatrix a) * D * star (U : CMatrix a)) *
        ((U : CMatrix a) * E * star (U : CMatrix a))
          = (U : CMatrix a) * D * (star (U : CMatrix a) * (U : CMatrix a)) *
              E * star (U : CMatrix a) := by noncomm_ring
      _ = (U : CMatrix a) * (D * E) * star (U : CMatrix a) := by
              rw [hUU]
              noncomm_ring
  calc
    ((((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) *
      ((U : CMatrix a) * (Matrix.diagonal fun i => (e i : ℂ)) *
        star (U : CMatrix a))).trace).re
        = (((U : CMatrix a) * (D * E) * star (U : CMatrix a)).trace).re := by
            rw [hprod]
    _ = ∑ i, d i * e i := by
            have hDE :
                D * E = Matrix.diagonal (fun i => (((d i * e i : ℝ)) : ℂ)) := by
              dsimp [D, E]
              rw [Matrix.diagonal_mul_diagonal]
              ext i j
              simp [Complex.ofReal_mul]
            rw [hDE]
            simpa using trace_unitary_conj_diagonal_ofReal_re U (fun i => d i * e i)

/-- Trace pairing of two real diagonal matrices conjugated by possibly
different unitaries. -/
theorem trace_mul_two_unitary_conj_diagonal_ofReal_re
    (U V : Matrix.unitaryGroup a ℂ) (d e : a → ℝ) :
    ((((U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a)) *
      ((V : CMatrix a) * (Matrix.diagonal fun i => (e i : ℂ)) *
        star (V : CMatrix a))).trace).re =
      ∑ i : a, ∑ j : a,
        d i * e j * Complex.normSq ((star (U : CMatrix a) * (V : CMatrix a)) i j) := by
  let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
  let E : CMatrix a := Matrix.diagonal fun i => (e i : ℂ)
  let W : CMatrix a := star (U : CMatrix a) * (V : CMatrix a)
  have htrace :
      (((U : CMatrix a) * D * star (U : CMatrix a)) *
        ((V : CMatrix a) * E * star (V : CMatrix a))).trace =
        (D * W * E * star W).trace := by
    calc
      (((U : CMatrix a) * D * star (U : CMatrix a)) *
        ((V : CMatrix a) * E * star (V : CMatrix a))).trace =
          ((U : CMatrix a) *
            (D * star (U : CMatrix a) * ((V : CMatrix a) * E * star (V : CMatrix a)))).trace := by
            congr 1
            noncomm_ring
      _ = ((D * star (U : CMatrix a) * ((V : CMatrix a) * E * star (V : CMatrix a))) *
            (U : CMatrix a)).trace := by
            rw [Matrix.trace_mul_comm]
      _ = (D * (star (U : CMatrix a) * (V : CMatrix a)) *
            E * (star (V : CMatrix a) * (U : CMatrix a))).trace := by
            congr 1
            noncomm_ring
      _ = (D * W * E * star W).trace := by
            simp [W, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  rw [htrace]
  change ((D * W * E * star W).trace).re =
    ∑ i : a, ∑ j : a, d i * e j * Complex.normSq (W i j)
  simp [D, E, Matrix.trace, Matrix.mul_apply, Matrix.diagonal,
    Matrix.star_apply, Complex.normSq_apply, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm]

/-- Real powers of a PSD matrix are diagonalized by the same eigenbasis, with
entrywise real powers of the eigenvalues. -/
theorem cMatrix_rpow_eq_eigenbasis_diagonal
    {A : CMatrix a} (hA : A.PosSemidef) (s : ℝ) :
    CFC.rpow A s =
      (hA.isHermitian.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i => ((hA.isHermitian.eigenvalues i ^ s : ℝ) : ℂ)) *
          star (hA.isHermitian.eigenvectorUnitary : CMatrix a) := by
  change A ^ s =
      (hA.isHermitian.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i => ((hA.isHermitian.eigenvalues i ^ s : ℝ) : ℂ)) *
          star (hA.isHermitian.eigenvectorUnitary : CMatrix a)
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s)
    (ha := Matrix.nonneg_iff_posSemidef.mpr hA)]
  rw [hA.isHermitian.cfc_eq]
  simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def]

/-- Finite-dimensional complex powers of a positive-definite matrix, expressed
in its spectral basis.

This is the matrix-valued analytic family needed for Riesz-Thorin style
interpolation. The real-axis compatibility theorem below connects it back to
the repository's existing `CFC.rpow` API. -/
def cMatrixPosDefComplexPower
    (A : CMatrix a) (hA : A.PosDef) (z : ℂ) : CMatrix a :=
  (hA.posSemidef.isHermitian.eigenvectorUnitary : CMatrix a) *
    Matrix.diagonal
      (fun i =>
        Complex.exp (z * ((Real.log (hA.posSemidef.isHermitian.eigenvalues i) : ℝ) : ℂ))) *
      star (hA.posSemidef.isHermitian.eigenvectorUnitary : CMatrix a)

/-- The positive-definite complex-power path is complex differentiable as a
matrix-valued function. -/
theorem cMatrixPosDefComplexPower_differentiable
    {A : CMatrix a} (hA : A.PosDef) :
    Differentiable ℂ (fun z : ℂ => cMatrixPosDefComplexPower A hA z) := by
  let U : Matrix.unitaryGroup a ℂ := hA.posSemidef.isHermitian.eigenvectorUnitary
  let D : ℂ → CMatrix a := fun z =>
    Matrix.diagonal
      (fun i =>
        Complex.exp (z * ((Real.log (hA.posSemidef.isHermitian.eigenvalues i) : ℝ) : ℂ)))
  have hD : Differentiable ℂ D := by
    apply differentiable_pi.2
    intro i
    apply differentiable_pi.2
    intro j
    by_cases hij : i = j
    · subst j
      simp [D, Matrix.diagonal]
    · simp [D, Matrix.diagonal, hij]
  change Differentiable ℂ fun z : ℂ => (U : CMatrix a) * D z * star (U : CMatrix a)
  have hD_entry (r c : a) : Differentiable ℂ fun z : ℂ => D z r c := by
    exact differentiable_pi.mp (differentiable_pi.mp hD r) c
  apply differentiable_pi.2
  intro i
  apply differentiable_pi.2
  intro j
  simp only [Matrix.mul_apply]
  have houter' : Differentiable ℂ
      (∑ x, fun z : ℂ => (∑ y, (U : CMatrix a) i y * D z y x) *
        star (U : CMatrix a) x j) :=
    Differentiable.sum (u := Finset.univ)
      (A := fun x z => (∑ y, (U : CMatrix a) i y * D z y x) *
        star (U : CMatrix a) x j)
      (fun x _ => by
        have hinner' : Differentiable ℂ
            (∑ y, fun z : ℂ => (U : CMatrix a) i y * D z y x) :=
          Differentiable.sum (u := Finset.univ)
            (A := fun y z => (U : CMatrix a) i y * D z y x)
            (fun y _ => (hD_entry y x).const_mul ((U : CMatrix a) i y))
        have hinner : Differentiable ℂ fun z : ℂ =>
            ∑ y, (U : CMatrix a) i y * D z y x := by
          convert hinner' using 1
          ext z
          simp
        exact hinner.mul_const (star (U : CMatrix a) x j))
  convert houter' using 1
  ext z
  simp

/-- Positive-definite complex powers are differentiable along every complex
affine path `z ↦ m * z + c`.

This avoids instance ambiguity when composing matrix-valued complex powers with
scalar affine maps in downstream interpolation proofs. -/
theorem cMatrixPosDefComplexPower_affine_differentiable
    {A : CMatrix a} (hA : A.PosDef) (m c : ℂ) :
    Differentiable ℂ fun z : ℂ => cMatrixPosDefComplexPower A hA (m * z + c) := by
  let U : Matrix.unitaryGroup a ℂ := hA.posSemidef.isHermitian.eigenvectorUnitary
  let D : ℂ → CMatrix a := fun z =>
    Matrix.diagonal
      (fun i =>
        Complex.exp
          ((m * z + c) *
            ((Real.log (hA.posSemidef.isHermitian.eigenvalues i) : ℝ) : ℂ)))
  have hD : Differentiable ℂ D := by
    apply differentiable_pi.2
    intro i
    apply differentiable_pi.2
    intro j
    by_cases hij : i = j
    · subst j
      simp [D, Matrix.diagonal]
      fun_prop
    · simp [D, Matrix.diagonal, hij]
  change Differentiable ℂ fun z : ℂ => (U : CMatrix a) * D z * star (U : CMatrix a)
  have hD_entry (r c' : a) : Differentiable ℂ fun z : ℂ => D z r c' := by
    exact differentiable_pi.mp (differentiable_pi.mp hD r) c'
  apply differentiable_pi.2
  intro i
  apply differentiable_pi.2
  intro j
  simp only [Matrix.mul_apply]
  have houter' : Differentiable ℂ
      (∑ x, fun z : ℂ => (∑ y, (U : CMatrix a) i y * D z y x) *
        star (U : CMatrix a) x j) :=
    Differentiable.sum (u := Finset.univ)
      (A := fun x z => (∑ y, (U : CMatrix a) i y * D z y x) *
        star (U : CMatrix a) x j)
      (fun x _ => by
        have hinner' : Differentiable ℂ
            (∑ y, fun z : ℂ => (U : CMatrix a) i y * D z y x) :=
          Differentiable.sum (u := Finset.univ)
            (A := fun y z => (U : CMatrix a) i y * D z y x)
            (fun y _ => (hD_entry y x).const_mul ((U : CMatrix a) i y))
        have hinner : Differentiable ℂ fun z : ℂ =>
            ∑ y, (U : CMatrix a) i y * D z y x := by
          convert hinner' using 1
          ext z
          simp
        exact hinner.mul_const (star (U : CMatrix a) x j))
  convert houter' using 1
  ext z
  simp

/-- On real exponents, the spectral complex-power family is exactly
`CFC.rpow`. -/
theorem cMatrixPosDefComplexPower_ofReal
    {A : CMatrix a} (hA : A.PosDef) (s : ℝ) :
    cMatrixPosDefComplexPower A hA (s : ℂ) = CFC.rpow A s := by
  unfold cMatrixPosDefComplexPower
  rw [cMatrix_rpow_eq_eigenbasis_diagonal hA.posSemidef s]
  have hdiag :
      Matrix.diagonal
          (fun i =>
            Complex.exp
              ((s : ℂ) *
                ((Real.log (hA.posSemidef.isHermitian.eigenvalues i) : ℝ) : ℂ))) =
        Matrix.diagonal
          (fun i => ((hA.posSemidef.isHermitian.eigenvalues i ^ s : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hpos : 0 < hA.posSemidef.isHermitian.eigenvalues i := hA.eigenvalues_pos i
      have harg :
          (s : ℂ) * ((Real.log (hA.posSemidef.isHermitian.eigenvalues i) : ℝ) : ℂ) =
            ((Real.log (hA.posSemidef.isHermitian.eigenvalues i) * s : ℝ) : ℂ) := by
        norm_num [mul_comm]
      simp [Matrix.diagonal, harg, Real.rpow_def_of_pos hpos, Complex.ofReal_exp]
    · simp [Matrix.diagonal, hij]
  rw [hdiag]

/-- Positive-definite complex powers multiply by adding exponents.

This is the source-aligned algebraic rule needed to factor the Beigi endpoint
weighted map into imaginary unitary rotations and the real unital CP endpoint.
-/
theorem cMatrixPosDefComplexPower_add
    {A : CMatrix a} (hA : A.PosDef) (z w : ℂ) :
    cMatrixPosDefComplexPower A hA z *
        cMatrixPosDefComplexPower A hA w =
      cMatrixPosDefComplexPower A hA (z + w) := by
  let U : Matrix.unitaryGroup a ℂ := hA.posSemidef.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hA.posSemidef.isHermitian.eigenvalues
  let Z : CMatrix a :=
    Matrix.diagonal
      (fun i => Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)))
  let W : CMatrix a :=
    Matrix.diagonal
      (fun i => Complex.exp (w * ((Real.log (d i) : ℝ) : ℂ)))
  let ZW : CMatrix a :=
    Matrix.diagonal
      (fun i => Complex.exp ((z + w) * ((Real.log (d i) : ℝ) : ℂ)))
  have hdiag : Z * W = ZW := by
    ext i j
    by_cases hij : i = j
    · subst j
      have harg :
          z * ((Real.log (d i) : ℝ) : ℂ) +
              w * ((Real.log (d i) : ℝ) : ℂ) =
            (z + w) * ((Real.log (d i) : ℝ) : ℂ) := by ring
      have hmul :
          Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)) *
              Complex.exp (w * ((Real.log (d i) : ℝ) : ℂ)) =
            Complex.exp ((z + w) * ((Real.log (d i) : ℝ) : ℂ)) := by
        rw [← Complex.exp_add, harg]
      simpa [Z, W, ZW, Matrix.mul_apply, Matrix.diagonal] using hmul
    · simp [Z, W, ZW, Matrix.mul_apply, Matrix.diagonal, hij]
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  change ((U : CMatrix a) * Z * star (U : CMatrix a)) *
      ((U : CMatrix a) * W * star (U : CMatrix a)) =
    (U : CMatrix a) * ZW * star (U : CMatrix a)
  calc
    ((U : CMatrix a) * Z * star (U : CMatrix a)) *
        ((U : CMatrix a) * W * star (U : CMatrix a)) =
        (U : CMatrix a) * (Z * W) * star (U : CMatrix a) := by
          calc
            ((U : CMatrix a) * Z * star (U : CMatrix a)) *
                ((U : CMatrix a) * W * star (U : CMatrix a)) =
                (U : CMatrix a) * Z * (star (U : CMatrix a) *
                  (U : CMatrix a)) * W * star (U : CMatrix a) := by
                    noncomm_ring
            _ = (U : CMatrix a) * Z * 1 * W * star (U : CMatrix a) := by
                  rw [hUstarU]
            _ = (U : CMatrix a) * (Z * W) * star (U : CMatrix a) := by
                  simp [Matrix.mul_assoc]
    _ = (U : CMatrix a) * ZW * star (U : CMatrix a) := by rw [hdiag]

/-- Complex powers satisfy the boundary identity
`(A^z)ᴴ A^z = A^(2 Re z)` for positive-definite matrices.

This is the finite-dimensional matrix-power endpoint used by the
Riesz-Thorin interpolation route. -/
theorem cMatrixPosDefComplexPower_star_mul_self
    {A : CMatrix a} (hA : A.PosDef) (z : ℂ) :
    star (cMatrixPosDefComplexPower A hA z) *
        cMatrixPosDefComplexPower A hA z =
      CFC.rpow A (2 * z.re) := by
  let U : Matrix.unitaryGroup a ℂ := hA.posSemidef.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hA.posSemidef.isHermitian.eigenvalues
  let D : CMatrix a :=
    Matrix.diagonal
      (fun i => Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)))
  have hDpow :
      star D * D =
        Matrix.diagonal (fun i => ((d i ^ (2 * z.re) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hpos : 0 < d i := hA.eigenvalues_pos i
      have harg_re : (z * ((Real.log (d i) : ℝ) : ℂ)).re = z.re * Real.log (d i) := by
        simp [Complex.mul_re]
      have hnormSq :
          Complex.normSq (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ))) =
            d i ^ (2 * z.re) := by
        rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, harg_re]
        calc
          (Real.exp (z.re * Real.log (d i))) ^ 2 =
              Real.exp (Real.log (d i) * (2 * z.re)) := by
                rw [sq, ← Real.exp_add]
                congr 1
                ring
          _ = d i ^ (2 * z.re) := by
                rw [Real.rpow_def_of_pos hpos]
      have hstar_mul :
          (starRingEnd ℂ) (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ))) *
              Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)) =
            ((d i ^ (2 * z.re) : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self]
        exact_mod_cast hnormSq
      simpa [D, Matrix.mul_apply, Matrix.diagonal, Matrix.conjTranspose_apply] using hstar_mul
    · have hji : ¬ j = i := fun h => hij h.symm
      simp [D, Matrix.mul_apply, Matrix.diagonal, hij, hji]
  have hUct : Matrix.conjTranspose (U : CMatrix a) = star (U : CMatrix a) := by
    rw [← Matrix.star_eq_conjTranspose]
  have hstarUct : Matrix.conjTranspose (star (U : CMatrix a)) = (U : CMatrix a) := by
    rw [← Matrix.star_eq_conjTranspose, star_star]
  have hDct : Matrix.conjTranspose D = star D := by
    rw [← Matrix.star_eq_conjTranspose]
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  change Matrix.conjTranspose ((U : CMatrix a) * D * star (U : CMatrix a)) *
      ((U : CMatrix a) * D * star (U : CMatrix a)) = CFC.rpow A (2 * z.re)
  calc
    Matrix.conjTranspose ((U : CMatrix a) * D * star (U : CMatrix a)) *
        ((U : CMatrix a) * D * star (U : CMatrix a)) =
        (U : CMatrix a) * (star D * D) * star (U : CMatrix a) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          rw [hstarUct, hDct, hUct]
          have hcollapse :
              star (U : CMatrix a) *
                  ((U : CMatrix a) * (D * star (U : CMatrix a))) =
                D * star (U : CMatrix a) := by
            calc
              star (U : CMatrix a) *
                  ((U : CMatrix a) * (D * star (U : CMatrix a))) =
                  (star (U : CMatrix a) * (U : CMatrix a)) *
                    (D * star (U : CMatrix a)) := by
                    rw [Matrix.mul_assoc]
              _ = 1 * (D * star (U : CMatrix a)) := by rw [hUstarU]
              _ = D * star (U : CMatrix a) := by rw [Matrix.one_mul]
          calc
            (U : CMatrix a) * (star D * star (U : CMatrix a)) *
                ((U : CMatrix a) * D * star (U : CMatrix a)) =
                (U : CMatrix a) * star D *
                  (star (U : CMatrix a) *
                    ((U : CMatrix a) * (D * star (U : CMatrix a)))) := by
                  noncomm_ring
            _ = (U : CMatrix a) * star D * (D * star (U : CMatrix a)) := by
                  rw [hcollapse]
            _ = (U : CMatrix a) * (star D * D) * star (U : CMatrix a) := by
                  noncomm_ring
    _ = (U : CMatrix a) *
          Matrix.diagonal (fun i => ((d i ^ (2 * z.re) : ℝ) : ℂ)) *
            star (U : CMatrix a) := by rw [hDpow]
    _ = CFC.rpow A (2 * z.re) := by
          rw [cMatrix_rpow_eq_eigenbasis_diagonal hA.posSemidef (2 * z.re)]

/-- Positive-definite complex powers are normal; the opposite boundary product
also reduces to the real power `A^(2 Re z)`.

This is the companion endpoint to
`cMatrixPosDefComplexPower_star_mul_self` and is needed when the interpolation
family is used on the Schrödinger side of a trace pairing. -/
theorem cMatrixPosDefComplexPower_mul_star_self
    {A : CMatrix a} (hA : A.PosDef) (z : ℂ) :
    cMatrixPosDefComplexPower A hA z *
        star (cMatrixPosDefComplexPower A hA z) =
      CFC.rpow A (2 * z.re) := by
  let U : Matrix.unitaryGroup a ℂ := hA.posSemidef.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hA.posSemidef.isHermitian.eigenvalues
  let D : CMatrix a :=
    Matrix.diagonal
      (fun i => Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)))
  have hDpow :
      D * star D =
        Matrix.diagonal (fun i => ((d i ^ (2 * z.re) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hpos : 0 < d i := hA.eigenvalues_pos i
      have harg_re : (z * ((Real.log (d i) : ℝ) : ℂ)).re = z.re * Real.log (d i) := by
        simp [Complex.mul_re]
      have hnormSq :
          Complex.normSq (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ))) =
            d i ^ (2 * z.re) := by
        rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, harg_re]
        calc
          (Real.exp (z.re * Real.log (d i))) ^ 2 =
              Real.exp (Real.log (d i) * (2 * z.re)) := by
                rw [sq, ← Real.exp_add]
                congr 1
                ring
          _ = d i ^ (2 * z.re) := by
                rw [Real.rpow_def_of_pos hpos]
      have hstar_mul :
          (starRingEnd ℂ) (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ))) *
              Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)) =
            ((d i ^ (2 * z.re) : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self]
        exact_mod_cast hnormSq
      simpa [D, Matrix.mul_apply, Matrix.diagonal, Matrix.conjTranspose_apply, mul_comm]
        using hstar_mul
    · have hji : ¬ j = i := fun h => hij h.symm
      simp [D, Matrix.mul_apply, Matrix.diagonal, hij, hji]
  have hUct : Matrix.conjTranspose (U : CMatrix a) = star (U : CMatrix a) := by
    rw [← Matrix.star_eq_conjTranspose]
  have hstarUct : Matrix.conjTranspose (star (U : CMatrix a)) = (U : CMatrix a) := by
    rw [← Matrix.star_eq_conjTranspose, star_star]
  have hDct : Matrix.conjTranspose D = star D := by
    rw [← Matrix.star_eq_conjTranspose]
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  change ((U : CMatrix a) * D * star (U : CMatrix a)) *
      Matrix.conjTranspose ((U : CMatrix a) * D * star (U : CMatrix a)) =
    CFC.rpow A (2 * z.re)
  calc
    ((U : CMatrix a) * D * star (U : CMatrix a)) *
        Matrix.conjTranspose ((U : CMatrix a) * D * star (U : CMatrix a)) =
        (U : CMatrix a) * (D * star D) * star (U : CMatrix a) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          rw [hstarUct, hDct, hUct]
          have hcollapse :
              star (U : CMatrix a) *
                  ((U : CMatrix a) * (star D * star (U : CMatrix a))) =
                star D * star (U : CMatrix a) := by
            calc
              star (U : CMatrix a) *
                  ((U : CMatrix a) * (star D * star (U : CMatrix a))) =
                  (star (U : CMatrix a) * (U : CMatrix a)) *
                    (star D * star (U : CMatrix a)) := by
                    rw [Matrix.mul_assoc]
              _ = 1 * (star D * star (U : CMatrix a)) := by rw [hUstarU]
              _ = star D * star (U : CMatrix a) := by rw [Matrix.one_mul]
          calc
            ((U : CMatrix a) * D * star (U : CMatrix a)) *
                ((U : CMatrix a) * (star D * star (U : CMatrix a))) =
                (U : CMatrix a) * D *
                  (star (U : CMatrix a) *
                    ((U : CMatrix a) * (star D * star (U : CMatrix a)))) := by
                  noncomm_ring
            _ = (U : CMatrix a) * D * (star D * star (U : CMatrix a)) := by
                  rw [hcollapse]
            _ = (U : CMatrix a) * (D * star D) * star (U : CMatrix a) := by
                  noncomm_ring
    _ = (U : CMatrix a) *
          Matrix.diagonal (fun i => ((d i ^ (2 * z.re) : ℝ) : ℂ)) *
            star (U : CMatrix a) := by rw [hDpow]
    _ = CFC.rpow A (2 * z.re) := by
          rw [cMatrix_rpow_eq_eigenbasis_diagonal hA.posSemidef (2 * z.re)]

/-- Complex powers sandwich real powers by adding twice the real part of the
complex exponent:
`A^z A^t (A^z)ᴴ = A^(t + 2 Re z)`.

This finite-dimensional identity is the algebraic spine of the strip
interpolation family used for sandwiched Renyi DPI. -/
theorem cMatrixPosDefComplexPower_mul_rpow_mul_star
    {A : CMatrix a} (hA : A.PosDef) (z : ℂ) (t : ℝ) :
    cMatrixPosDefComplexPower A hA z * CFC.rpow A t *
        star (cMatrixPosDefComplexPower A hA z) =
      CFC.rpow A (t + 2 * z.re) := by
  let U : Matrix.unitaryGroup a ℂ := hA.posSemidef.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hA.posSemidef.isHermitian.eigenvalues
  let Z : CMatrix a :=
    Matrix.diagonal
      (fun i => Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)))
  let R : CMatrix a := Matrix.diagonal (fun i => ((d i ^ t : ℝ) : ℂ))
  have hdiag :
      Z * R * star Z =
        Matrix.diagonal (fun i => ((d i ^ (t + 2 * z.re) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hpos : 0 < d i := hA.eigenvalues_pos i
      have harg_re : (z * ((Real.log (d i) : ℝ) : ℂ)).re = z.re * Real.log (d i) := by
        simp [Complex.mul_re]
      have hnormSq :
          Complex.normSq (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ))) =
            d i ^ (2 * z.re) := by
        rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, harg_re]
        calc
          (Real.exp (z.re * Real.log (d i))) ^ 2 =
              Real.exp (Real.log (d i) * (2 * z.re)) := by
                rw [sq, ← Real.exp_add]
                congr 1
                ring
          _ = d i ^ (2 * z.re) := by
                rw [Real.rpow_def_of_pos hpos]
      have hstar_mul :
          (starRingEnd ℂ) (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ))) *
              Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)) =
            ((d i ^ (2 * z.re) : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self]
        exact_mod_cast hnormSq
      have hmul :
          Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)) *
              ((d i ^ t : ℝ) : ℂ) *
              (starRingEnd ℂ)
                (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ))) =
            ((d i ^ (t + 2 * z.re) : ℝ) : ℂ) := by
        calc
          Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)) *
              ((d i ^ t : ℝ) : ℂ) *
              (starRingEnd ℂ)
                (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ))) =
              ((d i ^ t : ℝ) : ℂ) *
                (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)) *
                  (starRingEnd ℂ)
                    (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)))) := by
                ring
          _ = ((d i ^ t : ℝ) : ℂ) * ((d i ^ (2 * z.re) : ℝ) : ℂ) := by
                rw [mul_comm
                  (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)))
                  ((starRingEnd ℂ)
                    (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ))))]
                rw [hstar_mul]
          _ = ((d i ^ t * d i ^ (2 * z.re) : ℝ) : ℂ) := by norm_num
          _ = ((d i ^ (t + 2 * z.re) : ℝ) : ℂ) := by
                rw [Real.rpow_add hpos]
      simpa [Z, R, Matrix.mul_apply, Matrix.diagonal, Matrix.conjTranspose_apply]
        using hmul
    · have hji : ¬ j = i := fun h => hij h.symm
      simp [Z, R, Matrix.mul_apply, Matrix.diagonal, hij, hji]
  have hUct : Matrix.conjTranspose (U : CMatrix a) = star (U : CMatrix a) := by
    rw [← Matrix.star_eq_conjTranspose]
  have hstarUct : Matrix.conjTranspose (star (U : CMatrix a)) = (U : CMatrix a) := by
    rw [← Matrix.star_eq_conjTranspose, star_star]
  have hZct : Matrix.conjTranspose Z = star Z := by
    rw [← Matrix.star_eq_conjTranspose]
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  rw [cMatrix_rpow_eq_eigenbasis_diagonal hA.posSemidef t,
    cMatrix_rpow_eq_eigenbasis_diagonal hA.posSemidef (t + 2 * z.re)]
  change ((U : CMatrix a) * Z * star (U : CMatrix a)) *
      ((U : CMatrix a) * R * star (U : CMatrix a)) *
        Matrix.conjTranspose ((U : CMatrix a) * Z * star (U : CMatrix a)) =
      (U : CMatrix a) *
        Matrix.diagonal (fun i => ((d i ^ (t + 2 * z.re) : ℝ) : ℂ)) *
          star (U : CMatrix a)
  calc
    ((U : CMatrix a) * Z * star (U : CMatrix a)) *
        ((U : CMatrix a) * R * star (U : CMatrix a)) *
          Matrix.conjTranspose ((U : CMatrix a) * Z * star (U : CMatrix a)) =
        (U : CMatrix a) * (Z * R * star Z) * star (U : CMatrix a) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          rw [hstarUct, hZct, hUct]
          calc
            ((U : CMatrix a) * Z * star (U : CMatrix a)) *
                ((U : CMatrix a) * R * star (U : CMatrix a)) *
                  ((U : CMatrix a) * (star Z * star (U : CMatrix a))) =
                ((U : CMatrix a) * Z * (star (U : CMatrix a) * (U : CMatrix a))) *
                  R * (star (U : CMatrix a) * (U : CMatrix a)) *
                    star Z * star (U : CMatrix a) := by
                  noncomm_ring
            _ = (U : CMatrix a) * (Z * R * star Z) * star (U : CMatrix a) := by
                  rw [hUstarU]
                  simp [Matrix.mul_assoc]
    _ = (U : CMatrix a) *
        Matrix.diagonal (fun i => ((d i ^ (t + 2 * z.re) : ℝ) : ℂ)) *
          star (U : CMatrix a) := by rw [hdiag]

/-- On the imaginary axis, positive-definite complex powers are unitary. -/
theorem cMatrixPosDefComplexPower_star_mul_self_of_re_eq_zero
    {A : CMatrix a} (hA : A.PosDef) {z : ℂ} (hz : z.re = 0) :
    star (cMatrixPosDefComplexPower A hA z) *
        cMatrixPosDefComplexPower A hA z = 1 := by
  let U : Matrix.unitaryGroup a ℂ := hA.posSemidef.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hA.posSemidef.isHermitian.eigenvalues
  let D : CMatrix a :=
    Matrix.diagonal
      (fun i => Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)))
  have hDunit : star D * D = (1 : CMatrix a) := by
    ext i j
    by_cases hij : i = j
    · subst j
      have harg_re : (z * ((Real.log (d i) : ℝ) : ℂ)).re = 0 := by
        simp [Complex.mul_re, hz]
      have hnorm : ‖Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ))‖ = 1 := by
        rw [Complex.norm_exp, harg_re, Real.exp_zero]
      have hnormSq :
          Complex.normSq (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ))) = 1 := by
        rw [Complex.normSq_eq_norm_sq, hnorm]
        norm_num
      have hstar_mul :
          (starRingEnd ℂ) (Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ))) *
              Complex.exp (z * ((Real.log (d i) : ℝ) : ℂ)) = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self]
        exact_mod_cast hnormSq
      simpa [D, Matrix.mul_apply, Matrix.diagonal, Matrix.conjTranspose_apply] using hstar_mul
    · have hji : ¬ j = i := fun h => hij h.symm
      simp [D, Matrix.mul_apply, Matrix.diagonal, hij, hji]
  have hUct : Matrix.conjTranspose (U : CMatrix a) = star (U : CMatrix a) := by
    rw [← Matrix.star_eq_conjTranspose]
  have hstarUct : Matrix.conjTranspose (star (U : CMatrix a)) = (U : CMatrix a) := by
    rw [← Matrix.star_eq_conjTranspose, star_star]
  have hDct : Matrix.conjTranspose D = star D := by
    rw [← Matrix.star_eq_conjTranspose]
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
    Unitary.coe_star_mul_self U
  change Matrix.conjTranspose ((U : CMatrix a) * D * star (U : CMatrix a)) *
      ((U : CMatrix a) * D * star (U : CMatrix a)) = 1
  calc
    Matrix.conjTranspose ((U : CMatrix a) * D * star (U : CMatrix a)) *
        ((U : CMatrix a) * D * star (U : CMatrix a)) =
        (U : CMatrix a) * (star D * D) * star (U : CMatrix a) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          rw [hstarUct, hDct, hUct]
          have hcollapse :
              star (U : CMatrix a) *
                  ((U : CMatrix a) * (D * star (U : CMatrix a))) =
                D * star (U : CMatrix a) := by
            calc
              star (U : CMatrix a) *
                  ((U : CMatrix a) * (D * star (U : CMatrix a))) =
                  (star (U : CMatrix a) * (U : CMatrix a)) *
                    (D * star (U : CMatrix a)) := by
                    rw [Matrix.mul_assoc]
              _ = 1 * (D * star (U : CMatrix a)) := by rw [hUstarU]
              _ = D * star (U : CMatrix a) := by rw [Matrix.one_mul]
          calc
            (U : CMatrix a) * (star D * star (U : CMatrix a)) *
                ((U : CMatrix a) * D * star (U : CMatrix a)) =
                (U : CMatrix a) * star D *
                  (star (U : CMatrix a) *
                    ((U : CMatrix a) * (D * star (U : CMatrix a)))) := by
                  noncomm_ring
            _ = (U : CMatrix a) * star D * (D * star (U : CMatrix a)) := by
                  rw [hcollapse]
            _ = (U : CMatrix a) * (star D * D) * star (U : CMatrix a) := by
                  noncomm_ring
    _ = (U : CMatrix a) * 1 * star (U : CMatrix a) := by rw [hDunit]
    _ = 1 := by simp
/-- Positive real powers do not enlarge the support of a PSD matrix. In the
finite-dimensional kernel-inclusion convention, `A^α` is supported by `A`
for every `0 < α`. -/
theorem cMatrix_rpow_supports_self
    {A : CMatrix a} (hA : A.PosSemidef) {α : ℝ} (hα : 0 < α) :
    Matrix.Supports (CFC.rpow A α) A := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hA.isHermitian.eigenvectorUnitary
  let d : a → ℝ := fun i => hA.isHermitian.eigenvalues i
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    exact hA.eigenvalues_nonneg i
  have hdiagSupport :
      Matrix.Supports
        (Matrix.diagonal fun i => ((d i ^ α : ℝ) : ℂ) : CMatrix a)
        (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix a) := by
    apply Matrix.Supports.diagonal_of_real_zero_imp_zero
    intro i hi
    simp [hi, Real.zero_rpow (ne_of_gt hα)]
  have hconj := Matrix.Supports.unitary_conj hdiagSupport U
  have hpow :
      CFC.rpow A α =
        (U : CMatrix a) *
          Matrix.diagonal (fun i => ((d i ^ α : ℝ) : ℂ)) *
          star (U : CMatrix a) := by
    simpa [U, d] using cMatrix_rpow_eq_eigenbasis_diagonal hA α
  have hAdiag :
      A =
        (U : CMatrix a) *
          Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) *
          star (U : CMatrix a) := by
    simpa [U, d, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hA.isHermitian.spectral_theorem
  rw [hpow, hAdiag]
  exact hconj

/-- A positive semidefinite matrix with a zero diagonal entry has zero row and
column at that index. -/
theorem PosSemidef.zero_diag_zero_row_col
    {A : CMatrix a} (hA : A.PosSemidef) {i : a} (hii : A i i = 0) (j : a) :
    A i j = 0 ∧ A j i = 0 := by
  classical
  set e : a → ℂ := Pi.single i 1 with he
  have hei : e i = (1 : ℂ) := by
    rw [he, Pi.single_apply, if_pos rfl]
  have hek : ∀ k, k ≠ i → e k = 0 := fun k hk => by
    rw [he, Pi.single_apply, if_neg hk]
  have hmulVec : Matrix.mulVec A e = fun k => A k i := by
    ext k
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
    · simp [hei]
    · intro m _ hm
      simp [hek m hm]
    · simp [hei]
  have hform : dotProduct (star e) (Matrix.mulVec A e) = A i i := by
    rw [hmulVec, dotProduct, Finset.sum_eq_single i]
    · simp [hei]
    · intro k _ hk
      simp [hek k hk]
    · simp [hei]
  have hcol : Matrix.mulVec A e = 0 :=
    (hA.dotProduct_mulVec_zero_iff e).mp (by rw [hform, hii])
  have hji : A j i = 0 := by
    have h1 : (fun k => A k i) j = 0 := by
      rw [← hmulVec, hcol]
      simp
    exact h1
  refine ⟨?_, hji⟩
  have hherm : star A = A := hA.isHermitian.eq
  have hij : A i j = star (A j i) := by
    rw [show A i j = star A i j from by rw [hherm], Matrix.star_apply A i j]
  rw [hij, hji, star_zero]

omit [Fintype a] [DecidableEq a] in
/-- For a positive semidefinite matrix, a diagonal entry with zero real part is
zero as a complex number. -/
theorem PosSemidef.diag_eq_zero_of_re_eq_zero
    {A : CMatrix a} (hA : A.PosSemidef) {i : a} (hii : (A i i).re = 0) :
    A i i = 0 := by
  have hself : star (A i i) = A i i := by
    have h := congrFun (congrFun hA.isHermitian.eq i) i
    simpa [Matrix.star_apply] using h
  apply Complex.ext
  · simpa using hii
  · have him : -(A i i).im = (A i i).im := by
      simpa using congrArg Complex.im hself
    have him_zero : (A i i).im = 0 := by
      nlinarith [him]
    simpa using him_zero

/-- A PSD matrix whose diagonal entries vanish wherever a nonnegative diagonal
support vanishes is supported by that diagonal matrix. -/
theorem Matrix.Supports.of_posSemidef_diagonal
    {M : CMatrix a} (hM : M.PosSemidef) {d : a → ℝ} (_hd : ∀ i, 0 ≤ d i)
    (hzero : ∀ i, d i = 0 → M i i = 0) :
    Matrix.Supports M
      (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix a) := by
  intro v hv
  ext k
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro j _hj
  by_cases hdj : d j = 0
  · have hcol : M k j = 0 :=
      (PosSemidef.zero_diag_zero_row_col hM (hzero j hdj) k).2
    simp [hcol]
  · have hdjC : ((d j : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hdj
    have hvj : v j = 0 := by
      have hjv := congrFun hv j
      simpa [Matrix.mulVec, dotProduct, Matrix.diagonal, hdjC] using hjv
    simp [hvj]

namespace State

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- A bipartite density matrix is supported on the tensor product of the
supports of its two marginals. This is the finite-dimensional support fact
used to discharge the PSD-domain Petz trace positivity for barred mutual
information. -/
theorem matrix_supports_prod_marginals (ρ : State (Prod a b)) :
    Matrix.Supports ρ.matrix (ρ.marginalA.prod ρ.marginalB).matrix := by
  classical
  let ρA : State a := ρ.marginalA
  let ρB : State b := ρ.marginalB
  let UA : Matrix.unitaryGroup a ℂ := ρA.pos.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ := ρB.pos.isHermitian.eigenvectorUnitary
  let UAB : Matrix.unitaryGroup (Prod a b) ℂ :=
    ⟨Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b),
      kronecker_mem_unitaryGroup UA UB⟩
  let M' : CMatrix (Prod a b) := star (UAB : CMatrix (Prod a b)) * ρ.matrix * UAB
  let dA : a → ℝ := fun i => ρA.pos.isHermitian.eigenvalues i
  let dB : b → ℝ := fun j => ρB.pos.isHermitian.eigenvalues j
  let d : Prod a b → ℝ := fun x => dA x.1 * dB x.2
  have hdA_nonneg : ∀ i, 0 ≤ dA i := by
    intro i
    exact ρA.pos.eigenvalues_nonneg i
  have hdB_nonneg : ∀ j, 0 ≤ dB j := by
    intro j
    exact ρB.pos.eigenvalues_nonneg j
  have hd_nonneg : ∀ x, 0 ≤ d x := by
    intro x
    exact mul_nonneg (hdA_nonneg x.1) (hdB_nonneg x.2)
  have hM'pos : M'.PosSemidef := by
    simpa [M', Matrix.star_eq_conjTranspose] using
      ρ.pos.conjTranspose_mul_mul_same (UAB : CMatrix (Prod a b))
  have hptB :
      partialTraceB (a := a) (b := b) M' =
        Matrix.diagonal fun i => ((dA i : ℝ) : ℂ) := by
    have hloc := partialTraceB_local_unitary_conj (a := a) (b := b) ρ.matrix UA UB
    have hdiag :
        star (UA : CMatrix a) * ρA.matrix * (UA : CMatrix a) =
          Matrix.diagonal fun i => ((dA i : ℝ) : ℂ) := by
      have hspec := ρA.pos.isHermitian.spectral_theorem
      -- The spectral theorem is `ρA = UA * D * UAᴴ`; conjugating by `UAᴴ`
      -- gives the diagonal eigenvalue matrix.
      have hρA :
          ρA.matrix =
            (UA : CMatrix a) * (Matrix.diagonal fun i => ((dA i : ℝ) : ℂ)) *
              star (UA : CMatrix a) := by
        simpa [UA, dA, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
          using hspec
      calc
        star (UA : CMatrix a) * ρA.matrix * (UA : CMatrix a)
            = star (UA : CMatrix a) *
                ((UA : CMatrix a) * (Matrix.diagonal fun i => ((dA i : ℝ) : ℂ)) *
                  star (UA : CMatrix a)) * (UA : CMatrix a) := by
                rw [hρA]
        _ = (star (UA : CMatrix a) * (UA : CMatrix a)) *
              (Matrix.diagonal fun i => ((dA i : ℝ) : ℂ)) *
                (star (UA : CMatrix a) * (UA : CMatrix a)) := by
                noncomm_ring
        _ = Matrix.diagonal fun i => ((dA i : ℝ) : ℂ) := by
                rw [Unitary.coe_star_mul_self]
                simp
    simpa [M', UAB, ρA, State.marginalA_matrix] using hloc.trans hdiag
  have hptA :
      partialTraceA (a := a) (b := b) M' =
        Matrix.diagonal fun j => ((dB j : ℝ) : ℂ) := by
    have hloc := partialTraceA_local_unitary_conj (a := a) (b := b) ρ.matrix UA UB
    have hdiag :
        star (UB : CMatrix b) * ρB.matrix * (UB : CMatrix b) =
          Matrix.diagonal fun j => ((dB j : ℝ) : ℂ) := by
      have hspec := ρB.pos.isHermitian.spectral_theorem
      have hρB :
          ρB.matrix =
            (UB : CMatrix b) * (Matrix.diagonal fun j => ((dB j : ℝ) : ℂ)) *
              star (UB : CMatrix b) := by
        simpa [UB, dB, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
          using hspec
      calc
        star (UB : CMatrix b) * ρB.matrix * (UB : CMatrix b)
            = star (UB : CMatrix b) *
                ((UB : CMatrix b) * (Matrix.diagonal fun j => ((dB j : ℝ) : ℂ)) *
                  star (UB : CMatrix b)) * (UB : CMatrix b) := by
                rw [hρB]
        _ = (star (UB : CMatrix b) * (UB : CMatrix b)) *
              (Matrix.diagonal fun j => ((dB j : ℝ) : ℂ)) *
                (star (UB : CMatrix b) * (UB : CMatrix b)) := by
                noncomm_ring
        _ = Matrix.diagonal fun j => ((dB j : ℝ) : ℂ) := by
                rw [Unitary.coe_star_mul_self]
                simp
    simpa [M', UAB, ρB, State.marginalB_matrix] using hloc.trans hdiag
  have hzero : ∀ x : Prod a b, d x = 0 → M' x x = 0 := by
    intro x hdx
    rcases x with ⟨i, j⟩
    have hcases : dA i = 0 ∨ dB j = 0 := by
      exact mul_eq_zero.mp hdx
    have hdiag_re_zero : (M' (i, j) (i, j)).re = 0 := by
      rcases hcases with hAi | hBj
      · have hsum_complex := congrFun (congrFun hptB i) i
        have hsum_re := congrArg Complex.re hsum_complex
        have hsum_zero : (∑ k : b, (M' (i, k) (i, k)).re) = 0 := by
          simpa [partialTraceB, Matrix.diagonal, dA, hAi] using hsum_re
        have hnonneg : ∀ k ∈ (Finset.univ : Finset b), 0 ≤ (M' (i, k) (i, k)).re := by
          intro k _
          exact posSemidef_diagonal_re_nonneg hM'pos (i, k)
        have hle :
            (M' (i, j) (i, j)).re ≤
              ∑ k : b, (M' (i, k) (i, k)).re :=
          Finset.single_le_sum hnonneg (Finset.mem_univ j)
        exact le_antisymm (by simpa [hsum_zero] using hle)
          (posSemidef_diagonal_re_nonneg hM'pos (i, j))
      · have hsum_complex := congrFun (congrFun hptA j) j
        have hsum_re := congrArg Complex.re hsum_complex
        have hsum_zero : (∑ k : a, (M' (k, j) (k, j)).re) = 0 := by
          simpa [partialTraceA, Matrix.diagonal, dB, hBj] using hsum_re
        have hnonneg : ∀ k ∈ (Finset.univ : Finset a), 0 ≤ (M' (k, j) (k, j)).re := by
          intro k _
          exact posSemidef_diagonal_re_nonneg hM'pos (k, j)
        have hle :
            (M' (i, j) (i, j)).re ≤
              ∑ k : a, (M' (k, j) (k, j)).re :=
          Finset.single_le_sum hnonneg (Finset.mem_univ i)
        exact le_antisymm (by simpa [hsum_zero] using hle)
          (posSemidef_diagonal_re_nonneg hM'pos (i, j))
    exact PosSemidef.diag_eq_zero_of_re_eq_zero hM'pos hdiag_re_zero
  have hdiagSupport :
      Matrix.Supports M'
        (Matrix.diagonal fun x : Prod a b => ((d x : ℝ) : ℂ) : CMatrix (Prod a b)) :=
    Matrix.Supports.of_posSemidef_diagonal hM'pos hd_nonneg hzero
  have hconj := Matrix.Supports.unitary_conj hdiagSupport UAB
  have hMback :
      (UAB : CMatrix (Prod a b)) * M' * star (UAB : CMatrix (Prod a b)) =
        ρ.matrix := by
    have hUU : (UAB : CMatrix (Prod a b)) * star (UAB : CMatrix (Prod a b)) = 1 := by
      exact Unitary.coe_mul_star_self UAB
    change (UAB : CMatrix (Prod a b)) *
        (star (UAB : CMatrix (Prod a b)) * ρ.matrix * (UAB : CMatrix (Prod a b))) *
          star (UAB : CMatrix (Prod a b)) = ρ.matrix
    calc
      (UAB : CMatrix (Prod a b)) *
          (star (UAB : CMatrix (Prod a b)) * ρ.matrix * (UAB : CMatrix (Prod a b))) *
            star (UAB : CMatrix (Prod a b))
          =
            ((UAB : CMatrix (Prod a b)) * star (UAB : CMatrix (Prod a b))) *
              ρ.matrix *
                ((UAB : CMatrix (Prod a b)) * star (UAB : CMatrix (Prod a b))) := by
              noncomm_ring
      _ = ρ.matrix := by
              rw [hUU]
              simp
  have hNback :
      (UAB : CMatrix (Prod a b)) *
          (Matrix.diagonal fun x : Prod a b => ((d x : ℝ) : ℂ)) *
          star (UAB : CMatrix (Prod a b)) =
        (ρA.prod ρB).matrix := by
    have hA :
        ρA.matrix =
          (UA : CMatrix a) * (Matrix.diagonal fun i => ((dA i : ℝ) : ℂ)) *
            star (UA : CMatrix a) := by
      simpa [UA, dA, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
        using ρA.pos.isHermitian.spectral_theorem
    have hB :
        ρB.matrix =
          (UB : CMatrix b) * (Matrix.diagonal fun j => ((dB j : ℝ) : ℂ)) *
            star (UB : CMatrix b) := by
      simpa [UB, dB, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
        using ρB.pos.isHermitian.spectral_theorem
    let DA : CMatrix a := Matrix.diagonal fun i => ((dA i : ℝ) : ℂ)
    let DB : CMatrix b := Matrix.diagonal fun j => ((dB j : ℝ) : ℂ)
    have hD :
        (Matrix.diagonal fun x : Prod a b => ((d x : ℝ) : ℂ) : CMatrix (Prod a b)) =
          Matrix.kronecker DA DB := by
      ext x y
      by_cases hxy : x = y
      · subst y
        simp [DA, DB, d, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.diagonal]
      · have hneq : x.1 ≠ y.1 ∨ x.2 ≠ y.2 := by
          by_cases h1 : x.1 = y.1
          · right
            intro h2
            exact hxy (Prod.ext h1 h2)
          · left
            exact h1
        rcases hneq with hneqA | hneqB
        · simp [DA, DB, d, Matrix.kronecker, Matrix.kroneckerMap_apply,
            Matrix.diagonal, hxy, hneqA]
        · simp [DA, DB, d, Matrix.kronecker, Matrix.kroneckerMap_apply,
            Matrix.diagonal, hxy, hneqB]
    have hUAB :
        (UAB : CMatrix (Prod a b)) =
          Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b) := rfl
    have hstarUAB :
        star (UAB : CMatrix (Prod a b)) =
          Matrix.kronecker (star (UA : CMatrix a)) (star (UB : CMatrix b)) := by
      simpa [UAB, Matrix.star_eq_conjTranspose] using
        Matrix.conjTranspose_kronecker (UA : CMatrix a) (UB : CMatrix b)
    change (UAB : CMatrix (Prod a b)) *
          (Matrix.diagonal fun x : Prod a b => ((d x : ℝ) : ℂ)) *
          star (UAB : CMatrix (Prod a b)) =
        Matrix.kronecker ρA.matrix ρB.matrix
    rw [hD, hUAB, hstarUAB]
    change (Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b) *
          Matrix.kronecker DA DB) *
          Matrix.kronecker (star (UA : CMatrix a)) (star (UB : CMatrix b)) =
        Matrix.kronecker ρA.matrix ρB.matrix
    rw [hA, hB]
    simp [DA, DB, Matrix.mul_kronecker_mul, Matrix.mul_assoc]
  simpa [hMback, hNback, ρA, ρB] using hconj

/-- Positive real powers of a bipartite density matrix are supported on the
tensor product of the supports of its two marginals. -/
theorem rpow_matrix_supports_prod_marginals
    (ρ : State (Prod a b)) {α : ℝ} (hα : 0 < α) :
    Matrix.Supports (CFC.rpow ρ.matrix α) (ρ.marginalA.prod ρ.marginalB).matrix :=
  (cMatrix_rpow_supports_self ρ.pos hα).trans ρ.matrix_supports_prod_marginals

end State

/-- Unitary conjugation preserves positive semidefiniteness. -/
theorem posSemidef_unitary_conj {A : CMatrix a} (hA : A.PosSemidef)
    (U : Matrix.unitaryGroup a ℂ) :
    (star (U : CMatrix a) * A * (U : CMatrix a)).PosSemidef := by
  simpa [Matrix.mul_assoc] using hA.conjTranspose_mul_mul_same (U : CMatrix a)

/-- Real powers commute with inverse unitary conjugation on PSD matrices. -/
theorem cMatrix_rpow_unitary_conj {A : CMatrix a} (hA : A.PosSemidef)
    (U : Matrix.unitaryGroup a ℂ) {s : ℝ} (hs0 : 0 ≤ s) :
    CFC.rpow (star (U : CMatrix a) * A * (U : CMatrix a)) s =
      star (U : CMatrix a) * CFC.rpow A s * (U : CMatrix a) := by
  change (star (U : CMatrix a) * A * (U : CMatrix a)) ^ s =
    star (U : CMatrix a) * (A ^ s) * (U : CMatrix a)
  have hmap_nonneg : 0 ≤ star (U : CMatrix a) * A * (U : CMatrix a) :=
    Matrix.nonneg_iff_posSemidef.mpr (posSemidef_unitary_conj hA U)
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  rw [CFC.rpow_eq_cfc_real (a := star (U : CMatrix a) * A * (U : CMatrix a))
    (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa [Unitary.conjStarAlgAut_symm_apply] using
    (StarAlgHomClass.map_cfc
      ((Unitary.conjStarAlgAut ℂ (CMatrix a) U).symm)
      (fun x : ℝ => x ^ s) A
      (hf := (Real.continuous_rpow_const hs0).continuousOn)
      (hφ := by
        change Continuous fun A : CMatrix a => star (U : CMatrix a) * A * (U : CMatrix a)
        fun_prop)).symm

/-- Real powers commute with forward unitary conjugation on PSD matrices for
nonnegative exponents. -/
theorem cMatrix_rpow_conjStarAlgAut_nonneg
    (U : Matrix.unitaryGroup a ℂ) {A : CMatrix a} (hA : A.PosSemidef)
    {s : ℝ} (hs0 : 0 ≤ s) :
    CFC.rpow (Unitary.conjStarAlgAut ℂ _ U A) s =
      Unitary.conjStarAlgAut ℂ _ U (CFC.rpow A s) := by
  change (Unitary.conjStarAlgAut ℂ _ U A) ^ s =
    Unitary.conjStarAlgAut ℂ _ U (A ^ s)
  have hmap_nonneg : 0 ≤ Unitary.conjStarAlgAut ℂ (CMatrix a) U A := by
    rw [Unitary.conjStarAlgAut_apply]
    exact Matrix.nonneg_iff_posSemidef.mpr
      (hA.mul_mul_conjTranspose_same (U : CMatrix a))
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  rw [CFC.rpow_eq_cfc_real (a := Unitary.conjStarAlgAut ℂ (CMatrix a) U A)
    (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa using
    (StarAlgHomClass.map_cfc
      (Unitary.conjStarAlgAut ℂ (CMatrix a) U)
      (fun x : ℝ => x ^ s) A
      (hf := (Real.continuous_rpow_const hs0).continuousOn)
      (hφ := by
        change Continuous fun A : CMatrix a => (U : CMatrix a) * A * star (U : CMatrix a)
        fun_prop)).symm

private theorem cMatrix_rpow_kronecker_nonneg_core
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {s : ℝ} (hs0 : 0 ≤ s) :
    CFC.rpow (Matrix.kronecker A B) s =
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) := by
  let UA := hA.isHermitian.eigenvectorUnitary
  let UB := hB.isHermitian.eigenvectorUnitary
  let U : Matrix.unitaryGroup (Prod a b) ℂ :=
    ⟨Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b),
      Matrix.kronecker_mem_unitary UA.2 UB.2⟩
  let da : a -> ℝ := hA.isHermitian.eigenvalues
  let db : b -> ℝ := hB.isHermitian.eigenvalues
  let dprod : Prod a b -> ℝ := fun i => da i.1 * db i.2
  have hda : ∀ i, 0 ≤ da i := fun i => hA.eigenvalues_nonneg i
  have hdb : ∀ i, 0 ≤ db i := fun i => hB.eigenvalues_nonneg i
  have hdprod : ∀ i, 0 ≤ dprod i := fun i => mul_nonneg (hda i.1) (hdb i.2)
  have hA_spec :
      A = Unitary.conjStarAlgAut ℂ _ UA
        (Matrix.diagonal (fun i => (da i : ℂ))) := by
    simpa [UA, da, Function.comp_def] using hA.isHermitian.spectral_theorem
  have hB_spec :
      B = Unitary.conjStarAlgAut ℂ _ UB
        (Matrix.diagonal (fun i => (db i : ℂ))) := by
    simpa [UB, db, Function.comp_def] using hB.isHermitian.spectral_theorem
  have hAB_spec :
      Matrix.kronecker A B =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal (fun i => (dprod i : ℂ))) := by
    rw [hA_spec, hB_spec]
    simp [U, dprod, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal, Matrix.mul_assoc]
  have hDprod_psd :
      (Matrix.diagonal (fun i => (dprod i : ℂ)) : CMatrix (Prod a b)).PosSemidef :=
    Matrix.PosSemidef.diagonal (d := fun i => (dprod i : ℂ)) (by
      intro i
      change (0 : ℂ) ≤ (dprod i : ℂ)
      exact_mod_cast hdprod i)
  have hA_rpow :
      CFC.rpow A s =
        Unitary.conjStarAlgAut ℂ _ UA
          (Matrix.diagonal (fun i => ((da i ^ s : ℝ) : ℂ))) := by
    rw [hA_spec]
    rw [cMatrix_rpow_conjStarAlgAut_nonneg UA
      (Matrix.PosSemidef.diagonal (d := fun i => (da i : ℂ)) (by
        intro i
        change (0 : ℂ) ≤ (da i : ℂ)
        exact_mod_cast hda i)) hs0]
    rw [cMatrix_rpow_diagonal_ofReal da hda s]
  have hB_rpow :
      CFC.rpow B s =
        Unitary.conjStarAlgAut ℂ _ UB
          (Matrix.diagonal (fun i => ((db i ^ s : ℝ) : ℂ))) := by
    rw [hB_spec]
    rw [cMatrix_rpow_conjStarAlgAut_nonneg UB
      (Matrix.PosSemidef.diagonal (d := fun i => (db i : ℂ)) (by
        intro i
        change (0 : ℂ) ≤ (db i : ℂ)
        exact_mod_cast hdb i)) hs0]
    rw [cMatrix_rpow_diagonal_ofReal db hdb s]
  have hleft :
      CFC.rpow (Matrix.kronecker A B) s =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal (fun i => ((dprod i ^ s : ℝ) : ℂ))) := by
    rw [hAB_spec]
    rw [cMatrix_rpow_conjStarAlgAut_nonneg U hDprod_psd hs0]
    rw [cMatrix_rpow_diagonal_ofReal dprod hdprod s]
  have hdiag :
      Matrix.diagonal (fun i : Prod a b => ((dprod i ^ s : ℝ) : ℂ)) =
        Matrix.diagonal (fun i : Prod a b =>
          (((da i.1 ^ s) * (db i.2 ^ s) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [dprod, Real.mul_rpow (hda i.1) (hdb i.2)]
    · simp [Matrix.diagonal, hij]
  have hright :
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal (fun i : Prod a b =>
            (((da i.1 ^ s) * (db i.2 ^ s) : ℝ) : ℂ))) := by
    rw [hA_rpow, hB_rpow]
    simp [U, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal, Matrix.mul_assoc]
  rw [hleft, hdiag, hright]

/-- Kronecker products commute with `CFC.rpow` for positive semidefinite
matrices and nonnegative exponents. -/
theorem cMatrix_rpow_kronecker_nonneg
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {s : ℝ} (hs0 : 0 ≤ s) :
    CFC.rpow (Matrix.kronecker A B) s =
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) :=
  cMatrix_rpow_kronecker_nonneg_core hA hB hs0

/-- Real powers commute with forward unitary conjugation on positive-definite
matrices for arbitrary real exponents. -/
theorem cMatrix_rpow_conjStarAlgAut_posDef
    (U : Matrix.unitaryGroup a ℂ) {A : CMatrix a} (hA : A.PosDef)
    (s : ℝ) :
    CFC.rpow (Unitary.conjStarAlgAut ℂ _ U A) s =
      Unitary.conjStarAlgAut ℂ _ U (CFC.rpow A s) := by
  change (Unitary.conjStarAlgAut ℂ _ U A) ^ s =
    Unitary.conjStarAlgAut ℂ _ U (A ^ s)
  have hmap_nonneg : 0 ≤ Unitary.conjStarAlgAut ℂ (CMatrix a) U A := by
    rw [Unitary.conjStarAlgAut_apply]
    exact Matrix.nonneg_iff_posSemidef.mpr
      (hA.posSemidef.mul_mul_conjTranspose_same (U : CMatrix a))
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  rw [CFC.rpow_eq_cfc_real (a := Unitary.conjStarAlgAut ℂ (CMatrix a) U A)
    (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa using
    (StarAlgHomClass.map_cfc
      (Unitary.conjStarAlgAut ℂ (CMatrix a) U)
      (fun x : ℝ => x ^ s) A
      (hf := by
        intro x hx
        exact (Real.continuousAt_rpow_const x s
          (.inl (ne_of_gt ((Matrix.PosDef.isStrictlyPositive hA).spectrum_pos hx)))).continuousWithinAt)
      (hφ := by
        change Continuous fun A : CMatrix a => (U : CMatrix a) * A * star (U : CMatrix a)
        fun_prop)).symm

/-- The `p`-power trace of a positive semidefinite matrix, `Tr A^p`, as a real
number.  The PSD hypothesis is a parameter so downstream theorem statements
carry their domain explicitly. -/
def psdTracePower (A : CMatrix a) (_hA : A.PosSemidef) (p : ℝ) : ℝ :=
  (CFC.rpow A p).trace.re

/-- PSD power traces unfold to the sum of eigenvalue powers. -/
theorem psdTracePower_eq_sum_eigenvalues_rpow
    (A : CMatrix a) (hA : A.PosSemidef) (p : ℝ) :
    psdTracePower A hA p = ∑ i, hA.isHermitian.eigenvalues i ^ p := by
  rw [psdTracePower]
  change (Matrix.trace (A ^ p)).re = ∑ i, hA.isHermitian.eigenvalues i ^ p
  rw [CFC.rpow_eq_cfc_real (a := A) (y := p)
    (ha := Matrix.nonneg_iff_posSemidef.mpr hA)]
  rw [hA.isHermitian.cfc_eq]
  simp only [Matrix.IsHermitian.cfc]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [Function.comp_apply]

/-- PSD power traces are invariant under rectangular isometry conjugation.

For `Vᴴ V = I`, the matrix `V A Vᴴ` has the same nonzero spectrum as `A`,
with only additional zero eigenvalues. Positive powers kill the additional
zero roots, so the `Tr(A^p)` expression is unchanged for `p > 0`. -/
theorem psdTracePower_isometry_conj
    {r : Type v} [Fintype r] [DecidableEq r]
    (V : Matrix r a ℂ) {A : CMatrix a} (hA : A.PosSemidef)
    (hV : Matrix.conjTranspose V * V = (1 : CMatrix a))
    {p : ℝ} (hp : 0 < p) :
    psdTracePower (V * A * Matrix.conjTranspose V)
        (hA.mul_mul_conjTranspose_same V) p =
      psdTracePower A hA p := by
  rw [psdTracePower_eq_sum_eigenvalues_rpow,
    psdTracePower_eq_sum_eigenvalues_rpow]
  have hpoly := Matrix.charpoly_isometry_conj (V := V) A hV
  have hP : (V * A * Matrix.conjTranspose V).charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  have hQ : A.charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  have hroot :=
    Matrix.roots_re_rpow_sum_eq_of_X_pow_mul_eq (p := p) hp hP hQ hpoly
  have hVA := hA.mul_mul_conjTranspose_same V
  have hrootsVA := hVA.isHermitian.roots_charpoly_eq_eigenvalues
  have hrootsA := hA.isHermitian.roots_charpoly_eq_eigenvalues
  rw [hrootsVA, hrootsA] at hroot
  simpa using hroot

/-- Cyclic `AB`/`BA` invariance for PSD power traces.

When both square products are positive semidefinite, `AB` and `BA` have the
same characteristic polynomial, hence the same positive real-power trace. -/
theorem psdTracePower_mul_comm
    {A B : CMatrix a} (hAB : (A * B).PosSemidef) (hBA : (B * A).PosSemidef)
    {p : ℝ} (_hp : 0 < p) :
    psdTracePower (A * B) hAB p = psdTracePower (B * A) hBA p := by
  rw [psdTracePower_eq_sum_eigenvalues_rpow,
    psdTracePower_eq_sum_eigenvalues_rpow]
  have hpoly : (A * B).charpoly = (B * A).charpoly :=
    Matrix.charpoly_mul_comm A B
  have hroots :=
    congrArg (fun P : ℂ[X] => (P.roots.map fun z : ℂ => z.re ^ p).sum) hpoly
  have hrootsAB := hAB.isHermitian.roots_charpoly_eq_eigenvalues
  have hrootsBA := hBA.isHermitian.roots_charpoly_eq_eigenvalues
  simp [hrootsAB, hrootsBA] at hroots
  simpa using hroots

section RpowContinuity

open scoped Matrix.Norms.L2Operator

local instance cMatrixNonUnitalCStarAlgebraForSchattenContinuity
    (n : Type*) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (Matrix n n ℂ) := ⟨⟩

local instance cMatrixCStarAlgebraForSchattenContinuity
    (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) := ⟨⟩

local instance matrixNormalCFCForSchattenContinuity
    (n : Type*) [Fintype n] [DecidableEq n] :
    ContinuousFunctionalCalculus ℂ (Matrix n n ℂ) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance matrixNormalIsometricCFCForSchattenContinuity
    (n : Type*) [Fintype n] [DecidableEq n] :
    IsometricContinuousFunctionalCalculus ℂ (Matrix n n ℂ) IsStarNormal :=
  IsStarNormal.instIsometricContinuousFunctionalCalculus

/-- Positive real powers commute with rectangular isometry conjugation.

The proof uses the non-unital CFC functoriality for the star homomorphism
`X ↦ V X Vᴴ`. The positivity of the exponent is exactly what makes
`x ↦ x^s` vanish at zero, so the non-unital calculus applies. -/
theorem cMatrix_rpow_isometry_conj
    {r : Type v} [Fintype r] [DecidableEq r]
    (V : Matrix r a ℂ) {A : CMatrix a} (hA : A.PosSemidef)
    (hV : Matrix.conjTranspose V * V = (1 : CMatrix a))
    {s : ℝ} (hs : 0 < s) :
    CFC.rpow (V * A * Matrix.conjTranspose V) s =
      V * CFC.rpow A s * Matrix.conjTranspose V := by
  change (V * A * Matrix.conjTranspose V) ^ s =
    V * (A ^ s) * Matrix.conjTranspose V
  let φ := Matrix.isometryConjNonUnitalStarAlgHom V hV
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hVA : (V * A * Matrix.conjTranspose V).PosSemidef :=
    hA.mul_mul_conjTranspose_same V
  have hVA_nonneg : 0 ≤ V * A * Matrix.conjTranspose V :=
    Matrix.nonneg_iff_posSemidef.mpr hVA
  rw [CFC.rpow_eq_cfc_real (a := V * A * Matrix.conjTranspose V)
    (y := s) hVA_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  have hf0 : (fun x : ℝ => x ^ s) 0 = 0 :=
    Real.zero_rpow (ne_of_gt hs)
  have hmap := NonUnitalStarAlgHom.map_cfcₙ (φ := φ) (R := ℝ) (S := ℂ)
    (f := fun x : ℝ => x ^ s) (a := A)
    (hf₀ := hf0)
    (hf := (Real.continuous_rpow_const (le_of_lt hs)).continuousOn)
    (hφ := by
      dsimp [φ, Matrix.isometryConjNonUnitalStarAlgHom]
      refine continuous_matrix ?_
      intro i j
      change Continuous fun A : CMatrix a =>
        (V * A * Matrix.conjTranspose V) i j
      simp only [Matrix.mul_apply]
      fun_prop)
    (ha := by cfc_tac)
    (hφa := by cfc_tac)
  rw [cfcₙ_eq_cfc (f := fun x : ℝ => x ^ s) (a := A)
      ((Real.continuous_rpow_const (le_of_lt hs)).continuousOn) hf0] at hmap
  have hphiA : φ A = V * A * Matrix.conjTranspose V := rfl
  rw [hphiA] at hmap
  rw [cfcₙ_eq_cfc (f := fun x : ℝ => x ^ s)
      (a := V * A * Matrix.conjTranspose V)
      ((Real.continuous_rpow_const (le_of_lt hs)).continuousOn) hf0] at hmap
  simpa [φ, Matrix.isometryConjNonUnitalStarAlgHom] using hmap.symm

/-- Real positive matrix powers are continuous along PSD-constrained
convergent filters.  This is the finite-dimensional CFC continuity step needed
to pass from positive-definite regularizations back to PSD witnesses. -/
theorem cMatrix_rpow_tendsto_of_tendsto_posSemidef
    {X : Type*} {l : Filter X} {F : X → CMatrix a} {A : CMatrix a}
    {p : ℝ} (hp : 0 < p)
    (hF : Filter.Tendsto F l (nhds A))
    (hFpsd : ∀ᶠ x in l, (F x).PosSemidef)
    (hA : A.PosSemidef) :
    Filter.Tendsto (fun x => CFC.rpow (F x) p) l
      (nhds (CFC.rpow A p)) := by
  let f : ℝ≥0 → ℝ≥0 := fun x => x ^ p
  have hcontOn :
      ContinuousOn (fun A : CMatrix a => cfc f A)
        {A : CMatrix a | 0 ≤ A} := by
    exact ContinuousOn.cfc_nnreal_of_mem_nhdsSet
      (A := CMatrix a) (s := Set.univ) (f := f)
      (by simp)
      continuousOn_id
      (by intro x hx; exact hx)
      (by simpa [f] using
        (NNReal.continuousOn_rpow_const (s := Set.univ) (.inr hp.le)))
  have hcont := hcontOn.continuousWithinAt
    (by simpa using (Matrix.nonneg_iff_posSemidef.mpr hA))
  have hwithin : Filter.Tendsto F l
      (nhdsWithin A {A : CMatrix a | 0 ≤ A}) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hF, hFpsd.mono fun x hx => by
      simpa using (Matrix.nonneg_iff_posSemidef.mpr hx)⟩
  have hnn : Filter.Tendsto (fun x => cfc f (F x)) l (nhds (cfc f A)) :=
    hcont.tendsto.comp hwithin
  have hsource : cfc f A = CFC.rpow A p := by
    simp [f, CFC.rpow_def]
  have hevent : (fun x => cfc f (F x)) =ᶠ[l]
      (fun x => CFC.rpow (F x) p) := by
    filter_upwards [hFpsd] with x hx
    simp [f, CFC.rpow_def]
  rw [← hsource]
  exact hnn.congr' hevent

/-- Real matrix powers are continuous on the positive-definite cone, for any
real exponent.  This is the finite-dimensional CFC continuity step used when
high-`α` formulas contain negative reference powers but the limiting reference
is already positive definite. -/
theorem cMatrix_rpow_tendsto_of_tendsto_posDef
    {X : Type*} {l : Filter X} {F : X → CMatrix a} {A : CMatrix a}
    (p : ℝ)
    (hF : Filter.Tendsto F l (nhds A))
    (hFpd : ∀ᶠ x in l, (F x).PosDef)
    (hA : A.PosDef) :
    Filter.Tendsto (fun x => CFC.rpow (F x) p) l
      (nhds (CFC.rpow A p)) := by
  change Filter.Tendsto (fun x => (F x) ^ p) l (nhds (A ^ p))
  have hcont :=
    (CFC.continuousOn_rpow (A := CMatrix a) p).continuousWithinAt
      (by simpa using (Matrix.PosDef.isStrictlyPositive hA))
  have hwithin : Filter.Tendsto F l
      (nhdsWithin A {A : CMatrix a | IsStrictlyPositive A}) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hF, hFpd.mono fun x hx => by
      simpa using (Matrix.PosDef.isStrictlyPositive hx)⟩
  exact hcont.tendsto.comp hwithin

/-- The real trace of a matrix power is continuous along positive-definite
convergent filters, for any real exponent. -/
theorem cMatrix_rpow_trace_re_tendsto_of_tendsto_posDef
    {X : Type*} {l : Filter X} {F : X → CMatrix a} {A : CMatrix a}
    (p : ℝ)
    (hF : Filter.Tendsto F l (nhds A))
    (hFpd : ∀ᶠ x in l, (F x).PosDef)
    (hA : A.PosDef) :
    Filter.Tendsto (fun x => ((CFC.rpow (F x) p).trace).re) l
      (nhds ((CFC.rpow A p).trace.re)) := by
  have hpow := cMatrix_rpow_tendsto_of_tendsto_posDef p hF hFpd hA
  have htraceCont : Continuous fun M : CMatrix a => M.trace :=
    Continuous.matrix_trace continuous_id
  exact (Complex.continuous_re.tendsto _).comp (htraceCont.tendsto _ |>.comp hpow)

/-- The real trace of a positive matrix power is continuous along
PSD-constrained convergent filters. -/
theorem cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef
    {X : Type*} {l : Filter X} {F : X → CMatrix a} {A : CMatrix a}
    {p : ℝ} (hp : 0 < p)
    (hF : Filter.Tendsto F l (nhds A))
    (hFpsd : ∀ᶠ x in l, (F x).PosSemidef)
    (hA : A.PosSemidef) :
    Filter.Tendsto (fun x => ((CFC.rpow (F x) p).trace).re) l
      (nhds ((CFC.rpow A p).trace.re)) := by
  have hpow := cMatrix_rpow_tendsto_of_tendsto_posSemidef hp hF hFpsd hA
  have htraceCont : Continuous fun M : CMatrix a => M.trace :=
    Continuous.matrix_trace continuous_id
  exact (Complex.continuous_re.tendsto _).comp (htraceCont.tendsto _ |>.comp hpow)

omit [Fintype a] in
/-- Adding a nonnegative scalar multiple of the identity preserves positive
semidefiniteness. -/
theorem cMatrix_posSemidef_add_nonneg_smul_one_posSemidef
    {A : CMatrix a} (hA : A.PosSemidef) {ε : ℝ} (hε : 0 ≤ ε) :
    (A + ε • (1 : CMatrix a)).PosSemidef :=
  Matrix.PosSemidef.add hA (Matrix.PosSemidef.smul Matrix.PosSemidef.one hε)

/-- Right-regularizing a PSD matrix by `ε I` preserves the positive-power trace
in the limit `ε → 0+`. -/
theorem cMatrix_rpow_trace_re_tendsto_add_pos_smul_one
    {A : CMatrix a} (hA : A.PosSemidef) {p : ℝ} (hp : 0 < p) :
    Filter.Tendsto
      (fun ε : ℝ => ((CFC.rpow (A + ε • (1 : CMatrix a)) p).trace).re)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((CFC.rpow A p).trace.re)) := by
  have hpath : Filter.Tendsto (fun ε : ℝ => A + ε • (1 : CMatrix a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds A) := by
    have hcont : Continuous fun ε : ℝ => A + ε • (1 : CMatrix a) := by
      fun_prop
    simpa using (hcont.continuousWithinAt (x := (0 : ℝ))
      (s := Set.Ioi (0 : ℝ))).tendsto
  have hpsd : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (A + ε • (1 : CMatrix a)).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact cMatrix_posSemidef_add_nonneg_smul_one_posSemidef hA hε.le
  exact cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef hp hpath hpsd hA

omit [Fintype a] in
/-- The right-regularization path `A + ε I` tends to `A` as `ε → 0+`. -/
theorem cMatrix_tendsto_add_pos_smul_one
    {A : CMatrix a} :
    Filter.Tendsto (fun ε : ℝ => A + ε • (1 : CMatrix a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds A) := by
  have hcont : Continuous fun ε : ℝ => A + ε • (1 : CMatrix a) := by
    fun_prop
  simpa using (hcont.continuousWithinAt (x := (0 : ℝ))
    (s := Set.Ioi (0 : ℝ))).tendsto

/-- If `B` is already on the PSD `q`-unit sphere, then normalizing the
positive-definite regularization `B + δ I` converges back to `B`. -/
theorem cMatrix_normalized_regularized_tendsto_of_psdTracePower_eq_one
    {B : CMatrix a} (hB : B.PosSemidef) {q : ℝ} (hq : 0 < q)
    (hBq : psdTracePower B hB q = 1) :
    Filter.Tendsto
      (fun δ : ℝ =>
        let Bδ : CMatrix a := B + δ • (1 : CMatrix a)
        let scale : ℝ := ((CFC.rpow Bδ q).trace.re) ^ (-(1 / q))
        scale • Bδ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds B) := by
  have htrace := cMatrix_rpow_trace_re_tendsto_add_pos_smul_one hB hq
  have hscale : Filter.Tendsto
      (fun δ : ℝ => ((CFC.rpow (B + δ • (1 : CMatrix a)) q).trace.re) ^
        (-(1 / q)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 : ℝ)) := by
    have hcont : ContinuousAt (fun x : ℝ => x ^ (-(1 / q))) (1 : ℝ) :=
      Real.continuousAt_rpow_const 1 (-(1 / q)) (Or.inl one_ne_zero)
    have htrace_one : Filter.Tendsto
        (fun ε : ℝ => (trace (CFC.rpow (B + ε • (1 : CMatrix a)) q)).re)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 : ℝ)) := by
      have hBq' : (trace (B ^ q)).re = (1 : ℝ) := by
        simpa [psdTracePower] using hBq
      simpa [hBq'] using htrace
    simpa using hcont.tendsto.comp htrace_one
  have hpath := cMatrix_tendsto_add_pos_smul_one (A := B)
  simpa using hscale.smul hpath

end RpowContinuity

/-- Real powers commute with nonnegative real scalar multiplication of a PSD
matrix. -/
theorem cMatrix_rpow_real_smul_posSemidef_schatten
    {A : CMatrix a} (hA : A.PosSemidef) {lambda s : ℝ} (hlambda : 0 ≤ lambda) :
    CFC.rpow (lambda • A : CMatrix a) s =
      (lambda ^ s : ℝ) • CFC.rpow A s := by
  let U : Matrix.unitaryGroup a ℂ := hA.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hA.isHermitian.eigenvalues
  have hd : ∀ i, 0 ≤ d i := fun i => hA.eigenvalues_nonneg i
  have hA_spec :
      A = (U : CMatrix a) * (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a) := by
    simpa [U, d, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hA.isHermitian.spectral_theorem
  have hscaled_spec :
      (lambda • A : CMatrix a) =
        (U : CMatrix a) *
          (Matrix.diagonal fun i => ((lambda * d i : ℝ) : ℂ)) *
            star (U : CMatrix a) := by
    rw [hA_spec]
    have hdiag :
        (lambda • (Matrix.diagonal fun i => (d i : ℂ)) : CMatrix a) =
          Matrix.diagonal fun i => ((lambda * d i : ℝ) : ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.smul_apply]
      · simp [Matrix.smul_apply, Matrix.diagonal, hij]
    calc
      (lambda • (((U : CMatrix a) *
          (Matrix.diagonal fun i => (d i : ℂ))) * star (U : CMatrix a)) :
          CMatrix a)
          = (lambda • ((U : CMatrix a) *
              (Matrix.diagonal fun i => (d i : ℂ))) : CMatrix a) *
                star (U : CMatrix a) := by
              rw [Matrix.smul_mul]
      _ = ((U : CMatrix a) *
              (lambda • (Matrix.diagonal fun i => (d i : ℂ)) : CMatrix a)) *
                star (U : CMatrix a) := by
              rw [Matrix.mul_smul]
      _ = (U : CMatrix a) *
          (Matrix.diagonal fun i => ((lambda * d i : ℝ) : ℂ)) *
            star (U : CMatrix a) := by
              rw [hdiag]
  have hscaled_nonneg : ∀ i, 0 ≤ lambda * d i := fun i =>
    mul_nonneg hlambda (hd i)
  rw [hscaled_spec]
  rw [cMatrix_rpow_unitary_conj_diagonal_ofReal U (fun i => lambda * d i)
    hscaled_nonneg s]
  rw [cMatrix_rpow_eq_eigenbasis_diagonal hA s]
  have hdiag_pow :
      Matrix.diagonal (fun i => (((lambda * d i) ^ s : ℝ) : ℂ)) =
        ((lambda ^ s : ℝ) •
          Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) : CMatrix a) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.smul_apply, Real.mul_rpow hlambda (hd _)]
    · simp [Matrix.smul_apply, Matrix.diagonal, hij]
  rw [hdiag_pow]
  calc
    (U : CMatrix a) *
          (((lambda ^ s : ℝ) •
            Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) : CMatrix a)) *
        star (U : CMatrix a)
        = ((lambda ^ s : ℝ) •
            ((U : CMatrix a) *
              Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ))) : CMatrix a) *
            star (U : CMatrix a) := by
          rw [Matrix.mul_smul]
    _ = ((lambda ^ s : ℝ) •
          (((U : CMatrix a) *
            Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ))) *
              star (U : CMatrix a)) : CMatrix a) := by
          rw [Matrix.smul_mul]

/-- Real powers of an identity-regularized PSD matrix are diagonalized in the
same eigenbasis as the original PSD matrix.  This is the spectral form needed
for source regularization `σ + εI`; it reuses the existing unitary-diagonal
functional calculus rather than introducing a new CFC route. -/
theorem cMatrix_rpow_add_nonneg_smul_one_eigenbasis_diagonal
    {A : CMatrix a} (hA : A.PosSemidef) {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) :
    CFC.rpow (A + ε • (1 : CMatrix a)) s =
      (hA.isHermitian.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal
          (fun i => (((hA.isHermitian.eigenvalues i + ε) ^ s : ℝ) : ℂ)) *
        star (hA.isHermitian.eigenvectorUnitary : CMatrix a) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hA.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hA.isHermitian.eigenvalues
  let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
  have hd : ∀ i, 0 ≤ d i := fun i => hA.eigenvalues_nonneg i
  have hA_spec :
      A = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, d, D, Matrix.IsHermitian.spectral_theorem,
      Unitary.conjStarAlgAut_apply] using hA.isHermitian.spectral_theorem
  have hone_spec :
      (1 : CMatrix a) = (U : CMatrix a) * (1 : CMatrix a) *
        star (U : CMatrix a) := by
    symm
    simp
  have hsmul :
      (ε • ((U : CMatrix a) * (1 : CMatrix a) *
        star (U : CMatrix a)) : CMatrix a) =
        (U : CMatrix a) * (ε • (1 : CMatrix a)) * star (U : CMatrix a) := by
    calc
      (ε • (((U : CMatrix a) * (1 : CMatrix a)) *
          star (U : CMatrix a)) : CMatrix a)
          = (ε • ((U : CMatrix a) * (1 : CMatrix a)) : CMatrix a) *
              star (U : CMatrix a) := by
              rw [Matrix.smul_mul]
      _ = ((U : CMatrix a) * (ε • (1 : CMatrix a))) *
              star (U : CMatrix a) := by
              rw [Matrix.mul_smul]
      _ = (U : CMatrix a) * (ε • (1 : CMatrix a)) *
              star (U : CMatrix a) := by
              rfl
  have hdiag_add :
      D + ε • (1 : CMatrix a) =
        Matrix.diagonal (fun i => (((d i + ε : ℝ)) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Matrix.smul_apply, Matrix.diagonal, add_comm]
    · simp [D, Matrix.smul_apply, Matrix.diagonal, hij]
  have hreg_spec :
      A + ε • (1 : CMatrix a) =
        (U : CMatrix a) *
          Matrix.diagonal (fun i => (((d i + ε : ℝ)) : ℂ)) *
            star (U : CMatrix a) := by
    rw [hA_spec, hone_spec, hsmul]
    calc
      (U : CMatrix a) * D * star (U : CMatrix a) +
          (U : CMatrix a) * (ε • (1 : CMatrix a)) * star (U : CMatrix a)
          = (U : CMatrix a) * (D + ε • (1 : CMatrix a)) *
              star (U : CMatrix a) := by
              noncomm_ring
      _ = (U : CMatrix a) *
          Matrix.diagonal (fun i => (((d i + ε : ℝ)) : ℂ)) *
            star (U : CMatrix a) := by
              rw [hdiag_add]
  rw [hreg_spec]
  exact
    cMatrix_rpow_unitary_conj_diagonal_ofReal U (fun i => d i + ε)
      (fun i => add_nonneg (hd i) hε) s

/-- PSD power traces are homogeneous under nonnegative real scalar
multiplication. -/
theorem psdTracePower_real_smul_posSemidef
    {A : CMatrix a} (hA : A.PosSemidef) {lambda p : ℝ} (hlambda : 0 ≤ lambda) :
    psdTracePower (lambda • A : CMatrix a) (Matrix.PosSemidef.smul hA hlambda) p =
      lambda ^ p * psdTracePower A hA p := by
  rw [psdTracePower, cMatrix_rpow_real_smul_posSemidef_schatten hA hlambda,
    Matrix.trace_smul]
  simp [psdTracePower]

/-- A normalized positive `q`-power trace with `q > 0` makes a PSD matrix an
effect: every eigenvalue is at most one. -/
theorem posSemidef_le_one_of_psdTracePower_le_one
    {B : CMatrix a} (hB : B.PosSemidef) {q : ℝ} (hq : 0 < q)
    (hBq : psdTracePower B hB q ≤ 1) :
    B ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup a ℂ := hB.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun i => ((hB.isHermitian.eigenvalues i : ℝ) : ℂ))
  have hdiag : B = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hB.isHermitian.spectral_theorem
  have hpower_sum :
      ∑ i, hB.isHermitian.eigenvalues i ^ q ≤ 1 := by
    simpa [psdTracePower_eq_sum_eigenvalues_rpow B hB q] using hBq
  have heig_le_one : ∀ i, hB.isHermitian.eigenvalues i ≤ 1 := by
    intro i
    have hnonneg (j : a) : 0 ≤ hB.isHermitian.eigenvalues j :=
      hB.eigenvalues_nonneg j
    have hpow_nonneg (j : a) : 0 ≤ hB.isHermitian.eigenvalues j ^ q :=
      Real.rpow_nonneg (hnonneg j) q
    have hpow_le_sum :
        hB.isHermitian.eigenvalues i ^ q ≤
          ∑ j, hB.isHermitian.eigenvalues j ^ q := by
      calc
        hB.isHermitian.eigenvalues i ^ q
            ≤ hB.isHermitian.eigenvalues i ^ q +
                ∑ j ∈ Finset.univ.erase i, hB.isHermitian.eigenvalues j ^ q :=
              le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hpow_nonneg j)
        _ = ∑ j, hB.isHermitian.eigenvalues j ^ q := by
              rw [add_comm]
              exact Finset.sum_erase_add (s := Finset.univ)
                (f := fun j => hB.isHermitian.eigenvalues j ^ q) (Finset.mem_univ i)
    have hpow_le_one :
        hB.isHermitian.eigenvalues i ^ q ≤ 1 :=
      hpow_le_sum.trans hpower_sum
    have hpow_le_one_pow :
        hB.isHermitian.eigenvalues i ^ q ≤ (1 : ℝ) ^ q := by
      simpa using hpow_le_one
    exact (Real.rpow_le_rpow_iff (hnonneg i) zero_le_one hq).mp hpow_le_one_pow
  have hUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
    simp [U]
  have hsub :
      1 - B = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
    rw [hdiag]
    calc
      1 - (U : CMatrix a) * D * star (U : CMatrix a) =
          (U : CMatrix a) * 1 * star (U : CMatrix a) -
            (U : CMatrix a) * D * star (U : CMatrix a) := by
            rw [Matrix.mul_one, hUstar]
      _ = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
            noncomm_ring
  have hdiag_sub :
      (1 : CMatrix a) - D =
        Matrix.diagonal fun i => (((1 : ℝ) - hB.isHermitian.eigenvalues i : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  have hnonneg : 0 ≤ (1 : ℝ) - hB.isHermitian.eigenvalues i := by
    exact sub_nonneg.mpr (heig_le_one i)
  exact_mod_cast hnonneg

/-- PSD power traces are invariant under unitary conjugation. -/
theorem psdTracePower_unitary_conj
    (U : Matrix.unitaryGroup a ℂ) {A : CMatrix a} (hA : A.PosSemidef)
    {p : ℝ} (hp : 0 ≤ p) :
    psdTracePower (star (U : CMatrix a) * A * (U : CMatrix a))
      (posSemidef_unitary_conj hA U) p =
      psdTracePower A hA p := by
  rw [psdTracePower, psdTracePower, cMatrix_rpow_unitary_conj hA U hp]
  rw [Matrix.trace_mul_cycle]
  simp

/-- PSD power traces of nonnegative real diagonal matrices are entrywise
power sums. -/
theorem psdTracePower_diagonal_ofReal
    (d : a → ℝ) (hd : ∀ i, 0 ≤ d i) (p : ℝ) :
    psdTracePower (Matrix.diagonal fun i => (d i : ℂ) : CMatrix a)
      (Matrix.PosSemidef.diagonal (d := fun i => (d i : ℂ)) (by
        intro i
        change (0 : ℂ) ≤ (d i : ℂ)
        exact_mod_cast hd i)) p =
      ∑ i, d i ^ p := by
  rw [psdTracePower, cMatrix_rpow_diagonal_ofReal d hd p, Matrix.trace_diagonal]
  simp

/-- PSD power traces are bounded by the sum of diagonal `p`-powers in the
concave range `0 ≤ p ≤ 1`. -/
theorem psdTracePower_le_posSemidef_sum_diagonal_re_rpow
    {B : CMatrix a} (hB : B.PosSemidef) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    psdTracePower B hB p ≤ ∑ i, (B i i).re ^ p := by
  classical
  have hpoint :
      ∀ i, (∑ j,
        Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
          hB.isHermitian.eigenvalues j ^ p) ≤ (B i i).re ^ p :=
    fun i => eigenvalue_weighted_rpow_le_posSemidef_diagonal_re_rpow hB hp0 hp1 i
  have hdouble :
      (∑ i, ∑ j,
          Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
            hB.isHermitian.eigenvalues j ^ p) =
        ∑ j, hB.isHermitian.eigenvalues j ^ p := by
    calc
      (∑ i, ∑ j,
          Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
            hB.isHermitian.eigenvalues j ^ p)
          = ∑ j, ∑ i,
              Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
                hB.isHermitian.eigenvalues j ^ p := by
              rw [Finset.sum_comm]
      _ = ∑ j,
              (∑ i, Complex.normSq
                ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j)) *
                hB.isHermitian.eigenvalues j ^ p := by
              simp [Finset.sum_mul]
      _ = ∑ j, hB.isHermitian.eigenvalues j ^ p := by
              simp_rw [unitary_col_normSq_sum hB.isHermitian.eigenvectorUnitary]
              simp
  rw [psdTracePower_eq_sum_eigenvalues_rpow]
  rw [← hdouble]
  exact Finset.sum_le_sum fun i _ => hpoint i

/-- Trace pairing with a PSD right factor power, expanded in that factor's
eigenbasis. -/
theorem trace_mul_cMatrix_rpow_eq_conjugate_diag_sum
    (M : CMatrix a) {N : CMatrix a} (hN : N.PosSemidef) (s : ℝ) :
    ((M * CFC.rpow N s).trace).re =
      ∑ i,
        ((star (hN.isHermitian.eigenvectorUnitary : CMatrix a) * M *
          (hN.isHermitian.eigenvectorUnitary : CMatrix a)) i i).re *
            hN.isHermitian.eigenvalues i ^ s := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun i => ((hN.isHermitian.eigenvalues i ^ s : ℝ) : ℂ))
  have hpow : CFC.rpow N s = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D] using cMatrix_rpow_eq_eigenbasis_diagonal hN s
  have htrace :
      (M * CFC.rpow N s).trace =
        ((star (U : CMatrix a) * M * (U : CMatrix a)) * D).trace := by
    rw [hpow]
    calc
      (M * ((U : CMatrix a) * D * star (U : CMatrix a))).trace
          = (((M * (U : CMatrix a)) * D) * star (U : CMatrix a)).trace := by
              noncomm_ring
      _ = (star (U : CMatrix a) * ((M * (U : CMatrix a)) * D)).trace := by
              exact Matrix.trace_mul_comm (((M * (U : CMatrix a)) * D))
                (star (U : CMatrix a))
      _ = ((star (U : CMatrix a) * M * (U : CMatrix a)) * D).trace := by
              noncomm_ring
  have hdiag :
      (((star (U : CMatrix a) * M * (U : CMatrix a)) * D).trace).re =
        ∑ i,
          ((star (U : CMatrix a) * M * (U : CMatrix a)) i i).re *
            hN.isHermitian.eigenvalues i ^ s := by
    simp [D, Matrix.trace, Matrix.diagonal, Matrix.mul_apply, Complex.mul_re]
  rw [htrace, hdiag]

/-- Kernel support domination forces zero diagonal entries of the supported
matrix in zero-eigenvalue directions of the supporting PSD matrix. -/
theorem supports_conjugate_diagonal_re_eq_zero
    {M N : CMatrix a} (hN : N.PosSemidef) (hSupport : Matrix.Supports M N)
    {i : a} (hi : hN.isHermitian.eigenvalues i = 0) :
    ((star (hN.isHermitian.eigenvectorUnitary : CMatrix a) * M *
      (hN.isHermitian.eigenvectorUnitary : CMatrix a)) i i).re = 0 := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let v : a → ℂ := ⇑(hN.isHermitian.eigenvectorBasis i)
  have hNv : N.mulVec v = 0 := by
    have h := hN.isHermitian.mulVec_eigenvectorBasis i
    rw [hi] at h
    simpa [v] using h
  have hMv : M.mulVec v = 0 := hSupport v hNv
  have hMU : ∀ k, (M * (U : CMatrix a)) k i = 0 := by
    intro k
    have hk := congrFun hMv k
    simpa [v, U, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using hk
  have hentry :
      (star (U : CMatrix a) * M * (U : CMatrix a)) i i = 0 := by
    rw [Matrix.mul_assoc]
    simp [Matrix.mul_apply, hMU]
  simpa [U] using congrArg Complex.re hentry

/-- Kernel support domination kills the entire zero-eigenvalue column of the
supported matrix in the supporting PSD matrix's spectral basis.  This
right-support version does not require the supported matrix itself to be PSD. -/
theorem supports_conjugate_entry_eq_zero_of_right_zero
    {M N : CMatrix a} (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N)
    {i j : a} (hj : hN.isHermitian.eigenvalues j = 0) :
    (star (hN.isHermitian.eigenvectorUnitary : CMatrix a) * M *
      (hN.isHermitian.eigenvectorUnitary : CMatrix a)) i j = 0 := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let v : a → ℂ := ⇑(hN.isHermitian.eigenvectorBasis j)
  have hNv : N.mulVec v = 0 := by
    have h := hN.isHermitian.mulVec_eigenvectorBasis j
    rw [hj] at h
    simpa [v] using h
  have hMv : M.mulVec v = 0 := hSupport v hNv
  have hMU : ∀ k, (M * (U : CMatrix a)) k j = 0 := by
    intro k
    have hk := congrFun hMv k
    simpa [v, U, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using hk
  calc
    (star (hN.isHermitian.eigenvectorUnitary : CMatrix a) * M *
        (hN.isHermitian.eigenvectorUnitary : CMatrix a)) i j =
        (star (U : CMatrix a) * (M * (U : CMatrix a))) i j := by
          simp [U, Matrix.mul_assoc]
    _ = ∑ k, (star (U : CMatrix a)) i k * (M * (U : CMatrix a)) k j := by
          simp [Matrix.mul_apply]
    _ = 0 := by
          simp [hMU]

/-- Kernel support domination plus PSD of the supported matrix kills the
entire row and column in zero-eigenvalue directions of the supporting matrix's
spectral basis. -/
theorem supports_conjugate_entry_eq_zero_of_left_or_right_zero
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N)
    {i j : a}
    (hzero : hN.isHermitian.eigenvalues i = 0 ∨
      hN.isHermitian.eigenvalues j = 0) :
    (star (hN.isHermitian.eigenvectorUnitary : CMatrix a) * M *
      (hN.isHermitian.eigenvectorUnitary : CMatrix a)) i j = 0 := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let M' : CMatrix a := star (U : CMatrix a) * M * (U : CMatrix a)
  have hM' : M'.PosSemidef := by
    simpa [M'] using posSemidef_unitary_conj hM U
  rcases hzero with hi | hj
  · have hdiag :
        (M' i i).re = 0 := by
      simpa [M', U] using
        supports_conjugate_diagonal_re_eq_zero (M := M) (N := N) hN hSupport
          (i := i) hi
    exact (posSemidef_zero_diag_re_zero_row_col hM' hdiag j).1
  · have hdiag :
        (M' j j).re = 0 := by
      simpa [M', U] using
        supports_conjugate_diagonal_re_eq_zero (M := M) (N := N) hN hSupport
          (i := j) hj
    exact (posSemidef_zero_diag_re_zero_row_col hM' hdiag i).2

/-- The spectral support projector of a supporting PSD matrix fixes every PSD
matrix supported by it, on both the left and the right.

This is the finite-dimensional support-compression algebra needed when a
singular reference is first restricted to its support before applying a
full-rank argument. -/
theorem supportProjector_fixes_of_supports
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N) :
    let Pi : CMatrix a :=
      psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian
    Pi * M = M ∧ M * Pi = M := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let P : CMatrix a := Matrix.diagonal (fun i =>
    if 0 < hN.isHermitian.eigenvalues i then (1 : ℂ) else 0)
  let M' : CMatrix a := star (U : CMatrix a) * M * (U : CMatrix a)
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
    simp [U, Unitary.coe_star_mul_self hN.isHermitian.eigenvectorUnitary]
  have hUUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
    simp [U]
  have hPi_spec :
      psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian =
        (U : CMatrix a) * P * star (U : CMatrix a) := by
    simpa [U, P] using psdInvSqrt_support_eq hN
  have hM_reconstruct : (U : CMatrix a) * M' * star (U : CMatrix a) = M := by
    calc
      (U : CMatrix a) * M' * star (U : CMatrix a)
          = (U : CMatrix a) * (star (U : CMatrix a) * M *
              (U : CMatrix a)) * star (U : CMatrix a) := by rfl
      _ = ((U : CMatrix a) * star (U : CMatrix a)) * M *
            ((U : CMatrix a) * star (U : CMatrix a)) := by noncomm_ring
      _ = M := by simp [hUUstar]
  have hP_left : P * M' = M' := by
    ext i j
    by_cases hi : 0 < hN.isHermitian.eigenvalues i
    · simp [P, Matrix.mul_apply, Matrix.diagonal, hi]
    · have hzero : hN.isHermitian.eigenvalues i = 0 := by
        have hnn := hN.eigenvalues_nonneg i
        exact le_antisymm (not_lt.mp hi) hnn
      have hMij : M' i j = 0 := by
        simpa [M', U] using
          supports_conjugate_entry_eq_zero_of_left_or_right_zero
            (M := M) (N := N) hM hN hSupport (i := i) (j := j)
            (Or.inl hzero)
      simp [P, Matrix.mul_apply, Matrix.diagonal, hi, hMij]
  have hP_right : M' * P = M' := by
    ext i j
    by_cases hj : 0 < hN.isHermitian.eigenvalues j
    · simp [P, Matrix.mul_apply, Matrix.diagonal, hj]
    · have hzero : hN.isHermitian.eigenvalues j = 0 := by
        have hnn := hN.eigenvalues_nonneg j
        exact le_antisymm (not_lt.mp hj) hnn
      have hMij : M' i j = 0 := by
        simpa [M', U] using
          supports_conjugate_entry_eq_zero_of_left_or_right_zero
            (M := M) (N := N) hM hN hSupport (i := i) (j := j)
            (Or.inr hzero)
      simp [P, Matrix.mul_apply, Matrix.diagonal, hj, hMij]
  constructor
  · calc
      (psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian) * M
          = ((U : CMatrix a) * P * star (U : CMatrix a)) *
              ((U : CMatrix a) * M' * star (U : CMatrix a)) := by
                rw [hPi_spec, hM_reconstruct]
      _ = (U : CMatrix a) * (P * M') * star (U : CMatrix a) := by
            calc
              ((U : CMatrix a) * P * star (U : CMatrix a)) *
                  ((U : CMatrix a) * M' * star (U : CMatrix a))
                  = (U : CMatrix a) * P * (star (U : CMatrix a) *
                      (U : CMatrix a)) * M' * star (U : CMatrix a) := by
                    noncomm_ring
              _ = (U : CMatrix a) * P * 1 * M' * star (U : CMatrix a) := by
                    rw [hUstarU]
              _ = (U : CMatrix a) * (P * M') * star (U : CMatrix a) := by
                    noncomm_ring
      _ = M := by
            rw [hP_left, hM_reconstruct]
  · calc
      M * (psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian)
          = ((U : CMatrix a) * M' * star (U : CMatrix a)) *
              ((U : CMatrix a) * P * star (U : CMatrix a)) := by
                rw [hPi_spec, hM_reconstruct]
      _ = (U : CMatrix a) * (M' * P) * star (U : CMatrix a) := by
            calc
              ((U : CMatrix a) * M' * star (U : CMatrix a)) *
                  ((U : CMatrix a) * P * star (U : CMatrix a))
                  = (U : CMatrix a) * M' * (star (U : CMatrix a) *
                      (U : CMatrix a)) * P * star (U : CMatrix a) := by
                    noncomm_ring
              _ = (U : CMatrix a) * M' * 1 * P * star (U : CMatrix a) := by
                    rw [hUstarU]
              _ = (U : CMatrix a) * (M' * P) * star (U : CMatrix a) := by
                    noncomm_ring
      _ = M := by
            rw [hP_right, hM_reconstruct]

/-- If a PSD matrix is supported by `N`, then it is also supported by the
spectral support projector of `N`. -/
theorem Supports.of_supportProjector
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N) :
    Matrix.Supports M
      (psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian) := by
  intro v hv
  let Pi : CMatrix a :=
    psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian
  have hfix :=
    (supportProjector_fixes_of_supports (M := M) (N := N) hM hN hSupport).2
  have hmv := congrArg (fun A : CMatrix a => Matrix.mulVec A v) hfix.symm
  calc
    Matrix.mulVec M v = Matrix.mulVec (M * Pi) v := by
      simpa [Pi] using hmv
    _ = Matrix.mulVec M (Matrix.mulVec Pi v) := by
      rw [Matrix.mulVec_mulVec]
    _ = 0 := by
      simp [Pi, hv]

/-- The spectral support projector fixes every matrix supported by a PSD
reference on the right.  Unlike `supportProjector_fixes_of_supports`, this
single-sided form does not require the supported matrix to be PSD. -/
theorem supportProjector_right_fixes_of_supports
    {M N : CMatrix a} (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N) :
    let Pi : CMatrix a :=
      psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian
    M * Pi = M := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let P : CMatrix a := Matrix.diagonal (fun i =>
    if 0 < hN.isHermitian.eigenvalues i then (1 : ℂ) else 0)
  let M' : CMatrix a := star (U : CMatrix a) * M * (U : CMatrix a)
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
    simp [U, Unitary.coe_star_mul_self hN.isHermitian.eigenvectorUnitary]
  have hUUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
    simp [U]
  have hPi_spec :
      psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian =
        (U : CMatrix a) * P * star (U : CMatrix a) := by
    simpa [U, P] using psdInvSqrt_support_eq hN
  have hM_reconstruct : (U : CMatrix a) * M' * star (U : CMatrix a) = M := by
    calc
      (U : CMatrix a) * M' * star (U : CMatrix a)
          = (U : CMatrix a) * (star (U : CMatrix a) * M *
              (U : CMatrix a)) * star (U : CMatrix a) := by rfl
      _ = ((U : CMatrix a) * star (U : CMatrix a)) * M *
            ((U : CMatrix a) * star (U : CMatrix a)) := by noncomm_ring
      _ = M := by simp [hUUstar]
  have hP_right : M' * P = M' := by
    ext i j
    by_cases hj : 0 < hN.isHermitian.eigenvalues j
    · simp [P, Matrix.mul_apply, Matrix.diagonal, hj]
    · have hzero : hN.isHermitian.eigenvalues j = 0 := by
        have hnn := hN.eigenvalues_nonneg j
        exact le_antisymm (not_lt.mp hj) hnn
      have hMij : M' i j = 0 := by
        simpa [M', U] using
          supports_conjugate_entry_eq_zero_of_right_zero
            (M := M) (N := N) hN hSupport (i := i) (j := j) hzero
      simp [P, Matrix.mul_apply, Matrix.diagonal, hj, hMij]
  calc
    M * (psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian)
        = ((U : CMatrix a) * M' * star (U : CMatrix a)) *
            ((U : CMatrix a) * P * star (U : CMatrix a)) := by
              rw [hPi_spec, hM_reconstruct]
    _ = (U : CMatrix a) * (M' * P) * star (U : CMatrix a) := by
          calc
            ((U : CMatrix a) * M' * star (U : CMatrix a)) *
                ((U : CMatrix a) * P * star (U : CMatrix a))
                = (U : CMatrix a) * M' * (star (U : CMatrix a) *
                    (U : CMatrix a)) * P * star (U : CMatrix a) := by
                  noncomm_ring
            _ = (U : CMatrix a) * M' * 1 * P * star (U : CMatrix a) := by
                  rw [hUstarU]
            _ = (U : CMatrix a) * (M' * P) * star (U : CMatrix a) := by
                  noncomm_ring
    _ = M := by
          rw [hP_right, hM_reconstruct]

/-- The spectral support projector of a PSD matrix is supported by that PSD
matrix. -/
theorem supportProjector_supports
    (N : CMatrix a) (hN : N.PosSemidef) :
    Matrix.Supports
      (psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian)
      N := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let d : a → ℝ := fun i => hN.isHermitian.eigenvalues i
  let p : a → ℝ := fun i => if 0 < hN.isHermitian.eigenvalues i then 1 else 0
  let D : CMatrix a :=
    Matrix.diagonal fun i => ((d i : ℝ) : ℂ)
  let P : CMatrix a := Matrix.diagonal (fun i =>
    ((p i : ℝ) : ℂ))
  have hN_spec : N = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, d, Matrix.IsHermitian.spectral_theorem,
      Unitary.conjStarAlgAut_apply]
      using hN.isHermitian.spectral_theorem
  have hPi_spec :
      psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian =
        (U : CMatrix a) * P * star (U : CMatrix a) := by
    have hP :
        P = Matrix.diagonal (fun i =>
          if 0 < hN.isHermitian.eigenvalues i then (1 : ℂ) else 0) := by
      ext i j
      by_cases hij : i = j
      · subst j
        by_cases hi : 0 < hN.isHermitian.eigenvalues i
        · simp [P, p, hi]
        · simp [P, p, hi]
      · simp [P, Matrix.diagonal, hij]
    rw [hP]
    simpa [U] using psdInvSqrt_support_eq hN
  have hdiag : Matrix.Supports P D := by
    change Matrix.Supports
      (Matrix.diagonal fun i => ((p i : ℝ) : ℂ))
      (Matrix.diagonal fun i => ((d i : ℝ) : ℂ))
    apply Matrix.Supports.diagonal_of_real_zero_imp_zero
    intro i hi
    have hnot : ¬ 0 < hN.isHermitian.eigenvalues i := by
      change hN.isHermitian.eigenvalues i = 0 at hi
      rw [hi]
      exact lt_irrefl 0
    simp [p, d, hi]
  have hconj := Matrix.Supports.unitary_conj hdiag U
  change Matrix.Supports
      ((U : CMatrix a) * P * star (U : CMatrix a))
      ((U : CMatrix a) * D * star (U : CMatrix a)) at hconj
  rw [← hPi_spec, ← hN_spec] at hconj
  exact hconj

/-- The positive spectral support indices of a PSD matrix.  Compressing to
this subtype turns the reference into a positive-definite matrix on its
support. -/
def psdSupportIndex (N : CMatrix a) (hN : N.PosSemidef) : Type u :=
  {i : a // 0 < hN.isHermitian.eigenvalues i}

instance psdSupportIndex_fintype (N : CMatrix a) (hN : N.PosSemidef) :
    Fintype (psdSupportIndex N hN) := by
  unfold psdSupportIndex
  infer_instance

instance psdSupportIndex_decidableEq (N : CMatrix a) (hN : N.PosSemidef) :
    DecidableEq (psdSupportIndex N hN) := by
  unfold psdSupportIndex
  infer_instance

/-- The rectangular isometry whose columns are the eigenvectors of the
positive spectral support of a PSD matrix. -/
def psdSupportIsometry (N : CMatrix a) (hN : N.PosSemidef) :
    Matrix a (psdSupportIndex N hN) ℂ :=
  fun row idx => (hN.isHermitian.eigenvectorUnitary : CMatrix a) row idx.1

/-- The support-column matrix is an isometry. -/
theorem psdSupportIsometry_isometry (N : CMatrix a) (hN : N.PosSemidef) :
    Matrix.conjTranspose (psdSupportIsometry N hN) *
        psdSupportIsometry N hN =
      (1 : CMatrix (psdSupportIndex N hN)) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  ext i j
  have h :=
    congrArg (fun M : CMatrix a => M i.1 j.1)
      (Unitary.coe_star_mul_self U)
  by_cases hij : i = j
  · subst j
    simpa [psdSupportIsometry, U, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] using h
  · have hval : (i : psdSupportIndex N hN).1 ≠ j.1 := by
      intro hraw
      exact hij (Subtype.ext hraw)
    simpa [psdSupportIsometry, U, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, hij, hval] using h

/-- The range projection of the support isometry is the spectral support
projector of the PSD matrix. -/
theorem psdSupportIsometry_mul_conjTranspose_eq_supportProjector
    (N : CMatrix a) (hN : N.PosSemidef) :
    psdSupportIsometry N hN *
        Matrix.conjTranspose (psdSupportIsometry N hN) =
      psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let P : CMatrix a := Matrix.diagonal (fun i =>
    if 0 < hN.isHermitian.eigenvalues i then (1 : ℂ) else 0)
  have hPi_spec :
      psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian =
        (U : CMatrix a) * P * star (U : CMatrix a) := by
    simpa [U, P] using psdInvSqrt_support_eq hN
  rw [hPi_spec]
  ext i j
  let f : a → ℂ := fun x =>
    (U : CMatrix a) i x * star ((U : CMatrix a) j x)
  have hsub :
      (∑ x : psdSupportIndex N hN,
          (U : CMatrix a) i x.1 * star ((U : CMatrix a) j x.1)) =
        ∑ x ∈ (Finset.univ : Finset a) with
          0 < hN.isHermitian.eigenvalues x, f x := by
    simpa [f] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset a))
        (p := fun x => 0 < hN.isHermitian.eigenvalues x)
        (f := f))
  simp only [psdSupportIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diagonal, P, U]
  rw [hsub]
  simp [Finset.sum_filter, f, U]

/-- Compression to the positive spectral support of a PSD reference. -/
def psdSupportCompress (N : CMatrix a) (hN : N.PosSemidef)
    (M : CMatrix a) : CMatrix (psdSupportIndex N hN) :=
  Matrix.conjTranspose (psdSupportIsometry N hN) * M *
    psdSupportIsometry N hN

/-- Support compression preserves positive semidefiniteness. -/
theorem psdSupportCompress_posSemidef
    (N : CMatrix a) (hN : N.PosSemidef)
    {M : CMatrix a} (hM : M.PosSemidef) :
    (psdSupportCompress N hN M).PosSemidef := by
  simpa [psdSupportCompress] using
    Matrix.PosSemidef.conjTranspose_mul_mul_same hM
      (psdSupportIsometry N hN)

/-- Compressing an operator already embedded into the positive spectral support
recovers the operator on that support. -/
theorem psdSupportCompress_isometry_conj
    (N : CMatrix a) (hN : N.PosSemidef)
    (X : CMatrix (psdSupportIndex N hN)) :
    psdSupportCompress N hN
        (psdSupportIsometry N hN * X *
          Matrix.conjTranspose (psdSupportIsometry N hN)) =
      X := by
  let V : Matrix a (psdSupportIndex N hN) ℂ := psdSupportIsometry N hN
  calc
    psdSupportCompress N hN (V * X * Matrix.conjTranspose V)
        = Matrix.conjTranspose V * (V * X * Matrix.conjTranspose V) * V := by
          rfl
    _ = (Matrix.conjTranspose V * V) * X * (Matrix.conjTranspose V * V) := by
          simp [Matrix.mul_assoc]
    _ = X := by
          rw [psdSupportIsometry_isometry N hN]
          simp

/-- Embedding into the positive spectral support preserves trace. -/
theorem psdSupportIsometry_conj_trace
    (N : CMatrix a) (hN : N.PosSemidef)
    (X : CMatrix (psdSupportIndex N hN)) :
    (psdSupportIsometry N hN * X *
        Matrix.conjTranspose (psdSupportIsometry N hN)).trace = X.trace := by
  let V : Matrix a (psdSupportIndex N hN) ℂ := psdSupportIsometry N hN
  calc
    (V * X * Matrix.conjTranspose V).trace =
        ((V * X) * Matrix.conjTranspose V).trace := by
          simp [Matrix.mul_assoc]
    _ = (Matrix.conjTranspose V * (V * X)).trace := by
          rw [Matrix.trace_mul_comm]
    _ = ((Matrix.conjTranspose V * V) * X).trace := by
          simp [Matrix.mul_assoc]
    _ = X.trace := by
          rw [psdSupportIsometry_isometry N hN]
          simp

/-- Operators embedded into the positive spectral support of a PSD reference
are supported by that reference. -/
theorem psdSupportIsometry_conj_supports
    (N : CMatrix a) (hN : N.PosSemidef)
    (X : CMatrix (psdSupportIndex N hN)) :
    Matrix.Supports
      (psdSupportIsometry N hN * X *
        Matrix.conjTranspose (psdSupportIsometry N hN))
      N := by
  let V : Matrix a (psdSupportIndex N hN) ℂ := psdSupportIsometry N hN
  let Pi : CMatrix a :=
    psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian
  have hVV : V * Matrix.conjTranspose V = Pi := by
    simpa [V, Pi] using
      psdSupportIsometry_mul_conjTranspose_eq_supportProjector N hN
  have hfix : (V * X * Matrix.conjTranspose V) * Pi =
      V * X * Matrix.conjTranspose V := by
    calc
      (V * X * Matrix.conjTranspose V) * Pi =
          (V * X * Matrix.conjTranspose V) *
            (V * Matrix.conjTranspose V) := by rw [hVV]
      _ = V * X * (Matrix.conjTranspose V * V) * Matrix.conjTranspose V := by
            simp [Matrix.mul_assoc]
      _ = V * X * Matrix.conjTranspose V := by
            rw [psdSupportIsometry_isometry N hN]
            simp [Matrix.mul_assoc]
  have hMPi :
      Matrix.Supports (V * X * Matrix.conjTranspose V) Pi :=
    Matrix.Supports.of_mul_right_eq_self hfix
  have hPiN : Matrix.Supports Pi N := by
    simpa [Pi] using supportProjector_supports N hN
  exact Matrix.Supports.trans hMPi hPiN

/-- A matrix supported by `N` is exactly recovered after compression to the
positive spectral support of `N` and re-embedding by the support isometry. -/
theorem psdSupportCompress_reconstruct_of_supports
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N) :
    let V : Matrix a (psdSupportIndex N hN) ℂ := psdSupportIsometry N hN
    V * psdSupportCompress N hN M * Matrix.conjTranspose V = M := by
  classical
  dsimp
  let V : Matrix a (psdSupportIndex N hN) ℂ := psdSupportIsometry N hN
  let Pi : CMatrix a :=
    psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian
  have hVV : V * Matrix.conjTranspose V = Pi := by
    simpa [V, Pi] using
      psdSupportIsometry_mul_conjTranspose_eq_supportProjector N hN
  have hfix :=
    supportProjector_fixes_of_supports (M := M) (N := N) hM hN hSupport
  calc
    V * psdSupportCompress N hN M * Matrix.conjTranspose V
        = (V * Matrix.conjTranspose V) * M *
            (V * Matrix.conjTranspose V) := by
          simp [psdSupportCompress, V, Matrix.mul_assoc]
    _ = Pi * M * Pi := by rw [hVV]
    _ = M := by
          rw [show Pi * M = M from by simpa [Pi] using hfix.1]
          rw [show M * Pi = M from by simpa [Pi] using hfix.2]

/-- Compression to the positive spectral support preserves trace for supported
PSD matrices. -/
theorem psdSupportCompress_trace_of_supports
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N) :
    (psdSupportCompress N hN M).trace = M.trace := by
  classical
  let V : Matrix a (psdSupportIndex N hN) ℂ := psdSupportIsometry N hN
  have hrec :
      V * psdSupportCompress N hN M * Matrix.conjTranspose V = M := by
    simpa [V] using
      psdSupportCompress_reconstruct_of_supports
        (M := M) (N := N) hM hN hSupport
  have htrace := congrArg Matrix.trace hrec
  rw [Matrix.trace_mul_cycle, psdSupportIsometry_isometry, Matrix.one_mul] at htrace
  exact htrace

/-- Compression to the positive support preserves trace for any matrix with
right support contained in the PSD reference. -/
theorem psdSupportCompress_trace_of_supports_right
    {M N : CMatrix a} (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N) :
    (psdSupportCompress N hN M).trace = M.trace := by
  classical
  let V : Matrix a (psdSupportIndex N hN) ℂ := psdSupportIsometry N hN
  let Pi : CMatrix a :=
    psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian
  have hVV : V * Matrix.conjTranspose V = Pi := by
    simpa [V, Pi] using
      psdSupportIsometry_mul_conjTranspose_eq_supportProjector N hN
  have hright : M * Pi = M := by
    simpa [Pi] using
      supportProjector_right_fixes_of_supports (M := M) (N := N) hN hSupport
  calc
    (psdSupportCompress N hN M).trace =
        (Matrix.conjTranspose V * M * V).trace := by
          rfl
    _ = ((V * Matrix.conjTranspose V) * M).trace := by
          rw [Matrix.trace_mul_cycle]
    _ = (M * (V * Matrix.conjTranspose V)).trace := by
          rw [Matrix.trace_mul_comm]
    _ = (M * Pi).trace := by
          rw [hVV]
    _ = M.trace := by
          rw [hright]

/-- A matrix whose right support and conjugate-transpose right support are both
contained in a PSD reference is recovered after support compression and
re-embedding. -/
theorem psdSupportCompress_reconstruct_of_supports_right_and_conjTranspose
    {M N : CMatrix a} (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N)
    (hSupport_star : Matrix.Supports (Matrix.conjTranspose M) N) :
    psdSupportIsometry N hN * psdSupportCompress N hN M *
        Matrix.conjTranspose (psdSupportIsometry N hN) = M := by
  classical
  let V : Matrix a (psdSupportIndex N hN) ℂ := psdSupportIsometry N hN
  let Pi : CMatrix a :=
    psdInvSqrt N hN.isHermitian * N * psdInvSqrt N hN.isHermitian
  have hVV : V * Matrix.conjTranspose V = Pi := by
    simpa [V, Pi] using
      psdSupportIsometry_mul_conjTranspose_eq_supportProjector N hN
  have hright : M * Pi = M := by
    simpa [Pi] using
      supportProjector_right_fixes_of_supports (M := M) (N := N) hN hSupport
  have hstar_right : Matrix.conjTranspose M * Pi = Matrix.conjTranspose M := by
    simpa [Pi] using
      supportProjector_right_fixes_of_supports
        (M := Matrix.conjTranspose M) (N := N) hN hSupport_star
  have hPiHerm : Matrix.conjTranspose Pi = Pi := by
    calc
      Matrix.conjTranspose Pi =
          Matrix.conjTranspose (V * Matrix.conjTranspose V) := by rw [hVV]
      _ = V * Matrix.conjTranspose V := by
          simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = Pi := hVV
  have hleft : Pi * M = M := by
    have h := congrArg Matrix.conjTranspose hstar_right
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hPiHerm]
      using h
  calc
    psdSupportIsometry N hN * psdSupportCompress N hN M *
        Matrix.conjTranspose (psdSupportIsometry N hN)
        = V * psdSupportCompress N hN M * Matrix.conjTranspose V := by
          rfl
    _ = (V * Matrix.conjTranspose V) * M *
          (V * Matrix.conjTranspose V) := by
          simp [psdSupportCompress, V, Matrix.mul_assoc]
    _ = Pi * M * Pi := by rw [hVV]
    _ = M := by rw [hleft, hright]

/-- A PSD reference is reconstructed from its support compression. -/
theorem psdSupportCompress_reconstruct_self
    (N : CMatrix a) (hN : N.PosSemidef) :
    let V : Matrix a (psdSupportIndex N hN) ℂ := psdSupportIsometry N hN
    V * psdSupportCompress N hN N * Matrix.conjTranspose V = N := by
  exact
    psdSupportCompress_reconstruct_of_supports
      (M := N) (N := N) hN hN (Matrix.Supports.refl N)

/-- A PSD reference and its support compression have the same trace. -/
theorem psdSupportCompress_trace_self
    (N : CMatrix a) (hN : N.PosSemidef) :
    (psdSupportCompress N hN N).trace = N.trace :=
  psdSupportCompress_trace_of_supports
    (M := N) (N := N) hN hN (Matrix.Supports.refl N)

/-- If a trace-one PSD matrix is supported by a PSD reference, then the
reference has nonempty positive spectral support. -/
theorem psdSupportIndex_nonempty_of_trace_one_supports
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hMtr : M.trace = 1) (hSupport : Matrix.Supports M N) :
    Nonempty (psdSupportIndex N hN) := by
  classical
  by_contra hnon
  haveI : IsEmpty (psdSupportIndex N hN) := not_nonempty_iff.mp hnon
  have htrace :=
    psdSupportCompress_trace_of_supports
      (M := M) (N := N) hM hN hSupport
  have hzero : (psdSupportCompress N hN M).trace = 0 := by
    simp [Matrix.trace]
  have hone : (psdSupportCompress N hN M).trace = 1 := by
    calc
      (psdSupportCompress N hN M).trace = 0 := hzero
      _ = M.trace := by simpa using htrace
      _ = 1 := hMtr
  exact zero_ne_one (hzero.symm.trans hone)

/-- Compressing a PSD matrix to its own positive spectral support gives the
diagonal matrix of strictly positive eigenvalues. -/
theorem psdSupportCompress_self_eq_diagonal
    (N : CMatrix a) (hN : N.PosSemidef) :
    psdSupportCompress N hN N =
      (Matrix.diagonal fun i : psdSupportIndex N hN =>
        ((hN.isHermitian.eigenvalues i.1 : ℝ) : ℂ)) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let D : CMatrix a :=
    Matrix.diagonal fun i => ((hN.isHermitian.eigenvalues i : ℝ) : ℂ)
  have hspec :
      N = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hN.isHermitian.spectral_theorem
  have hdiag :
      star (U : CMatrix a) * N * (U : CMatrix a) = D := by
    have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
      simp [U]
    calc
      star (U : CMatrix a) * N * (U : CMatrix a)
          = star (U : CMatrix a) *
              ((U : CMatrix a) * D * star (U : CMatrix a)) *
                (U : CMatrix a) := by rw [hspec]
      _ = (star (U : CMatrix a) * (U : CMatrix a)) * D *
            (star (U : CMatrix a) * (U : CMatrix a)) := by
            noncomm_ring
      _ = D := by simp [hUstarU]
  ext i j
  have hentry :=
    congrArg (fun M : CMatrix a => M i.1 j.1) hdiag
  by_cases hij : i = j
  · subst j
    simpa [psdSupportCompress, psdSupportIsometry, U, D, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal, Matrix.one_apply] using hentry
  · have hval : (i : psdSupportIndex N hN).1 ≠ j.1 := by
      intro hraw
      exact hij (Subtype.ext hraw)
    simpa [psdSupportCompress, psdSupportIsometry, U, D, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal, Matrix.one_apply, hij, hval]
      using hentry

/-- A PSD reference becomes positive definite after compression to its
positive spectral support. -/
theorem psdSupportCompress_self_posDef
    (N : CMatrix a) (hN : N.PosSemidef) :
    (psdSupportCompress N hN N).PosDef := by
  rw [psdSupportCompress_self_eq_diagonal]
  rw [Matrix.posDef_diagonal_iff]
  intro i
  change 0 < ((hN.isHermitian.eigenvalues i.1 : ℝ) : ℂ)
  exact_mod_cast i.2

/-- A state supported by a PSD reference compresses to a state on the
reference's positive spectral support. -/
noncomputable def psdSupportCompressedState
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    State (psdSupportIndex σ hσ) where
  matrix := psdSupportCompress σ hσ ρ.matrix
  pos := psdSupportCompress_posSemidef σ hσ ρ.pos
  trace_eq_one := by
    have htrace :=
      psdSupportCompress_trace_of_supports
        (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport
    simpa [htrace] using ρ.trace_eq_one

@[simp]
theorem psdSupportCompressedState_matrix
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    (psdSupportCompressedState ρ hσ hSupport).matrix =
      psdSupportCompress σ hσ ρ.matrix := rfl

theorem psdSupportCompressedState_reference_posDef
    {σ : CMatrix a} (hσ : σ.PosSemidef) :
    (psdSupportCompress σ hσ σ).PosDef :=
  psdSupportCompress_self_posDef σ hσ

theorem psdSupportCompressedState_support_nonempty
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    Nonempty (psdSupportIndex σ hσ) :=
  psdSupportIndex_nonempty_of_trace_one_supports
    ρ.pos hσ ρ.trace_eq_one hSupport

/-- Any nonzero real power of a PSD reference is recovered by compressing the
reference to its positive spectral support, taking the power there, and
embedding back.  This is the support-domain power identity needed for the
high-`α` finite branch, where the reference exponent is negative. -/
theorem cMatrix_rpow_psdSupportCompress_reconstruct_self
    (N : CMatrix a) (hN : N.PosSemidef) {s : ℝ} (hs : s ≠ 0) :
    let V : Matrix a (psdSupportIndex N hN) ℂ := psdSupportIsometry N hN
    V * CFC.rpow (psdSupportCompress N hN N) s * Matrix.conjTranspose V =
      CFC.rpow N s := by
  classical
  dsimp
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let d : a → ℝ := fun i => hN.isHermitian.eigenvalues i
  have hcomp :
      psdSupportCompress N hN N =
        (Matrix.diagonal fun i : psdSupportIndex N hN =>
          ((d i.1 : ℝ) : ℂ)) := by
    simpa [d] using psdSupportCompress_self_eq_diagonal N hN
  have hcomp_pow :
      CFC.rpow (psdSupportCompress N hN N) s =
        (Matrix.diagonal fun i : psdSupportIndex N hN =>
          ((d i.1 ^ s : ℝ) : ℂ)) := by
    rw [hcomp]
    exact cMatrix_rpow_diagonal_ofReal
      (fun i : psdSupportIndex N hN => d i.1)
      (fun i => le_of_lt i.2) s
  have hNpow :
      CFC.rpow N s =
        (U : CMatrix a) *
          Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) *
            star (U : CMatrix a) := by
    simpa [U, d] using cMatrix_rpow_eq_eigenbasis_diagonal hN s
  rw [show N ^ s =
        (U : CMatrix a) *
          Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) *
            star (U : CMatrix a) from hNpow,
      show (psdSupportCompress N hN N) ^ s =
        (Matrix.diagonal fun i : psdSupportIndex N hN =>
          ((d i.1 ^ s : ℝ) : ℂ)) from hcomp_pow]
  ext i j
  let f : a → ℂ := fun x =>
    (U : CMatrix a) i x * ((d x ^ s : ℝ) : ℂ) *
      star ((U : CMatrix a) j x)
  have hsub :
      (∑ x : psdSupportIndex N hN,
          (U : CMatrix a) i x.1 * ((d x.1 ^ s : ℝ) : ℂ) *
            star ((U : CMatrix a) j x.1)) =
        ∑ x ∈ (Finset.univ : Finset a) with 0 < d x, f x := by
    simpa [f, d] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset a))
        (p := fun x => 0 < d x)
        (f := f))
  have hfilter :
      (∑ x ∈ (Finset.univ : Finset a) with 0 < d x, f x) =
        ∑ x, f x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxpos : 0 < d x
    · simp [hxpos]
    · have hdx : d x = 0 := by
        exact le_antisymm (not_lt.mp hxpos) (hN.eigenvalues_nonneg x)
      have hxpow : d x ^ s = 0 := by
        simpa [hdx] using Real.zero_rpow hs
      simp [hxpos, f, hxpow]
  simpa [psdSupportIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diagonal, f, U] using hsub.trans hfilter

/-- Schur-Horn/Jensen control of diagonal `q`-powers by the spectral
`q`-power trace for PSD matrices. -/
theorem posSemidef_sum_diagonal_re_rpow_le_psdTracePower
    {B : CMatrix a} (hB : B.PosSemidef) {q : ℝ} (hq : 1 ≤ q) :
    (∑ i, (B i i).re ^ q) ≤ psdTracePower B hB q := by
  classical
  have hpoint :
      ∀ i, (B i i).re ^ q ≤
        ∑ j, Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
          hB.isHermitian.eigenvalues j ^ q :=
    fun i => posSemidef_diagonal_re_rpow_le_eigenvalue_weighted_rpow hB hq i
  have hsum_le :
      (∑ i, (B i i).re ^ q) ≤
        ∑ i, ∑ j,
          Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
            hB.isHermitian.eigenvalues j ^ q :=
    Finset.sum_le_sum fun i _ => hpoint i
  have hdouble :
      (∑ i, ∑ j,
          Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
            hB.isHermitian.eigenvalues j ^ q) =
        ∑ j, hB.isHermitian.eigenvalues j ^ q := by
    calc
      (∑ i, ∑ j,
          Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
            hB.isHermitian.eigenvalues j ^ q)
          = ∑ j, ∑ i,
              Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
                hB.isHermitian.eigenvalues j ^ q := by
              rw [Finset.sum_comm]
      _ = ∑ j,
              (∑ i, Complex.normSq
                ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j)) *
                hB.isHermitian.eigenvalues j ^ q := by
              simp [Finset.sum_mul]
      _ = ∑ j, hB.isHermitian.eigenvalues j ^ q := by
              simp_rw [unitary_col_normSq_sum hB.isHermitian.eigenvectorUnitary]
              simp
  rw [psdTracePower_eq_sum_eigenvalues_rpow]
  exact hsum_le.trans_eq hdouble

@[simp]
theorem psdTracePower_eq (A : CMatrix a) (hA : A.PosSemidef) (p : ℝ) :
    psdTracePower A hA p = (CFC.rpow A p).trace.re :=
  rfl

/-- PSD power traces are nonnegative. -/
theorem psdTracePower_nonneg (A : CMatrix a) (hA : A.PosSemidef) (p : ℝ) :
    0 ≤ psdTracePower A hA p :=
  (Matrix.PosSemidef.trace_nonneg (cMatrix_rpow_posSemidef (A := A) (s := p) hA)).1

/-- PSD power traces multiply over Kronecker products. -/
theorem psdTracePower_kronecker
    {b : Type v} [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {p : Real} (hp : 0 <= p) :
    psdTracePower (Matrix.kronecker A B) (hA.kronecker hB) p =
      psdTracePower A hA p * psdTracePower B hB p := by
  rw [psdTracePower, cMatrix_rpow_kronecker_nonneg hA hB hp]
  change (Matrix.kroneckerMap (fun x y => x * y) (CFC.rpow A p)
      (CFC.rpow B p)).trace.re =
    psdTracePower A hA p * psdTracePower B hB p
  rw [Matrix.trace_kronecker]
  have hAim : ((CFC.rpow A p).trace).im = 0 := by
    have htrace_nonneg : 0 <= (CFC.rpow A p).trace :=
      Matrix.PosSemidef.trace_nonneg
        (cMatrix_rpow_posSemidef (A := A) (s := p) hA)
    exact htrace_nonneg.2.symm
  have hBim : ((CFC.rpow B p).trace).im = 0 := by
    have htrace_nonneg : 0 <= (CFC.rpow B p).trace :=
      Matrix.PosSemidef.trace_nonneg
        (cMatrix_rpow_posSemidef (A := B) (s := p) hB)
    exact htrace_nonneg.2.symm
  rw [Complex.mul_re, hAim, hBim]
  simp [psdTracePower]

/-- A nonzero PSD matrix has strictly positive `p`-power trace. -/
theorem psdTracePower_pos_of_ne_zero
    (A : CMatrix a) (hA : A.PosSemidef) {p : ℝ}
    (hAne : A ≠ 0) :
    0 < psdTracePower A hA p := by
  classical
  rw [psdTracePower_eq_sum_eigenvalues_rpow]
  have hexists : ∃ i, hA.isHermitian.eigenvalues i ≠ 0 := by
    by_contra hno
    have hzero : hA.isHermitian.eigenvalues = 0 := by
      funext i
      exact not_not.mp (by
        intro hi
        exact hno ⟨i, hi⟩)
    exact hAne ((hA.isHermitian.eigenvalues_eq_zero_iff).mp hzero)
  rcases hexists with ⟨i, hi⟩
  exact Finset.sum_pos' (fun j _ =>
      Real.rpow_nonneg (hA.eigenvalues_nonneg j) p)
    ⟨i, Finset.mem_univ i,
      Real.rpow_pos_of_pos (lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hi)) p⟩

/-- Scaling a positive-definite matrix by the inverse `q`-power trace factor
normalizes its `q`-power trace to one. -/
theorem psdTracePower_normalized_real_smul_eq_one_of_posDef [Nonempty a]
    {C : CMatrix a} (hC : C.PosDef) {q : ℝ} (hq : 0 < q) :
    psdTracePower
        (((psdTracePower C hC.posSemidef q) ^ (-(1 / q))) • C : CMatrix a)
        (Matrix.PosSemidef.smul hC.posSemidef
          (Real.rpow_nonneg (psdTracePower_nonneg C hC.posSemidef q) (-(1 / q))))
        q = 1 := by
  let S : ℝ := psdTracePower C hC.posSemidef q
  have hCne : C ≠ 0 := by
    intro hzero
    have htr : (0 : ℂ) < C.trace := Matrix.PosDef.trace_pos hC
    rw [hzero] at htr
    simp at htr
  have hSpos : 0 < S := by
    simpa [S] using psdTracePower_pos_of_ne_zero C hC.posSemidef hCne
  have hSnonneg : 0 ≤ S := le_of_lt hSpos
  have hscale_nonneg : 0 ≤ S ^ (-(1 / q)) := Real.rpow_nonneg hSnonneg _
  change psdTracePower ((S ^ (-(1 / q))) • C : CMatrix a)
      (Matrix.PosSemidef.smul hC.posSemidef
        (Real.rpow_nonneg hSnonneg (-(1 / q)))) q = 1
  rw [psdTracePower_real_smul_posSemidef hC.posSemidef hscale_nonneg]
  have hpow : (S ^ (-(1 / q))) ^ q = S⁻¹ := by
    calc
      (S ^ (-(1 / q))) ^ q = S ^ (-(1 / q) * q) := by
        rw [← Real.rpow_mul hSpos.le]
      _ = S ^ (-1 : ℝ) := by
        congr 1
        field_simp [ne_of_gt hq]
      _ = S⁻¹ := by
        rw [Real.rpow_neg_one]
  rw [hpow]
  change S⁻¹ * S = 1
  field_simp [ne_of_gt hSpos]

/-- Scaling a nonzero PSD matrix by the inverse `q`-power trace factor
normalizes its `q`-power trace to one. -/
theorem psdTracePower_normalized_real_smul_eq_one_of_ne_zero
    {C : CMatrix a} (hC : C.PosSemidef) (hCne : C ≠ 0) {q : ℝ}
    (hq : 0 < q) :
    psdTracePower
        (((psdTracePower C hC q) ^ (-(1 / q))) • C : CMatrix a)
        (Matrix.PosSemidef.smul hC
          (Real.rpow_nonneg (psdTracePower_nonneg C hC q) (-(1 / q))))
        q = 1 := by
  let S : ℝ := psdTracePower C hC q
  have hSpos : 0 < S := by
    simpa [S] using psdTracePower_pos_of_ne_zero C hC hCne
  have hSnonneg : 0 ≤ S := le_of_lt hSpos
  have hscale_nonneg : 0 ≤ S ^ (-(1 / q)) := Real.rpow_nonneg hSnonneg _
  change psdTracePower ((S ^ (-(1 / q))) • C : CMatrix a)
      (Matrix.PosSemidef.smul hC
        (Real.rpow_nonneg hSnonneg (-(1 / q)))) q = 1
  rw [psdTracePower_real_smul_posSemidef hC hscale_nonneg]
  have hpow : (S ^ (-(1 / q))) ^ q = S⁻¹ := by
    calc
      (S ^ (-(1 / q))) ^ q = S ^ (-(1 / q) * q) := by
        rw [← Real.rpow_mul hSpos.le]
      _ = S ^ (-1 : ℝ) := by
        congr 1
        field_simp [ne_of_gt hq]
      _ = S⁻¹ := by
        rw [Real.rpow_neg_one]
  rw [hpow]
  change S⁻¹ * S = 1
  field_simp [ne_of_gt hSpos]
/-- If a nonzero PSD matrix is supported on a PSD matrix, then pairing it
with any real power of the supporting matrix has strictly positive trace. -/
theorem trace_mul_cMatrix_rpow_pos_of_support
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hMne : M ≠ 0) (hSupport : Matrix.Supports M N)
    (s : ℝ) :
    0 < ((M * CFC.rpow N s).trace).re := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let M' : CMatrix a := star (U : CMatrix a) * M * (U : CMatrix a)
  let x : a → ℝ := fun i => (M' i i).re
  let w : a → ℝ := fun i => hN.isHermitian.eigenvalues i
  have hM' : M'.PosSemidef := by
    simpa [M'] using posSemidef_unitary_conj hM U
  have hx_nonneg : ∀ i, 0 ≤ x i := by
    intro i
    exact posSemidef_diagonal_re_nonneg hM' i
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    exact hN.eigenvalues_nonneg i
  have hsumx_pos : 0 < ∑ i, x i := by
    have htraceM_pos : 0 < M.trace.re := by
      have hpow := psdTracePower_pos_of_ne_zero M hM (p := 1) hMne
      simpa [psdTracePower, CFC.rpow_one M
        (ha := Matrix.nonneg_iff_posSemidef.mpr hM)] using hpow
    have htraceM' : M'.trace = M.trace := by
      calc
        M'.trace = (((star (U : CMatrix a) * M) * (U : CMatrix a))).trace := by
          simp [M', Matrix.mul_assoc]
        _ = (((U : CMatrix a) * (star (U : CMatrix a) * M))).trace := by
          exact Matrix.trace_mul_comm (star (U : CMatrix a) * M) (U : CMatrix a)
        _ = (((U : CMatrix a) * star (U : CMatrix a)) * M).trace := by
          rw [Matrix.mul_assoc]
        _ = M.trace := by
          have hUU : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
            exact Unitary.coe_mul_star_self U
          rw [hUU, Matrix.one_mul]
    have hsumx : ∑ i, x i = M.trace.re := by
      calc
        ∑ i, x i = M'.trace.re := by
          simp [x, Matrix.trace]
        _ = M.trace.re := by
          rw [htraceM']
    rw [hsumx]
    exact htraceM_pos
  have hexists : ∃ i, 0 < x i := by
    by_contra hno
    have hx_zero : ∀ i, x i = 0 := by
      intro i
      exact le_antisymm (not_lt.mp (by
        intro hxi
        exact hno ⟨i, hxi⟩)) (hx_nonneg i)
    have hsum_zero : ∑ i, x i = 0 := by
      simp [hx_zero]
    linarith
  rcases hexists with ⟨i, hxi_pos⟩
  have hwi_ne : w i ≠ 0 := by
    intro hwi
    have hxi_zero :
        x i = 0 := by
      simpa [x, w, M', U] using
        supports_conjugate_diagonal_re_eq_zero (M := M) (N := N) hN hSupport
          (i := i) hwi
    linarith
  have hwi_pos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi_ne)
  have hterm_pos : 0 < x i * w i ^ s :=
    mul_pos hxi_pos (Real.rpow_pos_of_pos hwi_pos s)
  have hsum_pos : 0 < ∑ i, x i * w i ^ s := by
    exact Finset.sum_pos'
      (fun j _ => mul_nonneg (hx_nonneg j)
        (Real.rpow_nonneg (hw_nonneg j) s))
      ⟨i, Finset.mem_univ i, hterm_pos⟩
  have htrace :
      ((M * CFC.rpow N s).trace).re =
        ∑ i, x i * w i ^ s := by
    simpa [x, w, M', U] using
      trace_mul_cMatrix_rpow_eq_conjugate_diag_sum (M := M) (N := N) hN s
  rw [htrace]
  exact hsum_pos

/-- Support-aware identity regularization for trace pairings with arbitrary
real powers.

Even for negative `s`, the trace pairing is continuous along `N + ε I` when
the left factor is supported by `N`: the potentially singular zero-eigenvalue
directions of `N` are killed by the support hypothesis.  This is the finite
dimensional regularization-removal step used in the KW reverse-Holder route. -/
theorem trace_mul_cMatrix_rpow_add_pos_smul_one_tendsto_of_support
    {M N : CMatrix a} (hN : N.PosSemidef)
    (hSupport : Matrix.Supports M N) (s : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => ((M * CFC.rpow (N + ε • (1 : CMatrix a)) s).trace).re)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((M * CFC.rpow N s).trace.re)) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hN.isHermitian.eigenvalues
  let M' : CMatrix a := star (U : CMatrix a) * M * (U : CMatrix a)
  have hd_nonneg : ∀ i, 0 ≤ d i := fun i => hN.eigenvalues_nonneg i
  have hdiag_trace
      (e : a → ℝ) :
      ((M * ((U : CMatrix a) *
            (Matrix.diagonal fun i => ((e i : ℂ) : ℂ)) *
          star (U : CMatrix a))).trace).re =
        ∑ i, (M' i i).re * e i := by
    let D : CMatrix a := Matrix.diagonal fun i => ((e i : ℂ) : ℂ)
    have htrace :
        (M * ((U : CMatrix a) * D * star (U : CMatrix a))).trace =
          (M' * D).trace := by
      calc
        (M * ((U : CMatrix a) * D * star (U : CMatrix a))).trace =
            ((M * (U : CMatrix a) * D) * star (U : CMatrix a)).trace := by
              congr 1
              noncomm_ring
        _ = (star (U : CMatrix a) * (M * (U : CMatrix a) * D)).trace := by
              exact Matrix.trace_mul_comm (M * (U : CMatrix a) * D)
                (star (U : CMatrix a))
        _ = (M' * D).trace := by
              congr 1
              simp [M', Matrix.mul_assoc]
    rw [htrace]
    simp [D, Matrix.trace, Matrix.diagonal, Matrix.mul_apply, Complex.mul_re]
  have htarget :
      ((M * CFC.rpow N s).trace).re =
        ∑ i, (M' i i).re * d i ^ s := by
    have hpow :
        CFC.rpow N s =
          (U : CMatrix a) *
            (Matrix.diagonal fun i => (((d i ^ s : ℝ) : ℂ) : ℂ)) *
          star (U : CMatrix a) := by
      simpa [U, d] using cMatrix_rpow_eq_eigenbasis_diagonal hN s
    rw [hpow]
    simpa [M', U, d] using hdiag_trace (fun i => d i ^ s)
  have hpath :
      (fun ε : ℝ => ((M * CFC.rpow (N + ε • (1 : CMatrix a)) s).trace).re)
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      fun ε : ℝ => ∑ i, (M' i i).re * (d i + ε) ^ s := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_nonneg : 0 ≤ ε := le_of_lt hε
    have hpow :
        CFC.rpow (N + ε • (1 : CMatrix a)) s =
          (U : CMatrix a) *
            (Matrix.diagonal fun i => ((((d i + ε) ^ s : ℝ) : ℂ) : ℂ)) *
          star (U : CMatrix a) := by
      simpa [U, d] using
        cMatrix_rpow_add_nonneg_smul_one_eigenbasis_diagonal hN hε_nonneg s
    rw [hpow]
    simpa [M', U, d] using hdiag_trace (fun i => (d i + ε) ^ s)
  have hterm :
      ∀ i,
        Filter.Tendsto (fun ε : ℝ => (M' i i).re * (d i + ε) ^ s)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds ((M' i i).re * d i ^ s)) := by
    intro i
    by_cases hdi : d i = 0
    · have hMii : (M' i i).re = 0 := by
        simpa [M', U, d] using
          supports_conjugate_diagonal_re_eq_zero (M := M) (N := N) hN hSupport
            (i := i) hdi
      simp [hMii]
    · have hdi_pos : 0 < d i := lt_of_le_of_ne (hd_nonneg i) (Ne.symm hdi)
      have hlin :
          Filter.Tendsto (fun ε : ℝ => d i + ε)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d i)) := by
        have hid : Filter.Tendsto (fun ε : ℝ => ε)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
          (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
        simpa using
          (tendsto_const_nhds.add hid)
      have hpow :
          Filter.Tendsto (fun ε : ℝ => (d i + ε) ^ s)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d i ^ s)) :=
        (Real.continuousAt_rpow_const (d i) s (Or.inl (ne_of_gt hdi_pos))).tendsto.comp
          hlin
      exact tendsto_const_nhds.mul hpow
  have hsum :
      Filter.Tendsto (fun ε : ℝ => ∑ i, (M' i i).re * (d i + ε) ^ s)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (∑ i, (M' i i).re * d i ^ s)) :=
    tendsto_finsetSum Finset.univ fun i _ => hterm i
  rw [htarget]
  exact hsum.congr' hpath.symm

/-- The first power trace is the ordinary trace. -/
@[simp]
theorem psdTracePower_one (A : CMatrix a) (hA : A.PosSemidef) :
    psdTracePower A hA (1 : ℝ) = A.trace.re := by
  simp [psdTracePower, CFC.rpow_one A (ha := Matrix.nonneg_iff_posSemidef.mpr hA)]

@[simp]
theorem psdTracePower_two (A : CMatrix a) (hA : A.PosSemidef) :
    psdTracePower A hA (2 : ℝ) = (A * A).trace.re := by
  rw [psdTracePower]
  have hpow : CFC.rpow A (2 : ℝ) = A * A := by
    simpa [pow_two] using
      (CFC.rpow_natCast A 2 (Matrix.nonneg_iff_posSemidef.mpr hA))
  rw [hpow]

/-- A mathematically valid order for a finite-dimensional Schatten norm. -/
def SchattenOrder := {p : ℝ // 0 < p}

namespace SchattenOrder

instance : Coe SchattenOrder ℝ := ⟨fun p => p.1⟩

/-- Construct a safe Schatten order from an explicit positivity proof. -/
def ofPositive {p : ℝ} (hp : 0 < p) : SchattenOrder := ⟨p, hp⟩

/-- Construct a safe Schatten order from the common stronger hypothesis `1 < p`. -/
def ofOneLt {p : ℝ} (hp : 1 < p) : SchattenOrder :=
  ⟨p, lt_trans zero_lt_one hp⟩

/-- Schatten order one. -/
def one : SchattenOrder := ⟨1, zero_lt_one⟩

/-- Schatten order two. -/
def two : SchattenOrder := ⟨2, by norm_num⟩

@[simp]
theorem coe_one : (one : ℝ) = 1 := rfl

@[simp]
theorem coe_two : (two : ℝ) = 2 := rfl

@[simp]
theorem coe_ofPositive {p : ℝ} (hp : 0 < p) :
    (ofPositive hp : ℝ) = p := rfl

@[simp]
theorem coe_ofOneLt {p : ℝ} (hp : 1 < p) :
    (ofOneLt hp : ℝ) = p := rfl

end SchattenOrder

/-- The unconstrained spectral expression underlying the PSD Schatten norm.

This helper is intentionally kept under `QIT.Internal`: at nonpositive orders
it is a totalized real expression, not a source-faithful Schatten norm. -/
def Internal.psdSchattenExpression
    (A : CMatrix a) (hA : A.PosSemidef) (p : ℝ) : ℝ :=
  Real.rpow (psdTracePower A hA p) (1 / p)

/-- The Schatten `p`-norm of a positive semidefinite matrix at a positive order. -/
def psdSchattenPNorm
    (A : CMatrix a) (hA : A.PosSemidef) (p : SchattenOrder) : ℝ :=
  Internal.psdSchattenExpression A hA p

/-- The Schatten `p`-norm of a general finite-dimensional operator, defined
through its absolute value `sqrt (Lᴴ * L)`. -/
def schattenPNorm (L : CMatrix a) (p : SchattenOrder) : ℝ :=
  psdSchattenPNorm (psdSqrt (Matrix.conjTranspose L * L))
    (psdSqrt_pos (Matrix.conjTranspose L * L)) p

@[simp]
theorem psdSchattenPNorm_eq (A : CMatrix a) (hA : A.PosSemidef) (p : SchattenOrder) :
    psdSchattenPNorm A hA p =
      Real.rpow ((CFC.rpow A (p : ℝ)).trace.re) (1 / (p : ℝ)) :=
  rfl

/-- PSD Schatten `p`-norm expressions are nonnegative. -/
theorem psdSchattenPNorm_nonneg
    (A : CMatrix a) (hA : A.PosSemidef) (p : SchattenOrder) :
    0 ≤ psdSchattenPNorm A hA p :=
  Real.rpow_nonneg (psdTracePower_nonneg A hA p) _

/-- PSD Schatten `p`-norm expressions are continuous along PSD-constrained
convergent filters for `0 < p`.

This is the norm-level companion to
`cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef`.  It packages the final
real-power step so callers do not need to repeat the trace-power continuity
argument when proving continuity of sandwiched-Renyi objective functions. -/
theorem psdSchattenPNorm_tendsto_of_tendsto_posSemidef
    {X : Type*} {l : Filter X} {F : X → CMatrix a} {A : CMatrix a}
    (p : SchattenOrder)
    (hF : Filter.Tendsto F l (nhds A))
    (hFpsd : ∀ x, (F x).PosSemidef)
    (hA : A.PosSemidef) :
    Filter.Tendsto (fun x => psdSchattenPNorm (F x) (hFpsd x) p) l
      (nhds (psdSchattenPNorm A hA p)) := by
  have htrace :
      Filter.Tendsto (fun x => psdTracePower (F x) (hFpsd x) p) l
        (nhds (psdTracePower A hA p)) := by
    simpa [psdTracePower] using
      cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef p.property hF
        (Filter.Eventually.of_forall hFpsd) hA
  have hexp_nonneg : 0 ≤ (1 / (p : ℝ)) := one_div_nonneg.mpr p.property.le
  have hpow :
      ContinuousAt (fun x : ℝ => x ^ (1 / p : ℝ)) (psdTracePower A hA p) :=
    Real.continuousAt_rpow_const (psdTracePower A hA p) (1 / p) (Or.inr hexp_nonneg)
  simpa [psdSchattenPNorm, Internal.psdSchattenExpression] using
    hpow.tendsto.comp htrace

/-- PSD Schatten `p`-norm expressions multiply over Kronecker products. -/
theorem psdSchattenPNorm_kronecker
    {b : Type v} [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (p : SchattenOrder) :
    psdSchattenPNorm (Matrix.kronecker A B) (hA.kronecker hB) p =
      psdSchattenPNorm A hA p * psdSchattenPNorm B hB p := by
  rw [psdSchattenPNorm, psdSchattenPNorm, psdSchattenPNorm,
    Internal.psdSchattenExpression,
    psdTracePower_kronecker hA hB p.property.le]
  exact Real.mul_rpow (psdTracePower_nonneg A hA p)
    (psdTracePower_nonneg B hB p)

/-- A nonzero PSD matrix has strictly positive spectral Schatten `p`-norm
expression. -/
theorem psdSchattenPNorm_pos_of_ne_zero
    (A : CMatrix a) (hA : A.PosSemidef) {p : SchattenOrder}
    (hAne : A ≠ 0) :
    0 < psdSchattenPNorm A hA p :=
  Real.rpow_pos_of_pos (psdTracePower_pos_of_ne_zero A hA hAne) (1 / (p : ℝ))

/-- PSD Schatten `p`-norm expressions are homogeneous under nonnegative real
scalar multiplication. -/
theorem psdSchattenPNorm_real_smul
    {A : CMatrix a} (hA : A.PosSemidef) {lambda : Real}
    (hlambda : 0 <= lambda) (p : SchattenOrder) :
    psdSchattenPNorm (lambda • A : CMatrix a)
        (Matrix.PosSemidef.smul hA hlambda) p =
      lambda * psdSchattenPNorm A hA p := by
  have hp : 0 < (p : Real) := p.property
  rw [psdSchattenPNorm, Internal.psdSchattenExpression,
    psdTracePower_real_smul_posSemidef hA hlambda]
  have hbase : 0 <= lambda ^ (p : Real) := Real.rpow_nonneg hlambda p
  have htrace : 0 <= psdTracePower A hA p := psdTracePower_nonneg A hA p
  rw [show (lambda ^ (p : Real) * psdTracePower A hA p).rpow
      (1 / (p : Real)) =
      (lambda ^ (p : Real)) ^ (1 / (p : Real)) *
        (psdTracePower A hA p) ^ (1 / (p : Real)) by
    exact Real.mul_rpow hbase htrace]
  have hp_ne : (p : Real) ≠ 0 := ne_of_gt hp
  have hpow : (lambda ^ (p : Real)) ^ (1 / (p : Real)) = lambda := by
    calc
      (lambda ^ (p : Real)) ^ (1 / (p : Real)) =
          lambda ^ ((p : Real) * (1 / (p : Real))) := by
        rw [← Real.rpow_mul hlambda]
      _ = lambda ^ (1 : Real) := by
        congr 1
        field_simp [hp_ne]
      _ = lambda := Real.rpow_one lambda
  rw [hpow]
  simp [psdSchattenPNorm, Internal.psdSchattenExpression, one_div]

/-- The PSD Schatten expression is insensitive to the particular PSD proof
attached to definitionally equal matrices. -/
theorem psdSchattenPNorm_congr
    {A B : CMatrix a} (hAB : A = B)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (p : SchattenOrder) :
    psdSchattenPNorm A hA p = psdSchattenPNorm B hB p := by
  subst B
  simp [psdSchattenPNorm, Internal.psdSchattenExpression, psdTracePower]

/-- The PSD Schatten expression of the zero matrix is zero for nonzero
exponents. -/
theorem psdSchattenPNorm_zero (p : SchattenOrder) :
    psdSchattenPNorm (0 : CMatrix a) Matrix.PosSemidef.zero p = 0 := by
  rw [psdSchattenPNorm, Internal.psdSchattenExpression, psdTracePower]
  rw [CFC.zero_rpow (A := CMatrix a) (ne_of_gt p.property)]
  rw [Matrix.trace_zero]
  change Real.rpow (0 : Real) (1 / (p : ℝ)) = 0
  rw [one_div]
  exact Real.zero_rpow (inv_ne_zero (ne_of_gt p.property))

/-- Strict positivity of the PSD Schatten expression forces strict positivity
of the underlying positive power trace when `p > 1`. -/
theorem psdTracePower_pos_of_psdSchattenPNorm_pos_of_one_lt
    {A : CMatrix a} (hA : A.PosSemidef) {p : Real}
    (hp : 1 < p) (hnorm : 0 < psdSchattenPNorm A hA ⟨p, lt_trans zero_lt_one hp⟩) :
    0 < psdTracePower A hA p := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hexp_ne : 1 / p ≠ 0 := one_div_ne_zero (ne_of_gt hp_pos)
  have htrace_nonneg : 0 <= psdTracePower A hA p :=
    psdTracePower_nonneg A hA p
  have htrace_ne : psdTracePower A hA p ≠ 0 := by
    intro htrace_zero
    have hnorm_zero : psdSchattenPNorm A hA ⟨p, hp_pos⟩ = 0 := by
      rw [psdSchattenPNorm, Internal.psdSchattenExpression, htrace_zero]
      exact Real.zero_rpow hexp_ne
    exact (ne_of_gt hnorm) hnorm_zero
  exact lt_of_le_of_ne htrace_nonneg (Ne.symm htrace_ne)

/-- A positive-definite matrix has strictly positive spectral Schatten
`p`-norm expression on any nonempty finite space. -/
theorem psdSchattenPNorm_pos_of_posDef [Nonempty a]
    {A : CMatrix a} (hA : A.PosDef) {p : SchattenOrder} :
    0 < psdSchattenPNorm A hA.posSemidef p := by
  have hAne : A ≠ 0 := by
    intro hzero
    have htr : (0 : ℂ) < A.trace := Matrix.PosDef.trace_pos hA
    rw [hzero] at htr
    simp at htr
  exact psdSchattenPNorm_pos_of_ne_zero A hA.posSemidef hAne

/-- At `p = 1`, the PSD Schatten expression is the real trace. -/
@[simp]
theorem psdSchattenPNorm_one (A : CMatrix a) (hA : A.PosSemidef) :
    psdSchattenPNorm A hA SchattenOrder.one = A.trace.re := by
  change Real.rpow (psdTracePower A hA (1 : ℝ)) (1 / (1 : ℝ)) = A.trace.re
  rw [psdTracePower_one]
  simp [Real.rpow_one]

/-- At `p = 2`, the PSD Schatten norm is the square root of the quadratic trace. -/
@[simp]
theorem psdSchattenPNorm_two (A : CMatrix a) (hA : A.PosSemidef) :
    psdSchattenPNorm A hA SchattenOrder.two = Real.sqrt ((A * A).trace.re) := by
  change Real.rpow (psdTracePower A hA (2 : ℝ)) (1 / (2 : ℝ)) =
    Real.sqrt ((A * A).trace.re)
  rw [psdTracePower_two]
  exact (Real.sqrt_eq_rpow _).symm

/-- On the positive cone, the general Schatten norm agrees with the PSD specialization. -/
theorem schattenPNorm_eq_psdSchattenPNorm
    (A : CMatrix a) (hA : A.PosSemidef) (p : SchattenOrder) :
    schattenPNorm A p = psdSchattenPNorm A hA p := by
  have hstar : Matrix.conjTranspose A = A := hA.isHermitian.eq
  have hsqrt : psdSqrt (Matrix.conjTranspose A * A) = A := by
    rw [hstar]
    simpa [psdSqrt, sq] using (CFC.sqrt_sq A hA.nonneg)
  unfold schattenPNorm
  exact psdSchattenPNorm_congr hsqrt _ _ p

/-- The order-one Schatten norm is the trace norm. -/
@[simp]
theorem schattenPNorm_one (L : CMatrix a) :
    schattenPNorm L SchattenOrder.one = traceNorm L := by
  rw [schattenPNorm, psdSchattenPNorm_one]
  rfl

/-- The order-two Schatten norm is the Frobenius/Hilbert--Schmidt norm. -/
@[simp]
theorem schattenPNorm_two (L : CMatrix a) :
    schattenPNorm L SchattenOrder.two =
      Real.sqrt ((Matrix.conjTranspose L * L).trace.re) := by
  rw [schattenPNorm, psdSchattenPNorm_two,
    psdSqrt_mul_self_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self L)]

/-- Finite scalar reverse Holder inequality in the normalized-weight form used
by the PSD reverse-Holder proof. -/
theorem real_sum_rpow_one_div_le_reverse_holder {ι : Type*} [Fintype ι]
    {x w : ι → ℝ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hx : ∀ i, 0 ≤ x i)
    (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1)
    (hsupp : ∀ i, w i = 0 → x i = 0) :
    (∑ i, x i ^ p) ^ (1 / p) ≤
      ∑ i, x i * w i ^ (1 - 1 / p) := by
  classical
  let z : ι → ℝ := fun i => if h : w i = 0 then 0 else x i / (w i ^ (1 / p))
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    dsimp [z]
    split_ifs with _h
    · exact le_rfl
    · exact div_nonneg (hx i) (Real.rpow_nonneg (hw i) _)
  have hz_mem : ∀ i ∈ (Finset.univ : Finset ι), z i ∈ Set.Ici (0 : ℝ) := by
    intro i _
    exact hz_nonneg i
  have hconc := (Real.concaveOn_rpow (p := p) (le_of_lt hp0) (le_of_lt hp1)).le_map_sum
      (t := (Finset.univ : Finset ι)) (w := w) (p := z)
      (by intro i _; exact hw i)
      (by simpa using hwsum)
      hz_mem
  have hzsum :
      (∑ i ∈ (Finset.univ : Finset ι), w i • z i) =
        ∑ i, x i * w i ^ (1 - 1 / p) := by
    simp only [smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hw0 : w i = 0
    · simp [z, hw0, hsupp i hw0]
    · have hwpos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hw0)
      calc
        w i * z i
            = w i * (x i / w i ^ (1 / p)) := by simp [z, hw0]
        _ = x i * (w i / w i ^ (1 / p)) := by ring
        _ = x i * (w i ^ (1 : ℝ) / w i ^ (1 / p)) := by rw [Real.rpow_one]
        _ = x i * (w i ^ (1 - 1 / p)) := by
          rw [← Real.rpow_sub hwpos]
  have hpower_sum :
      (∑ i ∈ (Finset.univ : Finset ι), w i • (z i ^ p)) =
        ∑ i, x i ^ p := by
    simp only [smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hw0 : w i = 0
    · simp [z, hw0, hsupp i hw0, Real.zero_rpow (ne_of_gt hp0)]
    · have hwpos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hw0)
      have hxnonneg := hx i
      have hwpow_nonneg : 0 ≤ w i ^ (1 / p) := Real.rpow_nonneg (hw i) _
      calc
        w i * z i ^ p
            = w i * (x i / w i ^ (1 / p)) ^ p := by simp [z, hw0]
        _ = w i * (x i ^ p / (w i ^ (1 / p)) ^ p) := by
              rw [Real.div_rpow hxnonneg hwpow_nonneg]
        _ = w i * (x i ^ p / w i) := by
              rw [← Real.rpow_mul hwpos.le]
              have hp_ne : p ≠ 0 := ne_of_gt hp0
              rw [one_div_mul_cancel hp_ne, Real.rpow_one]
        _ = x i ^ p := by
              field_simp [hw0]
  have hpow_le :
      ∑ i, x i ^ p ≤
        (∑ i, x i * w i ^ (1 - 1 / p)) ^ p := by
    rw [hpower_sum, hzsum] at hconc
    simpa using hconc
  have hleft_nonneg : 0 ≤ ∑ i, x i ^ p := by
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hx i) p
  have hright_nonneg : 0 ≤ ∑ i, x i * w i ^ (1 - 1 / p) := by
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hx i) (Real.rpow_nonneg (hw i) _)
  have hleftnorm_nonneg : 0 ≤ (∑ i, x i ^ p) ^ (1 / p) :=
    Real.rpow_nonneg hleft_nonneg _
  have hpow_goal :
      ((∑ i, x i ^ p) ^ (1 / p)) ^ p ≤
        (∑ i, x i * w i ^ (1 - 1 / p)) ^ p := by
    rw [one_div]
    rw [Real.rpow_inv_rpow hleft_nonneg (ne_of_gt hp0)]
    simpa [one_div] using hpow_le
  exact (Real.rpow_le_rpow_iff hleftnorm_nonneg hright_nonneg hp0).mp hpow_goal

/-- The normalized reverse-Holder candidate `wᵢ = xᵢ^p / ∑ⱼ xⱼ^p`
attains the scalar lower bound.  The proof treats `xᵢ = 0` explicitly, which
is essential because the reverse exponent `1 - 1 / p` is negative when
`0 < p < 1`. -/
theorem real_sum_reverse_holder_optimizer_value {ι : Type*} [Fintype ι]
    {x : ι → ℝ} {p : ℝ}
    (hp0 : 0 < p) (hx : ∀ i, 0 ≤ x i)
    (hSpos : 0 < ∑ i, x i ^ p) :
    (∑ i, x i * (x i ^ p / (∑ j, x j ^ p)) ^ (1 - 1 / p)) =
      (∑ i, x i ^ p) ^ (1 / p) := by
  classical
  let S : ℝ := ∑ i, x i ^ p
  let r : ℝ := 1 - 1 / p
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have hSpos' : 0 < S := by simpa [S] using hSpos
  have hr_mul : p * r = p - 1 := by
    dsimp [r]
    field_simp [hp_ne]
  have hpow_mul : 1 + p * r = p := by
    rw [hr_mul]
    ring
  have hterm : ∀ i, x i * (x i ^ p / S) ^ r = x i ^ p / S ^ r := by
    intro i
    have hxpow_nonneg : 0 ≤ x i ^ p := Real.rpow_nonneg (hx i) p
    calc
      x i * (x i ^ p / S) ^ r
          = x i * ((x i ^ p) ^ r / S ^ r) := by
              rw [Real.div_rpow hxpow_nonneg hSpos'.le r]
      _ = x i * (x i ^ (p * r) / S ^ r) := by
              rw [← Real.rpow_mul (hx i)]
      _ = (x i * x i ^ (p * r)) / S ^ r := by ring
      _ = x i ^ p / S ^ r := by
              congr 1
              by_cases hzero : x i = 0
              · simp [hzero, Real.zero_rpow hp_ne]
              · have hxpos : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hzero)
                calc
                  x i * x i ^ (p * r)
                      = x i ^ (1 : ℝ) * x i ^ (p * r) := by rw [Real.rpow_one]
                  _ = x i ^ (1 + p * r) := by
                        rw [← Real.rpow_add hxpos]
                  _ = x i ^ p := by rw [hpow_mul]
  calc
    (∑ i, x i * (x i ^ p / (∑ j, x j ^ p)) ^ (1 - 1 / p))
        = ∑ i, x i ^ p / S ^ r := by
            apply Finset.sum_congr rfl
            intro i _
            simpa [S, r] using hterm i
    _ = S / S ^ r := by
            simp [S, Finset.sum_div]
    _ = S ^ (1 / p) := by
            calc
              S / S ^ r = S ^ (1 : ℝ) / S ^ r := by rw [Real.rpow_one]
              _ = S ^ (1 - r) := by rw [Real.rpow_sub hSpos' 1 r]
              _ = S ^ (1 / p) := by
                    congr 1
                    dsimp [r]
                    ring

/-- Noncommutative Holder upper bound for PSD trace pairings, expressed with
PSD spectral Schatten expressions.  If the right factor has normalized
`q`-power trace, the real trace pairing is bounded by the left factor's
Schatten `p` expression. -/
theorem posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
    {M B : CMatrix a} (hM : M.PosSemidef) (hB : B.PosSemidef)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hq : 1 ≤ q)
    (hBq : psdTracePower B hB q ≤ 1) :
    ((M * B).trace).re ≤ psdSchattenPNorm M hM ⟨p, hpq.pos⟩ := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hM.isHermitian.eigenvectorUnitary
  let B' : CMatrix a := star (U : CMatrix a) * B * (U : CMatrix a)
  have hB' : B'.PosSemidef := by
    simpa [B'] using posSemidef_unitary_conj hB U
  have htrace :
      ((M * B).trace).re =
        ∑ i ∈ (Finset.univ : Finset a),
          hM.isHermitian.eigenvalues i * (B' i i).re := by
    simpa [U, B'] using
      posSemidef_trace_mul_eq_eigenvalue_conjugate_diag_sum (M := M) (B := B) hM
  have hholder :
      ∑ i ∈ (Finset.univ : Finset a),
          hM.isHermitian.eigenvalues i * (B' i i).re ≤
        (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i ^ p) ^ (1 / p) *
          (∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q) ^ (1 / q) :=
    Real.inner_le_Lp_mul_Lq_of_nonneg
      (s := (Finset.univ : Finset a))
      (f := fun i => hM.isHermitian.eigenvalues i)
      (g := fun i => (B' i i).re)
      hpq
      (fun i _ => hM.eigenvalues_nonneg i)
      (fun i _ => posSemidef_diagonal_re_nonneg hB' i)
  have hMnorm :
      (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i ^ p) ^ (1 / p) =
        psdSchattenPNorm M hM ⟨p, hpq.pos⟩ := by
    rw [psdSchattenPNorm, Internal.psdSchattenExpression,
      psdTracePower_eq_sum_eigenvalues_rpow]
    simp
  have hBpower_conj :
      psdTracePower B' hB' q = psdTracePower B hB q := by
    dsimp [B']
    exact psdTracePower_unitary_conj U hB (p := q) (le_of_lt hpq.symm.pos)
  have hBdiag_sum_le_one :
      ∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q ≤ 1 := by
    have hdiag_le := posSemidef_sum_diagonal_re_rpow_le_psdTracePower hB' hq
    have hpower_le : psdTracePower B' hB' q ≤ 1 := by
      rw [hBpower_conj]
      exact hBq
    have hdiag_le' :
        ∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q ≤ psdTracePower B' hB' q := by
      simpa using hdiag_le
    exact hdiag_le'.trans hpower_le
  have hBdiag_sum_nonneg :
      0 ≤ ∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q := by
    exact Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (posSemidef_diagonal_re_nonneg hB' i) q
  have hBnorm_le :
      (∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q) ^ (1 / q) ≤ 1 :=
    Real.rpow_le_one hBdiag_sum_nonneg hBdiag_sum_le_one hpq.symm.one_div_nonneg
  calc
    ((M * B).trace).re =
        ∑ i ∈ (Finset.univ : Finset a),
          hM.isHermitian.eigenvalues i * (B' i i).re := htrace
    _ ≤ (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i ^ p) ^ (1 / p) *
          (∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q) ^ (1 / q) := hholder
    _ = psdSchattenPNorm M hM ⟨p, hpq.pos⟩ *
          (∑ i ∈ (Finset.univ : Finset a), (B' i i).re ^ q) ^ (1 / q) := by
            rw [hMnorm]
    _ ≤ psdSchattenPNorm M hM ⟨p, hpq.pos⟩ * 1 :=
          mul_le_mul_of_nonneg_left hBnorm_le
            (psdSchattenPNorm_nonneg M hM ⟨p, hpq.pos⟩)
    _ = psdSchattenPNorm M hM ⟨p, hpq.pos⟩ := by rw [mul_one]

/-- Source-shaped finite-dimensional PSD Holder trace bound.

This is the positive-matrix specialization of Tomamichel
`metric.tex`, Lemma `lm:hoelder`, equation `eq:hoelder1`, in the form used by
the finite-resource conditional-Renyi route.  The source's general operator
bound is intentionally specialized here to PSD trace pairings, which is the
downstream shape needed in `cond.tex`.
-/
theorem psdTraceMul_le_psdSchattenPNorm_mul
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    {p q : ℝ} (_hp1 : 1 < p) (hpq : p.HolderConjugate q) :
    ((M * N).trace).re ≤
      psdSchattenPNorm M hM ⟨p, hpq.pos⟩ *
        psdSchattenPNorm N hN ⟨q, hpq.symm.pos⟩ := by
  by_cases hNzero : N = 0
  · have htrace : ((M * N).trace).re = 0 := by
      simp [hNzero]
    rw [htrace]
    exact mul_nonneg (psdSchattenPNorm_nonneg M hM ⟨p, hpq.pos⟩)
      (psdSchattenPNorm_nonneg N hN ⟨q, hpq.symm.pos⟩)
  · let S : ℝ := psdTracePower N hN q
    have hq_pos : 0 < q := hpq.symm.pos
    have hSpos : 0 < S := by
      simpa [S] using psdTracePower_pos_of_ne_zero N hN hNzero
    have hSnonneg : 0 ≤ S := le_of_lt hSpos
    let scale : ℝ := S ^ (-(1 / q))
    have hscale_nonneg : 0 ≤ scale := Real.rpow_nonneg hSnonneg (-(1 / q))
    let B : CMatrix a := scale • N
    have hB : B.PosSemidef := by
      simpa [B, scale] using Matrix.PosSemidef.smul hN hscale_nonneg
    have hBq_eq : psdTracePower B hB q = 1 := by
      simpa [B, S, scale, hB] using
        psdTracePower_normalized_real_smul_eq_one_of_ne_zero hN hNzero hq_pos
    have hholder :
        ((M * B).trace).re ≤ psdSchattenPNorm M hM ⟨p, hpq.pos⟩ :=
      posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
        (M := M) (B := B) hM hB hpq (le_of_lt hpq.symm.lt) (le_of_eq hBq_eq)
    have htrace_smul :
        ((M * B).trace).re = scale * ((M * N).trace).re := by
      simp [B, Matrix.trace_smul, Complex.mul_re, scale]
    have hscale_mul_norm :
        scale * psdSchattenPNorm N hN ⟨q, hpq.symm.pos⟩ = 1 := by
      change S ^ (-(1 / q)) * S ^ (1 / q) = 1
      calc
        S ^ (-(1 / q)) * S ^ (1 / q) = S ^ (-(1 / q) + 1 / q) := by
          rw [← Real.rpow_add hSpos]
        _ = S ^ (0 : ℝ) := by
          congr 1
          ring
        _ = 1 := Real.rpow_zero S
    have hnorm_scale :
        psdSchattenPNorm N hN ⟨q, hpq.symm.pos⟩ * scale = 1 := by
      rw [mul_comm, hscale_mul_norm]
    have hholder_scaled :
        scale * ((M * N).trace).re ≤ psdSchattenPNorm M hM ⟨p, hpq.pos⟩ := by
      simpa [htrace_smul] using hholder
    calc
      ((M * N).trace).re =
          (psdSchattenPNorm N hN ⟨q, hpq.symm.pos⟩ * scale) *
            ((M * N).trace).re := by
            rw [hnorm_scale, one_mul]
      _ = psdSchattenPNorm N hN ⟨q, hpq.symm.pos⟩ *
          (scale * ((M * N).trace).re) := by
            ring
      _ ≤ psdSchattenPNorm N hN ⟨q, hpq.symm.pos⟩ *
          psdSchattenPNorm M hM ⟨p, hpq.pos⟩ :=
            mul_le_mul_of_nonneg_left hholder_scaled
              (psdSchattenPNorm_nonneg N hN ⟨q, hpq.symm.pos⟩)
      _ = psdSchattenPNorm M hM ⟨p, hpq.pos⟩ *
          psdSchattenPNorm N hN ⟨q, hpq.symm.pos⟩ := by
            ring

/-- Dual `q`-unit-ball criterion for PSD Schatten expressions.

If a positive matrix pairs against every PSD test matrix no larger than that
test matrix's `p`-Schatten expression, then its `q`-power trace is at most one.
The proof tests the bound on `B^(q-1)`, so this is the reverse direction needed
to turn trace-pairing estimates into the rotated-adjoint `q`-ball contraction
in the sandwiched Renyi DPI route. -/
theorem psdTracePower_le_one_of_trace_mul_le_psdSchattenPNorm
    {B : CMatrix a} (hB : B.PosSemidef) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (hbound : ∀ M : CMatrix a, ∀ hM : M.PosSemidef,
      ((M * B).trace).re ≤ psdSchattenPNorm M hM ⟨p, hpq.pos⟩) :
    psdTracePower B hB q ≤ 1 := by
  classical
  let S : ℝ := psdTracePower B hB q
  let M : CMatrix a := CFC.rpow B (q - 1)
  have hM : M.PosSemidef := by
    simpa [M] using cMatrix_rpow_posSemidef (A := B) (s := q - 1) hB
  have hp_pos : 0 < p := hpq.pos
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hq_pos : 0 < q := hpq.symm.pos
  have hq_sub_pos : 0 < q - 1 := hpq.symm.sub_one_pos
  have hq_sub_nonneg : 0 ≤ q - 1 := le_of_lt hq_sub_pos
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using psdTracePower_nonneg B hB q
  have htrace_eq : ((M * B).trace).re = S := by
    let U : Matrix.unitaryGroup a ℂ := hB.isHermitian.eigenvectorUnitary
    let d : a → ℝ := fun i => hB.isHermitian.eigenvalues i
    have hMdiag :
        M =
          (U : CMatrix a) *
            Matrix.diagonal (fun i => ((d i ^ (q - 1) : ℝ) : ℂ)) *
              star (U : CMatrix a) := by
      simpa [M, U, d] using cMatrix_rpow_eq_eigenbasis_diagonal hB (q - 1)
    have hBdiag :
        B =
          (U : CMatrix a) *
            Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) *
              star (U : CMatrix a) := by
      simpa [U, d, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
        using hB.isHermitian.spectral_theorem
    have hterm : ∀ i, d i ^ (q - 1) * d i = d i ^ q := by
      intro i
      have hd_nonneg : 0 ≤ d i := hB.eigenvalues_nonneg i
      by_cases hzero : d i = 0
      · simp [hzero, Real.zero_rpow (ne_of_gt hq_sub_pos),
          Real.zero_rpow (ne_of_gt hq_pos)]
      · have hd_pos : 0 < d i := lt_of_le_of_ne hd_nonneg (Ne.symm hzero)
        calc
          d i ^ (q - 1) * d i =
              d i ^ (q - 1) * d i ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = d i ^ ((q - 1) + 1) := by
                rw [← Real.rpow_add hd_pos]
          _ = d i ^ q := by ring_nf
    calc
      ((M * B).trace).re =
          ((((U : CMatrix a) *
                Matrix.diagonal (fun i => ((d i ^ (q - 1) : ℝ) : ℂ)) *
                  star (U : CMatrix a)) *
              ((U : CMatrix a) *
                Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) *
                  star (U : CMatrix a))).trace).re := by
            rw [hMdiag, hBdiag]
      _ = ∑ i, d i ^ (q - 1) * d i := by
            simpa using
              trace_mul_unitary_conj_diagonal_ofReal_re
                U (fun i => d i ^ (q - 1)) d
      _ = ∑ i, d i ^ q := by
            exact Finset.sum_congr rfl fun i _ => hterm i
      _ = S := by
            simpa [S, d] using (psdTracePower_eq_sum_eigenvalues_rpow B hB q).symm
  have hM_power : psdTracePower M hM p = S := by
    have hmul : (q - 1) * p = q := hpq.symm.sub_one_mul_conj
    have hpow : CFC.rpow M p = CFC.rpow B q := by
      simpa [M] using
        cMatrix_rpow_rpow_of_nonneg hB hq_sub_nonneg hp_nonneg hmul
    calc
      psdTracePower M hM p = (CFC.rpow M p).trace.re := rfl
      _ = (CFC.rpow B q).trace.re := by rw [hpow]
      _ = S := rfl
  have hS_le_norm : S ≤ psdSchattenPNorm M hM ⟨p, hp_pos⟩ := by
    simpa [htrace_eq] using hbound M hM
  have hM_trace_re : (CFC.rpow M p).trace.re = S := by
    change psdTracePower M hM p = S
    exact hM_power
  have hM_pow_trace_re : (trace (M ^ p)).re = S := by
    simpa using hM_trace_re
  have hS_le_rpow : S ≤ S ^ p⁻¹ := by
    simpa [psdSchattenPNorm, Internal.psdSchattenExpression,
      hM_pow_trace_re, one_div] using hS_le_norm
  by_contra hnot
  have hS_gt_one : 1 < S := lt_of_not_ge hnot
  have hS_pow_le : S ^ p ≤ S := by
    have hle := (Real.le_rpow_inv_iff_of_pos hS_nonneg hS_nonneg hp_pos).mp
      hS_le_rpow
    simpa using hle
  have hS_lt_pow : S < S ^ p :=
    Real.self_lt_rpow_of_one_lt hS_gt_one hpq.lt
  linarith

/-- Dual PSD Schatten `q`-unit-ball criterion as an equivalence.

This packages the Holder upper bound and the extremal reverse test into the
exact form used by the sandwiched Renyi DPI route: a positive witness has
normalized `q`-power trace iff it pairs against every positive test operator no
larger than that operator's PSD `p`-Schatten expression. -/
theorem psdTracePower_le_one_iff_trace_mul_le_psdSchattenPNorm
    {B : CMatrix a} (hB : B.PosSemidef) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    psdTracePower B hB q ≤ 1 ↔
      ∀ M : CMatrix a, ∀ hM : M.PosSemidef,
        ((M * B).trace).re ≤ psdSchattenPNorm M hM ⟨p, hpq.pos⟩ := by
  constructor
  · intro hBq M hM
    exact
      posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
        hM hB hpq (le_of_lt hpq.symm.lt) hBq
  · intro hbound
    exact psdTracePower_le_one_of_trace_mul_le_psdSchattenPNorm hB hpq hbound

/-- Source-shaped PSD trace Holder upper bound for the positive-power side of
the variational formula.  The exponent is written as `r = 1 / q`, where `p` and
`q` are Holder conjugates; equivalently `r = 1 - 1 / p`. -/
theorem psd_trace_rpow_holder_variational_upper
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hNtr : N.trace.re = 1)
    {p q r : ℝ} (hpq : p.HolderConjugate q) (hr : r = 1 / q) :
    ((M * CFC.rpow N r).trace).re ≤ psdSchattenPNorm M hM ⟨p, hpq.pos⟩ := by
  let B : CMatrix a := CFC.rpow N r
  have hB : B.PosSemidef := cMatrix_rpow_posSemidef (A := N) (s := r) hN
  have hr_nonneg : 0 ≤ r := by
    rw [hr]
    exact hpq.symm.one_div_nonneg
  have hq_nonneg : 0 ≤ q := le_of_lt hpq.symm.pos
  have hrq : r * q = 1 := by
    rw [hr]
    exact one_div_mul_cancel hpq.symm.ne_zero
  have hpow : CFC.rpow B q = N := by
    dsimp [B]
    change (N ^ r) ^ q = N
    rw [CFC.rpow_rpow_of_exponent_nonneg N r q hr_nonneg hq_nonneg
      (Matrix.nonneg_iff_posSemidef.mpr hN)]
    rw [hrq]
    simp [CFC.rpow_one N (ha := Matrix.nonneg_iff_posSemidef.mpr hN)]
  have hBq_eq : psdTracePower B hB q = 1 := by
    rw [psdTracePower, hpow, hNtr]
  have hBq : psdTracePower B hB q ≤ 1 := le_of_eq hBq_eq
  simpa [B] using
    posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
      (M := M) (B := B) hM hB hpq (le_of_lt hpq.symm.lt) hBq

/-- Source-shaped PSD trace reverse-Holder lower bound for the
`0 < p < 1` side of Tomamichel's Schatten variational formula.  The
support hypothesis is the finite-dimensional kernel-inclusion form of
`M << N`, and `r = 1 - 1 / p` is negative in this range. -/
theorem psd_trace_rpow_reverse_holder_variational
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hNtr : N.trace.re = 1)
    (hSupport : Matrix.Supports M N)
    {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hr : r = 1 - 1 / p) :
    psdSchattenPNorm M hM ⟨p, hp0⟩ ≤ ((M * CFC.rpow N r).trace).re := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hN.isHermitian.eigenvectorUnitary
  let M' : CMatrix a := star (U : CMatrix a) * M * (U : CMatrix a)
  let x : a → ℝ := fun i => (M' i i).re
  let w : a → ℝ := fun i => hN.isHermitian.eigenvalues i
  have hM' : M'.PosSemidef := by
    simpa [M'] using posSemidef_unitary_conj hM U
  have hx : ∀ i, 0 ≤ x i := by
    intro i
    exact posSemidef_diagonal_re_nonneg hM' i
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    exact hN.eigenvalues_nonneg i
  have hwsum : ∑ i, w i = 1 := by
    have htrace := congrArg Complex.re hN.isHermitian.trace_eq_sum_eigenvalues
    simpa [w, hNtr] using htrace.symm
  have hsupp : ∀ i, w i = 0 → x i = 0 := by
    intro i hi
    simpa [x, w, M', U] using
      supports_conjugate_diagonal_re_eq_zero (M := M) (N := N) hN hSupport
        (i := i) hi
  have hscalar :
      (∑ i, x i ^ p) ^ (1 / p) ≤
        ∑ i, x i * w i ^ (1 - 1 / p) :=
    real_sum_rpow_one_div_le_reverse_holder hp0 hp1 hx hw hwsum hsupp
  have htrace :
      ((M * CFC.rpow N r).trace).re =
        ∑ i, x i * w i ^ r := by
    simpa [x, w, M', U] using
      trace_mul_cMatrix_rpow_eq_conjugate_diag_sum (N := N) M hN r
  have hscalar_r :
      (∑ i, x i ^ p) ^ (1 / p) ≤
        ∑ i, x i * w i ^ r := by
    simpa [hr, x, w] using hscalar
  have htracePower_conj :
      psdTracePower M' hM' p = psdTracePower M hM p := by
    simpa [M'] using psdTracePower_unitary_conj U hM (p := p) (le_of_lt hp0)
  have hdiag_bound : psdTracePower M' hM' p ≤ ∑ i, x i ^ p := by
    simpa [x] using
      psdTracePower_le_posSemidef_sum_diagonal_re_rpow hM'
        (p := p) (le_of_lt hp0) (le_of_lt hp1)
  have hnorm_bound :
      psdSchattenPNorm M hM ⟨p, hp0⟩ ≤ (∑ i, x i ^ p) ^ (1 / p) := by
    rw [psdSchattenPNorm, Internal.psdSchattenExpression]
    rw [← htracePower_conj]
    exact Real.rpow_le_rpow
      (psdTracePower_nonneg M' hM' p) hdiag_bound (one_div_nonneg.mpr (le_of_lt hp0))
  calc
    psdSchattenPNorm M hM ⟨p, hp0⟩ ≤ (∑ i, x i ^ p) ^ (1 / p) := hnorm_bound
    _ ≤ ∑ i, x i * w i ^ r := hscalar_r
    _ = ((M * CFC.rpow N r).trace).re := htrace.symm

/-- Source-shaped reverse-Holder side-state specialization.

This packages Tomamichel `metric.tex`, Lemma `lm:hoelder`, equation
`eq:hoelder2`, in the normalized side-state form used to derive the
finite-resource Schatten variational formula.  The source's raw
`Tr(MN)` reverse Holder inequality is applied downstream with
`N = σ^(1 - 1 / p)` and `Tr σ = 1`; this wrapper exposes exactly that
finite-dimensional PSD specialization.
-/
theorem psdTraceRpow_reverseHolder_source
    {M sigma : CMatrix a} (hM : M.PosSemidef) (hsigma : sigma.PosSemidef)
    (hsigma_tr : sigma.trace.re = 1)
    (hSupport : Matrix.Supports M sigma)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    psdSchattenPNorm M hM ⟨p, hp0⟩ ≤
      ((M * CFC.rpow sigma (1 - 1 / p)).trace).re :=
  psd_trace_rpow_reverse_holder_variational
    hM hsigma hsigma_tr hSupport hp0 hp1 rfl

/-- A fixed computational-basis density state, used only to witness
nonemptiness of normalized side-state optimizations in the zero-operator
boundary case. -/
private def basisDensityState [Nonempty a] : State a where
  matrix :=
    Matrix.diagonal fun i =>
      if i = Classical.choice (inferInstance : Nonempty a) then (1 : ℂ) else 0
  pos := by
    exact Matrix.PosSemidef.diagonal (by
      intro i
      by_cases h : i = Classical.choice (inferInstance : Nonempty a)
      · simp [h]
      · simp [h])
  trace_eq_one := by
    rw [Matrix.trace]
    simp

/-- Positive-Holder normalized side-state objective values from
Tomamichel2015FiniteResources, `metric.tex:131-137`, Lemma `lm:hoelder-var`:
`N ∈ cSnorm(A)` is represented by `State a`. -/
def psdTraceHolderStateValueSet (M : CMatrix a) (p : ℝ) : Set ℝ :=
  {x | ∃ σ : State a,
    x = ((M * CFC.rpow σ.matrix (1 - 1 / p)).trace).re}

/-- Reverse-Holder normalized side-state objective values with the source
support condition `M << N`. -/
def psdTraceReverseHolderNormalizedStateValueSet (M : CMatrix a) (p : ℝ) :
    Set ℝ :=
  {x | ∃ σ : State a, Matrix.Supports M σ.matrix ∧
    x = ((M * CFC.rpow σ.matrix (1 - 1 / p)).trace).re}

private theorem state_trace_re_eq_one (σ : State a) :
    σ.matrix.trace.re = 1 := by
  simpa using congrArg Complex.re σ.trace_eq_one

private theorem trace_mul_state_rpow_zero_eq_trace
    (M : CMatrix a) (σ : State a) :
    ((M * CFC.rpow σ.matrix (0 : ℝ)).trace).re = M.trace.re := by
  have hpow : CFC.rpow σ.matrix (0 : ℝ) = 1 :=
    CFC.rpow_zero σ.matrix (ha := Matrix.nonneg_iff_posSemidef.mpr σ.pos)
  rw [hpow, Matrix.mul_one]

/-- Reverse-Holder witness handoff for `0 < p < 1`.

To upper-bound a PSD Schatten expression in the subunit range, it is enough to
find one normalized supporting side-state whose reverse-Holder trace objective
is bounded by the desired scalar. This is the finite-dimensional variational
step used by the `1 / 2 ≤ α < 1` sandwiched-Renyi DPI route. -/
theorem psdSchattenPNorm_le_of_reverseHolder_trace_le
    {M N : CMatrix a} (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hNtr : N.trace.re = 1)
    (hSupport : Matrix.Supports M N)
    {p C : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (htrace_le : ((M * CFC.rpow N (1 - 1 / p)).trace).re ≤ C) :
    psdSchattenPNorm M hM ⟨p, hp0⟩ ≤ C :=
  (psd_trace_rpow_reverse_holder_variational
    hM hN hNtr hSupport hp0 hp1 rfl).trans htrace_le

/-- Reverse-Holder normalized PSD side-state objective values for a fixed
PSD matrix and exponent parameter. -/
def psdTraceReverseHolderStateValueSet (M : CMatrix a) (p : ℝ) : Set ℝ :=
  {x | ∃ N : CMatrix a, ∃ _hN : N.PosSemidef,
    N.trace.re = 1 ∧ Matrix.Supports M N ∧
      x = ((M * CFC.rpow N (1 - 1 / p)).trace).re}

/-- Every normalized PSD side-state value in the reverse-Holder optimization
is bounded below by the PSD Schatten `p` expression. -/
theorem psdTraceReverseHolderStateValueSet_lowerBound
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    psdSchattenPNorm M hM ⟨p, hp0⟩ ∈
      lowerBounds (psdTraceReverseHolderStateValueSet M p) := by
  intro x hx
  rcases hx with ⟨N, hN, hNtr, hSupport, rfl⟩
  exact psd_trace_rpow_reverse_holder_variational
    (M := M) (N := N) hM hN hNtr hSupport hp0 hp1 rfl

/-- Infimum lower-bound form of the reverse-Holder variational inequality. -/
theorem psdTraceReverseHolderStateValueSet_le_sInf
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hne : (psdTraceReverseHolderStateValueSet M p).Nonempty) :
    psdSchattenPNorm M hM ⟨p, hp0⟩ ≤
      sInf (psdTraceReverseHolderStateValueSet M p) :=
  le_csInf hne (psdTraceReverseHolderStateValueSet_lowerBound hM hp0 hp1)

/-- A side-state value attaining the Schatten expression is a genuine
minimizer of the reverse-Holder normalized PSD optimization.  This separates
the reusable support/negative-power lower bound from the later construction of
an optimizer in the full conditional-Renyi route. -/
theorem psdTraceReverseHolderStateValueSet_isLeast_of_mem
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hmem : psdSchattenPNorm M hM ⟨p, hp0⟩ ∈
      psdTraceReverseHolderStateValueSet M p) :
    IsLeast (psdTraceReverseHolderStateValueSet M p)
      (psdSchattenPNorm M hM ⟨p, hp0⟩) :=
  ⟨hmem, psdTraceReverseHolderStateValueSet_lowerBound hM hp0 hp1⟩

/-- The normalized PSD optimizer for the reverse-Holder side when
`Tr M^p > 0`, written in an eigenbasis of `M`. -/
def psdTraceReverseHolderOptimizer
    (M : CMatrix a) (hM : M.PosSemidef) (p : ℝ) : CMatrix a :=
  let U : Matrix.unitaryGroup a ℂ := hM.isHermitian.eigenvectorUnitary
  let S : ℝ := psdTracePower M hM p
  (U : CMatrix a) *
    Matrix.diagonal
      (fun i => (((hM.isHermitian.eigenvalues i ^ p) / S : ℝ) : ℂ)) *
    star (U : CMatrix a)

/-- The explicit reverse-Holder optimizer is a normalized supporting PSD
side-state and attains the Schatten expression whenever `Tr M^p` is strictly
positive. -/
theorem psdTraceReverseHolderOptimizer_props
    {M : CMatrix a} (hM : M.PosSemidef)
    {p : ℝ} (hp0 : 0 < p)
    (hSpos : 0 < psdTracePower M hM p) :
    ∃ _hN : (psdTraceReverseHolderOptimizer M hM p).PosSemidef,
      (psdTraceReverseHolderOptimizer M hM p).trace.re = 1 ∧
        Matrix.Supports M (psdTraceReverseHolderOptimizer M hM p) ∧
          psdSchattenPNorm M hM ⟨p, hp0⟩ =
            ((M * CFC.rpow (psdTraceReverseHolderOptimizer M hM p)
                (1 - 1 / p)).trace).re := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hM.isHermitian.eigenvectorUnitary
  let d : a → ℝ := fun i => hM.isHermitian.eigenvalues i
  let S : ℝ := psdTracePower M hM p
  let n : a → ℝ := fun i => d i ^ p / S
  let N : CMatrix a := (U : CMatrix a) *
    Matrix.diagonal (fun i => ((n i : ℝ) : ℂ)) * star (U : CMatrix a)
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    exact hM.eigenvalues_nonneg i
  have hSsum : S = ∑ i, d i ^ p := by
    simpa [S, d] using psdTracePower_eq_sum_eigenvalues_rpow M hM p
  have hSposS : 0 < S := by
    simpa [S] using hSpos
  have hSpos_sum : 0 < ∑ i, d i ^ p := by
    simpa [hSsum] using hSposS
  have hn_nonneg : ∀ i, 0 ≤ n i := by
    intro i
    exact div_nonneg (Real.rpow_nonneg (hd i) p) (le_of_lt hSpos)
  have hN : N.PosSemidef := by
    have hdiag : (Matrix.diagonal fun i => ((n i : ℝ) : ℂ) : CMatrix a).PosSemidef :=
      Matrix.PosSemidef.diagonal (d := fun i => ((n i : ℝ) : ℂ)) (by
        intro i
        change (0 : ℂ) ≤ ((n i : ℝ) : ℂ)
        exact_mod_cast hn_nonneg i)
    simpa [N] using hdiag.mul_mul_conjTranspose_same (U : CMatrix a)
  have hNtr : N.trace.re = 1 := by
    calc
      N.trace.re = ∑ i, n i := by
        simpa [N] using trace_unitary_conj_diagonal_ofReal_re U n
      _ = (∑ i, d i ^ p) / S := by
        simp [n, Finset.sum_div]
      _ = 1 := by
        rw [← hSsum]
        exact div_self (ne_of_gt hSpos)
  have hMdiag :
      M = (U : CMatrix a) * (Matrix.diagonal fun i => ((d i : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
    simpa [U, d, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hM.isHermitian.spectral_theorem
  have hSupport : Matrix.Supports M N := by
    have hdiagSupport :
        Matrix.Supports
          (Matrix.diagonal fun i => ((d i : ℝ) : ℂ) : CMatrix a)
          (Matrix.diagonal fun i => ((n i : ℝ) : ℂ) : CMatrix a) := by
      apply Matrix.Supports.diagonal_of_real_zero_imp_zero
      intro i hi
      have hnum : d i ^ p = 0 := by
        have hS_ne : S ≠ 0 := ne_of_gt hSpos
        exact (div_eq_zero_iff.mp hi).resolve_right hS_ne
      exact (Real.rpow_eq_zero (hd i) (ne_of_gt hp0)).mp hnum
    have hconj := Matrix.Supports.unitary_conj hdiagSupport U
    simpa [N, hMdiag] using hconj
  let r : ℝ := 1 - 1 / p
  have hNpow :
      CFC.rpow N r =
        (U : CMatrix a) *
          Matrix.diagonal (fun i => ((n i ^ r : ℝ) : ℂ)) *
          star (U : CMatrix a) := by
    simpa [N] using cMatrix_rpow_unitary_conj_diagonal_ofReal U n hn_nonneg r
  have htrace :
      ((M * CFC.rpow N r).trace).re = ∑ i, d i * n i ^ r := by
    rw [hMdiag, hNpow]
    simpa using trace_mul_unitary_conj_diagonal_ofReal_re U d (fun i => n i ^ r)
  have hscalar :
      ∑ i, d i * n i ^ r = (∑ i, d i ^ p) ^ (1 / p) := by
    have hn_eq : ∀ i, n i = d i ^ p / (∑ j, d j ^ p) := by
      intro i
      simp [n, hSsum]
    calc
      ∑ i, d i * n i ^ r =
          ∑ i, d i * (d i ^ p / (∑ j, d j ^ p)) ^ r := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hn_eq i]
      _ = (∑ i, d i ^ p) ^ (1 / p) := by
            simpa [r] using
              real_sum_reverse_holder_optimizer_value (ι := a) (x := d) hp0 hd hSpos_sum
  have hnorm :
      psdSchattenPNorm M hM ⟨p, hp0⟩ = (∑ i, d i ^ p) ^ (1 / p) := by
    rw [psdSchattenPNorm, Internal.psdSchattenExpression,
      psdTracePower_eq_sum_eigenvalues_rpow]
    simp [d]
  have hattain :
      psdSchattenPNorm M hM ⟨p, hp0⟩ =
        ((M * CFC.rpow N (1 - 1 / p)).trace).re := by
    calc
      psdSchattenPNorm M hM ⟨p, hp0⟩ = (∑ i, d i ^ p) ^ (1 / p) := hnorm
      _ = ∑ i, d i * n i ^ r := hscalar.symm
      _ = ((M * CFC.rpow N (1 - 1 / p)).trace).re := by
        simpa [r] using htrace.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [psdTraceReverseHolderOptimizer, U, d, S, n, N] using hN
  · simpa [psdTraceReverseHolderOptimizer, U, d, S, n, N] using hNtr
  · simpa [psdTraceReverseHolderOptimizer, U, d, S, n, N] using hSupport
  · simpa [psdTraceReverseHolderOptimizer, U, d, S, n, N] using hattain

private theorem psdTraceHolderStateValueSet_norm_mem [Nonempty a]
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ} (hp0 : 0 < p) :
    psdSchattenPNorm M hM ⟨p, hp0⟩ ∈ psdTraceHolderStateValueSet M p := by
  by_cases hMzero : M = 0
  · subst M
    refine ⟨basisDensityState (a := a), ?_⟩
    rw [psdSchattenPNorm_zero ⟨p, hp0⟩]
    simp
  · have hSpos : 0 < psdTracePower M hM p :=
      psdTracePower_pos_of_ne_zero M hM hMzero
    rcases psdTraceReverseHolderOptimizer_props hM hp0 hSpos with
      ⟨hN, hNtr, _hSupport, hattain⟩
    let σ : State a :=
      { matrix := psdTraceReverseHolderOptimizer M hM p
        pos := hN
        trace_eq_one := by
          apply Complex.ext
          · simpa using hNtr
          · exact (Matrix.PosSemidef.trace_nonneg hN).2.symm }
    refine ⟨σ, ?_⟩
    simpa [σ] using hattain

private theorem psdTraceReverseHolderNormalizedStateValueSet_norm_mem [Nonempty a]
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ} (hp0 : 0 < p) :
    psdSchattenPNorm M hM ⟨p, hp0⟩ ∈
      psdTraceReverseHolderNormalizedStateValueSet M p := by
  by_cases hMzero : M = 0
  · subst M
    refine ⟨basisDensityState (a := a), Matrix.Supports.zero_left _, ?_⟩
    rw [psdSchattenPNorm_zero ⟨p, hp0⟩]
    simp
  · have hSpos : 0 < psdTracePower M hM p :=
      psdTracePower_pos_of_ne_zero M hM hMzero
    rcases psdTraceReverseHolderOptimizer_props hM hp0 hSpos with
      ⟨hN, hNtr, hSupport, hattain⟩
    let σ : State a :=
      { matrix := psdTraceReverseHolderOptimizer M hM p
        pos := hN
        trace_eq_one := by
          apply Complex.ext
          · simpa using hNtr
          · exact (Matrix.PosSemidef.trace_nonneg hN).2.symm }
    refine ⟨σ, ?_, ?_⟩
    · simpa [σ] using hSupport
    · simpa [σ] using hattain

/-- Source-shaped maximum branch of Tomamichel's positive-operator Schatten
variational formula, over normalized states, for `p > 1`. -/
theorem psdTraceHolderStateValueSet_isGreatest_of_one_lt [Nonempty a]
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ} (hp : 1 < p) :
    IsGreatest (psdTraceHolderStateValueSet M p)
      (psdSchattenPNorm M hM ⟨p, lt_trans zero_lt_one hp⟩) := by
  constructor
  · exact psdTraceHolderStateValueSet_norm_mem hM (lt_trans zero_lt_one hp)
  · intro x hx
    rcases hx with ⟨σ, rfl⟩
    let q : ℝ := Real.conjExponent p
    have hpq : p.HolderConjugate q := by
      simpa [q] using Real.HolderConjugate.conjExponent hp
    have hr : 1 - 1 / p = 1 / q := by
      simpa [q, one_div] using hpq.one_sub_inv
    exact psd_trace_rpow_holder_variational_upper
      hM σ.pos (state_trace_re_eq_one σ) hpq hr

/-- Boundary `p = 1` case of Tomamichel's maximum branch. -/
theorem psdTraceHolderStateValueSet_isGreatest_one [Nonempty a]
    {M : CMatrix a} (hM : M.PosSemidef) :
    IsGreatest (psdTraceHolderStateValueSet M (1 : ℝ))
      (psdSchattenPNorm M hM SchattenOrder.one) := by
  constructor
  · refine ⟨basisDensityState (a := a), ?_⟩
    rw [show 1 - 1 / (1 : ℝ) = 0 by norm_num]
    rw [trace_mul_state_rpow_zero_eq_trace M (basisDensityState (a := a))]
    exact psdSchattenPNorm_one M hM
  · intro x hx
    rcases hx with ⟨σ, rfl⟩
    rw [show 1 - 1 / (1 : ℝ) = 0 by norm_num]
    rw [trace_mul_state_rpow_zero_eq_trace M σ]
    exact le_of_eq (psdSchattenPNorm_one M hM).symm

/-- Source-shaped maximum branch of Tomamichel's positive-operator Schatten
variational formula, over normalized states, for `p ≥ 1`. -/
theorem psdTraceHolderStateValueSet_isGreatest [Nonempty a]
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ} (hp : 1 ≤ p) :
    IsGreatest (psdTraceHolderStateValueSet M p)
      (psdSchattenPNorm M hM ⟨p, lt_of_lt_of_le zero_lt_one hp⟩) := by
  rcases lt_or_eq_of_le hp with hp_lt | rfl
  · exact psdTraceHolderStateValueSet_isGreatest_of_one_lt hM hp_lt
  · exact psdTraceHolderStateValueSet_isGreatest_one hM

/-- Supremum form of the `p ≥ 1` normalized-state Schatten variational
formula. -/
theorem psdTraceHolderStateValueSet_sSup_eq [Nonempty a]
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ} (hp : 1 ≤ p) :
    sSup (psdTraceHolderStateValueSet M p) =
      psdSchattenPNorm M hM ⟨p, lt_of_lt_of_le zero_lt_one hp⟩ :=
  (psdTraceHolderStateValueSet_isGreatest hM hp).csSup_eq

/-- Boundary `p = 1` case of Tomamichel's reverse-Holder minimum branch. -/
theorem psdTraceReverseHolderNormalizedStateValueSet_isLeast_one [Nonempty a]
    {M : CMatrix a} (hM : M.PosSemidef) :
    IsLeast (psdTraceReverseHolderNormalizedStateValueSet M (1 : ℝ))
      (psdSchattenPNorm M hM SchattenOrder.one) := by
  constructor
  · exact psdTraceReverseHolderNormalizedStateValueSet_norm_mem hM zero_lt_one
  · intro x hx
    rcases hx with ⟨σ, _hSupport, rfl⟩
    rw [show 1 - 1 / (1 : ℝ) = 0 by norm_num]
    rw [trace_mul_state_rpow_zero_eq_trace M σ]
    exact le_of_eq (psdSchattenPNorm_one M hM)

/-- Strict subunit branch of Tomamichel's reverse-Holder normalized-state
variational formula. -/
theorem psdTraceReverseHolderNormalizedStateValueSet_isLeast_of_lt_one [Nonempty a]
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    IsLeast (psdTraceReverseHolderNormalizedStateValueSet M p)
      (psdSchattenPNorm M hM ⟨p, hp0⟩) := by
  constructor
  · exact psdTraceReverseHolderNormalizedStateValueSet_norm_mem hM hp0
  · intro x hx
    rcases hx with ⟨σ, hSupport, rfl⟩
    exact psdTraceRpow_reverseHolder_source
      hM σ.pos (state_trace_re_eq_one σ) hSupport hp0 hp1

/-- Source-shaped minimum branch of Tomamichel's positive-operator Schatten
variational formula, over normalized supporting states, for `0 < p ≤ 1`. -/
theorem psdTraceReverseHolderNormalizedStateValueSet_isLeast [Nonempty a]
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    IsLeast (psdTraceReverseHolderNormalizedStateValueSet M p)
      (psdSchattenPNorm M hM ⟨p, hp0⟩) := by
  rcases lt_or_eq_of_le hp1 with hp_lt | rfl
  · exact psdTraceReverseHolderNormalizedStateValueSet_isLeast_of_lt_one hM hp0 hp_lt
  · exact psdTraceReverseHolderNormalizedStateValueSet_isLeast_one hM

/-- Infimum form of the `0 < p ≤ 1` normalized-state reverse-Holder
variational formula. -/
theorem psdTraceReverseHolderNormalizedStateValueSet_sInf_eq [Nonempty a]
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    sInf (psdTraceReverseHolderNormalizedStateValueSet M p) =
      psdSchattenPNorm M hM ⟨p, hp0⟩ :=
  (psdTraceReverseHolderNormalizedStateValueSet_isLeast hM hp0 hp1).csInf_eq

/-- The explicit reverse-Holder optimizer is the normalized positive power
`M^p / Tr(M^p)`.

The definition above is spectral, because that form is convenient for the
reverse-Holder proof.  This theorem exposes the source-shaped power-state form
needed by the low-`α` sandwiched Renyi DPI route. -/
theorem psdTraceReverseHolderOptimizer_eq_inv_tracePower_smul_rpow
    {M : CMatrix a} (hM : M.PosSemidef)
    {p : ℝ} :
    psdTraceReverseHolderOptimizer M hM p =
      (((psdTracePower M hM p)⁻¹ : ℝ) : ℂ) • CFC.rpow M p := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hM.isHermitian.eigenvectorUnitary
  let d : a → ℝ := fun i => hM.isHermitian.eigenvalues i
  let S : ℝ := psdTracePower M hM p
  let D : CMatrix a :=
    Matrix.diagonal (fun i => ((d i ^ p : ℝ) : ℂ))
  have hpow :
      CFC.rpow M p = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, d, D] using cMatrix_rpow_eq_eigenbasis_diagonal hM p
  have hdiag :
      (Matrix.diagonal (fun i => (((d i ^ p) / S : ℝ) : ℂ)) : CMatrix a) =
        (((S⁻¹ : ℝ) : ℂ) • D) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Matrix.smul_apply, div_eq_mul_inv, mul_comm]
    · simp [D, Matrix.smul_apply, Matrix.diagonal, hij]
  have hsmul :
      (U : CMatrix a) * ((((S⁻¹ : ℝ) : ℂ) • D)) *
          star (U : CMatrix a) =
        (((S⁻¹ : ℝ) : ℂ) • ((U : CMatrix a) * D * star (U : CMatrix a))) := by
    calc
      (U : CMatrix a) * ((((S⁻¹ : ℝ) : ℂ) • D)) *
          star (U : CMatrix a) =
          (((S⁻¹ : ℝ) : ℂ) • ((U : CMatrix a) * D)) *
            star (U : CMatrix a) := by
            rw [Matrix.mul_smul]
      _ = (((S⁻¹ : ℝ) : ℂ) • (((U : CMatrix a) * D) *
            star (U : CMatrix a))) := by
            rw [Matrix.smul_mul]
      _ = (((S⁻¹ : ℝ) : ℂ) • ((U : CMatrix a) * D *
            star (U : CMatrix a))) := rfl
  calc
    psdTraceReverseHolderOptimizer M hM p =
        (U : CMatrix a) *
          (Matrix.diagonal (fun i => (((d i ^ p) / S : ℝ) : ℂ)) : CMatrix a) *
          star (U : CMatrix a) := by
          simp [psdTraceReverseHolderOptimizer, U, d, S]
    _ = (U : CMatrix a) * ((((S⁻¹ : ℝ) : ℂ) • D)) *
          star (U : CMatrix a) := by
          rw [hdiag]
    _ = (((S⁻¹ : ℝ) : ℂ) • ((U : CMatrix a) * D * star (U : CMatrix a))) := by
          exact hsmul
    _ = (((psdTracePower M hM p)⁻¹ : ℝ) : ℂ) • CFC.rpow M p := by
          rw [hpow]

/-- The reverse-Holder optimizer attains the Schatten expression whenever
`Tr M^p` is strictly positive. -/
theorem psdTraceReverseHolderOptimizer_mem
    {M : CMatrix a} (hM : M.PosSemidef)
    {p : ℝ} (hp0 : 0 < p)
    (hSpos : 0 < psdTracePower M hM p) :
    psdSchattenPNorm M hM ⟨p, hp0⟩ ∈ psdTraceReverseHolderStateValueSet M p := by
  rcases psdTraceReverseHolderOptimizer_props hM hp0 hSpos with
    ⟨hN, hNtr, hSupport, hattain⟩
  exact ⟨psdTraceReverseHolderOptimizer M hM p, hN, hNtr, hSupport, hattain⟩

/-- The explicit reverse-Holder optimizer is full-rank whenever the reference
PSD matrix has strictly positive spectrum.  This is the full-rank side-state
upgrade needed before using negative powers in the low-`α` DPI route. -/
theorem psdTraceReverseHolderOptimizer_posDef
    {M : CMatrix a} (hM : M.PosSemidef)
    {p : ℝ}
    (hSpos : 0 < psdTracePower M hM p)
    (heig_pos : ∀ i, 0 < hM.isHermitian.eigenvalues i) :
    (psdTraceReverseHolderOptimizer M hM p).PosDef := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hM.isHermitian.eigenvectorUnitary
  let d : a → ℝ := fun i => hM.isHermitian.eigenvalues i
  let S : ℝ := psdTracePower M hM p
  let n : a → ℝ := fun i => d i ^ p / S
  have hSposS : 0 < S := by
    simpa [S] using hSpos
  have hn_pos : ∀ i, 0 < n i := by
    intro i
    exact div_pos (Real.rpow_pos_of_pos (by simpa [d] using heig_pos i) p) hSposS
  have hdiag :
      (Matrix.diagonal (fun i => ((n i : ℝ) : ℂ)) : CMatrix a).PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    change 0 < ((n i : ℝ) : ℂ)
    exact_mod_cast hn_pos i
  have hconj :
      ((U : CMatrix a) *
          (Matrix.diagonal (fun i => ((n i : ℝ) : ℂ)) : CMatrix a) *
          star (U : CMatrix a)).PosDef := by
    rw [Matrix.IsUnit.posDef_star_right_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix a))]
    exact hdiag
  simpa [psdTraceReverseHolderOptimizer, U, d, S, n] using hconj

/-- Full-rank input version of `psdTraceReverseHolderOptimizer_posDef`. -/
theorem psdTraceReverseHolderOptimizer_posDef_of_posDef
    {M : CMatrix a} (hM : M.PosSemidef) (hMdef : M.PosDef)
    {p : ℝ}
    (hSpos : 0 < psdTracePower M hM p) :
    (psdTraceReverseHolderOptimizer M hM p).PosDef :=
  psdTraceReverseHolderOptimizer_posDef hM hSpos (by
    intro i
    simpa using hMdef.eigenvalues_pos i)

/-- Direct side-state form of the reverse-Holder optimizer.

For a nonzero PSD power trace in the subunit range, there is a normalized PSD
side-state supporting `M` whose reverse-Holder trace objective attains the PSD
Schatten expression. -/
theorem exists_psdTraceReverseHolder_sideState_attaining
    {M : CMatrix a} (hM : M.PosSemidef)
    {p : ℝ} (hp0 : 0 < p)
    (hSpos : 0 < psdTracePower M hM p) :
    ∃ N : CMatrix a, ∃ _hN : N.PosSemidef,
      N.trace.re = 1 ∧ Matrix.Supports M N ∧
        psdSchattenPNorm M hM ⟨p, hp0⟩ =
          ((M * CFC.rpow N (1 - 1 / p)).trace).re := by
  simpa [psdTraceReverseHolderStateValueSet] using
    (psdTraceReverseHolderOptimizer_mem hM hp0 hSpos)

/-- Exact reverse-Holder variational formula as a minimum, in the nonzero
power-trace case. -/
theorem psdTraceReverseHolderStateValueSet_isLeast_of_tracePower_pos
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hSpos : 0 < psdTracePower M hM p) :
    IsLeast (psdTraceReverseHolderStateValueSet M p)
      (psdSchattenPNorm M hM ⟨p, hp0⟩) :=
  psdTraceReverseHolderStateValueSet_isLeast_of_mem hM hp0 hp1
    (psdTraceReverseHolderOptimizer_mem hM hp0 hSpos)

/-- Exact `sInf` form of the reverse-Holder variational formula in the nonzero
power-trace case. -/
theorem psdTraceReverseHolderStateValueSet_sInf_eq_of_tracePower_pos
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hSpos : 0 < psdTracePower M hM p) :
    sInf (psdTraceReverseHolderStateValueSet M p) =
      psdSchattenPNorm M hM ⟨p, hp0⟩ :=
  (psdTraceReverseHolderStateValueSet_isLeast_of_tracePower_pos
    hM hp0 hp1 hSpos).csInf_eq

/-- Exact reverse-Holder variational formula as a minimum for nonzero PSD
matrices. -/
theorem psdTraceReverseHolderStateValueSet_isLeast_of_ne_zero
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hMne : M ≠ 0) :
    IsLeast (psdTraceReverseHolderStateValueSet M p)
      (psdSchattenPNorm M hM ⟨p, hp0⟩) :=
  psdTraceReverseHolderStateValueSet_isLeast_of_tracePower_pos hM hp0 hp1
    (psdTracePower_pos_of_ne_zero M hM hMne)

/-- Exact `sInf` form of the reverse-Holder variational formula for nonzero
PSD matrices. -/
theorem psdTraceReverseHolderStateValueSet_sInf_eq_of_ne_zero
    {M : CMatrix a} (hM : M.PosSemidef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hMne : M ≠ 0) :
    sInf (psdTraceReverseHolderStateValueSet M p) =
      psdSchattenPNorm M hM ⟨p, hp0⟩ :=
  (psdTraceReverseHolderStateValueSet_isLeast_of_ne_zero
    hM hp0 hp1 hMne).csInf_eq

/-- PSD `q`-unit-ball trace values paired with a fixed PSD matrix. -/
def psdTraceHolderUnitBallValueSet (M : CMatrix a) (q : ℝ) : Set ℝ :=
  {x | ∃ B : CMatrix a, ∃ hB : B.PosSemidef,
    psdTracePower B hB q ≤ 1 ∧ x = ((M * B).trace).re}

/-- Finite-dimensional PSD trace Holder variational formula over the PSD
`q`-unit ball.  This is the matrix core behind the `p ≥ 1` side of
Tomamichel's Schatten Holder variational lemma. -/
theorem psdTraceHolderUnitBall_isGreatest
    {M : CMatrix a} (hM : M.PosSemidef) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    IsGreatest (psdTraceHolderUnitBallValueSet M q)
      (psdSchattenPNorm M hM ⟨p, hpq.pos⟩) := by
  classical
  constructor
  · let U : Matrix.unitaryGroup a ℂ := hM.isHermitian.eigenvectorUnitary
    let f : a → ℝ≥0 := fun i => ⟨hM.isHermitian.eigenvalues i, hM.eigenvalues_nonneg i⟩
    rcases (NNReal.isGreatest_Lp (s := (Finset.univ : Finset a)) f hpq).1 with
      ⟨g, hg, hval⟩
    let d : a → ℝ := fun i => (g i : ℝ)
    let D : CMatrix a := Matrix.diagonal fun i => (d i : ℂ)
    have hd : ∀ i, 0 ≤ d i := fun i => (g i).2
    have hD : D.PosSemidef := by
      dsimp [D, d]
      exact Matrix.PosSemidef.diagonal (d := fun i => ((g i : ℝ) : ℂ)) (by
        intro i
        change (0 : ℂ) ≤ ((g i : ℝ) : ℂ)
        exact_mod_cast (g i).2)
    let B : CMatrix a := (U : CMatrix a) * D * star (U : CMatrix a)
    have hB : B.PosSemidef := by
      simpa [B] using hD.mul_mul_conjTranspose_same (U : CMatrix a)
    have hUBU : star (U : CMatrix a) * B * (U : CMatrix a) = D := by
      have hUU : star (U : CMatrix a) * (U : CMatrix a) = 1 :=
        Unitary.coe_star_mul_self U
      calc
        star (U : CMatrix a) * B * (U : CMatrix a)
            = (star (U : CMatrix a) * (U : CMatrix a)) * D *
                (star (U : CMatrix a) * (U : CMatrix a)) := by
                dsimp [B]
                noncomm_ring
        _ = D := by simp [hUU]
    have hBpower_eq_Dpower :
        psdTracePower B hB q = psdTracePower D hD q := by
      rw [psdTracePower, psdTracePower]
      have htrace :
          (CFC.rpow D q).trace.re = (CFC.rpow B q).trace.re := by
        rw [← hUBU]
        rw [cMatrix_rpow_unitary_conj hB U (le_of_lt hpq.symm.pos)]
        rw [Matrix.trace_mul_cycle]
        simp
      exact htrace.symm
    have hDpower :
        psdTracePower D hD q = ∑ i, d i ^ q := by
      dsimp [D]
      simpa [d] using psdTracePower_diagonal_ofReal (a := a) d hd q
    have hgNN : ∑ i ∈ (Finset.univ : Finset a), g i ^ q ≤ 1 := by
      simpa using hg
    have hgR : (∑ i ∈ (Finset.univ : Finset a), d i ^ q) ≤ 1 := by
      have hgR0 :
          ((∑ i ∈ (Finset.univ : Finset a), g i ^ q : ℝ≥0) : ℝ) ≤ (1 : ℝ) := by
        exact_mod_cast hgNN
      simpa [d] using hgR0
    have hBq : psdTracePower B hB q ≤ 1 := by
      rw [hBpower_eq_Dpower, hDpower]
      simpa using hgR
    have htraceB :
        ((M * B).trace).re = ∑ i ∈ (Finset.univ : Finset a),
          hM.isHermitian.eigenvalues i * d i := by
      rw [posSemidef_trace_mul_eq_eigenvalue_conjugate_diag_sum
        (M := M) (B := B) hM]
      change (∑ i, hM.isHermitian.eigenvalues i *
          ((star (U : CMatrix a) * B * (U : CMatrix a)) i i).re) =
        ∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i * d i
      rw [hUBU]
      simp [D]
    have hvalR :
        (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i * d i) =
          psdSchattenPNorm M hM ⟨p, hpq.pos⟩ := by
      have hval_coe := congrArg (fun x : ℝ≥0 => (x : ℝ)) hval
      have hvalR0 :
          (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i * d i) =
            (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i ^ p) ^ (1 / p) := by
        simpa [f, d] using hval_coe
      calc
        (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i * d i)
            = (∑ i ∈ (Finset.univ : Finset a), hM.isHermitian.eigenvalues i ^ p) ^
                (1 / p) := hvalR0
        _ = psdSchattenPNorm M hM ⟨p, hpq.pos⟩ := by
            rw [psdSchattenPNorm, Internal.psdSchattenExpression,
              psdTracePower_eq_sum_eigenvalues_rpow]
            simp
    refine ⟨B, hB, hBq, ?_⟩
    rw [htraceB, hvalR]
  · intro x hx
    rcases hx with ⟨B, hB, hBq, rfl⟩
    exact posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
      (M := M) (B := B) hM hB hpq (le_of_lt hpq.symm.lt) hBq

/-- Supremum form of the PSD trace Holder variational formula. -/
theorem psdTraceHolderUnitBall_sSup_eq
    {M : CMatrix a} (hM : M.PosSemidef) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    sSup (psdTraceHolderUnitBallValueSet M q) =
      psdSchattenPNorm M hM ⟨p, hpq.pos⟩ :=
  (psdTraceHolderUnitBall_isGreatest hM hpq).csSup_eq

/-- To prove a PSD Schatten `p`-norm bound from the Holder variational formula,
it suffices to bound every normalized PSD `q`-unit-ball trace pairing.

This is the reusable variational handoff needed by the sandwiched-Renyi DPI
route: the channel-specific work can focus on transporting arbitrary positive
dual witnesses through the Heisenberg adjoint. -/
theorem psdSchattenPNorm_le_of_traceHolderUnitBall_le
    {b : Type v} [Fintype b] [DecidableEq b]
    {M : CMatrix a} {N : CMatrix b} (hM : M.PosSemidef) (hN : N.PosSemidef)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hbound : ∀ B : CMatrix a, ∀ hB : B.PosSemidef,
      psdTracePower B hB q ≤ 1 →
        ((M * B).trace).re ≤ psdSchattenPNorm N hN ⟨p, hpq.pos⟩) :
    psdSchattenPNorm M hM ⟨p, hpq.pos⟩ ≤
      psdSchattenPNorm N hN ⟨p, hpq.pos⟩ := by
  rcases (psdTraceHolderUnitBall_isGreatest hM hpq).1 with ⟨B, hB, hBq, hval⟩
  rw [hval]
  exact hbound B hB hBq

/-- The trace product of two PSD matrices is nonnegative in real part.

This local version avoids importing the later SDP trace-duality layer into the
Schatten kernel module. -/
theorem cMatrix_trace_mul_posSemidef_re_nonneg_schatten
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ ((A * B).trace).re := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hA.isHermitian.eigenvectorUnitary
  have hB' : (star (U : CMatrix a) * B * (U : CMatrix a)).PosSemidef := by
    simpa [U] using posSemidef_unitary_conj hB U
  rw [posSemidef_trace_mul_eq_eigenvalue_conjugate_diag_sum (M := A) (B := B) hA]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hA.eigenvalues_nonneg i) (posSemidef_diagonal_re_nonneg hB' i)

/-- Trace pairing with a fixed positive test matrix is monotone in the Loewner
order. -/
theorem cMatrix_trace_mul_le_of_le_posSemidef_right
    {A B C : CMatrix a} (hC : C.PosSemidef) (hAB : A ≤ B) :
    ((A * C).trace).re ≤ ((B * C).trace).re := by
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hnonneg : 0 ≤ (((B - A) * C).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg_schatten hdiff hC
  have htrace :
      (((B - A) * C).trace).re =
        ((B * C).trace).re - ((A * C).trace).re := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  linarith

/-- PSD Schatten `p`-norm expressions are monotone for positive Loewner order
when `p > 1`.

The proof uses the local Holder unit-ball variational formula: every positive
dual test matrix bounded in the conjugate Schatten gauge pairs with the smaller
operator no more than with the larger one. -/
theorem psdSchattenPNorm_mono_of_le
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {p : ℝ} (hp : 1 < p) (hAB : A ≤ B) :
    psdSchattenPNorm A hA ⟨p, lt_trans zero_lt_one hp⟩ ≤
      psdSchattenPNorm B hB ⟨p, lt_trans zero_lt_one hp⟩ := by
  let q : ℝ := Real.conjExponent p
  have hpq : p.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent hp
  refine psdSchattenPNorm_le_of_traceHolderUnitBall_le hA hB hpq ?_
  intro C hC hCq
  calc
    ((A * C).trace).re ≤ ((B * C).trace).re :=
      cMatrix_trace_mul_le_of_le_posSemidef_right hC hAB
    _ ≤ psdSchattenPNorm B hB ⟨p, lt_trans zero_lt_one hp⟩ :=
      posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
        hB hC hpq (le_of_lt hpq.symm.lt) hCq

/-- Cyclic `AB`/`BA` invariance for PSD Schatten `p`-norm expressions. -/
theorem psdSchattenPNorm_mul_comm
    {A B : CMatrix a} (hAB : (A * B).PosSemidef) (hBA : (B * A).PosSemidef)
    {p : ℝ} (hp : 0 < p) :
    psdSchattenPNorm (A * B) hAB ⟨p, hp⟩ =
      psdSchattenPNorm (B * A) hBA ⟨p, hp⟩ := by
  unfold psdSchattenPNorm Internal.psdSchattenExpression
  rw [psdTracePower_mul_comm hAB hBA hp]

/-- PSD Schatten `p`-norm expressions are convex on the positive cone for
`p > 1`.

This is the Holder-unit-ball proof of the finite-dimensional convexity used in
the Khatri--Wilde Sion step for sandwiched Rényi channel mutual information. -/
theorem psdSchattenPNorm_convex_combo_le
    {A B : CMatrix a} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {p s t : ℝ} (hp : 1 < p) (hs : 0 ≤ s) (ht : 0 ≤ t) (_hst : s + t = 1) :
    psdSchattenPNorm (s • A + t • B)
        (Matrix.PosSemidef.add
          (Matrix.PosSemidef.smul hA hs)
          (Matrix.PosSemidef.smul hB ht)) ⟨p, lt_trans zero_lt_one hp⟩ ≤
      s * psdSchattenPNorm A hA ⟨p, lt_trans zero_lt_one hp⟩ +
        t * psdSchattenPNorm B hB ⟨p, lt_trans zero_lt_one hp⟩ := by
  let q : ℝ := Real.conjExponent p
  have hpq : p.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent hp
  let hmix : (s • A + t • B).PosSemidef :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hA hs)
      (Matrix.PosSemidef.smul hB ht)
  rcases (psdTraceHolderUnitBall_isGreatest
      (M := s • A + t • B) hmix (p := p) (q := q) hpq).1 with
    ⟨C, hC, hCq, hval⟩
  rw [hval]
  have hAtrace :
      ((A * C).trace).re ≤
        psdSchattenPNorm A hA ⟨p, lt_trans zero_lt_one hp⟩ :=
    posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
      hA hC hpq (le_of_lt hpq.symm.lt) hCq
  have hBtrace :
      ((B * C).trace).re ≤
        psdSchattenPNorm B hB ⟨p, lt_trans zero_lt_one hp⟩ :=
    posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
      hB hC hpq (le_of_lt hpq.symm.lt) hCq
  have htrace :
      (((s • A + t • B) * C).trace).re =
        s * ((A * C).trace).re + t * ((B * C).trace).re := by
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul, Complex.add_re]
    simp [Complex.mul_re]
  rw [htrace]
  exact add_le_add
    (mul_le_mul_of_nonneg_left hAtrace hs)
    (mul_le_mul_of_nonneg_left hBtrace ht)

/-- A PSD power-trace inequality implies the matching PSD Schatten expression
inequality for positive exponents. -/
theorem psdSchattenPNorm_le_of_psdTracePower_le
    {b : Type v} [Fintype b] [DecidableEq b]
    {M : CMatrix a} {N : CMatrix b} (hM : M.PosSemidef) (hN : N.PosSemidef)
    {p : ℝ} (hp : 0 < p)
    (hpower : psdTracePower M hM p ≤ psdTracePower N hN p) :
    psdSchattenPNorm M hM ⟨p, hp⟩ ≤ psdSchattenPNorm N hN ⟨p, hp⟩ := by
  rw [psdSchattenPNorm, psdSchattenPNorm,
    Internal.psdSchattenExpression, Internal.psdSchattenExpression]
  exact Real.rpow_le_rpow
    (psdTracePower_nonneg M hM p) hpower
    (one_div_nonneg.mpr (le_of_lt hp))

/-- A PSD Schatten `p`-norm inequality implies the matching `p`-power trace
inequality when both power traces are strictly positive. -/
theorem psdTracePower_le_of_psdSchattenPNorm_le
    {b : Type v} [Fintype b] [DecidableEq b]
    {M : CMatrix a} {N : CMatrix b} (hM : M.PosSemidef) (hN : N.PosSemidef)
    {p : ℝ} (hp : 0 < p)
    (hMpos : 0 < psdTracePower M hM p)
    (hNpos : 0 < psdTracePower N hN p)
    (hnorm : psdSchattenPNorm M hM ⟨p, hp⟩ ≤ psdSchattenPNorm N hN ⟨p, hp⟩) :
    psdTracePower M hM p ≤ psdTracePower N hN p := by
  rw [psdSchattenPNorm, Internal.psdSchattenExpression] at hnorm
  exact (Real.rpow_le_rpow_iff (le_of_lt hMpos) (le_of_lt hNpos)
    (one_div_pos.2 hp)).mp hnorm

end

end QIT
