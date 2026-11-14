/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Nonlocality.YangNavascues.Fourier
public import QIT.States.Purification.ReferenceIsometry
public import QIT.Nonlocality.TwoQubit

/-!
# Base-aware ancilla embeddings for the Yang-Navascues local isometry

This module records the source-sensitive indexing convention needed before
assembling the Coladangelo-Goh-Scarani Yang-Navascues local isometry: the
target's distinguished Schmidt coefficient `c_0` must be sent to Fourier index
`0`.  It also provides the small zero-ancilla reference isometry used by later
local-isometry calculations.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

namespace QIT
namespace YangNavascues

universe u v w

noncomputable section

namespace SchmidtTarget

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The zero Fourier index for a target whose index type is nonempty via `target.base`. -/
def baseIndex (target : SchmidtTarget ι) : Fin (Fintype.card ι) :=
  ⟨0, Fintype.card_pos_iff.mpr ⟨target.base⟩⟩

@[simp]
theorem baseIndex_val (target : SchmidtTarget ι) :
    (target.baseIndex : ℕ) = 0 :=
  rfl

/--
A base-aware finite-index bridge for the YN Fourier construction.

This records the source indexing convention that the distinguished source index
`target.base` is sent to Fourier index `0`.
-/
structure BaseReindexToFin (target : SchmidtTarget ι) where
  /-- The chosen finite ordering used by the Fourier construction. -/
  toEquiv : ι ≃ Fin (Fintype.card ι)
  /-- The distinguished coefficient `c_0` is placed at Fourier index `0`. -/
  base_eq_zero : toEquiv target.base = target.baseIndex

namespace BaseReindexToFin

variable {target : SchmidtTarget ι}

@[simp]
theorem toEquiv_base (B : BaseReindexToFin target) :
    B.toEquiv target.base = target.baseIndex :=
  B.base_eq_zero

end BaseReindexToFin
end SchmidtTarget

/-- Fourier acting on the ancilla of `H × Fin d`, leaving the system register unchanged. -/
def ancillaFourierMatrix {H : Type u} [Fintype H] [DecidableEq H]
    (d : ℕ) [NeZero d] : CMatrix (H × Fin d) :=
  (1 : CMatrix H) ⊗ₖ fourierMatrix d

/-- Inverse Fourier acting on the ancilla of `H × Fin d`. -/
def ancillaInverseFourierMatrix {H : Type u} [Fintype H] [DecidableEq H]
    (d : ℕ) [NeZero d] : CMatrix (H × Fin d) :=
  (1 : CMatrix H) ⊗ₖ inverseFourierMatrix d

/-- The ancilla Fourier operator is an isometry. -/
theorem ancillaFourierMatrix_isometry {H : Type u} [Fintype H] [DecidableEq H]
    (d : ℕ) [NeZero d] :
    Matrix.conjTranspose (ancillaFourierMatrix (H := H) d) *
        ancillaFourierMatrix (H := H) d = 1 := by
  simp [ancillaFourierMatrix, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    fourierMatrix_isUnitary]

/-- The inverse ancilla Fourier operator is an isometry. -/
theorem ancillaInverseFourierMatrix_isometry {H : Type u} [Fintype H] [DecidableEq H]
    (d : ℕ) [NeZero d] :
    Matrix.conjTranspose (ancillaInverseFourierMatrix (H := H) d) *
        ancillaInverseFourierMatrix (H := H) d = 1 := by
  have hmem : fourierMatrix d ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    simpa [Matrix.star_eq_conjTranspose] using fourierMatrix_isUnitary d
  have hright : fourierMatrix d * Matrix.conjTranspose (fourierMatrix d) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hmem
  simp [ancillaInverseFourierMatrix, inverseFourierMatrix, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_conjTranspose, hright]

/-- Applying the ancilla Fourier unfolds to the Kronecker definition. -/
@[simp]
theorem ancillaFourierMatrix_eq {H : Type u} [Fintype H] [DecidableEq H]
    (d : ℕ) [NeZero d] :
    ancillaFourierMatrix (H := H) d = (1 : CMatrix H) ⊗ₖ fourierMatrix d :=
  rfl

/-- Applying the inverse ancilla Fourier unfolds to the Kronecker definition. -/
@[simp]
theorem ancillaInverseFourierMatrix_eq {H : Type u} [Fintype H] [DecidableEq H]
    (d : ℕ) [NeZero d] :
    ancillaInverseFourierMatrix (H := H) d = (1 : CMatrix H) ⊗ₖ inverseFourierMatrix d :=
  rfl

/-- A block-controlled family of unitaries is an isometry. -/
theorem controlledOperator_isometry {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (U : Fin d → CMatrix H)
    (hU : ∀ k, Matrix.conjTranspose (U k) * U k = 1) :
    Matrix.conjTranspose (controlledOperator U) * controlledOperator U = 1 := by
  classical
  ext x y
  rcases x with ⟨hx, kx⟩
  rcases y with ⟨hy, ky⟩
  by_cases hkk : kx = ky
  · subst ky
    have hentry := congrFun (congrFun (hU kx) hx) hy
    rw [Matrix.mul_apply]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simpa [controlledOperator, Matrix.conjTranspose, Matrix.one_apply] using hentry
  · have hkrev : ky ≠ kx := fun h => hkk h.symm
    rw [Matrix.mul_apply]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp [controlledOperator, Matrix.conjTranspose, hkk, hkrev]

/-- A block-controlled family of unitary-group matrices is an isometry. -/
theorem controlledUnitary_isometry {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (U : Fin d → Matrix.unitaryGroup H ℂ) :
    Matrix.conjTranspose (controlledUnitary U) * controlledUnitary U = 1 := by
  apply controlledOperator_isometry
  intro k
  simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self (U k)

/-- Left-multiplying an isometry by an isometry on the codomain remains an isometry. -/
theorem left_mul_isometry {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (U : CMatrix b) (A : Matrix b a ℂ)
    (hU : Matrix.conjTranspose U * U = 1)
    (hA : Matrix.conjTranspose A * A = 1) :
    Matrix.conjTranspose (U * A) * (U * A) = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc
    Matrix.conjTranspose A * Matrix.conjTranspose U * (U * A)
        = Matrix.conjTranspose A * (Matrix.conjTranspose U * U) * A := by
            simp [Matrix.mul_assoc]
    _ = Matrix.conjTranspose A * A := by simp [hU]
    _ = 1 := hA

private theorem matrix_smul_mul_smul {n : Type u} [Fintype n]
    (a b : ℂ) (A B : CMatrix n) :
    (a • A) * (b • B) = (a * b) • (A * B) := by
  ext i j
  simp [Matrix.mul_apply, Finset.mul_sum, mul_comm, mul_left_comm]

private theorem circle_star_mul_self_local (z : Circle) :
    star (z : ℂ) * (z : ℂ) = 1 := by
  have h : (Complex.normSq (z : ℂ) : ℂ) = star (z : ℂ) * (z : ℂ) :=
    Complex.normSq_eq_conj_mul_self
  rw [Circle.normSq_coe] at h
  simpa [Complex.star_def] using h.symm

private theorem fourierRoot_pow_star_mul_self (d : ℕ) [NeZero d] (n : ℕ) :
    star ((fourierRoot d) ^ n) * (fourierRoot d) ^ n = 1 := by
  have hroot : star (fourierRoot d) * fourierRoot d = 1 := by
    dsimp [fourierRoot]
    exact circle_star_mul_self_local (ZMod.toCircle 1)
  rw [star_pow, ← mul_pow, hroot, one_pow]

private theorem projectionFamily_sum_idempotent {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    (∑ k : Fin d, P k) * (∑ k : Fin d, P k) = ∑ k : Fin d, P k := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum]
  rw [Finset.sum_eq_single i]
  · exact hIdem i
  · intro j _ hji
    exact hOrth i j (fun h => hji h.symm)
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem projectionFamily_sum_left {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) (i : Fin d) :
    (∑ k : Fin d, P k) * P i = P i := by
  classical
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single i]
  · exact hIdem i
  · intro j _ hji
    exact hOrth j i hji
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem projectionFamily_sum_right {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) (i : Fin d) :
    P i * (∑ k : Fin d, P k) = P i := by
  classical
  rw [Matrix.mul_sum]
  rw [Finset.sum_eq_single i]
  · exact hIdem i
  · intro j _ hji
    exact hOrth i j (fun h => hji h.symm)
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem weightedProjectionFamily_isometry {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (hHerm : ∀ k, (P k).IsHermitian)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    Matrix.conjTranspose (∑ k : Fin d, (fourierRoot d) ^ (k : ℕ) • P k) *
        (∑ k : Fin d, (fourierRoot d) ^ (k : ℕ) • P k) =
      ∑ k : Fin d, P k := by
  classical
  rw [Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_smul, Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [show (P i)ᴴ = P i by simpa [Matrix.IsHermitian] using hHerm i]
    rw [matrix_smul_mul_smul]
    rw [hIdem i, fourierRoot_pow_star_mul_self]
    simp
  · intro j _ hji
    rw [show (P i)ᴴ = P i by simpa [Matrix.IsHermitian] using hHerm i]
    rw [matrix_smul_mul_smul]
    rw [hOrth i j (fun h => hji h.symm)]
    simp
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem weightedProjectionFamily_left_complement {H : Type u}
    [Fintype H] [DecidableEq H] {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (c : Fin d → ℂ)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    (∑ k : Fin d, c k • P k) * (1 - ∑ k : Fin d, P k) = 0 := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  calc
    (c i • P i) * (1 - ∑ k : Fin d, P k)
        = c i • (P i * (1 - ∑ k : Fin d, P k)) := by
            rw [Matrix.smul_mul]
    _ = 0 := by
            rw [Matrix.mul_sub, projectionFamily_sum_right P hIdem hOrth i]
            simp

private theorem weightedProjectionFamily_right_complement {H : Type u}
    [Fintype H] [DecidableEq H] {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (c : Fin d → ℂ)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    (1 - ∑ k : Fin d, P k) * (∑ k : Fin d, c k • P k) = 0 := by
  classical
  rw [Matrix.mul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  calc
    (1 - ∑ k : Fin d, P k) * (c i • P i)
        = c i • ((1 - ∑ k : Fin d, P k) * P i) := by
            rw [Matrix.mul_smul]
    _ = 0 := by
            rw [Matrix.sub_mul, projectionFamily_sum_left P hIdem hOrth i]
            simp

private theorem projectionFamily_complement_idempotent {H : Type u}
    [Fintype H] [DecidableEq H] {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    (1 - ∑ k : Fin d, P k) * (1 - ∑ k : Fin d, P k) =
        1 - ∑ k : Fin d, P k := by
  have hsum := projectionFamily_sum_idempotent P hIdem hOrth
  calc
    (1 - ∑ k : Fin d, P k) * (1 - ∑ k : Fin d, P k)
        = 1 - ∑ k : Fin d, P k - ∑ k : Fin d, P k +
            (∑ k : Fin d, P k) * (∑ k : Fin d, P k) := by
            noncomm_ring
    _ = 1 - ∑ k : Fin d, P k := by
            rw [hsum]
            noncomm_ring

/--
The CGS phase operator is an isometry for any pairwise orthogonal projection
family.  The complement term handles the source-general Bob case where the
family need not be complete.
-/
theorem phaseOperator_isometry_of_orthogonal_projection_family
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (hHerm : ∀ k, (P k).IsHermitian)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    Matrix.conjTranspose (phaseOperator P) * phaseOperator P = 1 := by
  classical
  let W : CMatrix H := ∑ k : Fin d, (fourierRoot d) ^ (k : ℕ) • P k
  let S : CMatrix H := ∑ k : Fin d, P k
  have hW : Matrix.conjTranspose W * W = S := by
    simpa [W, S] using weightedProjectionFamily_isometry P hHerm hIdem hOrth
  have hWC : W * (1 - S) = 0 := by
    simpa [W, S] using weightedProjectionFamily_left_complement P
      (fun k : Fin d => (fourierRoot d) ^ (k : ℕ)) hIdem hOrth
  have hCW : (1 - S) * W = 0 := by
    simpa [W, S] using weightedProjectionFamily_right_complement P
      (fun k : Fin d => (fourierRoot d) ^ (k : ℕ)) hIdem hOrth
  have hC : (1 - S) * (1 - S) = 1 - S := by
    simpa [S] using projectionFamily_complement_idempotent P hIdem hOrth
  have hCherm : Matrix.conjTranspose (1 - S) = 1 - S := by
    have hS : Matrix.conjTranspose S = S := by
      calc
        Matrix.conjTranspose S = ∑ k : Fin d, Matrix.conjTranspose (P k) := by
            simp [S, Matrix.conjTranspose_sum]
        _ = ∑ k : Fin d, P k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simpa [Matrix.IsHermitian] using hHerm k
        _ = S := by simp [S]
    simp [hS]
  have hWconj :
      Matrix.conjTranspose W =
        ∑ k : Fin d, star ((fourierRoot d) ^ (k : ℕ)) • P k := by
    calc
      Matrix.conjTranspose W =
          ∑ k : Fin d,
            star ((fourierRoot d) ^ (k : ℕ)) • Matrix.conjTranspose (P k) := by
            simp [W, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
      _ = ∑ k : Fin d, star ((fourierRoot d) ^ (k : ℕ)) • P k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [show Matrix.conjTranspose (P k) = P k by
              simpa [Matrix.IsHermitian] using hHerm k]
  have hWconjC : Matrix.conjTranspose W * (1 - S) = 0 := by
    have h :=
      weightedProjectionFamily_left_complement P
        (fun k : Fin d => star ((fourierRoot d) ^ (k : ℕ))) hIdem hOrth
    rw [hWconj]
    simpa [S] using h
  have hCWconj : (1 - S) * Matrix.conjTranspose W = 0 := by
    have h :=
      weightedProjectionFamily_right_complement P
        (fun k : Fin d => star ((fourierRoot d) ^ (k : ℕ))) hIdem hOrth
    rw [hWconj]
    simpa [S] using h
  calc
    Matrix.conjTranspose (phaseOperator P) * phaseOperator P
        = Matrix.conjTranspose (W + (1 - S)) * (W + (1 - S)) := by
            simp [phaseOperator, W, S]
    _ = (Matrix.conjTranspose W + (1 - S)) * (W + (1 - S)) := by
            rw [Matrix.conjTranspose_add, hCherm]
    _ = Matrix.conjTranspose W * W + Matrix.conjTranspose W * (1 - S) +
          ((1 - S) * W + (1 - S) * (1 - S)) := by
            noncomm_ring
    _ = 1 := by
            rw [hW, hWconjC, hCW, hC]
            noncomm_ring

private theorem matrix_pow_isometry {H : Type u} [Fintype H] [DecidableEq H]
    (A : CMatrix H) (hA : Matrix.conjTranspose A * A = 1) (n : ℕ) :
    Matrix.conjTranspose (A ^ n) * A ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact left_mul_isometry (A ^ n) A ih hA

/-- Controlled powers of a CGS phase operator form an isometry. -/
theorem controlledPhase_isometry_of_orthogonal_projection_family
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (hHerm : ∀ k, (P k).IsHermitian)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    Matrix.conjTranspose (controlledPhase P) * controlledPhase P = 1 := by
  apply controlledOperator_isometry
  intro k
  exact matrix_pow_isometry (phaseOperator P)
    (phaseOperator_isometry_of_orthogonal_projection_family P hHerm hIdem hOrth) (k : ℕ)

/-- Matrix embedding `|h>` as `|h> tensor |zero>` on an ancilla `Fin d`. -/
def ancillaZeroMatrix {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (zero : Fin d) : Matrix (H × Fin d) H ℂ :=
  fun x h => if x = (h, zero) then 1 else 0

/-- The zero-ancilla embedding is an isometry. -/
theorem ancillaZeroMatrix_isometry {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (zero : Fin d) :
    Matrix.conjTranspose (ancillaZeroMatrix (H := H) zero) *
        ancillaZeroMatrix (H := H) zero = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [ancillaZeroMatrix, Matrix.mul_apply]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [ancillaZeroMatrix, Matrix.mul_apply, hij, hji]

/-- Zero-ancilla embedding packaged as a `ReferenceIsometry`. -/
def ancillaZeroReferenceIsometry (H : Type u) [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (zero : Fin d) : ReferenceIsometry H (H × Fin d) where
  matrix := ancillaZeroMatrix (H := H) zero
  isometry := ancillaZeroMatrix_isometry (H := H) zero

@[simp]
theorem ancillaZeroReferenceIsometry_matrix {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (zero : Fin d) :
    (ancillaZeroReferenceIsometry H zero).matrix = ancillaZeroMatrix (H := H) zero :=
  rfl

/-- Applying the zero-ancilla isometry recovers the original vector on the zero block. -/
theorem ancillaZeroReferenceIsometry_mulVec_zero
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] {zero : Fin d} (ψ : H → ℂ) (h : H) :
    ((ancillaZeroReferenceIsometry H zero).matrix.mulVec ψ) (h, zero) = ψ h := by
  simp [ancillaZeroReferenceIsometry, ancillaZeroMatrix, Matrix.mulVec, dotProduct]

/-- Applying the zero-ancilla isometry vanishes away from the zero block. -/
theorem ancillaZeroReferenceIsometry_mulVec_ne_zero
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] {zero : Fin d} (ψ : H → ℂ) (h : H) (k : Fin d)
    (hk : k ≠ zero) :
    ((ancillaZeroReferenceIsometry H zero).matrix.mulVec ψ) (h, k) = 0 := by
  simp [ancillaZeroReferenceIsometry, ancillaZeroMatrix, Matrix.mulVec, dotProduct, hk]

namespace YNData

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

variable (data : YNData ι HA HB)

/-- Alice's controlled local-unitary operator is an isometry. -/
theorem aliceControlledUnitary_isometry
    (B : SchmidtTarget.BaseReindexToFin data.target) :
    Matrix.conjTranspose (data.aliceControlledUnitary B.toEquiv) *
        data.aliceControlledUnitary B.toEquiv = 1 := by
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  simpa [aliceControlledUnitary] using
    controlledUnitary_isometry
      (fun k : Fin (Fintype.card ι) => data.aliceUnitary (B.toEquiv.symm k))

/-- Alice's controlled phase operator is an isometry. -/
theorem aliceControlledPhase_isometry
    (B : SchmidtTarget.BaseReindexToFin data.target) :
    Matrix.conjTranspose (data.aliceControlledPhase B.toEquiv) *
        data.aliceControlledPhase B.toEquiv = 1 := by
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  apply controlledPhase_isometry_of_orthogonal_projection_family
  · intro k
    exact data.aliceProjection.isHermitian (B.toEquiv.symm k)
  · intro k
    exact data.aliceProjection.idempotent (B.toEquiv.symm k)
  · intro i j hij
    apply data.aliceProjection.orthogonal
    intro h
    apply hij
    exact B.toEquiv.symm.injective h

/--
Alice's assembled CGS side operator up to the density-calculation boundary.

The matrix follows the source order `R_A * F⁻¹ * S_A * F * |0⟩`, leaving the
state-specific density calculation to the next child.
-/
def aliceSideMatrix (B : SchmidtTarget.BaseReindexToFin data.target) :
    Matrix (HA × Fin (Fintype.card ι)) HA ℂ :=
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  data.aliceControlledUnitary B.toEquiv *
    (ancillaInverseFourierMatrix (H := HA) (Fintype.card ι) *
      (data.aliceControlledPhase B.toEquiv *
        (ancillaFourierMatrix (H := HA) (Fintype.card ι) *
          ancillaZeroMatrix (H := HA) data.target.baseIndex)))

/-- Alice's assembled side operator is an isometry. -/
theorem aliceSideMatrix_isometry
    (B : SchmidtTarget.BaseReindexToFin data.target) :
    Matrix.conjTranspose (data.aliceSideMatrix B) * data.aliceSideMatrix B = 1 := by
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  unfold aliceSideMatrix
  apply left_mul_isometry
  · exact data.aliceControlledUnitary_isometry B
  · apply left_mul_isometry
    · exact ancillaInverseFourierMatrix_isometry (H := HA) (Fintype.card ι)
    · apply left_mul_isometry
      · exact data.aliceControlledPhase_isometry B
      · apply left_mul_isometry
        · exact ancillaFourierMatrix_isometry (H := HA) (Fintype.card ι)
        · exact ancillaZeroMatrix_isometry (H := HA) data.target.baseIndex

/-- Alice's assembled side operator packaged as a reference isometry. -/
def aliceSideIsometry (B : SchmidtTarget.BaseReindexToFin data.target) :
    ReferenceIsometry HA (HA × Fin (Fintype.card ι)) where
  matrix := data.aliceSideMatrix B
  isometry := data.aliceSideMatrix_isometry B

end YNData

namespace BobLocalOrthogonalization

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
variable {data : YNData ι HA HB} {rho : State (HA × HB)}

variable (W : BobLocalOrthogonalization data rho)

/-- Bob's controlled local-unitary operator is an isometry. -/
theorem bobControlledUnitary_isometry (_W : BobLocalOrthogonalization data rho)
    (B : SchmidtTarget.BaseReindexToFin data.target) :
    Matrix.conjTranspose (data.bobControlledUnitary B.toEquiv) *
        data.bobControlledUnitary B.toEquiv = 1 := by
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  simpa [YNData.bobControlledUnitary] using
    controlledUnitary_isometry
      (fun k : Fin (Fintype.card ι) => data.bobUnitary (B.toEquiv.symm k))

/-- Bob's controlled phase operator from the Bob-local replacement family is an isometry. -/
theorem bobControlledPhase_isometry
    (B : SchmidtTarget.BaseReindexToFin data.target) :
    Matrix.conjTranspose (W.bobControlledPhase B.toEquiv) *
        W.bobControlledPhase B.toEquiv = 1 := by
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  apply controlledPhase_isometry_of_orthogonal_projection_family
  · intro k
    exact (W.bobLocal (B.toEquiv.symm k)).isHermitian
  · intro k
    exact (W.bobLocal (B.toEquiv.symm k)).idempotent
  · intro i j hij
    apply W.orthogonal
    intro h
    apply hij
    exact B.toEquiv.symm.injective h

/--
Bob's assembled CGS side operator using the landed Bob-local replacement family
as the witness input, in source order `R_B * F⁻¹ * S_B * F * |0⟩`.
-/
def bobSideMatrix (W : BobLocalOrthogonalization data rho)
    (B : SchmidtTarget.BaseReindexToFin data.target) :
    Matrix (HB × Fin (Fintype.card ι)) HB ℂ :=
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  let _witness : BobLocalOrthogonalization data rho := W
  data.bobControlledUnitary B.toEquiv *
    (ancillaInverseFourierMatrix (H := HB) (Fintype.card ι) *
      (W.bobControlledPhase B.toEquiv *
        (ancillaFourierMatrix (H := HB) (Fintype.card ι) *
          ancillaZeroMatrix (H := HB) data.target.baseIndex)))

/-- Bob's assembled side operator is an isometry. -/
theorem bobSideMatrix_isometry
    (B : SchmidtTarget.BaseReindexToFin data.target) :
    Matrix.conjTranspose (W.bobSideMatrix B) * W.bobSideMatrix B = 1 := by
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  unfold bobSideMatrix
  apply left_mul_isometry
  · exact W.bobControlledUnitary_isometry B
  · apply left_mul_isometry
    · exact ancillaInverseFourierMatrix_isometry (H := HB) (Fintype.card ι)
    · apply left_mul_isometry
      · exact W.bobControlledPhase_isometry B
      · apply left_mul_isometry
        · exact ancillaFourierMatrix_isometry (H := HB) (Fintype.card ι)
        · exact ancillaZeroMatrix_isometry (H := HB) data.target.baseIndex

/-- Bob's assembled side operator packaged as a reference isometry. -/
def bobSideIsometry (B : SchmidtTarget.BaseReindexToFin data.target) :
    ReferenceIsometry HB (HB × Fin (Fintype.card ι)) where
  matrix := W.bobSideMatrix B
  isometry := W.bobSideMatrix_isometry B

end BobLocalOrthogonalization

namespace YNData

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

variable (data : YNData ι HA HB)

/-- The assembled CGS local isometry from Alice and Bob side operators. -/
def cgsLocalIsometry {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) :
    TwoQubit.LocalIsometry HA (HA × Fin (Fintype.card ι))
        HB (HB × Fin (Fintype.card ι)) where
  alice := data.aliceSideIsometry B
  bob := W.bobSideIsometry B

end YNData

end

end YangNavascues
end QIT
