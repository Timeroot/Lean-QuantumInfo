/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Pure
public import QIT.Util.Matrix.PosSqrt
public import QIT.Util.SDP.PSDCone
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Hermitian PSD trace-pairing duality

This module provides the real Hilbert-space layer on Hermitian complex matrices
used by the SDP/conic-duality route.  The public API represents continuous real
linear functionals on Hermitian matrices by trace pairing against a Hermitian
matrix, and upgrades positive functionals on the PSD cone to PSD
representatives.

The ambient bridge starts from an arbitrary continuous real functional on the
ambient `CMatrix n` space, restricts it to Hermitian matrices, and extracts a
positive-semidefinite Hermitian trace-pairing representative.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix Complex

namespace QIT

universe u

noncomputable section

variable {n : Type u} [Fintype n] [DecidableEq n]

/-! ## Matrix-level PSD trace-pairing support -/

omit [DecidableEq n] in
/-- The trace pairing with a rank-one kernel is the associated quadratic form. -/
theorem trace_mul_rankOneMatrix_eq_quadratic (T : CMatrix n) (x : n →₀ ℂ) :
    (T * rankOneMatrix (fun i => x i)).trace =
      x.sum (fun i xi => x.sum (fun j xj => star xi * T i j * xj)) := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, rankOneMatrix_apply, Finsupp.sum_fintype]
  ac_rfl

omit [DecidableEq n] in
/-- The trace of a product of Hermitian matrices is real. -/
theorem trace_mul_isHermitian_im_eq_zero {T A : CMatrix n}
    (hT : T.IsHermitian) (hA : A.IsHermitian) : ((T * A).trace).im = 0 := by
  have hstar : star ((T * A).trace) = (T * A).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hT.eq,
      Matrix.trace_mul_comm]
  have him := congrArg Complex.im hstar
  simp at him
  linarith

/-- The trace product of two PSD matrices is nonnegative in real part. -/
theorem cMatrix_trace_mul_posSemidef_re_nonneg {A B : CMatrix n}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ ((A * B).trace).re := by
  let S := psdSqrt A
  have hpsd : (S * B * S).PosSemidef := by
    have h := hB.mul_mul_conjTranspose_same S
    dsimp [S] at h
    rw [psdSqrt_isHermitian A] at h
    exact h
  have htrace : 0 ≤ (S * B * S).trace :=
    Matrix.PosSemidef.trace_nonneg hpsd
  have hEq : (A * B).trace = (S * B * S).trace := by
    have hsqrt : S * S = A := by
      simpa [S] using psdSqrt_mul_self_of_posSemidef hA
    rw [← hsqrt]
    calc
      ((S * S) * B).trace = (S * (S * B)).trace := by
        rw [Matrix.mul_assoc]
      _ = ((S * B) * S).trace := by
        rw [Matrix.trace_mul_comm]
      _ = (S * B * S).trace := by
        rw [Matrix.mul_assoc]
  rw [hEq]
  exact htrace.1

/-- Positive trace functionals preserve Loewner inequalities. -/
public theorem cMatrix_trace_mul_le_of_le_posSemidef_left
    {A B W : CMatrix n} (hW : W.PosSemidef) (hAB : A ≤ B) :
    ((W * A).trace).re ≤ ((W * B).trace).re := by
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hnonneg : 0 ≤ ((W * (B - A)).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hW hdiff
  have htrace :
      ((W * (B - A)).trace).re =
        ((W * B).trace).re - ((W * A).trace).re := by
    simp [Matrix.mul_sub, Matrix.trace_sub]
  rw [htrace] at hnonneg
  linarith

omit [DecidableEq n] in
private theorem posSemidef_of_trace_mul_rankOneMatrix_re_nonneg {T : CMatrix n}
    (hT : T.IsHermitian)
    (h : ∀ x : n →₀ ℂ, 0 ≤ ((T * rankOneMatrix (fun i => x i)).trace).re) :
    T.PosSemidef := by
  refine ⟨hT, ?_⟩
  intro x
  have hx := h x
  have hquad := trace_mul_rankOneMatrix_eq_quadratic T x
  have him : ((T * rankOneMatrix (fun i => x i)).trace).im = 0 := by
    exact trace_mul_isHermitian_im_eq_zero hT (rankOneMatrix_pos (fun i => x i)).1
  rw [hquad] at hx him
  rw [Complex.le_def]
  exact ⟨hx, him.symm⟩

/-- A Hermitian matrix is PSD iff it pairs nonnegatively with all PSD matrices. -/
theorem cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg {T : CMatrix n}
    (hT : T.IsHermitian) :
    T.PosSemidef ↔ ∀ A : CMatrix n, A.PosSemidef → 0 ≤ ((T * A).trace).re := by
  constructor
  · intro hTpsd A hA
    exact cMatrix_trace_mul_posSemidef_re_nonneg hTpsd hA
  · intro h
    exact posSemidef_of_trace_mul_rankOneMatrix_re_nonneg hT
      (fun x => h (rankOneMatrix (fun i => x i)) (rankOneMatrix_pos (fun i => x i)))

/-! ## Hermitian matrices as a real Hilbert space -/

/-- Hermitian complex matrices as a dedicated real Hilbert-space wrapper. -/
structure HermitianMatrix (n : Type u) [Fintype n] [DecidableEq n] where
  val : CMatrix n
  isHermitian : val.IsHermitian

namespace HermitianMatrix

instance : Coe (HermitianMatrix n) (CMatrix n) := ⟨HermitianMatrix.val⟩

@[ext]
theorem ext {X Y : HermitianMatrix n} (h : X.val = Y.val) : X = Y := by
  cases X with
  | mk X hX =>
  cases Y with
  | mk Y hY =>
  simp only at h
  subst h
  rfl

instance : Zero (HermitianMatrix n) := ⟨⟨0, Matrix.isHermitian_zero⟩⟩

instance : Add (HermitianMatrix n) :=
  ⟨fun X Y => ⟨X.val + Y.val, X.isHermitian.add Y.isHermitian⟩⟩

instance : Neg (HermitianMatrix n) :=
  ⟨fun X => ⟨-X.val, X.isHermitian.neg⟩⟩

instance : Sub (HermitianMatrix n) :=
  ⟨fun X Y => ⟨X.val - Y.val, X.isHermitian.sub Y.isHermitian⟩⟩

instance : SMul ℕ (HermitianMatrix n) :=
  ⟨fun k X => ⟨k • X.val, X.isHermitian.smul (IsSelfAdjoint.all k)⟩⟩

instance : SMul ℤ (HermitianMatrix n) :=
  ⟨fun k X => ⟨k • X.val, X.isHermitian.smul (IsSelfAdjoint.all k)⟩⟩

instance : SMul ℝ (HermitianMatrix n) :=
  ⟨fun c X => ⟨c • X.val, X.isHermitian.smul (IsSelfAdjoint.all c)⟩⟩

@[simp]
theorem val_zero : (0 : HermitianMatrix n).val = 0 := rfl

@[simp]
theorem val_add (X Y : HermitianMatrix n) : (X + Y).val = X.val + Y.val := rfl

@[simp]
theorem val_neg (X : HermitianMatrix n) : (-X).val = -X.val := rfl

@[simp]
theorem val_sub (X Y : HermitianMatrix n) : (X - Y).val = X.val - Y.val := rfl

@[simp]
theorem val_nsmul (k : ℕ) (X : HermitianMatrix n) : (k • X).val = k • X.val := rfl

@[simp]
theorem val_zsmul (k : ℤ) (X : HermitianMatrix n) : (k • X).val = k • X.val := rfl

@[simp]
theorem val_smul (c : ℝ) (X : HermitianMatrix n) : (c • X).val = c • X.val := rfl

theorem val_injective : Function.Injective (fun X : HermitianMatrix n => X.val) :=
  fun _ _ h => ext h

instance : AddCommGroup (HermitianMatrix n) :=
  Function.Injective.addCommGroup (fun X : HermitianMatrix n => X.val) val_injective
    val_zero val_add val_neg val_sub (fun X k => val_nsmul k X) (fun X k => val_zsmul k X)

/-- The additive inclusion of Hermitian matrices into ambient complex matrices. -/
def toCMatrixAddMonoidHom : HermitianMatrix n →+ CMatrix n where
  toFun X := X.val
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℝ (HermitianMatrix n) :=
  Function.Injective.module ℝ (toCMatrixAddMonoidHom (n := n)) val_injective
    (by intro _ _; rfl)

/-- The real-linear inclusion of Hermitian matrices into ambient complex matrices. -/
def toCMatrixLinear : HermitianMatrix n →ₗ[ℝ] CMatrix n where
  toFun X := X.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toCMatrixLinear_injective :
    Function.Injective (toCMatrixLinear : HermitianMatrix n →ₗ[ℝ] CMatrix n) :=
  val_injective

local instance ambientNormedAddCommGroup : NormedAddCommGroup (CMatrix n) :=
  Matrix.toMatrixNormedAddCommGroup (1 : CMatrix n) Matrix.PosDef.one

local instance ambientComplexInnerProductSpace : InnerProductSpace ℂ (CMatrix n) :=
  Matrix.toMatrixInnerProductSpace (1 : CMatrix n) Matrix.PosSemidef.one

local instance ambientRealInnerProductSpace : InnerProductSpace ℝ (CMatrix n) :=
  InnerProductSpace.complexToReal

local instance ambientNormedSpaceReal : NormedSpace ℝ (CMatrix n) :=
  inferInstance

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (HermitianMatrix n) :=
  NormedAddCommGroup.induced (HermitianMatrix n) (CMatrix n)
    (toCMatrixAddMonoidHom (n := n)) val_injective

noncomputable instance instNormedSpaceReal : NormedSpace ℝ (HermitianMatrix n) :=
  NormedSpace.induced ℝ (HermitianMatrix n) (CMatrix n)
    (toCMatrixLinear : HermitianMatrix n →ₗ[ℝ] CMatrix n)

noncomputable instance instInnerProductSpaceReal : InnerProductSpace ℝ (HermitianMatrix n) :=
  InnerProductSpace.induced (toCMatrixLinear : HermitianMatrix n →ₗ[ℝ] CMatrix n)

noncomputable instance instFiniteDimensionalReal : FiniteDimensional ℝ (HermitianMatrix n) :=
  FiniteDimensional.of_injective
    (toCMatrixLinear : HermitianMatrix n →ₗ[ℝ] CMatrix n) toCMatrixLinear_injective

noncomputable instance instCompleteSpace : CompleteSpace (HermitianMatrix n) :=
  FiniteDimensional.complete ℝ (HermitianMatrix n)

end HermitianMatrix

/-- The real trace pairing on Hermitian matrices. -/
def tracePairing (T X : HermitianMatrix n) : ℝ :=
  ((T.val * X.val).trace).re

/-- The Hermitian continuous dual. -/
abbrev HermitianDual (n : Type u) [Fintype n] [DecidableEq n] :=
  StrongDual ℝ (HermitianMatrix n)

namespace HermitianMatrix

/-- The inherited real Hilbert inner product is the trace pairing. -/
theorem inner_eq_tracePairing (T X : HermitianMatrix n) :
    inner ℝ T X = tracePairing T X := by
  letI : NormedAddCommGroup (CMatrix n) :=
    Matrix.toMatrixNormedAddCommGroup (1 : CMatrix n) Matrix.PosDef.one
  letI : InnerProductSpace ℂ (CMatrix n) :=
    Matrix.toMatrixInnerProductSpace (1 : CMatrix n) Matrix.PosSemidef.one
  letI : InnerProductSpace ℝ (CMatrix n) :=
    InnerProductSpace.complexToReal
  change re (inner ℂ
    ((toCMatrixLinear : HermitianMatrix n →ₗ[ℝ] CMatrix n) T)
    ((toCMatrixLinear : HermitianMatrix n →ₗ[ℝ] CMatrix n) X)) = _
  change ((X.val * 1 * T.valᴴ).trace).re = ((T.val * X.val).trace).re
  calc
    ((X.val * 1 * T.valᴴ).trace).re = ((X.val * T.val).trace).re := by
      rw [T.isHermitian.eq]
      simp
    _ = ((T.val * X.val).trace).re := by
      rw [Matrix.trace_mul_comm X.val T.val]

/-- The squared Frobenius norm agrees with self trace pairing. -/
theorem norm_sq_eq_tracePairing_self (X : HermitianMatrix n) :
    ‖X‖ ^ 2 = tracePairing X X := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ)]
  exact inner_eq_tracePairing X X

end HermitianMatrix

export HermitianMatrix (inner_eq_tracePairing norm_sq_eq_tracePairing_self)

/-- The trace-pairing functional represented by `T`. -/
noncomputable def tracePairingCLM (T : HermitianMatrix n) : HermitianDual n :=
  (InnerProductSpace.toDual ℝ (HermitianMatrix n)) T

@[simp]
theorem tracePairingCLM_apply (T X : HermitianMatrix n) :
    tracePairingCLM T X = tracePairing T X := by
  rw [tracePairingCLM, InnerProductSpace.toDual_apply_apply, inner_eq_tracePairing]

/-- Trace-pairing representatives are unique. -/
theorem tracePairingCLM_injective :
    Function.Injective (tracePairingCLM : HermitianMatrix n → HermitianDual n) :=
  (InnerProductSpace.toDual ℝ (HermitianMatrix n)).injective

/-- Every continuous real functional on Hermitian matrices is a trace pairing. -/
theorem exists_hermitian_tracePairing_representation
    (ℓ : HermitianDual n) :
    ∃ T : HermitianMatrix n, ∀ X, ℓ X = tracePairing T X := by
  let T := (InnerProductSpace.toDual ℝ (HermitianMatrix n)).symm ℓ
  refine ⟨T, ?_⟩
  intro X
  calc
    ℓ X = inner ℝ T X := by
      rw [← InnerProductSpace.toDual_symm_apply]
    _ = tracePairing T X := inner_eq_tracePairing T X

/-- Hermitian matrices included continuously into ambient complex matrices. -/
noncomputable def hermitianInclusion : HermitianMatrix n →L[ℝ] CMatrix n :=
  LinearMap.toContinuousLinearMap
    (HermitianMatrix.toCMatrixLinear : HermitianMatrix n →ₗ[ℝ] CMatrix n)

private theorem half_add_half_complex (z : ℂ) :
    (2 : ℝ)⁻¹ * z + (2 : ℝ)⁻¹ * z = z := by
  apply Complex.ext
  · simp
    ring
  · simp
    ring

/-- The Hermitian projection `(A + Aᴴ) / 2` as a real-linear map. -/
def hermitianProjectionLinear : CMatrix n →ₗ[ℝ] HermitianMatrix n where
  toFun A :=
    ⟨(2 : ℝ)⁻¹ • (A + Aᴴ),
      (Matrix.isHermitian_add_transpose_self A).smul (IsSelfAdjoint.all ((2 : ℝ)⁻¹))⟩
  map_add' A B := by
    ext i j
    simp [Matrix.conjTranspose_add, add_assoc, add_left_comm]
  map_smul' c A := by
    ext i j
    simp [Matrix.conjTranspose_smul, mul_comm, mul_left_comm, mul_assoc]

/-- The continuous Hermitian projection `(A + Aᴴ) / 2`. -/
noncomputable def hermitianProjection : CMatrix n →L[ℝ] HermitianMatrix n :=
  LinearMap.toContinuousLinearMap
    (hermitianProjectionLinear : CMatrix n →ₗ[ℝ] HermitianMatrix n)

@[simp]
theorem hermitianInclusion_apply (X : HermitianMatrix n) :
    hermitianInclusion X = X.val := rfl

@[simp]
theorem hermitianProjection_apply (A : CMatrix n) :
    (hermitianProjection A).val = (2 : ℝ)⁻¹ • (A + Aᴴ) := rfl

/-- The Hermitian projection fixes Hermitian matrices. -/
theorem hermitianProjection_fix (X : HermitianMatrix n) :
    hermitianProjection X.val = X := by
  ext i j
  simpa [X.isHermitian.eq] using half_add_half_complex (X.val i j)

/-- The Hermitian projection is unchanged on PSD matrices. -/
theorem hermitianProjection_of_posSemidef {A : CMatrix n} (hA : A.PosSemidef) :
    hermitianProjection A = ⟨A, hA.1⟩ := by
  ext i j
  simpa [hA.1.eq] using half_add_half_complex (A i j)

/-- A positive continuous Hermitian functional has a PSD trace-pairing representative. -/
theorem exists_posSemidef_tracePairing_representation
    (ℓ : HermitianDual n)
    (hℓ : ∀ X : HermitianMatrix n, X.val.PosSemidef → 0 ≤ ℓ X) :
    ∃ T : HermitianMatrix n,
      T.val.PosSemidef ∧ ∀ X, ℓ X = tracePairing T X := by
  rcases exists_hermitian_tracePairing_representation (n := n) ℓ with ⟨T, hT⟩
  have hpsd : T.val.PosSemidef := by
    refine (cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg T.isHermitian).2 ?_
    intro A hA
    let X : HermitianMatrix n := ⟨A, hA.1⟩
    have hx : 0 ≤ ℓ X := hℓ X hA
    simpa [X, tracePairing] using
      (show 0 ≤ tracePairing T X from by simpa [hT X] using hx)
  exact ⟨T, hpsd, hT⟩

/--
Any positive continuous real functional on ambient complex matrices restricts to
the Hermitian space and has a PSD Hermitian trace-pairing representative.
-/
theorem exists_posSemidef_tracePairing_representation_of_CMatrix
    (ℓ : CMatrix n →L[ℝ] ℝ)
    (hℓ : ∀ A : CMatrix n, A.PosSemidef → 0 ≤ ℓ A) :
    ∃ T : HermitianMatrix n,
      T.val.PosSemidef ∧ ∀ X : HermitianMatrix n, ℓ X.val = tracePairing T X := by
  let ℓH : HermitianDual n := ℓ.comp (hermitianInclusion : HermitianMatrix n →L[ℝ] CMatrix n)
  have hℓH : ∀ X : HermitianMatrix n, X.val.PosSemidef → 0 ≤ ℓH X := by
    intro X hX
    exact hℓ X.val hX
  rcases exists_posSemidef_tracePairing_representation (n := n) ℓH hℓH with
    ⟨T, hTpsd, hrep⟩
  refine ⟨T, hTpsd, ?_⟩
  intro X
  simpa [ℓH] using hrep X

end

end QIT
