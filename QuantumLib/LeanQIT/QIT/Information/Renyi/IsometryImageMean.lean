/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.RelativeEntropyDPI
public import QIT.Information.Renyi.DirectSumMean

/-!
# Isometry-image pinching and the divergence mean property

This module formalizes the image/complement step used in Tomamichel's
coherent-measurement uncertainty proof
[Tomamichel2015FiniteResources, apps.tex:193-215].  Compression by
an isometry is completed to a channel with an explicit failure flag.  On a
state supported in the isometry image, the result is the compressed state plus
a zero failure block; the direct-sum mean property then removes that block.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

namespace ReferenceIsometry

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Completely positive compression from the target of an isometry back to
its source. -/
private def compressionMap (V : ReferenceIsometry a b) : MatrixMap b a :=
  MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix)

@[simp]
private theorem compressionMap_apply (V : ReferenceIsometry a b) (X : CMatrix b) :
    V.compressionMap X =
      Matrix.conjTranspose V.matrix * X * V.matrix := by
  simp [compressionMap, MatrixMap.ofKraus]

private theorem matrix_mulVec_injective (V : ReferenceIsometry a b) :
    Function.Injective V.matrix.mulVec := by
  intro x y hxy
  have h := congrArg (Matrix.mulVec (Matrix.conjTranspose V.matrix)) hxy
  simpa [Matrix.mulVec_mulVec, V.isometry] using h

private theorem imageProjection_complement_posSemidef (V : ReferenceIsometry a b) :
    (1 - V.matrix * Matrix.conjTranspose V.matrix).PosSemidef := by
  let P : CMatrix b := V.matrix * Matrix.conjTranspose V.matrix
  have hPpos : P.PosSemidef := by
    simpa [P] using
      Matrix.posSemidef_conjTranspose_mul_self (Matrix.conjTranspose V.matrix)
  have hPid : P * P = P := by
    calc
      P * P = V.matrix *
          (Matrix.conjTranspose V.matrix * V.matrix) *
            Matrix.conjTranspose V.matrix := by
          simp [P, Matrix.mul_assoc]
      _ = P := by rw [V.isometry]; simp [P]
  simpa [P] using MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent P hPpos hPid

private theorem compressionMap_traceNonincreasingCP (V : ReferenceIsometry a b) :
    MatrixMap.TraceNonincreasingCP V.compressionMap where
  completelyPositive := MatrixMap.ofKraus_isCompletelyPositive _
  traceNonincreasing := by
    intro X hX
    have hcomp := V.imageProjection_complement_posSemidef
    have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hX hcomp
    have htrace :
        (V.compressionMap X).trace =
          (X * (V.matrix * Matrix.conjTranspose V.matrix)).trace := by
      rw [V.compressionMap_apply]
      calc
        (Matrix.conjTranspose V.matrix * X * V.matrix).trace =
            (V.matrix * Matrix.conjTranspose V.matrix * X).trace :=
          Matrix.trace_mul_cycle _ _ _
        _ = (X * (V.matrix * Matrix.conjTranspose V.matrix)).trace :=
          Matrix.trace_mul_comm _ _
    have hsplit :
        ((X * (1 - V.matrix * Matrix.conjTranspose V.matrix)).trace).re =
          X.trace.re - (V.compressionMap X).trace.re := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one, htrace]
      simp
    linarith

private theorem compressionMap_image (V : ReferenceIsometry a b) (X : CMatrix a) :
    V.compressionMap
        (V.matrix * X * Matrix.conjTranspose V.matrix) = X := by
  rw [V.compressionMap_apply]
  calc
    Matrix.conjTranspose V.matrix *
          (V.matrix * X * Matrix.conjTranspose V.matrix) * V.matrix =
        (Matrix.conjTranspose V.matrix * V.matrix) * X *
          (Matrix.conjTranspose V.matrix * V.matrix) := by
      simp [Matrix.mul_assoc]
    _ = X := by rw [V.isometry]; simp

/-- Compressing a positive-definite matrix by an isometry remains positive
definite. -/
theorem compression_posDef (V : ReferenceIsometry a b)
    {sigma : CMatrix b} (hSigma : sigma.PosDef) :
    (Matrix.conjTranspose V.matrix * sigma * V.matrix).PosDef :=
  hSigma.conjTranspose_mul_mul_same V.matrix_mulVec_injective

end ReferenceIsometry

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Put a normalized state in the right block of a binary direct sum. -/
private def rightZeroExtension (rho : State a) : State (Sum PUnit.{1} a) where
  matrix := Matrix.fromBlocks 0 0 0 rho.matrix
  pos := Matrix.fromBlocks_diagonal_posSemidef Matrix.PosSemidef.zero rho.pos
  trace_eq_one := by
    rw [Matrix.trace_fromBlocks_diagonal, rho.trace_eq_one]
    simp

@[simp]
private theorem rightZeroExtension_matrix (rho : State a) :
    rho.rightZeroExtension.matrix = Matrix.fromBlocks 0 0 0 rho.matrix :=
  rfl

private theorem rightZeroExtension_eq_reindex_directSumZero (rho : State a) :
    rho.rightZeroExtension =
      (rho.directSumZero PUnit.{1}).reindex (Equiv.sumComm a PUnit.{1}) := by
  apply State.ext
  ext i j
  cases i <;> cases j <;>
    simp [rightZeroExtension, State.reindex_matrix]

private theorem rightZeroExtension_supports_fromBlocks
    (rho : State a) {failure : CMatrix PUnit.{1}} {sigma : CMatrix a}
    (hSupport : Matrix.Supports rho.matrix sigma) :
    Matrix.Supports rho.rightZeroExtension.matrix
      (Matrix.fromBlocks failure 0 0 sigma) := by
  intro v hv
  rw [Matrix.fromBlocks_mulVec] at hv
  have hright : sigma.mulVec (fun i => v (Sum.inr i)) = 0 := by
    ext i
    have hi := congrFun hv (Sum.inr i)
    simpa using hi
  have hrho := hSupport _ hright
  rw [rightZeroExtension_matrix, Matrix.fromBlocks_mulVec]
  ext i
  cases i with
  | inl i => cases i; simp
  | inr i =>
      have hi := congrFun hrho i
      simpa using hi

private theorem supports_of_rightZeroExtension_supports_fromBlocks
    (rho : State a) {failure : CMatrix PUnit.{1}} {sigma : CMatrix a}
    (hSupport : Matrix.Supports rho.rightZeroExtension.matrix
      (Matrix.fromBlocks failure 0 0 sigma)) :
    Matrix.Supports rho.matrix sigma := by
  intro v hv
  let w : Sum PUnit.{1} a -> Complex := Sum.elim (fun _ => 0) v
  have href :
      (Matrix.fromBlocks failure 0 0 sigma).mulVec w = 0 := by
    rw [Matrix.fromBlocks_mulVec]
    ext i
    cases i with
    | inl i => cases i; simp [w, Matrix.mulVec, dotProduct]
    | inr i =>
        have hi := congrFun hv i
        simpa [w] using hi
  have hrho := hSupport w href
  have hi := funext fun i => congrFun hrho (Sum.inr i)
  simpa [rightZeroExtension, Matrix.fromBlocks_mulVec, w] using hi

private theorem relativeEntropyPSDReferenceTraceLogE_rightZeroExtension_of_supports
    (rho : State a) {failure : CMatrix PUnit.{1}} {sigma : CMatrix a}
    (hFailure : failure.PosSemidef) (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma) :
    relativeEntropyPSDReferenceTraceLogE rho.rightZeroExtension
        (Matrix.fromBlocks failure 0 0 sigma)
        (Matrix.fromBlocks_diagonal_posSemidef hFailure hSigma) =
      relativeEntropyPSDReferenceTraceLogE rho sigma hSigma := by
  let ref : CMatrix (Sum PUnit.{1} a) := Matrix.fromBlocks failure 0 0 sigma
  let hRef : ref.PosSemidef :=
    Matrix.fromBlocks_diagonal_posSemidef hFailure hSigma
  let hSupportBlock : Matrix.Supports rho.rightZeroExtension.matrix ref :=
    rho.rightZeroExtension_supports_fromBlocks hSupport
  let f : Real -> Real := fun x => if x = 0 then 0 else Real.log x
  have hEntropyBlock :
      (_root_.QIT.psdSupportCompressedState rho.rightZeroExtension hRef
        hSupportBlock).vonNeumann = rho.vonNeumann := by
    calc
      (_root_.QIT.psdSupportCompressedState rho.rightZeroExtension hRef
          hSupportBlock).vonNeumann = rho.rightZeroExtension.vonNeumann :=
        relativeEntropyTraceLog_vonNeumann_psdSupportCompressedState_eq
          rho.rightZeroExtension hRef hSupportBlock
      _ = rho.vonNeumann := by
        rw [rho.rightZeroExtension_eq_reindex_directSumZero,
          State.vonNeumann_reindex, directSumZero_vonNeumann]
  have hEntropy :
      (_root_.QIT.psdSupportCompressedState rho hSigma hSupport).vonNeumann =
        rho.vonNeumann :=
    relativeEntropyTraceLog_vonNeumann_psdSupportCompressedState_eq
      rho hSigma hSupport
  have hTraceBlock :
      (((_root_.QIT.psdSupportCompressedState rho.rightZeroExtension hRef
          hSupportBlock).matrix *
        State.psdLog (psdSupportCompress ref hRef ref)
          (psdSupportCompress_self_posDef ref hRef)).trace).re =
        ((rho.rightZeroExtension.matrix * cfc f ref).trace).re := by
    simpa [ref, hRef, f, _root_.QIT.psdSupportCompressedState] using
      relativeEntropyTraceLog_trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero
        rho.rightZeroExtension hRef hSupportBlock
  have hTrace :
      (((_root_.QIT.psdSupportCompressedState rho hSigma hSupport).matrix *
        State.psdLog (psdSupportCompress sigma hSigma sigma)
          (psdSupportCompress_self_posDef sigma hSigma)).trace).re =
        ((rho.matrix * cfc f sigma).trace).re := by
    simpa [f, _root_.QIT.psdSupportCompressedState] using
      relativeEntropyTraceLog_trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero
        rho hSigma hSupport
  have hBlockTraceEq :
      ((rho.rightZeroExtension.matrix * cfc f ref).trace).re =
        ((rho.matrix * cfc f sigma).trace).re := by
    rw [show cfc f ref =
        Matrix.fromBlocks (cfc f failure) 0 0 (cfc f sigma) by
      exact cMatrix_cfc_fromBlocks_diagonal hFailure hSigma f]
    simp [rightZeroExtension, Matrix.fromBlocks_multiply,
      Matrix.trace_fromBlocks_diagonal]
  rw [relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
      rho.rightZeroExtension hRef hSupportBlock,
    relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports rho hSigma hSupport]
  congr 1
  simp only [relativeEntropyPSDReferenceTraceLogFinite]
  rw [hEntropyBlock, hEntropy, hTraceBlock, hTrace, hBlockTraceEq]

end State

namespace MatrixMap.TraceNonincreasingCP

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The failure mass of the canonical channel completion is the trace lost by
the original trace-nonincreasing map. -/
private theorem trace_mul_lossEffect {Phi : MatrixMap a b}
    (hPhi : MatrixMap.TraceNonincreasingCP Phi) (X : CMatrix a) :
    (X * hPhi.lossEffect).trace = X.trace - (Phi X).trace := by
  rw [MatrixMap.TraceNonincreasingCP.lossEffect, Matrix.mul_sub,
    Matrix.trace_sub, Matrix.mul_one]
  have hdual := MatrixMap.ofKraus_trace_duality
    hPhi.kraus X (1 : CMatrix b)
  have hmap : MatrixMap.ofKraus hPhi.kraus X = Phi X := by
    rw [hPhi.ofKraus_kraus]
  rw [Matrix.mul_one, hmap] at hdual
  exact congrArg (fun z => X.trace - z) hdual.symm

end MatrixMap.TraceNonincreasingCP

namespace ReferenceIsometry

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Universe-pinned completion channel used by the image/complement proof. -/
private def compressionCompletion (V : ReferenceIsometry a b) :
    Channel (Sum PUnit.{1} b) (Sum PUnit.{1} a) :=
  V.compressionMap_traceNonincreasingCP.hatCompletion

private theorem compressionCompletion_apply_imageState (V : ReferenceIsometry a b)
    (rho : State a) :
    V.compressionCompletion.applyState
        ((Channel.ofReferenceIsometry V).applyState rho).rightZeroExtension =
      rho.rightZeroExtension := by
  let hComp := V.compressionMap_traceNonincreasingCP
  let image := (Channel.ofReferenceIsometry V).applyState rho
  have hcompression : V.compressionMap image.matrix = rho.matrix := by
    simpa [image, Channel.applyState, Channel.ofReferenceIsometry_map,
      MatrixMap.ofReferenceIsometry_apply] using V.compressionMap_image rho.matrix
  have hloss : (image.matrix * hComp.lossEffect).trace = 0 := by
    rw [hComp.trace_mul_lossEffect, hcompression, image.trace_eq_one,
      rho.trace_eq_one]
    simp
  apply State.ext
  change V.compressionCompletion.map (Matrix.fromBlocks 0 0 0 image.matrix) =
    Matrix.fromBlocks 0 0 0 rho.matrix
  change hComp.hatCompletion.map (Matrix.fromBlocks 0 0 0 image.matrix) =
    Matrix.fromBlocks 0 0 0 rho.matrix
  rw [hComp.hatCompletion_apply_fromBlocks (0 : CMatrix PUnit.{1}) image.matrix]
  ext i j
  cases i <;> cases j <;> simp [hcompression, hloss]

/-- The positive failure-reference block produced by compression completion. -/
private def compressionFailureReference (V : ReferenceIsometry a b)
    (sigma : CMatrix b) : CMatrix PUnit.{1} :=
  fun _ _ => 1 + (sigma * V.compressionMap_traceNonincreasingCP.lossEffect).trace

private theorem compressionFailureReference_posDef_of_posSemidef
    (V : ReferenceIsometry a b)
    {sigma : CMatrix b} (hSigma : sigma.PosSemidef) :
    (V.compressionFailureReference sigma).PosDef := by
  let hComp := V.compressionMap_traceNonincreasingCP
  let z : Complex := (sigma * hComp.lossEffect).trace
  have hzRe : 0 <= z.re := by
    exact cMatrix_trace_mul_posSemidef_re_nonneg hSigma
      hComp.lossEffect_posSemidef
  have hzIm : z.im = 0 := by
    exact trace_mul_posSemidef_im_eq_zero hSigma
      hComp.lossEffect_posSemidef
  have hone : 0 < 1 + z.re := by linarith
  have heq : V.compressionFailureReference sigma =
      ((1 + z.re : Real) : Complex) • (1 : CMatrix PUnit) := by
    ext i j
    cases i
    cases j
    apply Complex.ext
    · simp [compressionFailureReference, z]
    · simp [compressionFailureReference, z, hzIm]
  rw [heq]
  exact Matrix.PosDef.smul Matrix.PosDef.one (by exact_mod_cast hone)

private theorem compressionFailureReference_posDef (V : ReferenceIsometry a b)
    {sigma : CMatrix b} (hSigma : sigma.PosDef) :
    (V.compressionFailureReference sigma).PosDef :=
  V.compressionFailureReference_posDef_of_posSemidef hSigma.posSemidef

private theorem compressionCompletion_map_reference (V : ReferenceIsometry a b)
    (sigma : CMatrix b) :
    V.compressionCompletion.map
        (Matrix.fromBlocks (1 : CMatrix PUnit.{1}) 0 0 sigma) =
      Matrix.fromBlocks (V.compressionFailureReference sigma) 0 0
        (Matrix.conjTranspose V.matrix * sigma * V.matrix) := by
  let hComp := V.compressionMap_traceNonincreasingCP
  change hComp.hatCompletion.map
      (Matrix.fromBlocks (1 : CMatrix PUnit.{1}) 0 0 sigma) = _
  simpa [compressionFailureReference, V.compressionMap_apply] using
    hComp.hatCompletion_apply_fromBlocks (1 : CMatrix PUnit.{1}) sigma

end ReferenceIsometry

namespace State

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The support-aware Umegaki image/complement step for a possibly singular
reference.  This is the order-one boundary of Tomamichel's pinching-and-mean
argument: channel completion supplies a failure flag, trace-log DPI performs
the compression, and the zero-state direct-sum identity removes the flag. -/
theorem relativeEntropyPSDReferenceTraceLogE_isometryImage_ge_compression
    (rho : State a) (V : ReferenceIsometry a b)
    {sigma : CMatrix b} (hSigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports
      ((Channel.ofReferenceIsometry V).applyState rho).matrix sigma) :
    relativeEntropyPSDReferenceTraceLogE
        ((Channel.ofReferenceIsometry V).applyState rho) sigma hSigma >=
      relativeEntropyPSDReferenceTraceLogE rho
        (Matrix.conjTranspose V.matrix * sigma * V.matrix)
        (Matrix.PosSemidef.conjTranspose_mul_mul_same hSigma V.matrix) := by
  let image := (Channel.ofReferenceIsometry V).applyState rho
  let completion := V.compressionCompletion
  let inputState := image.rightZeroExtension
  let inputRef : CMatrix (Sum PUnit.{1} b) :=
    Matrix.fromBlocks (1 : CMatrix PUnit.{1}) 0 0 sigma
  let compressed : CMatrix a :=
    Matrix.conjTranspose V.matrix * sigma * V.matrix
  let failure : CMatrix PUnit.{1} := V.compressionFailureReference sigma
  have hInputRef : inputRef.PosSemidef :=
    Matrix.fromBlocks_diagonal_posSemidef Matrix.PosSemidef.one hSigma
  have hInputSupport : Matrix.Supports inputState.matrix inputRef := by
    exact image.rightZeroExtension_supports_fromBlocks hSupport
  have hDPI :
      relativeEntropyPSDReferenceTraceLogE inputState inputRef hInputRef >=
        relativeEntropyPSDReferenceTraceLogE (completion.applyState inputState)
          (completion.map inputRef) (completion.mapsPositive inputRef hInputRef) :=
    relativeEntropyPSDReferenceTraceLogE_dataProcessing_channel_ge
      inputState hInputRef completion
  have hFailure : failure.PosDef := by
    exact V.compressionFailureReference_posDef_of_posSemidef hSigma
  have hCompressed : compressed.PosSemidef := by
    exact Matrix.PosSemidef.conjTranspose_mul_mul_same hSigma V.matrix
  have hOutputSupport :
      Matrix.Supports (completion.applyState inputState).matrix
        (completion.map inputRef) :=
    channel_applyState_supports_of_supports inputState hInputRef completion
      hInputSupport
  have hOutputSupport' :
      Matrix.Supports rho.rightZeroExtension.matrix
        (Matrix.fromBlocks failure 0 0 compressed) := by
    simpa only [completion, inputState, inputRef, image, failure, compressed,
      V.compressionCompletion_apply_imageState rho,
      V.compressionCompletion_map_reference sigma] using hOutputSupport
  have hCompressedSupport : Matrix.Supports rho.matrix compressed :=
    rho.supports_of_rightZeroExtension_supports_fromBlocks hOutputSupport'
  calc
    relativeEntropyPSDReferenceTraceLogE
        ((Channel.ofReferenceIsometry V).applyState rho) sigma hSigma =
      relativeEntropyPSDReferenceTraceLogE inputState inputRef hInputRef := by
        symm
        exact image.relativeEntropyPSDReferenceTraceLogE_rightZeroExtension_of_supports
          Matrix.PosSemidef.one hSigma hSupport
    _ >= relativeEntropyPSDReferenceTraceLogE (completion.applyState inputState)
        (completion.map inputRef) (completion.mapsPositive inputRef hInputRef) := hDPI
    _ = relativeEntropyPSDReferenceTraceLogE rho compressed hCompressed := by
      have hmean :=
        rho.relativeEntropyPSDReferenceTraceLogE_rightZeroExtension_of_supports
          hFailure.posSemidef hCompressed hCompressedSupport
      simpa only [completion, inputState, inputRef, image, failure, compressed,
        V.compressionCompletion_apply_imageState rho,
        V.compressionCompletion_map_reference sigma] using hmean

private theorem sandwichedRenyiPSDReferenceE_rightZeroExtension
    (rho : State a) {failure : CMatrix PUnit.{1}} {sigma : CMatrix a}
    (hFailure : failure.PosDef) (hSigma : sigma.PosDef)
    (alpha : Real) (hAlpha : 1 / 2 <= alpha) :
    sandwichedRenyiPSDReferenceE rho.rightZeroExtension
        (Matrix.fromBlocks failure 0 0 sigma)
        (Matrix.fromBlocks_diagonal_posDef hFailure hSigma).posSemidef alpha =
      sandwichedRenyiPSDReferenceE rho sigma hSigma.posSemidef alpha := by
  let e : Sum a PUnit.{1} ≃ Sum PUnit.{1} a := Equiv.sumComm a PUnit.{1}
  have href :
      Matrix.reindex e e (Matrix.fromBlocks sigma 0 0 failure) =
        (Matrix.fromBlocks failure 0 0 sigma : CMatrix (Sum PUnit.{1} a)) := by
    ext i j
    cases i <;> cases j <;> simp [e, Matrix.reindex_apply]
  have hmean := sandwichedRenyiPSDReferenceE_directSumZero_reindex
    rho hSigma hFailure e hAlpha
  rw [rho.rightZeroExtension_eq_reindex_directSumZero]
  simpa only [href] using hmean

/-- Tomamichel's image/complement pinching and mean step for a finite
isometry.

For every finite sandwiched-Renyi order `alpha >= 1/2`, including the
support-aware Umegaki branch at `alpha = 1`, embedding a state by an isometry
cannot reduce its divergence below the divergence against the compressed
reference.  The proof completes `X |-> V^* X V` by a failure flag, applies
data processing, and removes the zero state block with the direct-sum mean
property [Tomamichel2015FiniteResources, apps.tex:193-215]. -/
theorem sandwichedRenyiPSDReferenceE_isometryImage_ge_compression
    (rho : State a) (V : ReferenceIsometry a b)
    {sigma : CMatrix b} (hSigma : sigma.PosDef)
    (alpha : Real) (hAlpha : 1 / 2 <= alpha) :
    sandwichedRenyiPSDReferenceE
        ((Channel.ofReferenceIsometry V).applyState rho) sigma
        hSigma.posSemidef alpha >=
      sandwichedRenyiPSDReferenceE rho
        (Matrix.conjTranspose V.matrix * sigma * V.matrix)
        (V.compression_posDef hSigma).posSemidef alpha := by
  let image := (Channel.ofReferenceIsometry V).applyState rho
  let hComp := V.compressionMap_traceNonincreasingCP
  let completion := V.compressionCompletion
  let inputState := image.rightZeroExtension
  let inputRef : CMatrix (Sum PUnit.{1} b) :=
    Matrix.fromBlocks (1 : CMatrix PUnit.{1}) 0 0 sigma
  have hInputRef : inputRef.PosDef := by
    exact Matrix.fromBlocks_diagonal_posDef Matrix.PosDef.one hSigma
  have hDPI :
      sandwichedRenyiPSDReferenceE inputState inputRef
          hInputRef.posSemidef alpha >=
        sandwichedRenyiPSDReferenceE (completion.applyState inputState)
          (completion.map inputRef)
          (completion.mapsPositive inputRef hInputRef.posSemidef) alpha := by
    by_cases hOne : alpha = 1
    · subst alpha
      rw [sandwichedRenyiPSDReferenceE_eq_traceLogE_of_eq_one _ _ rfl,
        sandwichedRenyiPSDReferenceE_eq_traceLogE_of_eq_one _ _ rfl]
      exact relativeEntropyPSDReferenceTraceLogE_dataProcessing_channel_ge
        inputState hInputRef.posSemidef completion
    · have hRange : (1 / 2 <= alpha ∧ alpha < 1) ∨ 1 < alpha := by
        rcases lt_or_gt_of_ne hOne with hLow | hHigh
        · exact Or.inl ⟨hAlpha, hLow⟩
        · exact Or.inr hHigh
      exact
        sandwichedRenyiPSDReferenceE_dataProcessing_channel_ge_of_half_le_lt_one_or_one_lt
          inputState hInputRef.posSemidef completion alpha hRange
  have hFailure : (V.compressionFailureReference sigma).PosDef :=
    V.compressionFailureReference_posDef hSigma
  have hCompression :
      (Matrix.conjTranspose V.matrix * sigma * V.matrix).PosDef :=
    V.compression_posDef hSigma
  calc
    sandwichedRenyiPSDReferenceE
        ((Channel.ofReferenceIsometry V).applyState rho) sigma
        hSigma.posSemidef alpha =
      sandwichedRenyiPSDReferenceE inputState inputRef
        hInputRef.posSemidef alpha := by
          symm
          exact sandwichedRenyiPSDReferenceE_rightZeroExtension
            image Matrix.PosDef.one hSigma alpha hAlpha
    _ >= sandwichedRenyiPSDReferenceE (completion.applyState inputState)
        (completion.map inputRef)
        (completion.mapsPositive inputRef hInputRef.posSemidef) alpha := hDPI
    _ = sandwichedRenyiPSDReferenceE rho
        (Matrix.conjTranspose V.matrix * sigma * V.matrix)
        hCompression.posSemidef alpha := by
          have hmean := sandwichedRenyiPSDReferenceE_rightZeroExtension
            rho hFailure hCompression alpha hAlpha
          simpa only [completion, inputState, inputRef, image,
            V.compressionCompletion_apply_imageState rho,
            V.compressionCompletion_map_reference sigma] using hmean

end State

end

end QIT
