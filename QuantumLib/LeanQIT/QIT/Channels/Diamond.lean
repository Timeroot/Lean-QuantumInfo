/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Channel
public import QIT.Classical.Bridge
public import QIT.Util.SDP.HermitianPSDTraceDuality
public import QIT.States.TraceNorm.PositivePart
public import QIT.States.TraceNorm.Variational
public import QIT.Util.BlockMatrix

/-!
# Source-shaped diamond trace distance for finite channels

This module supplies the finite-dimensional channel-difference and
diamond-distance-shaped API needed by the post-selection route.  The numerical
quantity is specialized to the finite-dimensional source statement: the
reference system is a copy of the input system, matching the CKR observation
that the supremum in the diamond norm is attained at input dimension.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x

noncomputable section

namespace MatrixMap

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

/-- Difference of two channel maps, as a linear map between matrix spaces. -/
def channelDifference (Φ Ψ : Channel a b) : MatrixMap a b :=
  Φ.map - Ψ.map

@[simp]
theorem channelDifference_apply (Φ Ψ : Channel a b) (X : CMatrix a) :
    channelDifference Φ Ψ X = Φ.map X - Ψ.map X :=
  rfl

/-- Normalized trace action of a linear matrix map on one input matrix. -/
def normalizedTraceAction (Δ : MatrixMap a b) (X : CMatrix a) : ℝ :=
  (1 / 2 : ℝ) * traceNorm (Δ X)

/-- Finite-ancilla normalized trace action of `Δ ⊗ id_r` on a state. -/
def ancillaNormalizedTraceAction (Δ : MatrixMap a b) (ω : State (Prod a r)) : ℝ :=
  normalizedTraceAction (kron Δ (Channel.idChannel r).map) ω.matrix

/-- A finite matrix map is trace nonincreasing on positive semidefinite inputs
when it never increases the real trace of a PSD matrix. -/
def IsTraceNonincreasing (Φ : MatrixMap a b) : Prop :=
  ∀ X : CMatrix a, X.PosSemidef → (Φ X).trace.re ≤ X.trace.re

omit [DecidableEq a] [DecidableEq b] in theorem krausAdjoint_posSemidef
    {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) {E : CMatrix b} (hE : E.PosSemidef) :
    (krausAdjoint K E).PosSemidef := by
  unfold krausAdjoint
  exact Matrix.posSemidef_sum Finset.univ fun k _ => by
    simpa [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      using hE.mul_mul_conjTranspose_same (Matrix.conjTranspose (K k))

/-- `krausAdjoint` of the unit is bounded by the unit for a trace-nonincreasing
Kraus map. -/
theorem krausAdjoint_one_le_of_traceNonincreasing
    {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ)
    (hTNI : IsTraceNonincreasing (ofKraus K)) :
    krausAdjoint K (1 : CMatrix b) ≤ 1 := by
  rw [Matrix.le_iff]
  refine (cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg ?_).2 ?_
  · exact Matrix.IsHermitian.sub Matrix.isHermitian_one
      (krausAdjoint_posSemidef K Matrix.PosSemidef.one).isHermitian
  · intro A hA
    have hle := hTNI A hA
    have hdual :
        (((ofKraus K) A) * (1 : CMatrix b)).trace =
          (A * krausAdjoint K (1 : CMatrix b)).trace :=
      ofKraus_trace_duality K A (1 : CMatrix b)
    rw [Matrix.mul_one] at hdual
    have htrace :
        ((A * ((1 : CMatrix a) - krausAdjoint K (1 : CMatrix b))).trace).re =
          A.trace.re - ((A * krausAdjoint K (1 : CMatrix b)).trace).re := by
      simp [Matrix.mul_sub, Matrix.trace_sub]
    rw [Matrix.trace_mul_comm]
    rw [htrace]
    rw [← hdual]
    exact sub_nonneg.mpr hle

/-- Minimal finite-dimensional trace-nonincreasing completely positive map
interface used by CKR extraction maps. -/
structure TraceNonincreasingCP (Φ : MatrixMap a b) : Prop where
  completelyPositive : IsCompletelyPositive Φ
  traceNonincreasing : IsTraceNonincreasing Φ

theorem TraceNonincreasingCP.mapsPositive {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) :
    ∀ X : CMatrix a, X.PosSemidef → (Φ X).PosSemidef :=
  isCompletelyPositive_mapsPositive Φ hΦ.completelyPositive

noncomputable def TraceNonincreasingCP.kraus {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) : (a × b) → Matrix b a ℂ :=
  Classical.choose (exists_kraus_of_choi_psd Φ hΦ.completelyPositive)

theorem TraceNonincreasingCP.ofKraus_kraus {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) :
    ofKraus hΦ.kraus = Φ :=
  (Classical.choose_spec (exists_kraus_of_choi_psd Φ hΦ.completelyPositive)).symm

theorem ofKraus_tracePreserving_of_krausAdjoint_one {κ : Type w} [Fintype κ]
    (K : κ → Matrix b a ℂ) (hK : krausAdjoint K (1 : CMatrix b) = 1) :
    IsTracePreserving (ofKraus K) := by
  intro X
  have hdual := ofKraus_trace_duality K X (1 : CMatrix b)
  rw [Matrix.mul_one] at hdual
  rw [hK, Matrix.mul_one] at hdual
  exact hdual

/-- Kraus-form matrix maps are completely positive. -/
theorem ofKraus_isCompletelyPositive {κ : Type*} [Fintype κ]
    (K : κ → Matrix b a ℂ) :
    IsCompletelyPositive (ofKraus K) := by
  rw [IsCompletelyPositive, choi_ofKraus]
  exact Matrix.posSemidef_sum Finset.univ fun k _ =>
    Matrix.posSemidef_vecMulVec_self_star _

variable (a b)

/-- Matrix-map form of tracing out the second tensor factor. -/
def partialTraceB : MatrixMap (Prod a b) a where
  toFun X := QIT.partialTraceB (a := a) (b := b) X
  map_add' X Y := by
    ext i j
    simp [QIT.partialTraceB, Finset.sum_add_distrib]
  map_smul' c X := by
    ext i j
    simp [QIT.partialTraceB, Finset.mul_sum]

/-- Matrix-map form of tracing out the first tensor factor. -/
def partialTraceA : MatrixMap (Prod a b) b where
  toFun X := QIT.partialTraceA (a := a) (b := b) X
  map_add' X Y := by
    ext i j
    simp [QIT.partialTraceA, Finset.sum_add_distrib]
  map_smul' c X := by
    ext i j
    simp [QIT.partialTraceA, Finset.mul_sum]

variable {a b}

private def partialTraceBKraus (k : b) : Matrix a (Prod a b) ℂ :=
  fun i x => if x = (i, k) then 1 else 0

private def partialTraceAKraus (k : a) : Matrix b (Prod a b) ℂ :=
  fun j x => if x = (k, j) then 1 else 0

private theorem ofKraus_partialTraceBKraus :
    ofKraus (partialTraceBKraus (a := a) (b := b)) = partialTraceB a b := by
  apply LinearMap.ext
  intro X
  ext i j
  simp only [ofKraus, partialTraceB, QIT.partialTraceB, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply]
  simp [partialTraceBKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_ite_eq']

private theorem ofKraus_partialTraceAKraus :
    ofKraus (partialTraceAKraus (a := a) (b := b)) = partialTraceA a b := by
  apply LinearMap.ext
  intro X
  ext i j
  simp only [ofKraus, partialTraceA, QIT.partialTraceA, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply]
  simp [partialTraceAKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_ite_eq']

/-- Tracing out the second tensor factor is trace-nonincreasing CP. -/
theorem partialTraceB_traceNonincreasingCP :
    TraceNonincreasingCP (partialTraceB a b) where
  completelyPositive := by
    rw [← ofKraus_partialTraceBKraus (a := a) (b := b)]
    exact ofKraus_isCompletelyPositive _
  traceNonincreasing := by
    intro X _hX
    change ((QIT.partialTraceB (a := a) (b := b) X).trace).re ≤ X.trace.re
    rw [QIT.partialTraceB_trace]

/-- Tracing out the first tensor factor is trace-nonincreasing CP. -/
theorem partialTraceA_traceNonincreasingCP :
    TraceNonincreasingCP (partialTraceA a b) where
  completelyPositive := by
    rw [← ofKraus_partialTraceAKraus (a := a) (b := b)]
    exact ofKraus_isCompletelyPositive _
  traceNonincreasing := by
    intro X _hX
    change ((QIT.partialTraceA (a := a) (b := b) X).trace).re ≤ X.trace.re
    rw [QIT.partialTraceA_trace]

@[simp]
theorem partialTraceB_apply (X : CMatrix (Prod a b)) :
    partialTraceB a b X = QIT.partialTraceB (a := a) (b := b) X :=
  rfl

@[simp]
theorem partialTraceA_apply (X : CMatrix (Prod a b)) :
    partialTraceA a b X = QIT.partialTraceA (a := a) (b := b) X :=
  rfl

noncomputable def TraceNonincreasingCP.lossEffect {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) : CMatrix a :=
  1 - krausAdjoint hΦ.kraus (1 : CMatrix b)

theorem TraceNonincreasingCP.lossEffect_posSemidef {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) :
    hΦ.lossEffect.PosSemidef := by
  classical
  let K := hΦ.kraus
  let A : CMatrix a := krausAdjoint K (1 : CMatrix b)
  have hApos : A.PosSemidef := by
    exact krausAdjoint_posSemidef K Matrix.PosSemidef.one
  have hHerm : (1 - A).IsHermitian :=
    Matrix.isHermitian_one.sub hApos.isHermitian
  rw [lossEffect]
  change (1 - A).PosSemidef
  rw [cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg hHerm]
  intro X hX
  have hKΦ : ofKraus K = Φ := by
    simpa [K] using hΦ.ofKraus_kraus
  have hdual :
      ((Φ X).trace).re = ((X * A).trace).re := by
    have h := ofKraus_trace_duality K X (1 : CMatrix b)
    rw [Matrix.mul_one] at h
    rw [hKΦ] at h
    simpa [A] using congrArg Complex.re h
  have htni := hΦ.traceNonincreasing X hX
  have htrace :
      (((1 - A) * X).trace).re = X.trace.re - ((X * A).trace).re := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul, Matrix.trace_mul_comm A X]
    simp
  linarith

noncomputable def TraceNonincreasingCP.hatCompletionKraus {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) :
    Sum (a × b) (Sum Unit a) → Matrix (Sum PUnit b) (Sum PUnit a) ℂ
  | Sum.inl k, Sum.inr y, Sum.inr x => hΦ.kraus k y x
  | Sum.inr (Sum.inl _), Sum.inl _, Sum.inl _ => 1
  | Sum.inr (Sum.inr l), Sum.inl _, Sum.inr x => psdSqrt hΦ.lossEffect l x
  | _, _, _ => 0

@[simp]
theorem TraceNonincreasingCP.hatCompletionKraus_original_fail_out {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) (k : a × b) (i : PUnit) (j : Sum PUnit a) :
    hΦ.hatCompletionKraus (Sum.inl k) (Sum.inl i) j = 0 := by
  cases j <;> rfl

@[simp]
theorem TraceNonincreasingCP.hatCompletionKraus_original_fail_in {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) (k : a × b) (i : b) (j : PUnit) :
    hΦ.hatCompletionKraus (Sum.inl k) (Sum.inr i) (Sum.inl j) = 0 :=
  rfl

@[simp]
theorem TraceNonincreasingCP.hatCompletionKraus_original_state_state {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) (k : a × b) (i : b) (j : a) :
    hΦ.hatCompletionKraus (Sum.inl k) (Sum.inr i) (Sum.inr j) =
      hΦ.kraus k i j :=
  rfl

@[simp]
theorem TraceNonincreasingCP.hatCompletionKraus_keep_fail_fail {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) (u : Unit) (i : PUnit) (j : PUnit) :
    hΦ.hatCompletionKraus (Sum.inr (Sum.inl u)) (Sum.inl i) (Sum.inl j) = 1 := by
  cases u
  cases i
  cases j
  rfl

@[simp]
theorem TraceNonincreasingCP.hatCompletionKraus_keep_fail_state {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) (u : Unit) (i : PUnit) (j : a) :
    hΦ.hatCompletionKraus (Sum.inr (Sum.inl u)) (Sum.inl i) (Sum.inr j) = 0 := by
  cases u
  cases i
  rfl

@[simp]
theorem TraceNonincreasingCP.hatCompletionKraus_keep_state_out {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) (u : Unit) (i : b) (j : Sum PUnit a) :
    hΦ.hatCompletionKraus (Sum.inr (Sum.inl u)) (Sum.inr i) j = 0 := by
  cases u
  cases j <;> rfl

@[simp]
theorem TraceNonincreasingCP.hatCompletionKraus_loss_fail_fail {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) (l : a) (i : PUnit) (j : PUnit) :
    hΦ.hatCompletionKraus (Sum.inr (Sum.inr l)) (Sum.inl i) (Sum.inl j) = 0 := by
  cases i
  cases j
  rfl

@[simp]
theorem TraceNonincreasingCP.hatCompletionKraus_loss_fail_state {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) (l : a) (i : PUnit) (j : a) :
    hΦ.hatCompletionKraus (Sum.inr (Sum.inr l)) (Sum.inl i) (Sum.inr j) =
      psdSqrt hΦ.lossEffect l j := by
  cases i
  rfl

@[simp]
theorem TraceNonincreasingCP.hatCompletionKraus_loss_state_out {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) (l : a) (i : b) (j : Sum PUnit a) :
    hΦ.hatCompletionKraus (Sum.inr (Sum.inr l)) (Sum.inr i) j = 0 := by
  cases j <;> rfl

theorem TraceNonincreasingCP.hatCompletionKraus_adjoint_one {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) :
    krausAdjoint hΦ.hatCompletionKraus (1 : CMatrix (Sum PUnit b)) = 1 := by
  classical
  ext x y
  cases x with
  | inl xi =>
      cases y with
      | inl yj =>
          cases xi
          cases yj
          simp [krausAdjoint, TraceNonincreasingCP.hatCompletionKraus,
            Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Fintype.sum_sum_type]
      | inr yj =>
          simp [krausAdjoint, TraceNonincreasingCP.hatCompletionKraus,
            Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Fintype.sum_sum_type]
  | inr xi =>
      cases y with
      | inl yj =>
          simp [krausAdjoint, TraceNonincreasingCP.hatCompletionKraus,
            Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Fintype.sum_sum_type]
      | inr yj =>
          have hsqrt :
              psdSqrt hΦ.lossEffect * psdSqrt hΦ.lossEffect =
                hΦ.lossEffect := by
            simpa using psdSqrt_mul_self_of_posSemidef hΦ.lossEffect_posSemidef
          have hentry :
              (∑ l : a, star (psdSqrt hΦ.lossEffect l xi) *
                  psdSqrt hΦ.lossEffect l yj) =
                hΦ.lossEffect xi yj := by
            have hHerm := psdSqrt_isHermitian hΦ.lossEffect
            calc
              (∑ l : a, star (psdSqrt hΦ.lossEffect l xi) *
                  psdSqrt hΦ.lossEffect l yj) =
                  ∑ l : a, psdSqrt hΦ.lossEffect xi l *
                    psdSqrt hΦ.lossEffect l yj := by
                    refine Finset.sum_congr rfl fun l _ => ?_
                    have hstar :
                        star (psdSqrt hΦ.lossEffect l xi) =
                          psdSqrt hΦ.lossEffect xi l := by
                      simpa [Matrix.conjTranspose_apply] using
                        congrFun (congrFun hHerm xi) l
                    rw [hstar]
                _ = (psdSqrt hΦ.lossEffect * psdSqrt hΦ.lossEffect) xi yj := by
                    simp [Matrix.mul_apply]
                _ = hΦ.lossEffect xi yj := by rw [hsqrt]
          have hbase :
              krausAdjoint hΦ.kraus (1 : CMatrix b) xi yj +
                  hΦ.lossEffect xi yj =
                (1 : CMatrix a) xi yj := by
            rw [TraceNonincreasingCP.lossEffect]
            simp [sub_eq_add_neg, add_comm, add_left_comm]
          have hentry' :
              (∑ x : a, (starRingEnd ℂ) (psdSqrt hΦ.lossEffect x xi) *
                  psdSqrt hΦ.lossEffect x yj) =
                hΦ.lossEffect xi yj := by
            simpa using hentry
          simpa [krausAdjoint, Matrix.one_apply, Matrix.sum_apply, Matrix.mul_apply,
            Matrix.conjTranspose_apply, hentry'] using hbase

noncomputable def TraceNonincreasingCP.hatCompletion {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) : Channel (Sum PUnit a) (Sum PUnit b) where
  map := ofKraus hΦ.hatCompletionKraus
  completelyPositive := by
    rw [IsCompletelyPositive, choi_ofKraus]
    exact Matrix.posSemidef_sum Finset.univ fun _ _ =>
      Matrix.posSemidef_vecMulVec_self_star _
  tracePreserving :=
    ofKraus_tracePreserving_of_krausAdjoint_one hΦ.hatCompletionKraus
      hΦ.hatCompletionKraus_adjoint_one
  mapsPositive := ofKraus_mapsPositive hΦ.hatCompletionKraus

theorem TraceNonincreasingCP.hatCompletion_apply_fromBlocks {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) (f : CMatrix PUnit) (X : CMatrix a) :
    hΦ.hatCompletion.map (Matrix.fromBlocks f 0 0 X) =
      Matrix.fromBlocks
        (fun i j : PUnit => f i j + (X * hΦ.lossEffect).trace)
        0 0 (Φ X) := by
  classical
  ext x y
  cases x with
  | inl xi =>
      cases y with
      | inl yj =>
          cases xi
          cases yj
          let S : CMatrix a := psdSqrt hΦ.lossEffect
          have hHerm : Matrix.conjTranspose S = S := by
            exact (psdSqrt_isHermitian hΦ.lossEffect).eq
          have hsqrt : S * S = hΦ.lossEffect := by
            simpa [S] using psdSqrt_mul_self_of_posSemidef hΦ.lossEffect_posSemidef
          have hloss :
              (∑ x : a, ∑ x_1 : a,
                  (∑ x_2 : a, psdSqrt hΦ.lossEffect x x_2 * X x_2 x_1) *
                    (starRingEnd ℂ) (psdSqrt hΦ.lossEffect x x_1)) =
                (X * hΦ.lossEffect).trace := by
            calc
              (∑ x : a, ∑ x_1 : a,
                  (∑ x_2 : a, psdSqrt hΦ.lossEffect x x_2 * X x_2 x_1) *
                    (starRingEnd ℂ) (psdSqrt hΦ.lossEffect x x_1)) =
                  (S * X * Matrix.conjTranspose S).trace := by
                    simp [S, Matrix.trace, Matrix.mul_apply,
                      Matrix.conjTranspose_apply, Finset.sum_mul]
              _ = (Matrix.conjTranspose S * (S * X)).trace := by
                    rw [Matrix.trace_mul_comm]
              _ = ((Matrix.conjTranspose S * S) * X).trace := by
                    rw [← Matrix.mul_assoc]
              _ = (X * (Matrix.conjTranspose S * S)).trace := by
                    rw [Matrix.trace_mul_comm]
              _ = (X * hΦ.lossEffect).trace := by
                    rw [hHerm, hsqrt]
          simpa [TraceNonincreasingCP.hatCompletion, MatrixMap.ofKraus,
            TraceNonincreasingCP.hatCompletionKraus, Matrix.sum_apply, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Fintype.sum_sum_type] using hloss
      | inr yj =>
          simp [TraceNonincreasingCP.hatCompletion, MatrixMap.ofKraus,
            TraceNonincreasingCP.hatCompletionKraus, Matrix.sum_apply, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Fintype.sum_sum_type]
  | inr xi =>
      cases y with
      | inl yj =>
          simp [TraceNonincreasingCP.hatCompletion, MatrixMap.ofKraus,
            TraceNonincreasingCP.hatCompletionKraus, Matrix.sum_apply, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Fintype.sum_sum_type]
      | inr yj =>
          calc
            (MatrixMap.ofKraus hΦ.hatCompletionKraus
                (Matrix.fromBlocks f 0 0 X)) (Sum.inr xi) (Sum.inr yj) =
                (MatrixMap.ofKraus hΦ.kraus X) xi yj := by
              simp [MatrixMap.ofKraus, TraceNonincreasingCP.hatCompletionKraus,
                Matrix.sum_apply, Matrix.conjTranspose_apply, Matrix.mul_apply,
                Fintype.sum_sum_type]
            _ = Φ X xi yj := by
              rw [hΦ.ofKraus_kraus]

/-- Trace-preserving CP maps are trace-nonincreasing CP maps. -/
theorem traceNonincreasingCP_of_tracePreserving {Φ : MatrixMap a b}
    (hCP : IsCompletelyPositive Φ) (hTP : IsTracePreserving Φ) :
    TraceNonincreasingCP Φ where
  completelyPositive := hCP
  traceNonincreasing := by
    intro X _hX
    rw [hTP X]

theorem kron_comp_apply {c : Type w} {d : Type x} {e : Type u} {f : Type v}
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
    (Φ₁ : MatrixMap a b) (Ψ₁ : MatrixMap c d)
    (Φ₂ : MatrixMap e a) (Ψ₂ : MatrixMap f c) (X : CMatrix (Prod e f)) :
    kron Φ₁ Ψ₁ ((kron Φ₂ Ψ₂) X) =
      kron (Φ₁.comp Φ₂) (Ψ₁.comp Ψ₂) X := by
  ext bd bd'
  rw [map_eq_sum_single (kron Φ₂ Ψ₂) X]
  simp_rw [map_sum]
  simp_rw [map_smul]
  simp only [Matrix.sum_apply]
  rw [map_eq_sum_single (kron (Φ₁.comp Φ₂) (Ψ₁.comp Ψ₂)) X]
  simp only [Matrix.sum_apply]
  change
    (∑ ef : Prod e f, ∑ ef' : Prod e f,
      (X ef ef' • (kron Φ₁ Ψ₁ ((kron Φ₂ Ψ₂) (Matrix.single ef ef' 1)))) bd bd') =
    (∑ ef : Prod e f, ∑ ef' : Prod e f,
      (X ef ef' • (kron (Φ₁.comp Φ₂) (Ψ₁.comp Ψ₂) (Matrix.single ef ef' 1))) bd bd')
  refine Finset.sum_congr rfl fun ef _ => ?_
  refine Finset.sum_congr rfl fun ef' _ => ?_
  simp only [Matrix.smul_apply]
  congr 1
  cases ef with
  | mk e0 f0 =>
  cases ef' with
  | mk e1 f1 =>
  rw [single_prod_eq_kronecker_single]
  rw [kron_apply_kronecker]
  rw [kron_apply_kronecker]
  rw [kron_apply_kronecker]
  rfl

/-- Slice formula for a matrix-map tensored with an identity channel.  The
`(b,r),(b',r')` entry of `(Φ ⊗ id)(X)` is obtained by applying `Φ` to the
`r,r'` reference slice of `X`. -/
theorem kron_idChannel_apply_slice {r : Type w} [Fintype r] [DecidableEq r]
    (Φ : MatrixMap a b) (X : CMatrix (Prod a r)) (br br' : Prod b r) :
    MatrixMap.kron Φ (Channel.idChannel r).map X br br' =
      Φ (fun i i' => X (i, br.2) (i', br'.2)) br.1 br'.1 := by
  classical
  rw [map_eq_sum_single Φ (fun i i' => X (i, br.2) (i', br'.2))]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  simp only [MatrixMap.kron, Channel.idChannel, MatrixMap.ofKraus, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one,
    Matrix.single]
  rw [Finset.sum_eq_single br.2]
  · rw [Finset.sum_eq_single br'.2]
    · simp
    · intro y _ hy
      simp [hy]
    · intro hnot
      simp at hnot
  · intro y _ hy
    have hy' : y ≠ br.2 := hy
    simp [hy']
  · intro hnot
    simp at hnot

/-- Slice formula for an identity channel tensored with a matrix-map.  The
`(a,d),(a',d')` entry of `(id ⊗ Φ)(X)` is obtained by applying `Φ` to the
`a,a'` input slice of `X`. -/
theorem kron_idChannel_left_apply_slice {c : Type w} {d : Type x}
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (Φ : MatrixMap c d) (X : CMatrix (Prod a c)) (ad ad' : Prod a d) :
    MatrixMap.kron (Channel.idChannel a).map Φ X ad ad' =
      Φ (fun j j' => X (ad.1, j) (ad'.1, j')) ad.2 ad'.2 := by
  classical
  rw [map_eq_sum_single (MatrixMap.kron (Channel.idChannel a).map Φ) X]
  rw [map_eq_sum_single Φ (fun j j' => X (ad.1, j) (ad'.1, j'))]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ ac : Prod a c, ∑ ac' : Prod a c,
      (X ac ac' •
        (MatrixMap.kron (Channel.idChannel a).map Φ
          (Matrix.single ac ac' (1 : Complex)))) ad ad') =
      ∑ ac : Prod a c, ∑ ac' : Prod a c,
        X ac ac' *
          ((if ac.1 = ad.1 ∧ ac'.1 = ad'.1 then (1 : Complex) else 0) *
            (Φ (Matrix.single ac.2 ac'.2 (1 : Complex)) ad.2 ad'.2)) := by
        refine Finset.sum_congr rfl fun ac _ => ?_
        refine Finset.sum_congr rfl fun ac' _ => ?_
        simp only [Matrix.smul_apply, smul_eq_mul]
        rw [single_prod_eq_kronecker_single]
        rw [MatrixMap.kron_apply_kronecker]
        simp [Channel.idChannel, MatrixMap.ofKraus, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.single]
    _ = ∑ j : c, ∑ j' : c,
        X (ad.1, j) (ad'.1, j') *
          (Φ (Matrix.single j j' (1 : Complex)) ad.2 ad'.2) := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single ad.1]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [Fintype.sum_prod_type]
          rw [Finset.sum_eq_single ad'.1]
          · simp
          · intro i' _ hi'
            apply Finset.sum_eq_zero
            intro j' _
            have hne : i' ≠ ad'.1 := hi'
            simp [hne]
          · intro hnot
            simp at hnot
        · intro i _ hi
          apply Finset.sum_eq_zero
          intro j _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_eq_zero
          intro i' _
          apply Finset.sum_eq_zero
          intro j' _
          have hne : i ≠ ad.1 := hi
          simp [hne]
        · intro hnot
          simp at hnot
    _ = ∑ j : c, ∑ j' : c,
        (X (ad.1, j) (ad'.1, j') •
          Φ (Matrix.single j j' (1 : Complex))) ad.2 ad'.2 := by
        simp [Matrix.smul_apply]

/-- A map on the right tensor factor commutes with tracing out the left factor. -/
theorem partialTraceA_kron_idChannel_left
    {c : Type w} {d : Type x} [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d]
    (Φ : MatrixMap c d) (X : CMatrix (Prod a c)) :
    QIT.partialTraceA (a := a) (b := d)
        (MatrixMap.kron (Channel.idChannel a).map Φ X) =
      Φ (QIT.partialTraceA (a := a) (b := c) X) := by
  ext j j'
  simp only [QIT.partialTraceA]
  have hpt :
      QIT.partialTraceA (a := a) (b := c) X =
        ∑ i : a, (fun x y => X (i, x) (i, y)) := by
    ext x y
    simp [QIT.partialTraceA]
  rw [hpt]
  have hmap :
      Φ (∑ i : a, (fun x y => X (i, x) (i, y))) =
        ∑ i : a, Φ (fun x y => X (i, x) (i, y)) := by
    rw [map_sum]
  have hmap_entry := congrFun (congrFun hmap j) j'
  calc
    (∑ i : a,
        MatrixMap.kron (Channel.idChannel a).map Φ X (i, j) (i, j')) =
        ∑ i : a, Φ (fun x y => X (i, x) (i, y)) j j' := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [MatrixMap.kron_idChannel_left_apply_slice]
    _ = (∑ i : a, Φ (fun x y => X (i, x) (i, y))) j j' := by
          simp only [Matrix.sum_apply]
    _ = Φ (∑ i : a, fun x y => X (i, x) (i, y)) j j' :=
          hmap_entry.symm

/-- A matrix map on the left/input factor commutes with an isometry acting on
the right/reference factor. -/
theorem kron_idChannel_apply_applyMatrixRight
    {r₁ : Type w} {r₂ : Type x}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    (Φ : MatrixMap a b) (V : ReferenceIsometry r₁ r₂)
    (X : CMatrix (Prod a r₁)) :
    MatrixMap.kron Φ (Channel.idChannel r₂).map (V.applyMatrixRight X) =
      V.applyMatrixRight (MatrixMap.kron Φ (Channel.idChannel r₁).map X) := by
  ext br br'
  rw [MatrixMap.kron_idChannel_apply_slice]
  have hslice :
      (fun i i' => V.applyMatrixRight X (i, br.2) (i', br'.2)) =
        ∑ y : r₁, ∑ x : r₁,
          (V.matrix br.2 x * star (V.matrix br'.2 y)) •
            (fun i i' => X (i, x) (i', y)) := by
    ext i i'
    simp [ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
      Matrix.mul_apply, Finset.sum_mul, mul_assoc, mul_comm]
  rw [hslice]
  have hmap :
      Φ (∑ y : r₁, ∑ x : r₁,
          (V.matrix br.2 x * star (V.matrix br'.2 y)) •
            (fun i i' => X (i, x) (i', y))) =
        ∑ y : r₁, ∑ x : r₁,
          (V.matrix br.2 x * star (V.matrix br'.2 y)) •
            Φ (fun i i' => X (i, x) (i', y)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact LinearMap.map_smul Φ (V.matrix br.2 x * star (V.matrix br'.2 y))
      (fun i i' => X (i, x) (i', y))
  have hmapEntry := congrFun (congrFun hmap br.1) br'.1
  calc
    Φ (∑ y : r₁, ∑ x : r₁,
        (V.matrix br.2 x * star (V.matrix br'.2 y)) •
          (fun i i' => X (i, x) (i', y))) br.1 br'.1
        = (∑ y : r₁, ∑ x : r₁,
            (V.matrix br.2 x * star (V.matrix br'.2 y)) •
              Φ (fun i i' => X (i, x) (i', y))) br.1 br'.1 := hmapEntry
    _ = V.applyMatrixRight (MatrixMap.kron Φ (Channel.idChannel r₁).map X) br br' := by
      simp [ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
        Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
        MatrixMap.kron_idChannel_apply_slice, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]

/-- A map on the target/right factor commutes with an isometry acting on the
left/reference factor. -/
theorem kron_idChannel_left_apply_applyMatrix
    {r₁ : Type w} {r₂ : Type x}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    (Φ : MatrixMap a b) (V : ReferenceIsometry r₁ r₂)
    (X : CMatrix (Prod r₁ a)) :
    MatrixMap.kron (Channel.idChannel r₂).map Φ (V.applyMatrix X) =
      V.applyMatrix (MatrixMap.kron (Channel.idChannel r₁).map Φ X) := by
  ext rb rb'
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  have hslice :
      (fun j j' => V.applyMatrix X (rb.1, j) (rb'.1, j')) =
        ∑ y : r₁, ∑ x : r₁,
          (V.matrix rb.1 x * star (V.matrix rb'.1 y)) •
            (fun j j' => X (x, j) (y, j')) := by
    ext j j'
    simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
      Matrix.mul_apply, Finset.sum_mul, mul_assoc, mul_comm]
  rw [hslice]
  have hmap :
      Φ (∑ y : r₁, ∑ x : r₁,
          (V.matrix rb.1 x * star (V.matrix rb'.1 y)) •
            (fun j j' => X (x, j) (y, j'))) =
        ∑ y : r₁, ∑ x : r₁,
          (V.matrix rb.1 x * star (V.matrix rb'.1 y)) •
            Φ (fun j j' => X (x, j) (y, j')) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact LinearMap.map_smul Φ (V.matrix rb.1 x * star (V.matrix rb'.1 y))
      (fun j j' => X (x, j) (y, j'))
  have hmapEntry := congrFun (congrFun hmap rb.2) rb'.2
  calc
    Φ (∑ y : r₁, ∑ x : r₁,
        (V.matrix rb.1 x * star (V.matrix rb'.1 y)) •
          (fun j j' => X (x, j) (y, j'))) rb.2 rb'.2
        = (∑ y : r₁, ∑ x : r₁,
            (V.matrix rb.1 x * star (V.matrix rb'.1 y)) •
              Φ (fun j j' => X (x, j) (y, j'))) rb.2 rb'.2 := hmapEntry
    _ = V.applyMatrix (MatrixMap.kron (Channel.idChannel r₁).map Φ X) rb rb' := by
      simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
        Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
        MatrixMap.kron_idChannel_left_apply_slice, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]

/-- Composition of two Kronecker-structured matrix maps acts by composing each
factor. -/
theorem kron_comp_apply_general
    {α β γ δ η θ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    [Fintype η] [DecidableEq η] [Fintype θ] [DecidableEq θ]
    (Φ₁ : MatrixMap α β) (Ψ₁ : MatrixMap γ δ)
    (Φ₂ : MatrixMap η α) (Ψ₂ : MatrixMap θ γ) (X : CMatrix (Prod η θ)) :
    kron Φ₁ Ψ₁ ((kron Φ₂ Ψ₂) X) =
      kron (Φ₁.comp Φ₂) (Ψ₁.comp Ψ₂) X := by
  ext bd bd'
  rw [map_eq_sum_single (kron Φ₂ Ψ₂) X]
  simp_rw [map_sum]
  simp_rw [map_smul]
  simp only [Matrix.sum_apply]
  rw [map_eq_sum_single (kron (Φ₁.comp Φ₂) (Ψ₁.comp Ψ₂)) X]
  simp only [Matrix.sum_apply]
  change
    (∑ ef : Prod η θ, ∑ ef' : Prod η θ,
      (X ef ef' • (kron Φ₁ Ψ₁ ((kron Φ₂ Ψ₂) (Matrix.single ef ef' 1)))) bd bd') =
    (∑ ef : Prod η θ, ∑ ef' : Prod η θ,
      (X ef ef' • (kron (Φ₁.comp Φ₂) (Ψ₁.comp Ψ₂) (Matrix.single ef ef' 1))) bd bd')
  refine Finset.sum_congr rfl fun ef _ => ?_
  refine Finset.sum_congr rfl fun ef' _ => ?_
  simp only [Matrix.smul_apply]
  congr 1
  cases ef with
  | mk e0 f0 =>
  cases ef' with
  | mk e1 f1 =>
  rw [single_prod_eq_kronecker_single]
  rw [kron_apply_kronecker]
  rw [kron_apply_kronecker]
  rw [kron_apply_kronecker]
  rfl

private theorem trace_kron_id_left_eq_trace_apply_partialTraceA
    {c : Type w} {d : Type x} [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d]
    (Φ : MatrixMap c d) (X : CMatrix (Prod a c)) :
    (MatrixMap.kron (Channel.idChannel a).map Φ X).trace =
      (Φ (QIT.partialTraceA (a := a) (b := c) X)).trace := by
  classical
  rw [trace_map_eq_sum_single (MatrixMap.kron (Channel.idChannel a).map Φ) X]
  rw [trace_map_eq_sum_single Φ (QIT.partialTraceA (a := a) (b := c) X)]
  calc
    (∑ ac : Prod a c, ∑ ac' : Prod a c,
        X ac ac' *
          (MatrixMap.kron (Channel.idChannel a).map Φ
            (Matrix.single ac ac' (1 : Complex))).trace) =
        ∑ ac : Prod a c, ∑ ac' : Prod a c,
          X ac ac' *
            ((if ac.1 = ac'.1 then (1 : Complex) else 0) *
              (Φ (Matrix.single ac.2 ac'.2 (1 : Complex))).trace) := by
          refine Finset.sum_congr rfl fun ac _ => ?_
          refine Finset.sum_congr rfl fun ac' _ => ?_
          rw [MatrixMap.trace_kron_single]
          rw [(Channel.idChannel a).tracePreserving]
          rw [trace_single_one]
    _ =
        ∑ j : c, ∑ j' : c,
          (QIT.partialTraceA (a := a) (b := c) X) j j' *
            (Φ (Matrix.single j j' (1 : Complex))).trace := by
          calc
            (∑ ac : Prod a c, ∑ ac' : Prod a c,
              X ac ac' *
                ((if ac.1 = ac'.1 then (1 : Complex) else 0) *
                  (Φ (Matrix.single ac.2 ac'.2 (1 : Complex))).trace)) =
              ∑ i : a, ∑ j : c, ∑ j' : c,
                X (i, j) (i, j') *
                  (Φ (Matrix.single j j' (1 : Complex))).trace := by
                rw [Fintype.sum_prod_type]
                refine Finset.sum_congr rfl fun i _ => ?_
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [Fintype.sum_prod_type]
                rw [Finset.sum_eq_single i]
                · simp
                · intro i' _ hi'
                  apply Finset.sum_eq_zero
                  intro j' _
                  have hne : i ≠ i' := hi'.symm
                  simp [hne]
                · intro hnot
                  simp at hnot
            _ = ∑ j : c, ∑ i : a, ∑ j' : c,
                X (i, j) (i, j') *
                  (Φ (Matrix.single j j' (1 : Complex))).trace := by
                rw [Finset.sum_comm]
            _ = ∑ j : c, ∑ j' : c, ∑ i : a,
                X (i, j) (i, j') *
                  (Φ (Matrix.single j j' (1 : Complex))).trace := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [Finset.sum_comm]
            _ = ∑ j : c, ∑ j' : c,
                (∑ i : a, X (i, j) (i, j')) *
                  (Φ (Matrix.single j j' (1 : Complex))).trace := by
                refine Finset.sum_congr rfl fun j _ => ?_
                refine Finset.sum_congr rfl fun j' _ => ?_
                rw [Finset.sum_mul]
            _ = ∑ j : c, ∑ j' : c,
                (QIT.partialTraceA (a := a) (b := c) X) j j' *
                  (Φ (Matrix.single j j' (1 : Complex))).trace := by
                simp [QIT.partialTraceA]

/-- Tensoring a trace-nonincreasing CP map on the right with an identity map on
the left is trace-nonincreasing CP. -/
theorem traceNonincreasingCP_id_kron
    {c : Type w} {d : Type x} [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d]
    {Φ : MatrixMap c d} (hΦ : TraceNonincreasingCP Φ) :
    TraceNonincreasingCP (MatrixMap.kron (Channel.idChannel a).map Φ) where
  completelyPositive :=
    MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map Φ
      (Channel.idChannel a).completelyPositive hΦ.completelyPositive
  traceNonincreasing := by
    intro X hX
    rw [trace_kron_id_left_eq_trace_apply_partialTraceA]
    have hpt : (QIT.partialTraceA (a := a) (b := c) X).PosSemidef :=
      partialTraceA_posSemidef hX
    have hle := hΦ.traceNonincreasing (QIT.partialTraceA (a := a) (b := c) X) hpt
    have htrace := partialTraceA_trace (a := a) (b := c) X
    linarith [congrArg Complex.re htrace]

private theorem trace_kron_id_right_eq_trace_apply_partialTraceB
    {c : Type w} {d : Type x} [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d]
    (Φ : MatrixMap c d) (X : CMatrix (Prod c a)) :
    (MatrixMap.kron Φ (Channel.idChannel a).map X).trace =
      (Φ (QIT.partialTraceB (a := c) (b := a) X)).trace := by
  classical
  rw [trace_map_eq_sum_single (MatrixMap.kron Φ (Channel.idChannel a).map) X]
  rw [trace_map_eq_sum_single Φ (QIT.partialTraceB (a := c) (b := a) X)]
  calc
    (∑ ca : Prod c a, ∑ ca' : Prod c a,
        X ca ca' *
          (MatrixMap.kron Φ (Channel.idChannel a).map
            (Matrix.single ca ca' (1 : Complex))).trace) =
        ∑ ca : Prod c a, ∑ ca' : Prod c a,
          X ca ca' *
            ((Φ (Matrix.single ca.1 ca'.1 (1 : Complex))).trace *
              (if ca.2 = ca'.2 then (1 : Complex) else 0)) := by
          refine Finset.sum_congr rfl fun ca _ => ?_
          refine Finset.sum_congr rfl fun ca' _ => ?_
          rw [MatrixMap.trace_kron_single]
          rw [(Channel.idChannel a).tracePreserving]
          rw [trace_single_one]
    _ =
        ∑ i : c, ∑ i' : c,
          (QIT.partialTraceB (a := c) (b := a) X) i i' *
            (Φ (Matrix.single i i' (1 : Complex))).trace := by
          calc
            (∑ ca : Prod c a, ∑ ca' : Prod c a,
              X ca ca' *
                ((Φ (Matrix.single ca.1 ca'.1 (1 : Complex))).trace *
                  (if ca.2 = ca'.2 then (1 : Complex) else 0))) =
              ∑ i : c, ∑ j : a, ∑ i' : c,
                X (i, j) (i', j) *
                  (Φ (Matrix.single i i' (1 : Complex))).trace := by
                rw [Fintype.sum_prod_type]
                refine Finset.sum_congr rfl fun i _ => ?_
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [Fintype.sum_prod_type]
                refine Finset.sum_congr rfl fun i' _ => ?_
                rw [Finset.sum_eq_single j]
                · simp
                · intro j' _ hj'
                  have hne : j ≠ j' := hj'.symm
                  simp [hne]
                · intro hnot
                  simp at hnot
            _ = ∑ i : c, ∑ i' : c, ∑ j : a,
                X (i, j) (i', j) *
                  (Φ (Matrix.single i i' (1 : Complex))).trace := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.sum_comm]
            _ = ∑ i : c, ∑ i' : c,
                (∑ j : a, X (i, j) (i', j)) *
                  (Φ (Matrix.single i i' (1 : Complex))).trace := by
                refine Finset.sum_congr rfl fun i _ => ?_
                refine Finset.sum_congr rfl fun i' _ => ?_
                rw [Finset.sum_mul]
            _ = ∑ i : c, ∑ i' : c,
                (QIT.partialTraceB (a := c) (b := a) X) i i' *
                  (Φ (Matrix.single i i' (1 : Complex))).trace := by
                simp [QIT.partialTraceB]

/-- Tensoring a trace-nonincreasing CP map on the left with an identity map on
the right is trace-nonincreasing CP. -/
theorem traceNonincreasingCP_kron_id
    {c : Type w} {d : Type x} [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d]
    {Φ : MatrixMap c d} (hΦ : TraceNonincreasingCP Φ) :
    TraceNonincreasingCP (MatrixMap.kron Φ (Channel.idChannel a).map) where
  completelyPositive :=
    MatrixMap.isCompletelyPositive_kron Φ (Channel.idChannel a).map
      hΦ.completelyPositive (Channel.idChannel a).completelyPositive
  traceNonincreasing := by
    intro X hX
    rw [trace_kron_id_right_eq_trace_apply_partialTraceB]
    have hpt : (QIT.partialTraceB (a := c) (b := a) X).PosSemidef :=
      partialTraceB_posSemidef hX
    have hle := hΦ.traceNonincreasing (QIT.partialTraceB (a := c) (b := a) X) hpt
    have htrace := partialTraceB_trace (a := c) (b := a) X
    linarith [congrArg Complex.re htrace]

private theorem traceNorm_sub_le_trace_add_of_posSemidef
    (A B : CMatrix a) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    traceNorm (A - B) ≤ A.trace.re + B.trace.re := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace (A - B)
  have hA_le : Complex.abs ((A * (U : CMatrix a)).trace) ≤ A.trace.re :=
    posSemidef_trace_mul_unitary_abs_le_trace_re A hA U
  have hB_le : Complex.abs ((B * (U : CMatrix a)).trace) ≤ B.trace.re :=
    posSemidef_trace_mul_unitary_abs_le_trace_re B hB U
  have htri :
      Complex.abs (((A - B) * (U : CMatrix a)).trace) ≤
        Complex.abs ((A * (U : CMatrix a)).trace) +
          Complex.abs ((B * (U : CMatrix a)).trace) := by
    rw [Matrix.sub_mul, Matrix.trace_sub]
    simpa [Complex.abs] using norm_sub_le ((A * (U : CMatrix a)).trace)
      ((B * (U : CMatrix a)).trace)
  calc
    traceNorm (A - B) = Complex.abs (((A - B) * (U : CMatrix a)).trace) := hU.symm
    _ ≤ Complex.abs ((A * (U : CMatrix a)).trace) +
          Complex.abs ((B * (U : CMatrix a)).trace) := htri
    _ ≤ A.trace.re + B.trace.re := add_le_add hA_le hB_le

private theorem negPart_trace_eq_posPart_trace_of_trace_zero (H : CMatrix a)
    (hH : H.IsHermitian) (htr : H.trace = 0) :
    (H⁻).trace.re = (H⁺).trace.re := by
  have hdecomp : H⁺ - H⁻ = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have htrace : (H⁺).trace - (H⁻).trace = 0 := by
    rw [← Matrix.trace_sub, hdecomp, htr]
  have hre := congrArg Complex.re htrace
  simp at hre
  linarith

/-- Trace-nonincreasing CP maps contract the trace norm of Hermitian trace-zero
inputs.  This is the finite-dimensional CKR extraction-map norm contraction
used by the post-selection route. -/
theorem traceNorm_apply_le_of_traceNonincreasingCP {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) {H : CMatrix a}
    (hH : H.IsHermitian) (htr : H.trace = 0) :
    traceNorm (Φ H) ≤ traceNorm H := by
  classical
  have hpos : H⁺.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg H)
  have hneg : H⁻.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)
  have hmap_pos : (Φ H⁺).PosSemidef := hΦ.mapsPositive H⁺ hpos
  have hmap_neg : (Φ H⁻).PosSemidef := hΦ.mapsPositive H⁻ hneg
  have hdecomp : H⁺ - H⁻ = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have hmap :
      Φ H = Φ H⁺ - Φ H⁻ := by
    calc
      Φ H = Φ (H⁺ - H⁻) := by rw [hdecomp]
      _ = Φ H⁺ - Φ H⁻ := by rw [map_sub]
  have htrace_le :
      (Φ H⁺).trace.re + (Φ H⁻).trace.re ≤
        (H⁺).trace.re + (H⁻).trace.re :=
    add_le_add (hΦ.traceNonincreasing H⁺ hpos)
      (hΦ.traceNonincreasing H⁻ hneg)
  have hneg_trace := negPart_trace_eq_posPart_trace_of_trace_zero H hH htr
  have hnormH := traceNorm_eq_two_posPart_trace_re_of_trace_zero H hH htr
  calc
    traceNorm (Φ H) = traceNorm (Φ H⁺ - Φ H⁻) := by rw [hmap]
    _ ≤ (Φ H⁺).trace.re + (Φ H⁻).trace.re :=
      traceNorm_sub_le_trace_add_of_posSemidef (Φ H⁺) (Φ H⁻) hmap_pos hmap_neg
    _ ≤ (H⁺).trace.re + (H⁻).trace.re := htrace_le
    _ = 2 * (H⁺).trace.re := by rw [hneg_trace]; ring
    _ = traceNorm H := hnormH.symm

/-- Normalized trace-action wrapper for trace-nonincreasing CP maps on
Hermitian trace-zero inputs. -/
theorem normalizedTraceAction_apply_le_of_traceNonincreasingCP {Φ : MatrixMap a b}
    (hΦ : TraceNonincreasingCP Φ) {H : CMatrix a}
    (hH : H.IsHermitian) (htr : H.trace = 0) :
    normalizedTraceAction Φ H ≤ (1 / 2 : ℝ) * traceNorm H := by
  unfold normalizedTraceAction
  exact mul_le_mul_of_nonneg_left
    (traceNorm_apply_le_of_traceNonincreasingCP hΦ hH htr) (by norm_num)

section BlockCompression

variable {ι : Type x} {β : Type w} [Fintype ι] [DecidableEq ι]
variable [Fintype β] [DecidableEq β]

/-- Compress a matrix on a classical-labelled system to the diagonal block
with label `i`.

This is the finite matrix-map version of applying the projection
`|i⟩⟨i| ⊗ I` and discarding the classical label. -/
def blockCompression (i : ι) : MatrixMap (Prod ι β) β where
  toFun X := fun x y => X (i, x) (i, y)
  map_add' X Y := by ext x y; rfl
  map_smul' c X := by ext x y; rfl

@[simp]
theorem blockCompression_apply (i : ι) (X : CMatrix (Prod ι β)) :
    blockCompression (β := β) i X = fun x y => X (i, x) (i, y) := rfl

private theorem choi_blockCompression (i : ι) :
    MatrixMap.choi (blockCompression (β := β) i) =
      Matrix.vecMulVec
        (fun x : Prod (Prod ι β) β =>
          if x.1.1 = i ∧ x.1.2 = x.2 then (1 : ℂ) else 0)
        (fun x : Prod (Prod ι β) β =>
          star (if x.1.1 = i ∧ x.1.2 = x.2 then (1 : ℂ) else 0)) := by
  ext x y
  rcases x with ⟨⟨xi, xb⟩, xo⟩
  rcases y with ⟨⟨yi, yb⟩, yo⟩
  simp [MatrixMap.choi, blockCompression, Matrix.single, Matrix.vecMulVec]
  by_cases hxi : xi = i <;> by_cases hxb : xb = xo <;>
    by_cases hyi : yi = i <;> by_cases hyb : yb = yo <;>
      simp [hxi, hxb, hyi, hyb]

theorem blockCompression_completelyPositive (i : ι) :
    IsCompletelyPositive (blockCompression (β := β) i) := by
  rw [MatrixMap.IsCompletelyPositive, choi_blockCompression]
  exact Matrix.posSemidef_vecMulVec_self_star _

private theorem blockCompression_trace_re_le (i : ι) {X : CMatrix (Prod ι β)}
    (hX : X.PosSemidef) :
    ((blockCompression (β := β) i X).trace).re ≤ X.trace.re := by
  simp only [blockCompression_apply, Matrix.trace]
  calc
    (∑ x : β, X (i, x) (i, x)).re = ∑ x : β, (X (i, x) (i, x)).re := by
      simp
    _ ≤ ∑ z : Prod ι β, (X z z).re := by
      rw [Fintype.sum_prod_type]
      exact Finset.single_le_sum (s := (Finset.univ : Finset ι))
        (f := fun j : ι => ∑ y : β, (X (j, y) (j, y)).re)
        (fun j _ => by
          exact Finset.sum_nonneg fun y _ =>
            (Complex.nonneg_iff.mp (hX.diag_nonneg (i := (j, y)))).1)
        (Finset.mem_univ i)
    _ = (∑ z : Prod ι β, X z z).re := by simp

/-- Classical diagonal-block compression is trace-nonincreasing completely
positive. -/
theorem blockCompression_traceNonincreasingCP (i : ι) :
    TraceNonincreasingCP (blockCompression (β := β) i) where
  completelyPositive := blockCompression_completelyPositive (β := β) i
  traceNonincreasing := by
    intro X hX
    exact blockCompression_trace_re_le (β := β) i hX

end BlockCompression

section SumInrCompression

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Compress a hat-extension matrix to its original-state success block.

For matrices on `Sum PUnit α`, this drops the one-dimensional failure block and
keeps the `Sum.inr` block indexed by `α`. -/
def sumInrCompression : MatrixMap (Sum PUnit.{u + 1} α) α where
  toFun X := fun x y => X (Sum.inr x) (Sum.inr y)
  map_add' X Y := by ext x y; rfl
  map_smul' c X := by ext x y; rfl

@[simp]
theorem sumInrCompression_apply (X : CMatrix (Sum PUnit.{u + 1} α)) :
    (sumInrCompression (α := α)) X = fun x y => X (Sum.inr x) (Sum.inr y) :=
  rfl

private theorem choi_sumInrCompression :
    MatrixMap.choi (sumInrCompression (α := α)) =
      Matrix.vecMulVec
        (fun x : Prod (Sum PUnit.{u + 1} α) α =>
          match x.1 with
          | Sum.inl _ => 0
          | Sum.inr i => if i = x.2 then (1 : ℂ) else 0)
        (fun x : Prod (Sum PUnit.{u + 1} α) α =>
          star
            (match x.1 with
            | Sum.inl _ => 0
            | Sum.inr i => if i = x.2 then (1 : ℂ) else 0)) := by
  ext x y
  rcases x with ⟨xi, xo⟩
  rcases y with ⟨yi, yo⟩
  cases xi with
  | inl xu =>
      cases yi with
      | inl yu => simp [MatrixMap.choi, sumInrCompression, Matrix.single, Matrix.vecMulVec]
      | inr yv => simp [MatrixMap.choi, sumInrCompression, Matrix.single, Matrix.vecMulVec]
  | inr xv =>
      cases yi with
      | inl yu => simp [MatrixMap.choi, sumInrCompression, Matrix.single, Matrix.vecMulVec]
      | inr yv =>
          by_cases hx : xv = xo <;> by_cases hy : yv = yo <;>
            simp [MatrixMap.choi, sumInrCompression, Matrix.single, Matrix.vecMulVec, hx, hy]

/-- Success-block compression is completely positive. -/
theorem sumInrCompression_completelyPositive :
    IsCompletelyPositive (sumInrCompression (α := α)) := by
  rw [MatrixMap.IsCompletelyPositive, choi_sumInrCompression]
  exact Matrix.posSemidef_vecMulVec_self_star _

private theorem sumInrCompression_trace_re_le {X : CMatrix (Sum PUnit.{u + 1} α)}
    (hX : X.PosSemidef) :
    (((sumInrCompression (α := α)) X).trace).re ≤ X.trace.re := by
  simp only [sumInrCompression_apply, Matrix.trace]
  have hfail_nonneg :
      0 ≤ (∑ u : PUnit, (X (Sum.inl u) (Sum.inl u)).re) := by
    exact Finset.sum_nonneg fun u _ =>
      (Complex.nonneg_iff.mp (hX.diag_nonneg (i := Sum.inl u))).1
  calc
    (∑ x : α, X (Sum.inr x) (Sum.inr x)).re =
        ∑ x : α, (X (Sum.inr x) (Sum.inr x)).re := by
          simp
    _ ≤ (∑ u : PUnit, (X (Sum.inl u) (Sum.inl u)).re) +
        ∑ x : α, (X (Sum.inr x) (Sum.inr x)).re := by
          linarith
    _ = (∑ z : Sum PUnit.{u + 1} α, (X z z).re) := by
          rw [Fintype.sum_sum_type]
    _ = (∑ z : Sum PUnit.{u + 1} α, X z z).re := by
          simp

/-- Success-block compression is trace-nonincreasing completely positive. -/
theorem sumInrCompression_traceNonincreasingCP :
    TraceNonincreasingCP (sumInrCompression (α := α)) where
  completelyPositive := sumInrCompression_completelyPositive (α := α)
  traceNonincreasing := by
    intro X hX
    exact sumInrCompression_trace_re_le (α := α) hX

end SumInrCompression

section SumInrBlockCompression

variable {extra : Type u} {α : Type v}
variable [Fintype extra] [DecidableEq extra] [Fintype α] [DecidableEq α]

/-- Compress a right-summand block from `Sum extra α` back to `α`.

This is the arbitrary-extra analogue of `sumInrCompression`, used for padding
arguments where the discarded summand is not just the one-dimensional
hat-extension failure branch. -/
def sumInrBlockCompression : MatrixMap (Sum extra α) α where
  toFun X := fun x y => X (Sum.inr x) (Sum.inr y)
  map_add' X Y := by ext x y; rfl
  map_smul' c X := by ext x y; rfl

@[simp]
theorem sumInrBlockCompression_apply (X : CMatrix (Sum extra α)) :
    (sumInrBlockCompression (extra := extra) (α := α)) X =
      fun x y => X (Sum.inr x) (Sum.inr y) :=
  rfl

private theorem choi_sumInrBlockCompression :
    MatrixMap.choi (sumInrBlockCompression (extra := extra) (α := α)) =
      Matrix.vecMulVec
        (fun x : Prod (Sum extra α) α =>
          match x.1 with
          | Sum.inl _ => 0
          | Sum.inr i => if i = x.2 then (1 : ℂ) else 0)
        (fun x : Prod (Sum extra α) α =>
          star
            (match x.1 with
            | Sum.inl _ => 0
            | Sum.inr i => if i = x.2 then (1 : ℂ) else 0)) := by
  ext x y
  rcases x with ⟨xi, xo⟩
  rcases y with ⟨yi, yo⟩
  cases xi with
  | inl xu =>
      cases yi with
      | inl yu =>
          simp [MatrixMap.choi, sumInrBlockCompression, Matrix.single, Matrix.vecMulVec]
      | inr yv =>
          simp [MatrixMap.choi, sumInrBlockCompression, Matrix.single, Matrix.vecMulVec]
  | inr xv =>
      cases yi with
      | inl yu =>
          simp [MatrixMap.choi, sumInrBlockCompression, Matrix.single, Matrix.vecMulVec]
      | inr yv =>
          by_cases hx : xv = xo <;> by_cases hy : yv = yo <;>
            simp [MatrixMap.choi, sumInrBlockCompression, Matrix.single, Matrix.vecMulVec, hx, hy]

/-- Arbitrary right-summand block compression is completely positive. -/
theorem sumInrBlockCompression_completelyPositive :
    IsCompletelyPositive (sumInrBlockCompression (extra := extra) (α := α)) := by
  rw [MatrixMap.IsCompletelyPositive, choi_sumInrBlockCompression]
  exact Matrix.posSemidef_vecMulVec_self_star _

private theorem sumInrBlockCompression_trace_re_le {X : CMatrix (Sum extra α)}
    (hX : X.PosSemidef) :
    (((sumInrBlockCompression (extra := extra) (α := α)) X).trace).re ≤ X.trace.re := by
  simp only [sumInrBlockCompression_apply, Matrix.trace]
  have hextra_nonneg :
      0 ≤ (∑ u : extra, (X (Sum.inl u) (Sum.inl u)).re) := by
    exact Finset.sum_nonneg fun u _ =>
      (Complex.nonneg_iff.mp (hX.diag_nonneg (i := Sum.inl u))).1
  calc
    (∑ x : α, X (Sum.inr x) (Sum.inr x)).re =
        ∑ x : α, (X (Sum.inr x) (Sum.inr x)).re := by
          simp
    _ ≤ (∑ u : extra, (X (Sum.inl u) (Sum.inl u)).re) +
        ∑ x : α, (X (Sum.inr x) (Sum.inr x)).re := by
          linarith
    _ = (∑ z : Sum extra α, (X z z).re) := by
          rw [Fintype.sum_sum_type]
    _ = (∑ z : Sum extra α, X z z).re := by
          simp

/-- Arbitrary right-summand block compression is trace-nonincreasing completely
positive. -/
theorem sumInrBlockCompression_traceNonincreasingCP :
    TraceNonincreasingCP (sumInrBlockCompression (extra := extra) (α := α)) where
  completelyPositive := sumInrBlockCompression_completelyPositive (extra := extra) (α := α)
  traceNonincreasing := by
    intro X hX
    exact sumInrBlockCompression_trace_re_le (extra := extra) (α := α) hX

end SumInrBlockCompression

section SumInrTraceDiscard

variable {r : Type u} {α : Type v} {β : Type w}
variable [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
variable [Fintype β] [DecidableEq β]

/-- Kraus operator for success-block extraction from a hatted bipartite target,
followed by tracing out the second success subsystem.

The input is indexed as `r × (PUnit ⊕ (α × β))`; the output keeps `α` and the
reference `r`.  The Kraus index is the discarded `β` coordinate. -/
def sumInrTraceDiscardKraus (k : β) :
    Matrix (Prod α r) (Prod r (Sum PUnit.{max v w + 1} (Prod α β))) ℂ :=
  fun out inp =>
    match inp.2 with
    | Sum.inl _ => 0
    | Sum.inr ab => if inp.1 = out.2 ∧ ab = (out.1, k) then 1 else 0

omit [Fintype r] [Fintype α] [Fintype β] in
private theorem sumInrTraceDiscardKraus_eq_zero_of_ne
    (k : β) (out : Prod α r)
    {inp : Prod r (Sum PUnit.{max v w + 1} (Prod α β))}
    (hneq : inp ≠ (out.2, Sum.inr (out.1, k))) :
    sumInrTraceDiscardKraus (r := r) (α := α) (β := β) k out inp = 0 := by
  classical
  rcases inp with ⟨i, s⟩
  cases s with
  | inl u => rfl
  | inr ab =>
      by_cases h : i = out.2 ∧ ab = (out.1, k)
      · exfalso
        exact hneq (by cases h.1; cases h.2; rfl)
      · simp [sumInrTraceDiscardKraus, h]

private theorem sumInrTraceDiscardKraus_mul_apply
    (k : β) (X : CMatrix (Prod r (Sum PUnit.{max v w + 1} (Prod α β))))
    (x y : Prod α r) :
    (sumInrTraceDiscardKraus (r := r) (α := α) (β := β) k * X *
      Matrix.conjTranspose
        (sumInrTraceDiscardKraus (r := r) (α := α) (β := β) k)) x y =
      X (x.2, Sum.inr (x.1, k)) (y.2, Sum.inr (y.1, k)) := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (y.2, Sum.inr (y.1, k))]
  · rw [Finset.sum_eq_single (x.2, Sum.inr (x.1, k))]
    · simp [sumInrTraceDiscardKraus]
    · intro z _ hz
      rw [sumInrTraceDiscardKraus_eq_zero_of_ne (r := r) (α := α) (β := β) k x hz]
      simp
    · simp
  · intro z _ hz
    rw [sumInrTraceDiscardKraus_eq_zero_of_ne (r := r) (α := α) (β := β) k y hz]
    simp
  · rw [Finset.sum_eq_single (x.2, Sum.inr (x.1, k))]
    · simp [sumInrTraceDiscardKraus]
    · intro z _ hz
      rw [sumInrTraceDiscardKraus_eq_zero_of_ne (r := r) (α := α) (β := β) k x hz]
      simp
    · simp

/-- Extract the success block from a hatted bipartite target and trace out the
second success subsystem. -/
def sumInrTraceDiscard :
    MatrixMap (Prod r (Sum PUnit.{max v w + 1} (Prod α β))) (Prod α r) where
  toFun X := fun x y =>
    ∑ k : β, X (x.2, Sum.inr (x.1, k)) (y.2, Sum.inr (y.1, k))
  map_add' X Y := by
    ext x y
    simp [Finset.sum_add_distrib]
  map_smul' c X := by
    ext x y
    simp [Finset.mul_sum]

@[simp]
theorem sumInrTraceDiscard_apply
    (X : CMatrix (Prod r (Sum PUnit.{max v w + 1} (Prod α β)))) :
    (sumInrTraceDiscard (r := r) (α := α) (β := β)) X =
      fun x y =>
        ∑ k : β, X (x.2, Sum.inr (x.1, k)) (y.2, Sum.inr (y.1, k)) := by
  rfl

private theorem sumInrTraceDiscard_eq_ofKraus :
    sumInrTraceDiscard (r := r) (α := α) (β := β) =
      MatrixMap.ofKraus (sumInrTraceDiscardKraus (r := r) (α := α) (β := β)) := by
  classical
  apply LinearMap.ext
  intro X
  ext x y
  simp only [sumInrTraceDiscard, MatrixMap.ofKraus, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply]
  simp [sumInrTraceDiscardKraus_mul_apply]

/-- Success-block trace-discard is completely positive. -/
theorem sumInrTraceDiscard_completelyPositive :
    IsCompletelyPositive (sumInrTraceDiscard (r := r) (α := α) (β := β)) := by
  rw [sumInrTraceDiscard_eq_ofKraus]
  exact MatrixMap.ofKraus_isCompletelyPositive
    (sumInrTraceDiscardKraus (r := r) (α := α) (β := β))

private theorem sumInrTraceDiscard_trace_re_le
    {X : CMatrix (Prod r (Sum PUnit.{max v w + 1} (Prod α β)))}
    (hX : X.PosSemidef) :
    (((sumInrTraceDiscard (r := r) (α := α) (β := β)) X).trace).re ≤
      X.trace.re := by
  classical
  simp only [sumInrTraceDiscard_apply, Matrix.trace]
  have hfail_nonneg :
      0 ≤ ∑ i : r, ∑ u : PUnit,
        (X (i, Sum.inl u) (i, Sum.inl u)).re := by
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun u _ =>
        (Complex.nonneg_iff.mp (hX.diag_nonneg (i := (i, Sum.inl u)))).1
  have hsuccess_re :
      (∑ x : Prod α r, ∑ k : β,
          X (x.2, Sum.inr (x.1, k)) (x.2, Sum.inr (x.1, k))).re =
        ∑ x : Prod α r, ∑ k : β,
          (X (x.2, Sum.inr (x.1, k)) (x.2, Sum.inr (x.1, k))).re := by
    simp
  have hsuccess_sum :
      (∑ x : Prod α r, ∑ k : β,
          (X (x.2, Sum.inr (x.1, k)) (x.2, Sum.inr (x.1, k))).re) =
        ∑ i : r, ∑ ab : Prod α β,
          (X (i, Sum.inr ab) (i, Sum.inr ab)).re := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
  have hfull_sum :
      (∑ z : Prod r (Sum PUnit.{max v w + 1} (Prod α β)), (X z z).re) =
        (∑ i : r, ∑ u : PUnit, (X (i, Sum.inl u) (i, Sum.inl u)).re) +
          ∑ i : r, ∑ ab : Prod α β,
            (X (i, Sum.inr ab) (i, Sum.inr ab)).re := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_sum_type]
    rw [Finset.sum_add_distrib]
  calc
    (∑ x : Prod α r, ∑ k : β,
        X (x.2, Sum.inr (x.1, k)) (x.2, Sum.inr (x.1, k))).re =
        ∑ x : Prod α r, ∑ k : β,
          (X (x.2, Sum.inr (x.1, k)) (x.2, Sum.inr (x.1, k))).re := hsuccess_re
    _ ≤
        (∑ i : r, ∑ u : PUnit, (X (i, Sum.inl u) (i, Sum.inl u)).re) +
        ∑ x : Prod α r, ∑ k : β,
          (X (x.2, Sum.inr (x.1, k)) (x.2, Sum.inr (x.1, k))).re := by
          linarith
    _ =
        ∑ z : Prod r (Sum PUnit.{max v w + 1} (Prod α β)), (X z z).re := by
          rw [hsuccess_sum, hfull_sum]
    _ = (∑ z : Prod r (Sum PUnit.{max v w + 1} (Prod α β)), X z z).re := by
          simp

/-- Success-block trace-discard is trace-nonincreasing completely positive. -/
theorem sumInrTraceDiscard_traceNonincreasingCP :
    TraceNonincreasingCP (sumInrTraceDiscard (r := r) (α := α) (β := β)) where
  completelyPositive := sumInrTraceDiscard_completelyPositive (r := r) (α := α) (β := β)
  traceNonincreasing := by
    intro X hX
    exact sumInrTraceDiscard_trace_re_le (r := r) (α := α) (β := β) hX

end SumInrTraceDiscard

/-- Kronecker product of matrix maps is linear in the left map. -/
theorem kron_sub_left (Φ Ψ : MatrixMap a b) (Γ : MatrixMap r r) :
    kron (Φ - Ψ) Γ = kron Φ Γ - kron Ψ Γ := by
  apply LinearMap.ext
  intro X
  ext br br'
  simp [kron, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem channelDifference_kron_id_apply_eq_output_sub
    (Φ Ψ : Channel a b) (ω : State (Prod a r)) :
    MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map ω.matrix =
      ((Φ.prod (Channel.idChannel r)).applyState ω).matrix -
        ((Ψ.prod (Channel.idChannel r)).applyState ω).matrix := by
  change MatrixMap.kron (Φ.map - Ψ.map) (Channel.idChannel r).map ω.matrix =
      MatrixMap.kron Φ.map (Channel.idChannel r).map ω.matrix -
        MatrixMap.kron Ψ.map (Channel.idChannel r).map ω.matrix
  rw [MatrixMap.kron_sub_left]
  rfl

theorem channelDifference_kron_id_apply_isHermitian
    (Φ Ψ : Channel a b) (ω : State (Prod a r)) :
    (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ)
      (Channel.idChannel r).map ω.matrix).IsHermitian := by
  rw [channelDifference_kron_id_apply_eq_output_sub]
  exact ((Φ.prod (Channel.idChannel r)).applyState ω).pos.isHermitian.sub
    ((Ψ.prod (Channel.idChannel r)).applyState ω).pos.isHermitian

theorem channelDifference_kron_id_apply_trace_eq_zero
    (Φ Ψ : Channel a b) (ω : State (Prod a r)) :
    (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ)
      (Channel.idChannel r).map ω.matrix).trace = 0 := by
  rw [channelDifference_kron_id_apply_eq_output_sub]
  rw [Matrix.trace_sub]
  rw [((Φ.prod (Channel.idChannel r)).applyState ω).trace_eq_one]
  rw [((Ψ.prod (Channel.idChannel r)).applyState ω).trace_eq_one]
  simp

/-- Rewriting helper for pure-state CKR reductions: applying a right-reference
isometry before a channel difference is the same as applying it after the
channel difference. -/
theorem channelDifference_kron_id_apply_applyPureVectorRight
    {r₁ : Type w} {r₂ : Type x}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    (Φ Ψ : Channel a b) (V : ReferenceIsometry r₁ r₂)
    (Ω : PureVector (Prod a r₁)) :
    MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r₂).map
        (V.applyPureVectorRight Ω).state.matrix =
      V.applyMatrixRight
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r₁).map
          Ω.state.matrix) := by
  rw [ReferenceIsometry.rankOne_applyPureVectorRight]
  rw [MatrixMap.kron_idChannel_apply_applyMatrixRight]

section ReferenceIsometryChannel

variable {r₁ : Type w} {r₂ : Type x}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

/-- The channel induced by an isometry on a finite reference system. -/
def ofReferenceIsometry (V : ReferenceIsometry r₁ r₂) : MatrixMap r₁ r₂ :=
  MatrixMap.ofKraus (fun _ : Unit => V.matrix)

@[simp]
theorem ofReferenceIsometry_apply (V : ReferenceIsometry r₁ r₂)
    (X : CMatrix r₁) :
    ofReferenceIsometry V X =
      V.matrix * X * Matrix.conjTranspose V.matrix := by
  simp [ofReferenceIsometry, MatrixMap.ofKraus]

theorem ofReferenceIsometry_ofInjective_single
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (i j : α) :
    ofReferenceIsometry (ReferenceIsometry.ofInjective f hf)
      (Matrix.single i j (1 : ℂ)) =
      Matrix.single (f i) (f j) (1 : ℂ) := by
  ext y y'
  rw [ofReferenceIsometry_apply]
  have hleft (k : α) :
      ((ReferenceIsometry.ofInjective f hf).matrix * Matrix.single i j (1 : ℂ)) y k =
        if k = j then (if y = f i then 1 else 0) else 0 := by
    rw [Matrix.mul_apply]
    by_cases hkj : k = j
    · subst k
      rw [Finset.sum_eq_single i]
      · simp [ReferenceIsometry.ofInjective]
      · intro x _ hx
        have hix : i ≠ x := fun h => hx h.symm
        simp [hix]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ i))
    · rw [Finset.sum_eq_zero]
      · simp [hkj]
      · intro x _
        have hjk : j ≠ k := fun h => hkj h.symm
        simp [hjk]
  rw [Matrix.mul_apply]
  simp_rw [hleft]
  by_cases hy' : y' = f j
  · rw [Finset.sum_eq_single j]
    · simp [hy', Matrix.conjTranspose, ReferenceIsometry.ofInjective,
        Matrix.single_apply, eq_comm]
    · intro k _ hk
      simp [hk]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ j))
  · rw [Finset.sum_eq_zero]
    · simp [hy', eq_comm]
    · intro k _
      by_cases hkj : k = j
      · subst k
        simp [hy', Matrix.conjTranspose, ReferenceIsometry.ofInjective]
      · simp [hkj]

theorem ofReferenceIsometry_isCompletelyPositive
    (V : ReferenceIsometry r₁ r₂) :
    IsCompletelyPositive (ofReferenceIsometry V) := by
  rw [ofReferenceIsometry, IsCompletelyPositive, choi_ofKraus]
  exact Matrix.posSemidef_sum Finset.univ (fun _ _ =>
    Matrix.posSemidef_vecMulVec_self_star
      (fun x : Prod r₁ r₂ => V.matrix x.2 x.1))

theorem ofReferenceIsometry_isTracePreserving
    (V : ReferenceIsometry r₁ r₂) :
    IsTracePreserving (ofReferenceIsometry V) := by
  intro X
  rw [ofReferenceIsometry_apply]
  exact V.trace_apply_block X

theorem ofReferenceIsometry_traceNonincreasingCP
    (V : ReferenceIsometry r₁ r₂) :
    TraceNonincreasingCP (ofReferenceIsometry V) :=
  traceNonincreasingCP_of_tracePreserving
    (ofReferenceIsometry_isCompletelyPositive V)
    (ofReferenceIsometry_isTracePreserving V)

theorem kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft
    (V : ReferenceIsometry r₁ r₂) (X : CMatrix (Prod r₁ a)) :
    MatrixMap.kron (ofReferenceIsometry V) (Channel.idChannel a).map X =
      V.applyMatrix X := by
  ext ra ra'
  rw [MatrixMap.kron_idChannel_apply_slice]
  change MatrixMap.ofReferenceIsometry V
      (ReferenceIsometry.targetBlock X ra.2 ra'.2) ra.1 ra'.1 =
    (V.matrix * ReferenceIsometry.targetBlock X ra.2 ra'.2 *
      Matrix.conjTranspose V.matrix) ra.1 ra'.1
  rw [MatrixMap.ofReferenceIsometry_apply]

theorem kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight
    (V : ReferenceIsometry r₁ r₂) (X : CMatrix (Prod a r₁)) :
    MatrixMap.kron (Channel.idChannel a).map (ofReferenceIsometry V) X =
      V.applyMatrixRight X := by
  ext x y
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  change ofReferenceIsometry V (ReferenceIsometry.rightBlock X x.1 y.1) x.2 y.2 =
    (V.matrix * ReferenceIsometry.rightBlock X x.1 y.1 *
      Matrix.conjTranspose V.matrix) x.2 y.2
  rw [ofReferenceIsometry_apply]

/-- A right-reference isometry does not increase the trace norm of Hermitian
trace-zero matrices.  This rectangular version is routed through the
trace-nonincreasing CP contraction for the isometry channel. -/
theorem traceNorm_applyMatrixRight_le_of_isHermitian_trace_zero
    (V : ReferenceIsometry r₁ r₂) {X : CMatrix (Prod a r₁)}
    (hX : X.IsHermitian) (htr : X.trace = 0) :
    traceNorm (V.applyMatrixRight X) ≤ traceNorm X := by
  rw [← kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight (a := a) V X]
  exact traceNorm_apply_le_of_traceNonincreasingCP
    (traceNonincreasingCP_id_kron
      (a := a) (hΦ := ofReferenceIsometry_traceNonincreasingCP V))
    hX htr

end ReferenceIsometryChannel

variable {κ : Type x} [Fintype κ]

/-- Scalar-output effect functional `X ↦ Tr(XE)`.

The Kraus form uses `sqrt(E)` so complete positivity is immediate when `E` is
positive semidefinite.  This is the finite matrix-map form of the extraction
functional used in CKR `extractpart` [ChristandlKoenigRenner2008Postselection,
christandl-koenig-renner-2008-postselection.tex:319-357]. -/
def traceEffectToUnit (E : CMatrix a) : MatrixMap a PUnit :=
  MatrixMap.ofKraus (fun k : a => fun (_ : PUnit) (i : a) => (psdSqrt E) k i)

private theorem traceEffectToUnit_krausAdjoint_one_of_posSemidef
    {E : CMatrix a} (hE : E.PosSemidef) :
    krausAdjoint (a := a) (b := PUnit)
      (fun k : a => fun (_ : PUnit) (i : a) => (psdSqrt E) k i)
      (1 : CMatrix PUnit) = E := by
  let K : a → Matrix PUnit a ℂ := fun k => fun (_ : PUnit) (i : a) =>
    (psdSqrt E) k i
  let S : CMatrix a := psdSqrt E
  have hSsq : S * S = E := by
    simpa [S] using psdSqrt_mul_self_of_posSemidef hE
  have hS : S.IsHermitian := by
    simpa [S] using psdSqrt_isHermitian E
  ext i j
  calc
    krausAdjoint K (1 : CMatrix PUnit) i j =
        ∑ k : a, star (S k i) * S k j := by
          simp [krausAdjoint, K, S, Matrix.sum_apply, Matrix.mul_apply]
    _ = ∑ k : a, S i k * S k j := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hstar : star (S k i) = S i k := by
            simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hS i) k
          simp [hstar]
    _ = (S * S) i j := by simp [Matrix.mul_apply]
    _ = E i j := by rw [hSsq]

theorem traceEffectToUnit_apply_of_posSemidef {E X : CMatrix a}
    (hE : E.PosSemidef) :
    traceEffectToUnit E X = fun _ _ : PUnit => (X * E).trace := by
  ext u v
  cases u
  cases v
  have hdual := ofKraus_trace_duality
    (a := a) (b := PUnit)
    (fun k : a => fun (_ : PUnit) (i : a) => (psdSqrt E) k i) X
    (1 : CMatrix PUnit)
  have hAdj := traceEffectToUnit_krausAdjoint_one_of_posSemidef (a := a) hE
  rw [traceEffectToUnit]
  have hleft :
      (((MatrixMap.ofKraus
          (fun k : a => fun (_ : PUnit) (i : a) => (psdSqrt E) k i)) X) *
          (1 : CMatrix PUnit)).trace =
        ((MatrixMap.ofKraus
          (fun k : a => fun (_ : PUnit) (i : a) => (psdSqrt E) k i)) X).trace := by
    rw [Matrix.mul_one]
  rw [hleft] at hdual
  rw [hAdj] at hdual
  simpa [Matrix.trace] using hdual

/-- Effect functionals are trace-nonincreasing CP when `0 ≤ E ≤ 1`. -/
theorem traceEffectToUnit_traceNonincreasingCP {E : CMatrix a}
    (hEpos : E.PosSemidef) (hEle : E ≤ 1) :
    TraceNonincreasingCP (traceEffectToUnit E) where
  completelyPositive := by
    rw [traceEffectToUnit, IsCompletelyPositive, choi_ofKraus]
    exact Matrix.posSemidef_sum Finset.univ fun k _ =>
      Matrix.posSemidef_vecMulVec_self_star _
  traceNonincreasing := by
    intro X hX
    rw [traceEffectToUnit_apply_of_posSemidef hEpos]
    have hcomp : (1 - E).PosSemidef := by
      rwa [← Matrix.le_iff]
    have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hX hcomp
    have hcalc :
        ((X * (1 - E)).trace).re = X.trace.re - ((X * E).trace).re := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one]
      simp
    have hle : ((X * E).trace).re ≤ X.trace.re := by
      linarith
    simpa [Matrix.trace] using hle

end MatrixMap

namespace ReferenceIsometry

variable {α : Type u} {β : Type v}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The basis permutation isometry induced by a finite equivalence. -/
def ofEquiv (e : α ≃ β) : ReferenceIsometry α β where
  matrix := fun y x => if y = e x then 1 else 0
  isometry := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.mul_apply, Matrix.conjTranspose]
    · have hji : j ≠ i := fun hji => h hji.symm
      simp [Matrix.mul_apply, Matrix.conjTranspose, h, hji]

end ReferenceIsometry

namespace Channel

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

/-- A chosen finite Kraus representation of a channel. -/
def kraus (Φ : Channel a b) : (Prod a b) → Matrix b a ℂ :=
  Classical.choose (MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive)

theorem map_eq_ofKraus (Φ : Channel a b) :
    Φ.map = MatrixMap.ofKraus (Φ.kraus) :=
  Classical.choose_spec (MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive)

/-- Heisenberg-picture pullback of an output effect along a channel. -/
def dualEffect (Φ : Channel a b) (E : CMatrix b) : CMatrix a :=
  MatrixMap.krausAdjoint Φ.kraus E

theorem applyState_dualEffect_trace
    (Φ : Channel a b) (ρ : State a) (E : CMatrix b) :
    (((Φ.applyState ρ).matrix * E).trace) =
      (ρ.matrix * Φ.dualEffect E).trace := by
  unfold dualEffect
  change ((Φ.map ρ.matrix) * E).trace =
    (ρ.matrix * MatrixMap.krausAdjoint Φ.kraus E).trace
  rw [Φ.map_eq_ofKraus]
  exact MatrixMap.ofKraus_trace_duality Φ.kraus ρ.matrix E

theorem dualEffect_posSemidef
    (Φ : Channel a b) {E : CMatrix b} (hE : E.PosSemidef) :
    (Φ.dualEffect E).PosSemidef := by
  exact MatrixMap.krausAdjoint_posSemidef Φ.kraus hE

theorem dualEffect_one_le (Φ : Channel a b) :
    Φ.dualEffect (1 : CMatrix b) ≤ 1 := by
  unfold dualEffect
  refine MatrixMap.krausAdjoint_one_le_of_traceNonincreasing Φ.kraus ?_
  intro X hX
  have hTNI :=
    (MatrixMap.traceNonincreasingCP_of_tracePreserving Φ.completelyPositive
      Φ.tracePreserving).traceNonincreasing X hX
  simpa [Φ.map_eq_ofKraus] using hTNI

theorem dualEffect_le_one_of_le_one
    (Φ : Channel a b) {E : CMatrix b} (hE : E ≤ 1) :
    Φ.dualEffect E ≤ 1 := by
  exact le_trans (MatrixMap.krausAdjoint_mono Φ.kraus hE) Φ.dualEffect_one_le

/-- The channel induced by a finite reference isometry. -/
def ofReferenceIsometry (V : ReferenceIsometry a b) : Channel a b where
  map := MatrixMap.ofReferenceIsometry V
  completelyPositive := MatrixMap.ofReferenceIsometry_isCompletelyPositive V
  tracePreserving := MatrixMap.ofReferenceIsometry_isTracePreserving V
  mapsPositive :=
    MatrixMap.isCompletelyPositive_mapsPositive (MatrixMap.ofReferenceIsometry V)
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)

@[simp]
theorem ofReferenceIsometry_map (V : ReferenceIsometry a b) :
    (Channel.ofReferenceIsometry V).map = MatrixMap.ofReferenceIsometry V :=
  rfl

/-- Applying a reference isometry on the left tensor factor to a product with the
identity channel acts by `ReferenceIsometry.applyMatrix`. -/
theorem ofReferenceIsometry_prod_id_applyState_matrix
    {r₁ : Type w} {r₂ : Type x}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) (ρ : State (Prod r₁ a)) :
    (((Channel.ofReferenceIsometry V).prod (Channel.idChannel a)).applyState ρ).matrix =
      V.applyMatrix ρ.matrix := by
  change MatrixMap.kron (Channel.ofReferenceIsometry V).map
      (Channel.idChannel a).map ρ.matrix = V.applyMatrix ρ.matrix
  rw [Channel.ofReferenceIsometry_map]
  exact MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft V ρ.matrix

/-- Relabel a finite channel system along a basis equivalence. -/
def reindex (e : a ≃ b) : Channel a b where
  map := MatrixMap.ofReferenceIsometry (ReferenceIsometry.ofEquiv e)
  completelyPositive :=
    MatrixMap.ofReferenceIsometry_isCompletelyPositive (ReferenceIsometry.ofEquiv e)
  tracePreserving :=
    MatrixMap.ofReferenceIsometry_isTracePreserving (ReferenceIsometry.ofEquiv e)
  mapsPositive :=
    MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.ofReferenceIsometry (ReferenceIsometry.ofEquiv e))
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive (ReferenceIsometry.ofEquiv e))

@[simp]
theorem reindex_applyState (e : a ≃ b) (ρ : State a) :
    (reindex e).applyState ρ = ρ.reindex e := by
  apply State.ext
  ext i j
  simp [Channel.applyState, reindex, MatrixMap.ofReferenceIsometry_apply,
    ReferenceIsometry.ofEquiv, State.reindex, Matrix.mul_apply]
  rw [Finset.sum_eq_single (e.symm j)]
  · rw [Finset.sum_eq_single (e.symm i)]
    · simp
    · intro x _ hx
      have hne : i ≠ e x := by
        intro hi
        apply hx
        simp [hi]
      simp [hne]
    · simp
  · intro x _ hx
    have hne : j ≠ e x := by
      intro hj
      apply hx
      simp [hj]
    simp [hne]
  · simp

/-- Channel form of tracing out the second tensor factor. -/
def traceOutRight (a : Type u) (b : Type v)
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    Channel (Prod a b) a where
  map := MatrixMap.partialTraceB a b
  completelyPositive :=
    (MatrixMap.partialTraceB_traceNonincreasingCP (a := a) (b := b)).completelyPositive
  tracePreserving := by
    intro X
    exact QIT.partialTraceB_trace (a := a) (b := b) X
  mapsPositive :=
    (MatrixMap.partialTraceB_traceNonincreasingCP (a := a) (b := b)).mapsPositive

/-- Channel form of tracing out the first tensor factor. -/
def traceOutLeft (a : Type u) (b : Type v)
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    Channel (Prod a b) b where
  map := MatrixMap.partialTraceA a b
  completelyPositive :=
    (MatrixMap.partialTraceA_traceNonincreasingCP (a := a) (b := b)).completelyPositive
  tracePreserving := by
    intro X
    exact QIT.partialTraceA_trace (a := a) (b := b) X
  mapsPositive :=
    (MatrixMap.partialTraceA_traceNonincreasingCP (a := a) (b := b)).mapsPositive

@[simp]
theorem traceOutRight_applyState (ρ : State (Prod a b)) :
    (traceOutRight a b).applyState ρ = ρ.marginalA := by
  apply State.ext
  rfl

@[simp]
theorem traceOutLeft_applyState (ρ : State (Prod a b)) :
    (traceOutLeft a b).applyState ρ = ρ.marginalB := by
  apply State.ext
  rfl

@[simp]
theorem traceOutLeft_map (X : CMatrix (Prod a b)) :
    (traceOutLeft a b).map X = QIT.partialTraceA (a := a) (b := b) X :=
  rfl

/-- Tracing out a left reference factor commutes with applying a channel on the
right tensor factor. -/
theorem traceOutLeft_prod_id_applyState_id_prod
    {p : Type u} {r : Type v} {a : Type w} {b : Type x}
    [Fintype p] [DecidableEq p] [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (N : Channel a b) (ρ : State (Prod (Prod p r) a)) :
    ((traceOutLeft p r).prod (Channel.idChannel b)).applyState
        (((Channel.idChannel (Prod p r)).prod N).applyState ρ) =
      ((Channel.idChannel r).prod N).applyState
        (((traceOutLeft p r).prod (Channel.idChannel a)).applyState ρ) := by
  apply State.ext
  change
    MatrixMap.kron (traceOutLeft p r).map
        (Channel.idChannel b).map
        (MatrixMap.kron (Channel.idChannel (Prod p r)).map N.map ρ.matrix) =
      MatrixMap.kron (Channel.idChannel r).map N.map
        (MatrixMap.kron (traceOutLeft p r).map
          (Channel.idChannel a).map ρ.matrix)
  have hleft₁ :
      (traceOutLeft p r).map.comp
          (Channel.idChannel (Prod p r)).map =
        (traceOutLeft p r).map := by
    ext X i j
    simp [Channel.idChannel, MatrixMap.ofKraus]
  have hleft₂ :
      (Channel.idChannel b).map.comp N.map = N.map := by
    ext X i j
    simp [Channel.idChannel, MatrixMap.ofKraus]
  have hright₁ :
      (Channel.idChannel r).map.comp (traceOutLeft p r).map =
        (traceOutLeft p r).map := by
    ext X i j
    simp [Channel.idChannel, MatrixMap.ofKraus]
  have hright₂ :
      N.map.comp (Channel.idChannel a).map = N.map := by
    ext X i j
    simp [Channel.idChannel, MatrixMap.ofKraus]
  calc
    MatrixMap.kron (traceOutLeft p r).map
        (Channel.idChannel b).map
        (MatrixMap.kron (Channel.idChannel (Prod p r)).map N.map ρ.matrix) =
      MatrixMap.kron
        ((traceOutLeft p r).map.comp
          (Channel.idChannel (Prod p r)).map)
        ((Channel.idChannel b).map.comp N.map) ρ.matrix := by
        exact MatrixMap.kron_comp_apply_general
          (traceOutLeft p r).map (Channel.idChannel b).map
          (Channel.idChannel (Prod p r)).map N.map ρ.matrix
    _ = MatrixMap.kron (traceOutLeft p r).map N.map ρ.matrix := by
        rw [hleft₁, hleft₂]
    _ = MatrixMap.kron
        ((Channel.idChannel r).map.comp (traceOutLeft p r).map)
        (N.map.comp (Channel.idChannel a).map) ρ.matrix := by
        rw [hright₁, hright₂]
    _ = MatrixMap.kron (Channel.idChannel r).map N.map
        (MatrixMap.kron (traceOutLeft p r).map
          (Channel.idChannel a).map ρ.matrix) := by
        exact (MatrixMap.kron_comp_apply_general
          (Channel.idChannel r).map N.map
          (traceOutLeft p r).map (Channel.idChannel a).map
          ρ.matrix).symm

/-- Channel form of discarding a finite system and retaining only its trace. -/
def traceToUnit (a : Type u) [Fintype a] [DecidableEq a] :
    Channel a PUnit.{u + 1} where
  map := MatrixMap.traceEffectToUnit (1 : CMatrix a)
  completelyPositive :=
    (MatrixMap.traceEffectToUnit_traceNonincreasingCP
      (a := a) Matrix.PosSemidef.one le_rfl).completelyPositive
  tracePreserving := by
    intro X
    rw [MatrixMap.traceEffectToUnit_apply_of_posSemidef Matrix.PosSemidef.one]
    rw [Matrix.mul_one]
    change (∑ _ : PUnit.{u + 1}, X.trace) = X.trace
    simp
  mapsPositive := by
    intro X hX
    exact (MatrixMap.traceEffectToUnit_traceNonincreasingCP
      (a := a) Matrix.PosSemidef.one le_rfl).mapsPositive X hX

/-- A replacer channel discards the input and prepares a fixed output state. -/
def replacer (τ : State b) : Channel a b :=
  (Channel.prepare (fun _ : PUnit.{u + 1} => τ)).comp (traceToUnit a)

@[simp]
theorem replacer_map (τ : State b) (X : CMatrix a) :
    (replacer (a := a) τ).map X = X.trace • τ.matrix := by
  ext i j
  simp [replacer, comp, traceToUnit, Channel.prepare_map,
    MatrixMap.traceEffectToUnit_apply_of_posSemidef Matrix.PosSemidef.one]

@[simp]
theorem replacer_applyState (τ : State b) (ρ : State a) :
    (replacer (a := a) τ).applyState ρ = τ := by
  apply State.ext
  simp [Channel.applyState, ρ.trace_eq_one]

/-- The map underlying a CPTP channel is trace-nonincreasing CP. -/
theorem traceNonincreasingCP_map (Φ : Channel a b) :
    MatrixMap.TraceNonincreasingCP Φ.map :=
  MatrixMap.traceNonincreasingCP_of_tracePreserving Φ.completelyPositive Φ.tracePreserving

theorem traceNonincreasingCP_kron_id (K : Channel b b) :
    MatrixMap.TraceNonincreasingCP (MatrixMap.kron K.map (Channel.idChannel r).map) := by
  simpa [Channel.prod] using traceNonincreasingCP_map (K.prod (Channel.idChannel r))

/-- CPTP channels contract normalized trace distance between finite states.

The proof uses only the trace-norm positive-part variational characterization:
pull back the output positive spectral projector along a Kraus representation
of the channel, observe that the pullback is again an effect, and compare with
the input positive part. -/
theorem normalizedTraceDistance_applyState_le
    (Φ : Channel a b) (ρ σ : State a) :
    (Φ.applyState ρ).normalizedTraceDistance (Φ.applyState σ) ≤
      ρ.normalizedTraceDistance σ := by
  classical
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd Φ.map Φ.completelyPositive
  let HIn : CMatrix a := ρ.matrix - σ.matrix
  let HOut : CMatrix b := (Φ.applyState ρ).matrix - (Φ.applyState σ).matrix
  let hHIn : HIn.IsHermitian := ρ.pos.isHermitian.sub σ.pos.isHermitian
  let hHOut : HOut.IsHermitian :=
    (Φ.applyState ρ).pos.isHermitian.sub (Φ.applyState σ).pos.isHermitian
  let P : CMatrix b := positiveSpectralProjector HOut hHOut
  have hPpos : P.PosSemidef := positiveSpectralProjector_posSemidef HOut hHOut
  have hPle : P ≤ 1 := positiveSpectralProjector_le_one HOut hHOut
  have hTPK : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact Φ.tracePreserving
  let E : CMatrix a := MatrixMap.krausAdjoint K P
  have hEeffect : E.PosSemidef ∧ E ≤ 1 := by
    simpa [E] using MatrixMap.krausAdjoint_effect_of_tracePreserving K hTPK hPpos hPle
  have hHOut_eq : HOut = MatrixMap.ofKraus K HIn := by
    simp [HOut, HIn, Channel.applyState, hK, map_sub]
  have hscore_out :
      ((HOut * P).trace).re = (HOut⁺).trace.re := by
    simpa [P] using positiveSpectralProjector_score_eq_posPart_trace HOut hHOut
  have hdual :
      ((HOut * P).trace).re = ((HIn * E).trace).re := by
    rw [hHOut_eq]
    simpa [E] using congrArg Complex.re (MatrixMap.ofKraus_trace_duality K HIn P)
  have hinput_bound :
      ((HIn * E).trace).re ≤ (HIn⁺).trace.re :=
    hermitian_trace_mul_effect_le_posPart_trace HIn E hHIn hEeffect.1 hEeffect.2
  rw [State.normalizedTraceDistance_eq_posPart_trace,
    State.normalizedTraceDistance_eq_posPart_trace]
  calc
    (HOut⁺).trace.re = ((HOut * P).trace).re := hscore_out.symm
    _ = ((HIn * E).trace).re := hdual
    _ ≤ (HIn⁺).trace.re := hinput_bound

/-- Finite-reference trace-distance bound for a pair of channels. -/
def AncillaTraceDistanceBound (Φ Ψ : Channel a b) (ε : ℝ) : Prop :=
  ∀ ω : State (Prod a r),
    ((Φ.prod (idChannel r)).applyState ω).normalizedTraceDistance
      ((Ψ.prod (idChannel r)).applyState ω) ≤ ε

/-- The finite-reference trace distance is the normalized trace action of the
channel-difference map tensored with the reference identity. -/
theorem ancillaChannelTraceDistance_eq_channelDifferenceAction
    (Φ Ψ : Channel a b) (ω : State (Prod a r)) :
    ((Φ.prod (idChannel r)).applyState ω).normalizedTraceDistance
      ((Ψ.prod (idChannel r)).applyState ω) =
        MatrixMap.ancillaNormalizedTraceAction
          (MatrixMap.channelDifference Φ Ψ) ω := by
  change
    (1 / 2 : ℝ) *
        traceNorm (((Φ.prod (idChannel r)).map ω.matrix) -
          ((Ψ.prod (idChannel r)).map ω.matrix)) =
      (1 / 2 : ℝ) *
        traceNorm ((MatrixMap.kron (MatrixMap.channelDifference Φ Ψ)
          (idChannel r).map) ω.matrix)
  congr 1
  change
    traceNorm (((MatrixMap.kron Φ.map (idChannel r).map) ω.matrix) -
        ((MatrixMap.kron Ψ.map (idChannel r).map) ω.matrix)) =
      traceNorm ((MatrixMap.kron (Φ.map - Ψ.map) (idChannel r).map) ω.matrix)
  rw [MatrixMap.kron_sub_left]
  rfl

/-- Source-shaped finite-dimensional diamond trace distance between channels.

The CKR post-selection source defines the diamond norm using an ancilla identity
and notes that, in finite dimension, the reference dimension may be chosen equal
to the input dimension.  This API records exactly that source-shaped numeric
quantity rather than a general Banach-space `cb` norm. -/
def diamondTraceDistance [Nonempty a] (Φ Ψ : Channel a b) : ℝ :=
  sSup (Set.range fun ω : State (Prod a a) =>
    ((Φ.prod (idChannel a)).applyState ω).normalizedTraceDistance
      ((Ψ.prod (idChannel a)).applyState ω))

private theorem state_prod_self_nonempty [Nonempty a] :
    Nonempty (State (Prod a a)) :=
  ⟨Classical.basisState (Classical.choice (inferInstance : Nonempty (Prod a a)))⟩

/-- A pointwise bound on the input-reference trace distance bounds the
source-shaped diamond trace distance. -/
theorem diamondTraceDistance_le_of_inputReferenceBound [Nonempty a]
    {Φ Ψ : Channel a b} {ε : ℝ}
    (h : ∀ ω : State (Prod a a),
      ((Φ.prod (idChannel a)).applyState ω).normalizedTraceDistance
        ((Ψ.prod (idChannel a)).applyState ω) ≤ ε) :
    diamondTraceDistance Φ Ψ ≤ ε := by
  unfold diamondTraceDistance
  haveI : Nonempty (State (Prod a a)) := state_prod_self_nonempty (a := a)
  exact csSup_le (Set.range_nonempty _) fun y hy => by
    rcases hy with ⟨ω, rfl⟩
    exact h ω

/-- A finite-ancilla bound for the input reference copy bounds the source-shaped
diamond trace distance. -/
theorem diamondTraceDistance_le_of_ancillaBound [Nonempty a]
    {Φ Ψ : Channel a b} {ε : ℝ}
    (h : AncillaTraceDistanceBound (a := a) (b := b) (r := a) Φ Ψ ε) :
    diamondTraceDistance Φ Ψ ≤ ε :=
  diamondTraceDistance_le_of_inputReferenceBound h

end Channel

end

namespace State

/-- A channel applied to the left subsystem (tensored with the identity on the
right) preserves the right marginal. Single shared home for this marginal
identity (previously duplicated in `HypothesisTesting.DPI` and
`Information.Renyi.RenyiDPI.ConditionalMeasurementSource`). -/
theorem marginalB_applyState_prod_id {a : Type u} {b : Type v} {c : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (ρ : State (Prod a b)) (D : Channel a c) :
    ((D.prod (Channel.idChannel b)).applyState ρ).marginalB = ρ.marginalB := by
  apply State.ext
  change partialTraceA (a := c) (b := b)
      (MatrixMap.kron D.map (Channel.idChannel b).map ρ.matrix) =
    partialTraceA (a := a) (b := b) ρ.matrix
  ext j j'
  simp only [partialTraceA]
  let S : CMatrix a := fun i i' => ρ.matrix (i, j) (i', j')
  have htrace :
      (D.map S).trace = S.trace :=
    D.tracePreserving S
  calc
    ∑ i : c, MatrixMap.kron D.map (Channel.idChannel b).map ρ.matrix (i, j) (i, j') =
        ∑ i : c, D.map S i i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simpa [S] using
            (MatrixMap.kron_idChannel_apply_slice (a := a) (b := c) (r := b)
              (Φ := D.map) (X := ρ.matrix) (br := (i, j)) (br' := (i, j')))
    _ = ∑ i : a, ρ.matrix (i, j) (i, j') := by
          simpa [S, Matrix.trace] using htrace

/-- A channel applied to the right subsystem (tensored with the identity on the
left) preserves the left marginal. -/
theorem marginalA_applyState_id_prod {a : Type u} {b : Type v} {c : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (ρ : State (Prod a b)) (D : Channel b c) :
    (((Channel.idChannel a).prod D).applyState ρ).marginalA = ρ.marginalA := by
  apply State.ext
  change partialTraceB (a := a) (b := c)
      (MatrixMap.kron (Channel.idChannel a).map D.map ρ.matrix) =
    partialTraceB (a := a) (b := b) ρ.matrix
  ext i i'
  simp only [partialTraceB]
  let S : CMatrix b := fun j j' => ρ.matrix (i, j) (i', j')
  have htrace :
      (D.map S).trace = S.trace :=
    D.tracePreserving S
  calc
    ∑ j : c, MatrixMap.kron (Channel.idChannel a).map D.map ρ.matrix (i, j) (i', j) =
        ∑ j : c, D.map S j j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simpa [S] using
            (MatrixMap.kron_idChannel_left_apply_slice (a := a)
              (Φ := D.map) (X := ρ.matrix) (ad := (i, j)) (ad' := (i', j)))
    _ = ∑ j : b, ρ.matrix (i, j) (i', j) := by
          simpa [S, Matrix.trace] using htrace

/-- The left marginal of a state transformed by a channel on the left factor
equals the channel applied to the left marginal. -/
theorem marginalA_applyState_prod_id {a : Type u} {b : Type v} {c : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (ρ : State (Prod a b)) (D : Channel a c) :
    ((D.prod (Channel.idChannel b)).applyState ρ).marginalA =
      D.applyState ρ.marginalA := by
  apply State.ext
  change partialTraceB (a := c) (b := b)
      (MatrixMap.kron D.map (Channel.idChannel b).map ρ.matrix) =
    D.map (partialTraceB (a := a) (b := b) ρ.matrix)
  ext i i'
  simp only [partialTraceB]
  let S : b → CMatrix a := fun j => fun x x' => ρ.matrix (x, j) (x', j)
  have hsum :
      (fun x x' => ∑ j : b, ρ.matrix (x, j) (x', j)) =
        ∑ j : b, S j := by
    ext x x'
    change (∑ j : b, ρ.matrix (x, j) (x', j)) =
      (∑ j : b, S j) x x'
    simp only [Matrix.sum_apply]
    rfl
  change (∑ j : b,
      MatrixMap.kron D.map (Channel.idChannel b).map ρ.matrix (i, j) (i', j)) =
    D.map (fun x x' => ∑ j : b, ρ.matrix (x, j) (x', j)) i i'
  rw [hsum, map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simpa [S] using
    (MatrixMap.kron_idChannel_apply_slice (a := a) (b := c) (r := b)
      (Φ := D.map) (X := ρ.matrix) (br := (i, j)) (br' := (i', j)))

end State

/-- Applying a trace-nonincreasing CP extraction map on a terminal reference
register and then dropping the unit output does not increase trace norm on
Hermitian trace-zero inputs. -/
theorem traceNorm_dropRightUnitMatrix_kron_id_le_of_traceNonincreasingCP
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {T : MatrixMap β PUnit} (hT : T.TraceNonincreasingCP)
    {H : CMatrix (Prod α β)} (hH : H.IsHermitian) (htr : H.trace = 0) :
    traceNorm
        (dropRightUnitMatrix
          ((MatrixMap.kron (Channel.idChannel α).map T) H)) ≤
      traceNorm H := by
  calc
    traceNorm
        (dropRightUnitMatrix
          ((MatrixMap.kron (Channel.idChannel α).map T) H)) ≤
        traceNorm ((MatrixMap.kron (Channel.idChannel α).map T) H) :=
          traceNorm_dropRightUnitMatrix_le _
    _ ≤ traceNorm H :=
          MatrixMap.traceNorm_apply_le_of_traceNonincreasingCP
            (MatrixMap.traceNonincreasingCP_id_kron (a := α) hT) hH htr

end QIT
