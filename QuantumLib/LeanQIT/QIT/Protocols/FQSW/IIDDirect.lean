/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.FQSW.IIDRates

/-!
# FQSW IID direct theorem

This file is a dependency-ordered leaf of `QIT.Protocols.FQSW`.  Declaration
names, namespaces, statements, and proof terms are preserved from the original
monolithic module.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z p u1 v1 w1

noncomputable section

local instance fqswIIDDirectCMatrixContinuousENorm {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) :=
  SeminormedAddGroup.toContinuousENorm

variable {a : Type u} {b : Type v} {r : Type w}
variable {q : Type x} {e : Type y} {et : Type z}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable [Fintype et] [DecidableEq et]

/-- Lift the compressed one-shot coordinates
`(A₁ × A₂) × B^typ × R^typ` into the full i.i.d. source coordinates
`A^n × B^n × R^n` using Alice's padded support lift and the Bob/reference
typical support inclusions. -/
def adhwFQSWIidCompressedSourceLiftMatrix
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    Matrix
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod (Prod (Prod q e) btyp) rtyp) ℂ :=
  Matrix.kronecker (Matrix.kronecker P.supportLiftMatrix B.supportIsometry.matrix)
    R.supportIsometry.matrix

/-- Lift the true simultaneous typical coordinates
`A^typ × B^typ × R^typ` into the full i.i.d. source coordinates
`A^n × B^n × R^n`. -/
def adhwFQSWIidTypicalSourceLiftMatrix
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    Matrix
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod (Prod atyp btyp) rtyp) ℂ :=
  Matrix.kronecker
    (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix)
    R.supportIsometry.matrix

/-- The compressed source lift has range equal to the simultaneous
`A^nB^nR^n` typical projector. -/
theorem adhwFQSWIidCompressedSourceLiftMatrix_mul_conjTranspose
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    let L := adhwFQSWIidCompressedSourceLiftMatrix P B R
    L * Matrix.conjTranspose L =
      adhwFQSWIidLiftProjectorTriple
        (a := a) (b := b) (r := r) n
        T.projectorA T.projectorB T.projectorR := by
  dsimp
  let LA : Matrix (TensorPower a n) (Prod q e) ℂ := P.supportLiftMatrix
  let LB : Matrix (TensorPower b n) btyp ℂ := B.supportIsometry.matrix
  let LR : Matrix (TensorPower r n) rtyp ℂ := R.supportIsometry.matrix
  have hA :
      LA * Matrix.conjTranspose LA =
        (adhwFQSWSystemAState ψ).typicalSubspaceProjector n T.typicalitySlack := by
    simpa [LA] using
      ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix_mul_conjTranspose P
  have hB :
      LB * Matrix.conjTranspose LB =
        (adhwFQSWSystemBState ψ).typicalSubspaceProjector n T.typicalitySlack := by
    simpa [LB] using B.supportIsometry_range_projector_eq
  have hR :
      LR * Matrix.conjTranspose LR =
        (adhwFQSWSystemRState ψ).typicalSubspaceProjector n T.typicalitySlack := by
    simpa [LR] using R.supportIsometry_range_projector_eq
  have hct_outer :
      Matrix.conjTranspose (Matrix.kronecker (Matrix.kronecker LA LB) LR) =
        Matrix.kronecker
          (Matrix.conjTranspose (Matrix.kronecker LA LB))
          (Matrix.conjTranspose LR) := by
    simpa [Matrix.kronecker] using
      Matrix.conjTranspose_kronecker (Matrix.kronecker LA LB) LR
  have hct_inner :
      Matrix.conjTranspose (Matrix.kronecker LA LB) =
        Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) := by
    simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker LA LB
  have hinner_mul :
      Matrix.kronecker LA LB *
          Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) =
        Matrix.kronecker (LA * Matrix.conjTranspose LA)
          (LB * Matrix.conjTranspose LB) := by
    simpa using
      (Matrix.mul_kronecker_mul
        LA (Matrix.conjTranspose LA) LB (Matrix.conjTranspose LB)).symm
  calc
    Matrix.kronecker (Matrix.kronecker LA LB) LR *
        Matrix.conjTranspose (Matrix.kronecker (Matrix.kronecker LA LB) LR) =
      Matrix.kronecker
        (Matrix.kronecker (LA * Matrix.conjTranspose LA)
          (LB * Matrix.conjTranspose LB))
        (LR * Matrix.conjTranspose LR) := by
        rw [hct_outer, hct_inner]
        calc
          Matrix.kronecker (Matrix.kronecker LA LB) LR *
              Matrix.kronecker
                (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
                (Matrix.conjTranspose LR) =
            Matrix.kronecker
              (Matrix.kronecker LA LB *
                Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
              (LR * Matrix.conjTranspose LR) := by
              exact
                (Matrix.mul_kronecker_mul
                  (Matrix.kronecker LA LB)
                  (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
                  LR (Matrix.conjTranspose LR)).symm
          _ =
            Matrix.kronecker
              (Matrix.kronecker (LA * Matrix.conjTranspose LA)
                (LB * Matrix.conjTranspose LB))
              (LR * Matrix.conjTranspose LR) := by
              exact congrArg
                (fun X => Matrix.kronecker X (LR * Matrix.conjTranspose LR))
                hinner_mul
    _ = Matrix.kronecker (Matrix.kronecker T.projectorA T.projectorB) T.projectorR := by
        rw [hA, hB, hR, ← T.projectorA_eq, ← T.projectorB_eq, ← T.projectorR_eq]

/-- The true typical-source lift has range equal to the simultaneous
`A^nB^nR^n` typical projector. -/
theorem adhwFQSWIidTypicalSourceLiftMatrix_mul_conjTranspose
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    let L0 := adhwFQSWIidTypicalSourceLiftMatrix P B R
    L0 * Matrix.conjTranspose L0 =
      adhwFQSWIidLiftProjectorTriple
        (a := a) (b := b) (r := r) n
        T.projectorA T.projectorB T.projectorR := by
  dsimp
  let LA : Matrix (TensorPower a n) atyp ℂ := P.supportIsometry.matrix
  let LB : Matrix (TensorPower b n) btyp ℂ := B.supportIsometry.matrix
  let LR : Matrix (TensorPower r n) rtyp ℂ := R.supportIsometry.matrix
  have hA :
      LA * Matrix.conjTranspose LA =
        (adhwFQSWSystemAState ψ).typicalSubspaceProjector n T.typicalitySlack := by
    simpa [LA] using P.supportIsometry_range_projector_eq
  have hB :
      LB * Matrix.conjTranspose LB =
        (adhwFQSWSystemBState ψ).typicalSubspaceProjector n T.typicalitySlack := by
    simpa [LB] using B.supportIsometry_range_projector_eq
  have hR :
      LR * Matrix.conjTranspose LR =
        (adhwFQSWSystemRState ψ).typicalSubspaceProjector n T.typicalitySlack := by
    simpa [LR] using R.supportIsometry_range_projector_eq
  have hct_outer :
      Matrix.conjTranspose (Matrix.kronecker (Matrix.kronecker LA LB) LR) =
        Matrix.kronecker
          (Matrix.conjTranspose (Matrix.kronecker LA LB))
          (Matrix.conjTranspose LR) := by
    simpa [Matrix.kronecker] using
      Matrix.conjTranspose_kronecker (Matrix.kronecker LA LB) LR
  have hct_inner :
      Matrix.conjTranspose (Matrix.kronecker LA LB) =
        Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) := by
    simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker LA LB
  have hinner_mul :
      Matrix.kronecker LA LB *
          Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) =
        Matrix.kronecker (LA * Matrix.conjTranspose LA)
          (LB * Matrix.conjTranspose LB) := by
    simpa using
      (Matrix.mul_kronecker_mul
        LA (Matrix.conjTranspose LA) LB (Matrix.conjTranspose LB)).symm
  calc
    Matrix.kronecker (Matrix.kronecker LA LB) LR *
        Matrix.conjTranspose (Matrix.kronecker (Matrix.kronecker LA LB) LR) =
      Matrix.kronecker
        (Matrix.kronecker (LA * Matrix.conjTranspose LA)
          (LB * Matrix.conjTranspose LB))
        (LR * Matrix.conjTranspose LR) := by
        rw [hct_outer, hct_inner]
        calc
          Matrix.kronecker (Matrix.kronecker LA LB) LR *
              Matrix.kronecker
                (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
                (Matrix.conjTranspose LR) =
            Matrix.kronecker
              (Matrix.kronecker LA LB *
                Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
              (LR * Matrix.conjTranspose LR) := by
              exact
                (Matrix.mul_kronecker_mul
                  (Matrix.kronecker LA LB)
                  (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
                  LR (Matrix.conjTranspose LR)).symm
          _ =
            Matrix.kronecker
              (Matrix.kronecker (LA * Matrix.conjTranspose LA)
                (LB * Matrix.conjTranspose LB))
              (LR * Matrix.conjTranspose LR) := by
              exact congrArg
                (fun X => Matrix.kronecker X (LR * Matrix.conjTranspose LR))
                hinner_mul
    _ = Matrix.kronecker (Matrix.kronecker T.projectorA T.projectorB) T.projectorR := by
        rw [hA, hB, hR, ← T.projectorA_eq, ← T.projectorB_eq, ← T.projectorR_eq]

/-- The compressed source lift's initial projection is exactly the padded
Alice typical-support projection, tensor the full Bob and reference typical
registers. -/
theorem adhwFQSWIidCompressedSourceLiftMatrix_conjTranspose_mul
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    let L := adhwFQSWIidCompressedSourceLiftMatrix P B R
    Matrix.conjTranspose L * L =
      Matrix.kronecker
        (Matrix.kronecker
          (P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix)
          (1 : CMatrix btyp))
        (1 : CMatrix rtyp) := by
  dsimp
  let LA : Matrix (TensorPower a n) (Prod q e) ℂ := P.supportLiftMatrix
  let LB : Matrix (TensorPower b n) btyp ℂ := B.supportIsometry.matrix
  let LR : Matrix (TensorPower r n) rtyp ℂ := R.supportIsometry.matrix
  have hA :
      Matrix.conjTranspose LA * LA =
        P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix := by
    simpa [LA] using
      ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix_conjTranspose_mul P
  have hB : Matrix.conjTranspose LB * LB = (1 : CMatrix btyp) := by
    simpa [LB] using B.supportIsometry.isometry
  have hR : Matrix.conjTranspose LR * LR = (1 : CMatrix rtyp) := by
    simpa [LR] using R.supportIsometry.isometry
  have hct_outer :
      Matrix.conjTranspose (Matrix.kronecker (Matrix.kronecker LA LB) LR) =
        Matrix.kronecker
          (Matrix.conjTranspose (Matrix.kronecker LA LB))
          (Matrix.conjTranspose LR) := by
    simpa [Matrix.kronecker] using
      Matrix.conjTranspose_kronecker (Matrix.kronecker LA LB) LR
  have hct_inner :
      Matrix.conjTranspose (Matrix.kronecker LA LB) =
        Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) := by
    simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker LA LB
  have hinner_mul :
      Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) *
          Matrix.kronecker LA LB =
        Matrix.kronecker (Matrix.conjTranspose LA * LA)
          (Matrix.conjTranspose LB * LB) := by
    simpa using
      (Matrix.mul_kronecker_mul
        (Matrix.conjTranspose LA) LA (Matrix.conjTranspose LB) LB).symm
  calc
    Matrix.conjTranspose (Matrix.kronecker (Matrix.kronecker LA LB) LR) *
        Matrix.kronecker (Matrix.kronecker LA LB) LR =
      Matrix.kronecker
        (Matrix.kronecker (Matrix.conjTranspose LA * LA)
          (Matrix.conjTranspose LB * LB))
        (Matrix.conjTranspose LR * LR) := by
        rw [hct_outer, hct_inner]
        calc
          Matrix.kronecker
              (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
              (Matrix.conjTranspose LR) *
              Matrix.kronecker (Matrix.kronecker LA LB) LR =
            Matrix.kronecker
              (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB) *
                Matrix.kronecker LA LB)
              (Matrix.conjTranspose LR * LR) := by
              exact
                (Matrix.mul_kronecker_mul
                  (Matrix.kronecker (Matrix.conjTranspose LA) (Matrix.conjTranspose LB))
                  (Matrix.kronecker LA LB)
                  (Matrix.conjTranspose LR) LR).symm
          _ =
            Matrix.kronecker
              (Matrix.kronecker (Matrix.conjTranspose LA * LA)
                (Matrix.conjTranspose LB * LB))
              (Matrix.conjTranspose LR * LR) := by
              exact congrArg
                (fun X => Matrix.kronecker X (Matrix.conjTranspose LR * LR))
                hinner_mul
    _ =
      Matrix.kronecker
        (Matrix.kronecker
          (P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix)
          (1 : CMatrix btyp))
        (1 : CMatrix rtyp) := by
        rw [hA, hB, hR]

/-- The compressed source lift is supported on its initial projection. -/
theorem adhwFQSWIidCompressedSourceLiftMatrix_mul_initialProjection
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    let L := adhwFQSWIidCompressedSourceLiftMatrix P B R
    let Q := Matrix.kronecker
      (Matrix.kronecker
        (P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix)
        (1 : CMatrix btyp))
      (1 : CMatrix rtyp)
    L * Q = L := by
  intro L Q
  let LA : Matrix (TensorPower a n) (Prod q e) ℂ := P.supportLiftMatrix
  let LB : Matrix (TensorPower b n) btyp ℂ := B.supportIsometry.matrix
  let LR : Matrix (TensorPower r n) rtyp ℂ := R.supportIsometry.matrix
  have hA :
      LA * (P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix) = LA := by
    simpa [LA] using
      ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix_mul_initialProjection P
  calc
    L * Q =
        Matrix.kronecker
          (Matrix.kronecker
            (LA * (P.isometry.matrix * Matrix.conjTranspose P.isometry.matrix))
            (LB * (1 : CMatrix btyp)))
          (LR * (1 : CMatrix rtyp)) := by
          dsimp [L, Q, adhwFQSWIidCompressedSourceLiftMatrix, LA, LB, LR]
          rw [← Matrix.mul_kronecker_mul]
          rw [← Matrix.mul_kronecker_mul]
    _ = L := by
          simp [hA, L, adhwFQSWIidCompressedSourceLiftMatrix, LA, LB, LR]

/-- The padded compressed lift factors through the true typical-source lift
followed by the adjoint of Alice's padded `A^typ ↪ A₁ × A₂` embedding. -/
theorem adhwFQSWIidCompressedSourceLiftMatrix_eq_typicalSourceLiftMatrix_mul_paddingAdjoint
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    let L := adhwFQSWIidCompressedSourceLiftMatrix P B R
    let L0 := adhwFQSWIidTypicalSourceLiftMatrix P B R
    let padAB : ReferenceIsometry (Prod atyp btyp) (Prod (Prod q e) btyp) :=
      P.isometry.prod (ReferenceIsometry.ofEquiv (Equiv.refl btyp))
    let K := Matrix.kronecker padAB.matrix (1 : CMatrix rtyp)
    L = L0 * Matrix.conjTranspose K := by
  intro L L0 padAB K
  have hpad :
      padAB.matrix =
        Matrix.kronecker P.isometry.matrix (1 : CMatrix btyp) := by
    ext i j
    simp [padAB, ReferenceIsometry.prod, ReferenceIsometry.ofEquiv,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
  have hpad_ct :
      Matrix.conjTranspose padAB.matrix =
        Matrix.kronecker (Matrix.conjTranspose P.isometry.matrix)
          (1 : CMatrix btyp) := by
    rw [hpad]
    simpa [Matrix.conjTranspose_one] using
      Matrix.conjTranspose_kronecker P.isometry.matrix (1 : CMatrix btyp)
  have hKct :
      Matrix.conjTranspose K =
        Matrix.kronecker
          (Matrix.kronecker (Matrix.conjTranspose P.isometry.matrix)
            (1 : CMatrix btyp))
          (1 : CMatrix rtyp) := by
    dsimp [K]
    rw [Matrix.conjTranspose_kronecker, hpad_ct]
    simp [Matrix.conjTranspose_one]
  symm
  calc
    L0 * Matrix.conjTranspose K =
        Matrix.kronecker
          (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix *
            Matrix.kronecker (Matrix.conjTranspose P.isometry.matrix)
              (1 : CMatrix btyp))
          (R.supportIsometry.matrix * (1 : CMatrix rtyp)) := by
          dsimp [L0, adhwFQSWIidTypicalSourceLiftMatrix]
          rw [hKct]
          exact
            (Matrix.mul_kronecker_mul
              (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix)
              (Matrix.kronecker (Matrix.conjTranspose P.isometry.matrix)
                (1 : CMatrix btyp))
              R.supportIsometry.matrix (1 : CMatrix rtyp)).symm
    _ =
        Matrix.kronecker
          (Matrix.kronecker
            (P.supportIsometry.matrix * Matrix.conjTranspose P.isometry.matrix)
            (B.supportIsometry.matrix * (1 : CMatrix btyp)))
          (R.supportIsometry.matrix * (1 : CMatrix rtyp)) := by
          exact congrArg
            (fun X => Matrix.kronecker X
              (R.supportIsometry.matrix * (1 : CMatrix rtyp)))
            (Matrix.mul_kronecker_mul
              P.supportIsometry.matrix (Matrix.conjTranspose P.isometry.matrix)
              B.supportIsometry.matrix (1 : CMatrix btyp)).symm
    _ = L := by
          simp [L, adhwFQSWIidCompressedSourceLiftMatrix,
            ADHWFQSWPaddedAtypEmbedding.supportLiftMatrix]

/-- Padding the true simultaneous-typical source preserves Alice's source
purity, and the typical lift identifies that purity with the normalized
simultaneous-typical source's `A` purity. -/
theorem adhwFQSWIidPaddedTypicalSource_a_purity_le
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp)
    (source0 : PureVector (Prod (Prod atyp btyp) rtyp))
    (hsource0_lift :
      (adhwFQSWIidTypicalSourceLiftMatrix P B R) *
          source0.state.matrix *
          Matrix.conjTranspose (adhwFQSWIidTypicalSourceLiftMatrix P B R) =
        T.normalizedTypicalSource.matrix) :
    let padAB : ReferenceIsometry (Prod atyp btyp) (Prod (Prod q e) btyp) :=
      P.isometry.prod (ReferenceIsometry.ofEquiv (Equiv.refl btyp))
    let source : PureVector (Prod (Prod (Prod q e) btyp) rtyp) :=
      padAB.applyPureVector source0
    adhwFQSWAPurity source ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))) := by
  intro padAB source
  let idB : ReferenceIsometry btyp btyp :=
    ReferenceIsometry.ofEquiv (Equiv.refl btyp)
  let ABtyp : ReferenceIsometry (Prod atyp btyp)
      (Prod (TensorPower a n) (TensorPower b n)) :=
    P.supportIsometry.prod B.supportIsometry
  have hT_AB :
      T.normalizedTypicalSource.marginalA.matrix =
        ABtyp.matrix * source0.state.marginalA.matrix *
          Matrix.conjTranspose ABtyp.matrix := by
    rw [State.marginalA_matrix, ← hsource0_lift]
    change partialTraceB (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n)
        (Matrix.kronecker ABtyp.matrix R.supportIsometry.matrix *
          source0.state.matrix *
          Matrix.conjTranspose
            (Matrix.kronecker ABtyp.matrix R.supportIsometry.matrix)) =
      ABtyp.matrix * source0.state.marginalA.matrix *
        Matrix.conjTranspose ABtyp.matrix
    rw [referenceIsometry_prod_partialTraceB_conj]
    rfl
  have hT_A :
      T.normalizedTypicalSource.marginalA.marginalA.matrix =
        P.supportIsometry.matrix * source0.state.marginalA.marginalA.matrix *
          Matrix.conjTranspose P.supportIsometry.matrix := by
    rw [State.marginalA_matrix, hT_AB]
    change partialTraceB (a := TensorPower a n) (b := TensorPower b n)
        (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix *
          source0.state.marginalA.matrix *
          Matrix.conjTranspose
            (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix)) =
      P.supportIsometry.matrix * source0.state.marginalA.marginalA.matrix *
        Matrix.conjTranspose P.supportIsometry.matrix
    rw [referenceIsometry_prod_partialTraceB_conj]
    rfl
  have hsource_AB :
      source.state.marginalA.matrix =
        padAB.matrix * source0.state.marginalA.matrix *
          Matrix.conjTranspose padAB.matrix := by
    simpa [source] using referenceIsometry_marginalA_applyPureVector padAB source0
  have hsource_A :
      source.state.marginalA.marginalA.matrix =
        P.isometry.matrix * source0.state.marginalA.marginalA.matrix *
          Matrix.conjTranspose P.isometry.matrix := by
    rw [State.marginalA_matrix, hsource_AB]
    change partialTraceB (a := Prod q e) (b := btyp)
        (Matrix.kronecker P.isometry.matrix idB.matrix *
          source0.state.marginalA.matrix *
          Matrix.conjTranspose (Matrix.kronecker P.isometry.matrix idB.matrix)) =
      P.isometry.matrix * source0.state.marginalA.marginalA.matrix *
        Matrix.conjTranspose P.isometry.matrix
    rw [referenceIsometry_prod_partialTraceB_conj]
    rfl
  have hsource_hs :
      hilbertSchmidtSq source.state.marginalA.marginalA.matrix =
        hilbertSchmidtSq source0.state.marginalA.marginalA.matrix := by
    rw [hsource_A]
    exact referenceIsometry_hilbertSchmidtSq_conj
      P.isometry source0.state.marginalA.marginalA
  have hT_hs :
      hilbertSchmidtSq T.normalizedTypicalSource.marginalA.marginalA.matrix =
        hilbertSchmidtSq source0.state.marginalA.marginalA.matrix := by
    rw [hT_A]
    exact referenceIsometry_hilbertSchmidtSq_conj
      P.supportIsometry source0.state.marginalA.marginalA
  rw [adhwFQSWAPurity, adhwFQSWARState_marginalA_eq_systemA,
    adhwFQSWSystemAState]
  rw [hsource_hs, ← hT_hs]
  exact T.purityA_le

/-- Padding the true simultaneous-typical source preserves Bob's source
purity, and the typical lift identifies that purity with the normalized
simultaneous-typical source's `B` purity. -/
theorem adhwFQSWIidPaddedTypicalSource_b_purity_le
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp)
    (source0 : PureVector (Prod (Prod atyp btyp) rtyp))
    (hsource0_lift :
      (adhwFQSWIidTypicalSourceLiftMatrix P B R) *
          source0.state.matrix *
          Matrix.conjTranspose (adhwFQSWIidTypicalSourceLiftMatrix P B R) =
        T.normalizedTypicalSource.matrix) :
    let padAB : ReferenceIsometry (Prod atyp btyp) (Prod (Prod q e) btyp) :=
      P.isometry.prod (ReferenceIsometry.ofEquiv (Equiv.refl btyp))
    let source : PureVector (Prod (Prod (Prod q e) btyp) rtyp) :=
      padAB.applyPureVector source0
    hilbertSchmidtSq source.state.marginalA.marginalB.matrix ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) := by
  intro padAB source
  let idB : ReferenceIsometry btyp btyp :=
    ReferenceIsometry.ofEquiv (Equiv.refl btyp)
  let ABtyp : ReferenceIsometry (Prod atyp btyp)
      (Prod (TensorPower a n) (TensorPower b n)) :=
    P.supportIsometry.prod B.supportIsometry
  have hT_AB :
      T.normalizedTypicalSource.marginalA.matrix =
        ABtyp.matrix * source0.state.marginalA.matrix *
          Matrix.conjTranspose ABtyp.matrix := by
    rw [State.marginalA_matrix, ← hsource0_lift]
    change partialTraceB (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n)
        (Matrix.kronecker ABtyp.matrix R.supportIsometry.matrix *
          source0.state.matrix *
          Matrix.conjTranspose
            (Matrix.kronecker ABtyp.matrix R.supportIsometry.matrix)) =
      ABtyp.matrix * source0.state.marginalA.matrix *
        Matrix.conjTranspose ABtyp.matrix
    rw [referenceIsometry_prod_partialTraceB_conj]
    rfl
  have hT_B :
      T.normalizedTypicalSource.marginalA.marginalB.matrix =
        B.supportIsometry.matrix * source0.state.marginalA.marginalB.matrix *
          Matrix.conjTranspose B.supportIsometry.matrix := by
    rw [State.marginalB_matrix, hT_AB]
    change partialTraceA (a := TensorPower a n) (b := TensorPower b n)
        (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix *
          source0.state.marginalA.matrix *
          Matrix.conjTranspose
            (Matrix.kronecker P.supportIsometry.matrix B.supportIsometry.matrix)) =
      B.supportIsometry.matrix * source0.state.marginalA.marginalB.matrix *
        Matrix.conjTranspose B.supportIsometry.matrix
    rw [referenceIsometry_prod_partialTraceA_conj]
    rfl
  have hsource_AB :
      source.state.marginalA.matrix =
        padAB.matrix * source0.state.marginalA.matrix *
          Matrix.conjTranspose padAB.matrix := by
    simpa [source] using referenceIsometry_marginalA_applyPureVector padAB source0
  have hsource_B :
      source.state.marginalA.marginalB.matrix =
        idB.matrix * source0.state.marginalA.marginalB.matrix *
          Matrix.conjTranspose idB.matrix := by
    rw [State.marginalB_matrix, hsource_AB]
    change partialTraceA (a := Prod q e) (b := btyp)
        (Matrix.kronecker P.isometry.matrix idB.matrix *
          source0.state.marginalA.matrix *
          Matrix.conjTranspose (Matrix.kronecker P.isometry.matrix idB.matrix)) =
      idB.matrix * source0.state.marginalA.marginalB.matrix *
        Matrix.conjTranspose idB.matrix
    rw [referenceIsometry_prod_partialTraceA_conj]
    rfl
  have hsource_hs :
      hilbertSchmidtSq source.state.marginalA.marginalB.matrix =
        hilbertSchmidtSq source0.state.marginalA.marginalB.matrix := by
    rw [hsource_B]
    exact referenceIsometry_hilbertSchmidtSq_conj
      idB source0.state.marginalA.marginalB
  have hT_hs :
      hilbertSchmidtSq T.normalizedTypicalSource.marginalA.marginalB.matrix =
        hilbertSchmidtSq source0.state.marginalA.marginalB.matrix := by
    rw [hT_B]
    exact referenceIsometry_hilbertSchmidtSq_conj
      B.supportIsometry source0.state.marginalA.marginalB
  rw [hsource_hs, ← hT_hs]
  exact T.purityB_le

/-- Padding the true simultaneous-typical source preserves the reference
purity, and the typical lift identifies that purity with the normalized
simultaneous-typical source's `R` purity. -/
theorem adhwFQSWIidPaddedTypicalSource_r_purity_le
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp)
    (source0 : PureVector (Prod (Prod atyp btyp) rtyp))
    (hsource0_lift :
      (adhwFQSWIidTypicalSourceLiftMatrix P B R) *
          source0.state.matrix *
          Matrix.conjTranspose (adhwFQSWIidTypicalSourceLiftMatrix P B R) =
        T.normalizedTypicalSource.matrix) :
    let padAB : ReferenceIsometry (Prod atyp btyp) (Prod (Prod q e) btyp) :=
      P.isometry.prod (ReferenceIsometry.ofEquiv (Equiv.refl btyp))
    let source : PureVector (Prod (Prod (Prod q e) btyp) rtyp) :=
      padAB.applyPureVector source0
    adhwFQSWRPurity source ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))) := by
  intro padAB source
  let ABtyp : ReferenceIsometry (Prod atyp btyp)
      (Prod (TensorPower a n) (TensorPower b n)) :=
    P.supportIsometry.prod B.supportIsometry
  have hT_R :
      T.normalizedTypicalSource.marginalB.matrix =
        R.supportIsometry.matrix * source0.state.marginalB.matrix *
          Matrix.conjTranspose R.supportIsometry.matrix := by
    rw [State.marginalB_matrix, ← hsource0_lift]
    change partialTraceA (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n)
        (Matrix.kronecker ABtyp.matrix R.supportIsometry.matrix *
          source0.state.matrix *
          Matrix.conjTranspose
            (Matrix.kronecker ABtyp.matrix R.supportIsometry.matrix)) =
      R.supportIsometry.matrix * source0.state.marginalB.matrix *
        Matrix.conjTranspose R.supportIsometry.matrix
    rw [referenceIsometry_prod_partialTraceA_conj]
    rfl
  have hsource_R :
      source.state.marginalB.matrix = source0.state.marginalB.matrix := by
    have hpur : source.Purifies source0.state.marginalB := by
      simpa [source] using
        padAB.applyPureVector_purifies (PureVector.purifies_marginalB source0)
    simpa [PureVector.purifies_iff, State.marginalB_matrix] using hpur
  have hsource_hs :
      hilbertSchmidtSq source.state.marginalB.matrix =
        hilbertSchmidtSq source0.state.marginalB.matrix := by
    rw [hsource_R]
  have hT_hs :
      hilbertSchmidtSq T.normalizedTypicalSource.marginalB.matrix =
        hilbertSchmidtSq source0.state.marginalB.matrix := by
    rw [hT_R]
    exact referenceIsometry_hilbertSchmidtSq_conj
      R.supportIsometry source0.state.marginalB
  rw [adhwFQSWRPurity, adhwFQSWARState_marginalB_eq_systemR,
    adhwFQSWSystemRState]
  rw [hsource_hs, ← hT_hs]
  exact T.purityR_le

/-- Narrow bridge from the compressed one-shot coordinates back to the
simultaneous typical source.  This records the concrete `A`/`B`/`R` typical
support isometries used by the next source-route slice without claiming the
final no-witness i.i.d. FQSW theorem. -/
structure ADHWFQSWIidCompressedSourceWitness
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e] where
  paddedAtypEmbedding :
    ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e
  typicalBobRegister :
    ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp
  typicalRefRegister :
    ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp
  unpaddedSource : PureVector (Prod (Prod atyp btyp) rtyp)
  source : PureVector (Prod (Prod (Prod q e) btyp) rtyp)
  source_eq_padded :
    source =
      (paddedAtypEmbedding.isometry.prod
        (ReferenceIsometry.ofEquiv (Equiv.refl btyp))).applyPureVector unpaddedSource
  unpadded_lifted_state_eq_normalizedTypicalSource :
    (let L := adhwFQSWIidTypicalSourceLiftMatrix
       paddedAtypEmbedding typicalBobRegister typicalRefRegister
     L * unpaddedSource.state.matrix * Matrix.conjTranspose L =
       T.normalizedTypicalSource.matrix)
  source_a_purity_le :
    adhwFQSWAPurity source ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ)))
  source_r_purity_le :
    adhwFQSWRPurity source ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ)))
  source_b_purity_le :
    hilbertSchmidtSq source.state.marginalA.marginalB.matrix ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ)))
  source_ar_purity_le :
    adhwFQSWARPurity source ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ)))
  lifted_state_eq_normalizedTypicalSource :
    (let L := adhwFQSWIidCompressedSourceLiftMatrix
       paddedAtypEmbedding typicalBobRegister typicalRefRegister
     L * source.state.matrix * Matrix.conjTranspose L =
       T.normalizedTypicalSource.matrix)
  source_traceNorm_le_original :
    traceNormDistance T.normalizedTypicalSource.matrix (adhwFQSWIidSourceState ψ n).matrix ≤ ε

namespace ADHWFQSWIidCompressedSourceWitness

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
variable {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
variable {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
variable {q : Type x} {e : Type y}
variable [Fintype atyp] [DecidableEq atyp] [Nonempty atyp]
variable [Fintype btyp] [DecidableEq btyp] [Nonempty btyp]
variable [Fintype rtyp] [DecidableEq rtyp]
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]

/-- Isometric lift from all three finite typical registers to the original IID
block registers. -/
def sourceLiftIsometry
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e) :
    ReferenceIsometry (Prod (Prod atyp btyp) rtyp)
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  (W.paddedAtypEmbedding.supportIsometry.prod
    W.typicalBobRegister.supportIsometry).prod
      W.typicalRefRegister.supportIsometry

/-- The finite-coordinate source decoded into the original IID systems. -/
def decodedSourceState
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e) :
    State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  (fqswChannelOfReferenceIsometry W.sourceLiftIsometry).applyState
    W.unpaddedSource.state

omit [Nonempty atyp] [Nonempty btyp] [Nonempty q] [Nonempty e] in
/-- Decoding the constructed finite-coordinate source recovers exactly the
normalized simultaneous-typical source. -/
theorem decodedSourceState_eq_normalizedTypicalSource
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e) :
    W.decodedSourceState = T.normalizedTypicalSource := by
  apply State.ext
  simpa [decodedSourceState, sourceLiftIsometry,
    fqswChannelOfReferenceIsometry, Channel.applyState,
    MatrixMap.ofReferenceIsometry_apply, PureVector.state,
    ReferenceIsometry.prod, adhwFQSWIidTypicalSourceLiftMatrix] using
      W.unpadded_lifted_state_eq_normalizedTypicalSource

/-- Decode all three finite one-shot source registers into the original IID
block registers using the physical Schumacher decoders. -/
def sourceDecoder
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e) :
    Channel (Prod (Prod (Prod q e) btyp) rtyp)
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  (W.paddedAtypEmbedding.physicalDecoder.prod
    W.typicalBobRegister.physicalDecoder).prod
      W.typicalRefRegister.physicalDecoder

/-- Embed the true finite typical registers into the padded one-shot source
registers, leaving the finite reference register unchanged. -/
def sourceEmbedding
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e) :
    Channel (Prod (Prod atyp btyp) rtyp)
      (Prod (Prod (Prod q e) btyp) rtyp) :=
  (fqswChannelOfReferenceIsometry
    (W.paddedAtypEmbedding.isometry.prod
      (ReferenceIsometry.ofEquiv (Equiv.refl btyp)))).prod
        (Channel.idChannel rtyp)

omit [Nonempty atyp] [Nonempty btyp] [Nonempty q] [Nonempty e] in
/-- The source embedding channel computes exactly the padded pure source stored
by the IID witness. -/
theorem sourceEmbedding_applyState_unpaddedSource
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e) :
    W.sourceEmbedding.applyState W.unpaddedSource.state = W.source.state := by
  unfold sourceEmbedding
  rw [fqswChannelOfReferenceIsometry_prod_id_applyState_pure]
  exact (congrArg PureVector.state W.source_eq_padded).symm

omit [Nonempty btyp] [Nonempty q] [Nonempty e] in
/-- Decoding immediately after the concrete padded source embedding is the
three-register typical-support lift. -/
theorem sourceDecoder_comp_sourceEmbedding
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e) :
    W.sourceDecoder.comp W.sourceEmbedding =
      fqswChannelOfReferenceIsometry W.sourceLiftIsometry := by
  unfold sourceDecoder sourceEmbedding sourceLiftIsometry
  rw [fqswChannelOfReferenceIsometry_prod,
    fqswChannelOfReferenceIsometry_ofEquiv_refl]
  rw [Channel.prod_comp_prod, Channel.prod_comp_prod]
  rw [W.paddedAtypEmbedding.physicalDecoder_comp_isometry_eq_supportIsometryChannel]
  rw [Channel.comp_idChannel, Channel.comp_idChannel]
  rw [W.typicalBobRegister.physicalDecoder_eq_supportIsometryChannel,
    W.typicalRefRegister.physicalDecoder_eq_supportIsometryChannel]
  rw [← fqswChannelOfReferenceIsometry_prod,
    ← fqswChannelOfReferenceIsometry_prod]

omit [Nonempty btyp] [Nonempty q] [Nonempty e] in
/-- The physical source decoder sends the padded one-shot source back to the
same decoded source state used by the normalized-typical bridge. -/
theorem sourceDecoder_applyState_source_eq_decodedSourceState
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e) :
    W.sourceDecoder.applyState W.source.state = W.decodedSourceState := by
  calc
    W.sourceDecoder.applyState W.source.state =
        W.sourceDecoder.applyState
          (W.sourceEmbedding.applyState W.unpaddedSource.state) := by
            rw [W.sourceEmbedding_applyState_unpaddedSource]
    _ = (W.sourceDecoder.comp W.sourceEmbedding).applyState W.unpaddedSource.state := by
          rw [Channel.applyState_comp]
    _ = W.decodedSourceState := by
          rw [W.sourceDecoder_comp_sourceEmbedding]
          rfl

/-- Decode the computed one-shot FQSW output back into the original IID source
registers while leaving the distilled ebit registers unchanged. -/
def decodedOneShotOutputState
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    State (Prod
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod e e)) :=
  (W.sourceDecoder.prod
    (Channel.idChannel (Prod e e))).applyState
      H.toOneShotProtocol.outputState

/-- Decode the source factor of the computed one-shot target while leaving its
maximally entangled pair unchanged. -/
def decodedOneShotTargetState
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    State (Prod
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod e e)) :=
  (W.sourceDecoder.prod
    (Channel.idChannel (Prod e e))).applyState
      H.toOneShotProtocol.targetState

/-- The source-shaped ideal target for the normalized simultaneous-typical
state and the ebit pairing selected by the one-shot theorem. -/
def normalizedTypicalTargetState
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    State (Prod
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod e e)) :=
  T.normalizedTypicalSource.prod
    (State.maximallyEntangled H.toOneShotProtocol.ebitPairing)

omit [Nonempty btyp] in
/-- Decoding the one-shot ideal target produces the normalized simultaneous-
typical source tensor the same canonical maximally entangled pair. -/
theorem decodedOneShotTargetState_eq_normalizedTypicalTargetState
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    W.decodedOneShotTargetState H = W.normalizedTypicalTargetState H := by
  have hid :
      (Channel.idChannel (Prod e e)).applyState
          (State.maximallyEntangled H.toOneShotProtocol.ebitPairing) =
        State.maximallyEntangled H.toOneShotProtocol.ebitPairing := by
    apply State.ext
    change (Channel.idChannel (Prod e e)).map
      (State.maximallyEntangled H.toOneShotProtocol.ebitPairing).matrix =
        (State.maximallyEntangled H.toOneShotProtocol.ebitPairing).matrix
    simp [Channel.idChannel, MatrixMap.ofKraus]
  unfold decodedOneShotTargetState normalizedTypicalTargetState
  rw [FQSWOneShotProtocol.targetState, Channel.applyState_prod]
  rw [hid]
  rw [W.sourceDecoder_applyState_source_eq_decodedSourceState,
    W.decodedSourceState_eq_normalizedTypicalSource]

/-- Alice's physical IID operation: Schumacher compression and padding,
followed by the concrete one-shot decoupling isometry selected by ADHW. -/
def physicalAliceOperation
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    Channel (TensorPower a n) (Prod q e) :=
  (fqswChannelOfReferenceIsometry H.toOneShotProtocol.aliceIsometry).comp
    W.paddedAtypEmbedding.physicalEncoder

/-- Bob's physical IID operation: compress `B^n`, apply the concrete one-shot
Uhlmann decoder, and decode both transferred typical systems back into the
original `A^n B^n` registers. -/
def physicalBobOperation
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    Channel (Prod q (TensorPower b n))
      (Prod (Prod (TensorPower a n) (TensorPower b n)) e) :=
  let pre : Channel (Prod q (TensorPower b n)) (Prod q btyp) :=
    (Channel.idChannel q).prod W.typicalBobRegister.physicalEncoder
  let oneShot : Channel (Prod q btyp) (Prod (Prod (Prod q e) btyp) e) :=
    fqswChannelOfReferenceIsometry H.toOneShotProtocol.bobIsometry
  let post : Channel (Prod (Prod (Prod q e) btyp) e)
      (Prod (Prod (TensorPower a n) (TensorPower b n)) e) :=
    (W.paddedAtypEmbedding.physicalDecoder.prod
      W.typicalBobRegister.physicalDecoder).prod (Channel.idChannel e)
  post.comp (oneShot.comp pre)

/-- The source-route data determines an actual block protocol on the original
IID registers; no preprocessing channel or semantic output field is supplied. -/
def toFQSWBlockProtocol
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    FQSWBlockProtocol ψ n q e e where
  aliceOperation := W.physicalAliceOperation H
  bobOperation := W.physicalBobOperation H
  ebitPairing := H.toOneShotProtocol.ebitPairing


private theorem idChannel_prod
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta] :
    (Channel.idChannel alpha).prod (Channel.idChannel beta) =
      Channel.idChannel (Prod alpha beta) := by
  rw [Channel.mk.injEq]
  apply LinearMap.ext
  intro X
  ext i j
  change MatrixMap.kron (Channel.idChannel alpha).map
      (Channel.idChannel beta).map X i j =
    (Channel.idChannel (Prod alpha beta)).map X i j
  rw [MatrixMap.kron_idChannel_apply_slice]
  simp [Channel.idChannel, MatrixMap.ofKraus]

/-- The channel pipeline computed by the finite-coordinate one-shot protocol. -/
private def oneShotOutputChannel
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    Channel (Prod (Prod (Prod q e) btyp) rtyp)
      (Prod (Prod (Prod (Prod q e) btyp) rtyp) (Prod e e)) :=
  let sourceRegroup :=
    Channel.reindex (fqswSourceToAliceInputEquiv (Prod q e) btyp rtyp)
  let alice :=
    (fqswChannelOfReferenceIsometry H.toOneShotProtocol.aliceIsometry).prod
      (Channel.idChannel (Prod btyp rtyp))
  let bobRegroup :=
    Channel.reindex (fqswAliceOutputToBobInputEquiv q e btyp rtyp)
  let bob :=
    (fqswChannelOfReferenceIsometry H.toOneShotProtocol.bobIsometry).prod
      (Channel.idChannel (Prod rtyp e))
  let finalRegroup :=
    Channel.reindex (fqswBobOutputToFinalEquiv (Prod q e) btyp e rtyp e)
  finalRegroup.comp (bob.comp (bobRegroup.comp (alice.comp sourceRegroup)))

/-- The channel pipeline computed by the concrete physical IID block. -/
private def physicalOutputChannel
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    Channel (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
        (Prod e e)) :=
  let sourceRegroup := Channel.reindex
    (fqswSourceToAliceInputEquiv (TensorPower a n) (TensorPower b n) (TensorPower r n))
  let alice := (W.physicalAliceOperation H).prod
    (Channel.idChannel (Prod (TensorPower b n) (TensorPower r n)))
  let bobRegroup := Channel.reindex
    (fqswAliceOutputToBobInputEquiv q e (TensorPower b n) (TensorPower r n))
  let bob := (W.physicalBobOperation H).prod
    (Channel.idChannel (Prod (TensorPower r n) e))
  let finalRegroup := Channel.reindex
    (fqswBobOutputToFinalEquiv
      (TensorPower a n) (TensorPower b n) e (TensorPower r n) e)
  finalRegroup.comp (bob.comp (bobRegroup.comp (alice.comp sourceRegroup)))

private theorem physicalOutputChannel_comp_sourceLift
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    (W.physicalOutputChannel H).comp
        (fqswChannelOfReferenceIsometry W.sourceLiftIsometry) =
      (W.sourceDecoder.prod (Channel.idChannel (Prod e e))).comp
        ((W.oneShotOutputChannel H).comp W.sourceEmbedding) := by
  let LA := fqswChannelOfReferenceIsometry W.paddedAtypEmbedding.supportIsometry
  let LB := fqswChannelOfReferenceIsometry W.typicalBobRegister.supportIsometry
  let LR := fqswChannelOfReferenceIsometry W.typicalRefRegister.supportIsometry
  let P := fqswChannelOfReferenceIsometry W.paddedAtypEmbedding.isometry
  let UA := fqswChannelOfReferenceIsometry H.toOneShotProtocol.aliceIsometry
  let VB := fqswChannelOfReferenceIsometry H.toOneShotProtocol.bobIsometry
  let IQ := Channel.idChannel q
  let IE := Channel.idChannel e
  let IB := Channel.idChannel btyp
  let IR := Channel.idChannel rtyp
  let Rsource0 := Channel.reindex (fqswSourceToAliceInputEquiv atyp btyp rtyp)
  let Rsource1 := Channel.reindex (fqswSourceToAliceInputEquiv (Prod q e) btyp rtyp)
  let RsourceN := Channel.reindex
    (fqswSourceToAliceInputEquiv (TensorPower a n) (TensorPower b n) (TensorPower r n))
  let Ralice0 := Channel.reindex (fqswAliceOutputToBobInputEquiv q e btyp rtyp)
  let RaliceN := Channel.reindex
    (fqswAliceOutputToBobInputEquiv q e (TensorPower b n) (TensorPower r n))
  let Rfinal0 := Channel.reindex
    (fqswBobOutputToFinalEquiv (Prod q e) btyp e rtyp e)
  let RfinalN := Channel.reindex
    (fqswBobOutputToFinalEquiv
      (TensorPower a n) (TensorPower b n) e (TensorPower r n) e)
  let DA := W.paddedAtypEmbedding.physicalDecoder
  let DB := W.typicalBobRegister.physicalDecoder
  let DR := W.typicalRefRegister.physicalDecoder
  let sourceLift := (LA.prod LB).prod LR
  let sourceEmbed := (P.prod IB).prod IR
  let afterAlice := (Channel.idChannel (Prod q e)).prod (LB.prod LR)
  let beforeBob := (IQ.prod LB).prod (LR.prod IE)
  let afterBob := ((DA.prod DB).prod IE).prod (LR.prod IE)
  have hSourceLiftChannel :
      fqswChannelOfReferenceIsometry W.sourceLiftIsometry = sourceLift := by
    unfold sourceLiftIsometry
    rw [fqswChannelOfReferenceIsometry_prod,
      fqswChannelOfReferenceIsometry_prod]
  have hSourceDecoderChannel : W.sourceDecoder = (DA.prod DB).prod DR := by
    rfl
  have hSourceEmbeddingChannel : W.sourceEmbedding = sourceEmbed := by
    unfold sourceEmbedding
    rw [fqswChannelOfReferenceIsometry_prod,
      fqswChannelOfReferenceIsometry_ofEquiv_refl]
  have hSource : RsourceN.comp sourceLift = (LA.prod (LB.prod LR)).comp Rsource0 := by
    exact (FQSWBlockProtocol.fqswSourceToAliceInput_naturality LA LB LR).symm
  have hEmbed : Rsource1.comp sourceEmbed =
      (P.prod (IB.prod IR)).comp Rsource0 := by
    exact (FQSWBlockProtocol.fqswSourceToAliceInput_naturality P IB IR).symm
  have hAliceLocal :
      ((W.physicalAliceOperation H).prod
          (Channel.idChannel (Prod (TensorPower b n) (TensorPower r n)))).comp
          (LA.prod (LB.prod LR)) =
        afterAlice.comp ((UA.prod (Channel.idChannel (Prod btyp rtyp))).comp
          (P.prod (IB.prod IR))) := by
    unfold physicalAliceOperation
    rw [Channel.prod_comp_prod, fqswChannel_comp_assoc,
      W.paddedAtypEmbedding.physicalEncoder_comp_supportIsometry]
    rw [Channel.idChannel_comp]
    rw [Channel.prod_comp_prod, Channel.idChannel_comp]
    rw [Channel.prod_comp_prod, Channel.idChannel_comp]
    rw [Channel.prod_comp_prod, Channel.comp_idChannel, Channel.comp_idChannel]
  have hAliceRegroup : RaliceN.comp afterAlice = beforeBob.comp Ralice0 := by
    dsimp only [RaliceN, afterAlice, beforeBob, Ralice0, IQ, IE]
    rw [show Channel.idChannel (Prod q e) = IQ.prod IE by
      exact idChannel_prod.symm]
    exact (FQSWBlockProtocol.fqswAliceOutputToBobInput_naturality IQ IE LB LR).symm
  have hBobLocal :
      ((W.physicalBobOperation H).prod
          (Channel.idChannel (Prod (TensorPower r n) e))).comp beforeBob =
        afterBob.comp (VB.prod (Channel.idChannel (Prod rtyp e))) := by
    unfold physicalBobOperation
    dsimp only
    rw [Channel.prod_comp_prod, Channel.idChannel_comp]
    rw [fqswChannel_comp_assoc, fqswChannel_comp_assoc]
    rw [Channel.prod_comp_prod, Channel.comp_idChannel,
      W.typicalBobRegister.physicalEncoder_comp_supportIsometry]
    rw [idChannel_prod, Channel.comp_idChannel]
    rw [Channel.prod_comp_prod, Channel.comp_idChannel]
  have hReferenceDecoder : DR = LR := by
    dsimp only [DR, LR]
    exact W.typicalRefRegister.physicalDecoder_eq_supportIsometryChannel
  have hFinal : RfinalN.comp afterBob =
      (((DA.prod DB).prod DR).prod (Channel.idChannel (Prod e e))).comp Rfinal0 := by
    rw [hReferenceDecoder]
    dsimp only [RfinalN, afterBob, DA, DB, LR, IE, Rfinal0]
    rw [show Channel.idChannel (Prod e e) = IE.prod IE by
      exact idChannel_prod.symm]
    exact (FQSWBlockProtocol.fqswAliceOutputToBobInput_naturality
      (q0 := Prod (Prod q e) btyp) (e0 := e) (b0 := rtyp) (r0 := e)
      (q1 := Prod (TensorPower a n) (TensorPower b n))
      (e1 := e) (b1 := TensorPower r n) (r1 := e)
      (DA.prod DB) IE LR IE).symm
  rw [hSourceLiftChannel, hSourceDecoderChannel, hSourceEmbeddingChannel]
  unfold physicalOutputChannel oneShotOutputChannel
  dsimp only
  simp only [fqswChannel_comp_assoc]
  rw [hSource]
  rw [← fqswChannel_comp_assoc _ _ Rsource0, hAliceLocal]
  simp only [fqswChannel_comp_assoc]
  rw [← hEmbed]
  rw [← fqswChannel_comp_assoc RaliceN afterAlice, hAliceRegroup]
  simp only [fqswChannel_comp_assoc]
  rw [← fqswChannel_comp_assoc
      ((W.physicalBobOperation H).prod
        (Channel.idChannel (Prod (TensorPower r n) e))) beforeBob,
    hBobLocal]
  simp only [fqswChannel_comp_assoc]
  rw [← fqswChannel_comp_assoc RfinalN afterBob, hFinal]
  simp only [fqswChannel_comp_assoc]
  rfl

/-- On the normalized simultaneous-typical source, the concrete physical IID
pipeline is exactly the decoded finite-coordinate one-shot output. -/
theorem physicalOutput_on_normalizedTypicalSource
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    (W.toFQSWBlockProtocol H).outputStateOfBlockState T.normalizedTypicalSource =
      W.decodedOneShotOutputState H := by
  rw [← W.decodedSourceState_eq_normalizedTypicalSource]
  unfold FQSWBlockProtocol.outputStateOfBlockState decodedSourceState
  dsimp only
  rw [← Channel.reindex_applyState, ← Channel.reindex_applyState,
    ← Channel.reindex_applyState]
  rw [← Channel.applyState_comp, ← Channel.applyState_comp,
    ← Channel.applyState_comp, ← Channel.applyState_comp]
  change (W.physicalOutputChannel H).applyState
      ((fqswChannelOfReferenceIsometry W.sourceLiftIsometry).applyState
        W.unpaddedSource.state) = W.decodedOneShotOutputState H
  rw [← Channel.applyState_comp, W.physicalOutputChannel_comp_sourceLift]
  unfold decodedOneShotOutputState
  rw [Channel.applyState_comp, Channel.applyState_comp]
  rw [W.sourceEmbedding_applyState_unpaddedSource]
  change (W.sourceDecoder.prod (Channel.idChannel (Prod e e))).applyState
      ((W.oneShotOutputChannel H).applyState W.source.state) =
    (W.sourceDecoder.prod (Channel.idChannel (Prod e e))).applyState
      H.toOneShotProtocol.outputState
  congr 1
  rw [← H.toOneShotProtocol.outputStateOfState_source_eq_outputState]
  unfold oneShotOutputChannel FQSWOneShotProtocol.outputStateOfState
  dsimp only
  rw [Channel.applyState_comp, Channel.applyState_comp, Channel.applyState_comp,
    Channel.applyState_comp]
  rw [Channel.reindex_applyState, Channel.reindex_applyState,
    Channel.reindex_applyState]

/-- The concrete physical IID pipeline is a channel, so it contracts the
trace distance between arbitrary block-source states. -/
private theorem physicalOutputChannel_applyState
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e)))
    (ρ : State
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))) :
    (W.physicalOutputChannel H).applyState ρ =
      (W.toFQSWBlockProtocol H).outputStateOfBlockState ρ := by
  unfold physicalOutputChannel FQSWBlockProtocol.outputStateOfBlockState
  dsimp only
  rw [Channel.applyState_comp, Channel.applyState_comp,
    Channel.applyState_comp, Channel.applyState_comp]
  rw [Channel.reindex_applyState, Channel.reindex_applyState,
    Channel.reindex_applyState]
  rfl

theorem physicalOutput_traceNormDistance_le
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e)))
    (ρ σ : State
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))) :
    traceNormDistance
        ((W.toFQSWBlockProtocol H).outputStateOfBlockState ρ).matrix
        ((W.toFQSWBlockProtocol H).outputStateOfBlockState σ).matrix ≤
      traceNormDistance ρ.matrix σ.matrix := by
  have hρ :
      (W.physicalOutputChannel H).applyState ρ =
        (W.toFQSWBlockProtocol H).outputStateOfBlockState ρ := by
    exact W.physicalOutputChannel_applyState H ρ
  have hσ :
      (W.physicalOutputChannel H).applyState σ =
        (W.toFQSWBlockProtocol H).outputStateOfBlockState σ := by
    exact W.physicalOutputChannel_applyState H σ
  have h := Channel.normalizedTraceDistance_applyState_le
    (W.physicalOutputChannel H) ρ σ
  rw [hρ, hσ] at h
  unfold State.normalizedTraceDistance normalizedTraceDistance at h
  nlinarith

omit [Nonempty btyp] in
/-- Decoding the one-shot output and target back into the original IID
registers cannot increase their trace-norm error. -/
theorem decodedOneShot_traceNormError_le
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    traceNormDistance (W.decodedOneShotOutputState H).matrix
        (W.normalizedTypicalTargetState H).matrix ≤
      H.toOneShotProtocol.traceNormError := by
  let Φ := W.sourceDecoder.prod (Channel.idChannel (Prod e e))
  have h := Channel.normalizedTraceDistance_applyState_le Φ
    H.toOneShotProtocol.outputState H.toOneShotProtocol.targetState
  have hraw :
      traceNormDistance (W.decodedOneShotOutputState H).matrix
          (W.decodedOneShotTargetState H).matrix ≤
        H.toOneShotProtocol.traceNormError := by
    unfold decodedOneShotOutputState decodedOneShotTargetState
    change traceNormDistance
        (Φ.applyState H.toOneShotProtocol.outputState).matrix
        (Φ.applyState H.toOneShotProtocol.targetState).matrix ≤
      traceNormDistance H.toOneShotProtocol.outputState.matrix
        H.toOneShotProtocol.targetState.matrix
    unfold State.normalizedTraceDistance normalizedTraceDistance at h
    nlinarith
  rw [← W.decodedOneShotTargetState_eq_normalizedTypicalTargetState H]
  exact hraw

private theorem adhwFQSW_traceNormDistance_triangle
    {α : Type*} [Fintype α] [DecidableEq α]
    (ρ σ τ : State α) :
    traceNormDistance ρ.matrix τ.matrix ≤
      traceNormDistance ρ.matrix σ.matrix + traceNormDistance σ.matrix τ.matrix := by
  have h := State.normalizedTraceDistance_triangle ρ σ τ
  unfold State.normalizedTraceDistance normalizedTraceDistance at h
  nlinarith

omit [Nonempty q] in
private theorem fqswBlock_outputState_eq_adhwIidSource
    (C : FQSWBlockProtocol ψ n q e et) :
    C.outputState = C.outputStateOfBlockState (adhwFQSWIidSourceState ψ n) := by
  unfold FQSWBlockProtocol.outputState FQSWBlockProtocol.outputStateOfState
    adhwFQSWIidSourceState adhwFQSWIidPureVector
  rw [PureVector.reindex_state, PureVector.tensorPower_state]

section

set_option maxHeartbeats 800000

/-- The actual physical block output obeys the ADHW double-triangle bound.
Both perturbation terms are distances between the original IID source and the
normalized simultaneous-typical source; the middle term is the computed
one-shot protocol error transported through the physical decoders. -/
theorem toFQSWBlockProtocol_output_traceNormDistance_le_sourceRoute
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    traceNormDistance
        ((W.toFQSWBlockProtocol H).outputStateOfBlockState
          (adhwFQSWIidSourceState ψ n)).matrix
        (W.toFQSWBlockProtocol H).targetState.matrix ≤
      2 * ε + H.toOneShotProtocol.traceNormError := by
  let C := W.toFQSWBlockProtocol H
  let source := adhwFQSWIidSourceState ψ n
  let typical := T.normalizedTypicalSource
  let ebit := State.maximallyEntangled H.toOneShotProtocol.ebitPairing
  have hsource : traceNormDistance source.matrix typical.matrix ≤ ε := by
    rw [traceNormDistance_comm]
    exact W.source_traceNorm_le_original
  have htransport :
      traceNormDistance (C.outputStateOfBlockState source).matrix
          (C.outputStateOfBlockState typical).matrix ≤
        traceNormDistance source.matrix typical.matrix := by
    exact W.physicalOutput_traceNormDistance_le H source typical
  have hmiddle :
      traceNormDistance (C.outputStateOfBlockState typical).matrix
          (typical.prod ebit).matrix ≤
        H.toOneShotProtocol.traceNormError := by
    rw [show C.outputStateOfBlockState typical = W.decodedOneShotOutputState H by
      exact W.physicalOutput_on_normalizedTypicalSource H]
    simpa [typical, ebit, normalizedTypicalTargetState] using
      W.decodedOneShot_traceNormError_le H
  have htarget :
      traceNormDistance (typical.prod ebit).matrix C.targetState.matrix ≤ ε := by
    change traceNormDistance (typical.prod ebit).matrix (source.prod ebit).matrix ≤ ε
    exact (fqswProdRight_traceNormDistance_le typical source ebit).trans
      W.source_traceNorm_le_original
  calc
    traceNormDistance (C.outputStateOfBlockState source).matrix C.targetState.matrix ≤
        traceNormDistance (C.outputStateOfBlockState source).matrix
            (C.outputStateOfBlockState typical).matrix +
          traceNormDistance (C.outputStateOfBlockState typical).matrix
            C.targetState.matrix :=
      adhwFQSW_traceNormDistance_triangle _ _ _
    _ ≤ traceNormDistance source.matrix typical.matrix +
          (traceNormDistance (C.outputStateOfBlockState typical).matrix
              (typical.prod ebit).matrix +
            traceNormDistance (typical.prod ebit).matrix C.targetState.matrix) :=
      add_le_add htransport (adhwFQSW_traceNormDistance_triangle _ _ _)
    _ ≤ ε + (H.toOneShotProtocol.traceNormError + ε) :=
      add_le_add hsource (add_le_add hmiddle htarget)
    _ = 2 * ε + H.toOneShotProtocol.traceNormError := by ring

/-- Computed-error form of the physical ADHW source-route estimate. -/
theorem toFQSWBlockProtocol_traceNormError_le_sourceRoute
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e))) :
    (W.toFQSWBlockProtocol H).traceNormError ≤
      2 * ε + H.toOneShotProtocol.traceNormError := by
  unfold FQSWBlockProtocol.traceNormError
  rw [fqswBlock_outputState_eq_adhwIidSource]
  exact W.toFQSWBlockProtocol_output_traceNormDistance_le_sourceRoute H

end

end ADHWFQSWIidCompressedSourceWitness

/-- Construct the compressed pure source whose lift is the normalized
simultaneously typical i.i.d. source. -/
theorem exists_adhwFQSWIidCompressedSourceWitness
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    (P : ADHWFQSWPaddedAtypEmbedding ψ n T.typicalitySlack atyp q e)
    (B : ADHWFQSWIidTypicalBobRegister ψ n δ ε T btyp)
    (R : ADHWFQSWIidTypicalRefRegister ψ n δ ε T rtyp) :
    Nonempty
      (ADHWFQSWIidCompressedSourceWitness
        ψ n δ ε T atyp btyp rtyp q e) := by
  classical
  let φ := adhwFQSWIidPureVector ψ n
  let ρ := adhwFQSWIidSourceState ψ n
  let L := adhwFQSWIidCompressedSourceLiftMatrix P B R
  let L0 := adhwFQSWIidTypicalSourceLiftMatrix P B R
  let padAB : ReferenceIsometry (Prod atyp btyp) (Prod (Prod q e) btyp) :=
    P.isometry.prod (ReferenceIsometry.ofEquiv (Equiv.refl btyp))
  let K : Matrix (Prod (Prod (Prod q e) btyp) rtyp) (Prod (Prod atyp btyp) rtyp) ℂ :=
    Matrix.kronecker padAB.matrix (1 : CMatrix rtyp)
  let Pi := adhwFQSWIidLiftProjectorTriple
    (a := a) (b := b) (r := r) n T.projectorA T.projectorB T.projectorR
  let v0 := Matrix.mulVec (Matrix.conjTranspose L0) φ.amp
  have hL0range : L0 * Matrix.conjTranspose L0 = Pi := by
    simpa [L0, Pi] using
      adhwFQSWIidTypicalSourceLiftMatrix_mul_conjTranspose P B R
  rcases T.projectorA_statement with ⟨_hPApsd, _hPAherm, hPAid, _hPAle⟩
  rcases T.projectorB_statement with ⟨_hPBpsd, _hPBherm, hPBid, _hPBle⟩
  rcases T.projectorR_statement with ⟨_hPRpsd, _hPRherm, hPRid, _hPRle⟩
  have hPAidT : T.projectorA * T.projectorA = T.projectorA := by
    simpa [T.projectorA_eq] using hPAid
  have hPBidT : T.projectorB * T.projectorB = T.projectorB := by
    simpa [T.projectorB_eq] using hPBid
  have hPRidT : T.projectorR * T.projectorR = T.projectorR := by
    simpa [T.projectorR_eq] using hPRid
  have hPiid : Pi * Pi = Pi := by
    simpa [Pi] using
      adhwFQSWIidLiftProjectorTriple_idempotent
        (a := a) (b := b) (r := r) n
        T.projectorA T.projectorB T.projectorR hPAidT hPBidT hPRidT
  have hrank :
      rankOneMatrix v0 = Matrix.conjTranspose L0 * ρ.matrix * L0 := by
    calc
      rankOneMatrix v0 =
          Matrix.conjTranspose L0 * rankOneMatrix φ.amp *
            Matrix.conjTranspose (Matrix.conjTranspose L0) := by
            simpa [v0] using
              rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose
                (Matrix.conjTranspose L0) φ.amp
      _ = Matrix.conjTranspose L0 * ρ.matrix * L0 := by
            simp [ρ, φ, adhwFQSWIidSourceState, PureVector.state_matrix,
              Matrix.mul_assoc]
  have hvtrace_to_range :
      (rankOneMatrix v0).trace = (ρ.matrix * Pi).trace := by
    calc
      (rankOneMatrix v0).trace =
          (Matrix.conjTranspose L0 * ρ.matrix * L0).trace := by rw [hrank]
      _ = (Matrix.conjTranspose L0 * (ρ.matrix * L0)).trace := by
            exact congrArg Matrix.trace
              (Matrix.mul_assoc (Matrix.conjTranspose L0) ρ.matrix L0)
      _ = ((ρ.matrix * L0) * Matrix.conjTranspose L0).trace := by
            exact Matrix.trace_mul_comm (Matrix.conjTranspose L0) (ρ.matrix * L0)
      _ = (ρ.matrix * (L0 * Matrix.conjTranspose L0)).trace := by
            exact congrArg Matrix.trace
              (Matrix.mul_assoc ρ.matrix L0 (Matrix.conjTranspose L0))
      _ = (ρ.matrix * Pi).trace := by rw [hL0range]
  have hprojected_trace :
      (Pi * ρ.matrix * Pi).trace = (ρ.matrix * Pi).trace := by
    calc
      (Pi * ρ.matrix * Pi).trace =
          (Pi * (ρ.matrix * Pi)).trace := by
            exact congrArg Matrix.trace (Matrix.mul_assoc Pi ρ.matrix Pi)
      _ = ((ρ.matrix * Pi) * Pi).trace := by
            exact Matrix.trace_mul_comm Pi (ρ.matrix * Pi)
      _ = (ρ.matrix * (Pi * Pi)).trace := by
            exact congrArg Matrix.trace (Matrix.mul_assoc ρ.matrix Pi Pi)
      _ = (ρ.matrix * Pi).trace := by rw [hPiid]
  have hvtrace_eq :
      (rankOneMatrix v0).trace = (Pi * ρ.matrix * Pi).trace := by
    rw [hvtrace_to_range, hprojected_trace]
  have hpos : 0 < (rankOneMatrix v0).trace.re := by
    have hproj : 0 < (Pi * ρ.matrix * Pi).trace.re := by
      simpa [Pi, ρ, adhwFQSWIidProjectedSourceMatrix] using
        T.normalizedTypicalSource_projected_trace_pos
    rw [hvtrace_eq]
    exact hproj
  let source0 : PureVector (Prod (Prod atyp btyp) rtyp) :=
    PureVector.normalize v0 hpos
  let source : PureVector (Prod (Prod (Prod q e) btyp) rtyp) :=
    padAB.applyPureVector source0
  have hlift_rank :
      L0 * rankOneMatrix v0 * Matrix.conjTranspose L0 = Pi * ρ.matrix * Pi := by
    calc
      L0 * rankOneMatrix v0 * Matrix.conjTranspose L0 =
          L0 * (Matrix.conjTranspose L0 * ρ.matrix * L0) *
            Matrix.conjTranspose L0 := by
            rw [hrank]
      _ = (L0 * Matrix.conjTranspose L0) * ρ.matrix *
            (L0 * Matrix.conjTranspose L0) := by
            simp [Matrix.mul_assoc]
      _ = Pi * ρ.matrix * Pi := by rw [hL0range]
  have hsource0_lift :
      L0 * source0.state.matrix * Matrix.conjTranspose L0 =
        T.normalizedTypicalSource.matrix := by
    dsimp [source0]
    calc
      L0 * (PureVector.normalize v0 hpos).state.matrix * Matrix.conjTranspose L0 =
          L0 * (((((rankOneMatrix v0).trace.re)⁻¹ : ℝ) : ℂ) • rankOneMatrix v0) *
            Matrix.conjTranspose L0 := by
            rw [PureVector.normalize_state_matrix]
      _ = (((((rankOneMatrix v0).trace.re)⁻¹ : ℝ) : ℂ) •
            (L0 * rankOneMatrix v0 * Matrix.conjTranspose L0)) := by
            simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = (((((Pi * ρ.matrix * Pi).trace.re)⁻¹ : ℝ) : ℂ) •
            (Pi * ρ.matrix * Pi)) := by
            rw [hlift_rank]
            have htrace_re :
                (rankOneMatrix v0).trace.re = (Pi * ρ.matrix * Pi).trace.re :=
              congrArg Complex.re hvtrace_eq
            rw [htrace_re]
      _ = T.normalizedTypicalSource.matrix := by
            simpa [Pi, ρ, adhwFQSWIidProjectedSourceMatrix] using
              (T.normalizedTypicalSource_matrix_eq).symm
  have hsource_state :
      source.state.matrix =
        K * source0.state.matrix * Matrix.conjTranspose K := by
    simpa [source, K, PureVector.state_matrix,
      ReferenceIsometry.applyPureVector_amp] using
      (padAB.rankOne_applyAmp source0.amp).trans
        (referenceIsometry_applyMatrix_eq_kronecker_one_conj
          padAB (rankOneMatrix source0.amp))
  have hKiso :
      Matrix.conjTranspose K * K =
        (1 : CMatrix (Prod (Prod atyp btyp) rtyp)) := by
    let idR : ReferenceIsometry rtyp rtyp :=
      ReferenceIsometry.ofEquiv (Equiv.refl rtyp)
    let padR : ReferenceIsometry (Prod (Prod atyp btyp) rtyp)
        (Prod (Prod (Prod q e) btyp) rtyp) :=
      padAB.prod idR
    have hpadR : padR.matrix = K := by
      ext i j
      simp [padR, idR, K, ReferenceIsometry.prod, ReferenceIsometry.ofEquiv,
        Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
    simpa [hpadR] using padR.isometry
  have hL_eq :
      L = L0 * Matrix.conjTranspose K := by
    simpa [L, L0, padAB, K] using
      adhwFQSWIidCompressedSourceLiftMatrix_eq_typicalSourceLiftMatrix_mul_paddingAdjoint
        P B R
  have hsource_a_purity_le :
      adhwFQSWAPurity source ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))) := by
    simpa [padAB, source] using
      adhwFQSWIidPaddedTypicalSource_a_purity_le P B R source0 hsource0_lift
  have hsource_r_purity_le :
      adhwFQSWRPurity source ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))) := by
    simpa [padAB, source] using
      adhwFQSWIidPaddedTypicalSource_r_purity_le P B R source0 hsource0_lift
  have hsource_b_purity_le :
      hilbertSchmidtSq source.state.marginalA.marginalB.matrix ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) := by
    simpa [padAB, source] using
      adhwFQSWIidPaddedTypicalSource_b_purity_le P B R source0 hsource0_lift
  have hsource_ar_purity_le :
      adhwFQSWARPurity source ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) := by
    rw [adhwFQSWARPurity_eq_systemBPurity source]
    exact hsource_b_purity_le
  refine
    ⟨{ paddedAtypEmbedding := P
       typicalBobRegister := B
       typicalRefRegister := R
       unpaddedSource := source0
       source := source
       source_eq_padded := rfl
       unpadded_lifted_state_eq_normalizedTypicalSource := hsource0_lift
       source_a_purity_le := hsource_a_purity_le
       source_r_purity_le := hsource_r_purity_le
       source_b_purity_le := hsource_b_purity_le
       source_ar_purity_le := hsource_ar_purity_le
       lifted_state_eq_normalizedTypicalSource := ?_
       source_traceNorm_le_original := T.normalized_traceNorm_le }⟩
  calc
    L * source.state.matrix * Matrix.conjTranspose L =
        (L0 * Matrix.conjTranspose K) *
          (K * source0.state.matrix * Matrix.conjTranspose K) *
          Matrix.conjTranspose (L0 * Matrix.conjTranspose K) := by
          rw [hL_eq, hsource_state]
    _ = L0 * source0.state.matrix * Matrix.conjTranspose L0 := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          calc
            (L0 * Matrix.conjTranspose K) *
                (K * source0.state.matrix * Matrix.conjTranspose K) *
                (K * Matrix.conjTranspose L0) =
              L0 * ((Matrix.conjTranspose K * K) *
                  source0.state.matrix * (Matrix.conjTranspose K * K)) *
                  Matrix.conjTranspose L0 := by
                simp [Matrix.mul_assoc]
            _ = L0 * source0.state.matrix * Matrix.conjTranspose L0 := by
                  rw [hKiso]
                  simp [Matrix.mul_assoc]
    _ = T.normalizedTypicalSource.matrix := hsource0_lift

/-- Constant absorption used by the strengthened mixed source-route `skoro`
estimate.  The `4 ≤ nδ` tail condition and nonnegative mutual information
absorb the remaining factor of two. -/
private theorem fqsw_two_mul_twentyOneEighth_delta_pow_le_target_pow
    (n : ℕ) (I δ : ℝ)
    (hI_nonneg : 0 ≤ I)
    (hn_large : 4 ≤ (n : ℝ) * δ) :
    2 * (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δ)) ≤
      (2 : ℝ) ^ ((n : ℝ) * (I + 3 * δ)) := by
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hconst_absorb :
      (2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (I + (3 / 8 : ℝ) * δ)) := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (I + (3 / 8 : ℝ) * δ)) := by
        refine Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) ?_
        have hdelta_part : 1 ≤ (n : ℝ) * ((3 / 8 : ℝ) * δ) := by
          calc
            (1 : ℝ) ≤ 3 / 2 := by norm_num
            _ ≤ (3 / 8 : ℝ) * ((n : ℝ) * δ) := by nlinarith
            _ = (n : ℝ) * ((3 / 8 : ℝ) * δ) := by ring
        have hIpart : 0 ≤ (n : ℝ) * I := mul_nonneg hn_nonneg hI_nonneg
        calc
          (1 : ℝ) ≤ (n : ℝ) * ((3 / 8 : ℝ) * δ) := hdelta_part
          _ ≤ (n : ℝ) * I + (n : ℝ) * ((3 / 8 : ℝ) * δ) :=
                le_add_of_nonneg_left hIpart
          _ = (n : ℝ) * (I + (3 / 8 : ℝ) * δ) := by ring
  have hpow_nonneg :
      0 ≤ (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δ)) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hmul := mul_le_mul_of_nonneg_right hconst_absorb hpow_nonneg
  calc
    2 * (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δ)) ≤
        (2 : ℝ) ^ ((n : ℝ) * (I + (3 / 8 : ℝ) * δ)) *
          (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δ)) := hmul
    _ = (2 : ℝ) ^ ((n : ℝ) * (I + 3 * δ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- Scalar `skoro` estimate for the mixed-slack padded source route.  The
`AR` term uses the source `AR` purity, while the product term uses the separate
`A` and `R` purity estimates.  The finite `q` upper rounding and `4 ≤ nδ`
absorb the constants without changing the source denominator `|q|²`. -/
private theorem fqsw_mixed_source_fourthRootArgument_scalar_le_skoro
    (n : ℕ) (I EB HA HB HR δtyp δrate Q E Rdim Apu Rpu ARpu : ℝ)
    (hbaseAR : (1 / 2 : ℝ) * I + EB + HR - HB = I)
    (hbaseProd : (1 / 2 : ℝ) * I + EB - HA = 0)
    (hI_nonneg : 0 ≤ I)
    (hδrate_nonneg : 0 ≤ δrate)
    (hδtyp_le_eighth : δtyp ≤ δrate / 8)
    (hn_large : 4 ≤ (n : ℝ) * δrate)
    (hE_nonneg : 0 ≤ E) (hRdim_nonneg : 0 ≤ Rdim)
    (hApu_nonneg : 0 ≤ Apu) (hRpu_nonneg : 0 ≤ Rpu) (hARpu_nonneg : 0 ≤ ARpu)
    (hQ_upper :
      Q ≤ (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + (9 / 4 : ℝ) * δrate)))
    (hE_upper :
      E ≤ (2 : ℝ) ^ ((n : ℝ) * EB))
    (hRdim_upper :
      Rdim ≤ (2 : ℝ) ^ ((n : ℝ) * (HR + δtyp)))
    (hApu_upper :
      Apu ≤ (2 : ℝ) ^ (-((n : ℝ) * (HA - δtyp))))
    (hRpu_upper :
      Rpu ≤ (2 : ℝ) ^ (-((n : ℝ) * (HR - δtyp))))
    (hARpu_upper :
      ARpu ≤ (2 : ℝ) ^ (-((n : ℝ) * (HB - δtyp)))) :
    (2 * Q * E * Rdim / (Q ^ 2)) * (ARpu + 2 * Apu * Rpu) ≤
      4 * (2 : ℝ) ^ ((n : ℝ) * (I + 3 * δrate)) / (Q ^ 2) := by
  let qPow : ℝ :=
    (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + (9 / 4 : ℝ) * δrate))
  let ePow : ℝ := (2 : ℝ) ^ ((n : ℝ) * EB)
  let rPow : ℝ := (2 : ℝ) ^ ((n : ℝ) * (HR + δtyp))
  let aPurPow : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (HA - δtyp)))
  let rPurPow : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (HR - δtyp)))
  let arPurPow : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (HB - δtyp)))
  let targetPow : ℝ := (2 : ℝ) ^ ((n : ℝ) * (I + 3 * δrate))
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hqPow_nonneg : 0 ≤ qPow := by
    dsimp [qPow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hePow_nonneg : 0 ≤ ePow := by
    dsimp [ePow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hrPow_nonneg : 0 ≤ rPow := by
    dsimp [rPow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have haPurPow_nonneg : 0 ≤ aPurPow := by
    dsimp [aPurPow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hrPurPow_nonneg : 0 ≤ rPurPow := by
    dsimp [rPurPow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have harPurPow_nonneg : 0 ≤ arPurPow := by
    dsimp [arPurPow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have htargetPow_nonneg : 0 ≤ targetPow := by
    dsimp [targetPow]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hQ_upper' : Q ≤ qPow := by simpa [qPow] using hQ_upper
  have hE_upper' : E ≤ ePow := by simpa [ePow] using hE_upper
  have hRdim_upper' : Rdim ≤ rPow := by simpa [rPow] using hRdim_upper
  have hApu_upper' : Apu ≤ aPurPow := by simpa [aPurPow] using hApu_upper
  have hRpu_upper' : Rpu ≤ rPurPow := by simpa [rPurPow] using hRpu_upper
  have hARpu_upper' : ARpu ≤ arPurPow := by simpa [arPurPow] using hARpu_upper
  have hQE : Q * E ≤ qPow * ePow :=
    mul_le_mul hQ_upper' hE_upper' hE_nonneg hqPow_nonneg
  have hQER : Q * E * Rdim ≤ qPow * ePow * rPow :=
    mul_le_mul hQE hRdim_upper' hRdim_nonneg
      (mul_nonneg hqPow_nonneg hePow_nonneg)
  have hQERAR : Q * E * Rdim * ARpu ≤ qPow * ePow * rPow * arPurPow :=
    mul_le_mul hQER hARpu_upper' hARpu_nonneg
      (mul_nonneg (mul_nonneg hqPow_nonneg hePow_nonneg) hrPow_nonneg)
  have hARpow :
      qPow * ePow * rPow * arPurPow =
        (2 : ℝ) ^ ((n : ℝ) * (I + (9 / 4 : ℝ) * δrate + 2 * δtyp)) := by
    dsimp [qPow, ePow, rPow, arPurPow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    calc
      (n : ℝ) * ((1 / 2 : ℝ) * I + (9 / 4 : ℝ) * δrate) +
              (n : ℝ) * EB + (n : ℝ) * (HR + δtyp) +
              -((n : ℝ) * (HB - δtyp)) =
          (n : ℝ) * (((1 / 2 : ℝ) * I + EB + HR - HB) +
            (9 / 4 : ℝ) * δrate + 2 * δtyp) := by ring
      _ = (n : ℝ) * (I + (9 / 4 : ℝ) * δrate + 2 * δtyp) := by
            rw [hbaseAR]
  have hARexp_le :
      (n : ℝ) * (I + (9 / 4 : ℝ) * δrate + 2 * δtyp) ≤
        (n : ℝ) * (I + 3 * δrate) := by
    have htyp : 2 * δtyp ≤ (1 / 4 : ℝ) * δrate := by nlinarith
    have hinner :
        I + (9 / 4 : ℝ) * δrate + 2 * δtyp ≤
          I + 3 * δrate := by
      calc
        I + (9 / 4 : ℝ) * δrate + 2 * δtyp
            ≤ I + (9 / 4 : ℝ) * δrate + (1 / 4 : ℝ) * δrate := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left htyp (I + (9 / 4 : ℝ) * δrate)
        _ = I + (5 / 2 : ℝ) * δrate := by ring
        _ ≤ I + 3 * δrate := by nlinarith
    exact mul_le_mul_of_nonneg_left hinner hn_nonneg
  have hARpow_le_target :
      (2 : ℝ) ^ ((n : ℝ) * (I + (9 / 4 : ℝ) * δrate + 2 * δtyp)) ≤
        targetPow := by
    dsimp [targetPow]
    exact Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hARexp_le
  have hARterm_le :
      2 * Q * E * Rdim * ARpu / (Q ^ 2) ≤
        2 * targetPow / (Q ^ 2) := by
    have hnum :
        2 * Q * E * Rdim * ARpu ≤ 2 * targetPow := by
      have hcore :
          Q * E * Rdim * ARpu ≤ targetPow := by
        exact hQERAR.trans (by simpa [hARpow] using hARpow_le_target)
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left hcore (by norm_num : (0 : ℝ) ≤ 2))
    exact div_le_div_of_nonneg_right hnum (sq_nonneg Q)
  have hQERA : Q * E * Rdim * Apu ≤ qPow * ePow * rPow * aPurPow :=
    mul_le_mul hQER hApu_upper' hApu_nonneg
      (mul_nonneg (mul_nonneg hqPow_nonneg hePow_nonneg) hrPow_nonneg)
  have hQERARprod :
      Q * E * Rdim * Apu * Rpu ≤ qPow * ePow * rPow * aPurPow * rPurPow :=
    mul_le_mul hQERA hRpu_upper' hRpu_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hqPow_nonneg hePow_nonneg) hrPow_nonneg)
        haPurPow_nonneg)
  have hProdPow :
      qPow * ePow * rPow * aPurPow * rPurPow =
        (2 : ℝ) ^ ((n : ℝ) * ((9 / 4 : ℝ) * δrate + 3 * δtyp)) := by
    dsimp [qPow, ePow, rPow, aPurPow, rPurPow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    calc
      (n : ℝ) * ((1 / 2 : ℝ) * I + (9 / 4 : ℝ) * δrate) +
              (n : ℝ) * EB + (n : ℝ) * (HR + δtyp) +
              -((n : ℝ) * (HA - δtyp)) +
              -((n : ℝ) * (HR - δtyp)) =
          (n : ℝ) * (((1 / 2 : ℝ) * I + EB - HA) +
            (9 / 4 : ℝ) * δrate + 3 * δtyp) := by ring
      _ = (n : ℝ) * ((9 / 4 : ℝ) * δrate + 3 * δtyp) := by
            rw [hbaseProd]
            ring
  have hProdExp_le_twentyOneEighth :
      (n : ℝ) * ((9 / 4 : ℝ) * δrate + 3 * δtyp) ≤
        (n : ℝ) * ((21 / 8 : ℝ) * δrate) := by
    have htyp : 3 * δtyp ≤ (3 / 8 : ℝ) * δrate := by nlinarith
    have hinner :
        (9 / 4 : ℝ) * δrate + 3 * δtyp ≤ (21 / 8 : ℝ) * δrate := by
      calc
        (9 / 4 : ℝ) * δrate + 3 * δtyp
            ≤ (9 / 4 : ℝ) * δrate + (3 / 8 : ℝ) * δrate := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left htyp ((9 / 4 : ℝ) * δrate)
        _ = (21 / 8 : ℝ) * δrate := by ring
    exact mul_le_mul_of_nonneg_left hinner hn_nonneg
  have hProdPow_le_twentyOneEighth :
      (2 : ℝ) ^ ((n : ℝ) * ((9 / 4 : ℝ) * δrate + 3 * δtyp)) ≤
        (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δrate)) :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hProdExp_le_twentyOneEighth
  have htwo_prod_le_target :
      2 * (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δrate)) ≤ targetPow := by
    exact
      fqsw_two_mul_twentyOneEighth_delta_pow_le_target_pow
        n I δrate hI_nonneg hn_large
  have hProdterm_le :
      4 * Q * E * Rdim * Apu * Rpu / (Q ^ 2) ≤
        2 * targetPow / (Q ^ 2) := by
    have hnum :
        4 * Q * E * Rdim * Apu * Rpu ≤ 2 * targetPow := by
      have hcore :
          Q * E * Rdim * Apu * Rpu ≤
            (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δrate)) := by
        calc
          Q * E * Rdim * Apu * Rpu ≤
              qPow * ePow * rPow * aPurPow * rPurPow := hQERARprod
          _ = (2 : ℝ) ^ ((n : ℝ) * ((9 / 4 : ℝ) * δrate + 3 * δtyp)) :=
                hProdPow
          _ ≤ (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δrate)) :=
                hProdPow_le_twentyOneEighth
      have hscaled :
          4 * (Q * E * Rdim * Apu * Rpu) ≤
            4 * (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δrate)) :=
        mul_le_mul_of_nonneg_left hcore (by norm_num : (0 : ℝ) ≤ 4)
      have htarget_scaled :
          4 * (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δrate)) ≤
            2 * targetPow := by
        calc
          4 * (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δrate)) =
              2 * (2 * (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δrate))) := by ring
          _ ≤ 2 * targetPow :=
              mul_le_mul_of_nonneg_left htwo_prod_le_target
                (by norm_num : (0 : ℝ) ≤ 2)
      have hscaled' :
          4 * Q * E * Rdim * Apu * Rpu ≤
            4 * (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δrate)) := by
        calc
          4 * Q * E * Rdim * Apu * Rpu =
              4 * (Q * E * Rdim * Apu * Rpu) := by ring
          _ ≤ 4 * (2 : ℝ) ^ ((n : ℝ) * ((21 / 8 : ℝ) * δrate)) := hscaled
      exact hscaled'.trans htarget_scaled
    exact div_le_div_of_nonneg_right hnum (sq_nonneg Q)
  calc
    (2 * Q * E * Rdim / (Q ^ 2)) * (ARpu + 2 * Apu * Rpu)
        = 2 * Q * E * Rdim * ARpu / (Q ^ 2) +
            4 * Q * E * Rdim * Apu * Rpu / (Q ^ 2) := by ring
    _ ≤ 2 * targetPow / (Q ^ 2) + 2 * targetPow / (Q ^ 2) :=
          add_le_add hARterm_le hProdterm_le
    _ = 4 * targetPow / (Q ^ 2) := by ring
    _ = 4 * (2 : ℝ) ^ ((n : ℝ) * (I + 3 * δrate)) / (Q ^ 2) := by
          rfl

/-- The padded compressed source satisfies the strengthened ADHW source-route
`skoro` fourth-root argument bound when the typicality slack is at most one
eighth of the rate slack. -/
theorem ADHWFQSWIidCompressedSourceWitness.fourthRootArgument_le_iid_skoro_mixed
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e]
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δtyp ε T atyp btyp rtyp q e)
    (balancedRateChoice : ADHWFQSWIidBalancedRateChoice ψ n δrate q e)
    (hδrate_nonneg : 0 ≤ δrate)
    (hδtyp_le_eighth : δtyp ≤ δrate / 8)
    (hn_large : 4 ≤ (n : ℝ) * δrate) :
    adhwFQSWOneShotFourthRootArgument W.source q ≤
      4 * (2 : ℝ) ^ ((n : ℝ) *
        (mutualInformation ψ.state.coherentTransferReferenceState + 3 * δrate)) /
        ((Fintype.card q : ℝ) ^ 2) := by
  let I : ℝ := mutualInformation ψ.state.coherentTransferReferenceState
  let EB : ℝ := ψ.fqswEbitYieldRate
  let HA : ℝ := adhwFQSWEntropyA ψ
  let HB : ℝ := adhwFQSWEntropyB ψ
  let HR : ℝ := adhwFQSWEntropyR ψ
  have hbaseAR : (1 / 2 : ℝ) * I + EB + HR - HB = I := by
    dsimp [I, EB, HA, HB, HR]
    unfold PureVector.fqswEbitYieldRate
    rw [adhwFQSWMutualInformationAR_eq_entropyA_add_entropyR_sub_entropyB,
      adhwFQSWMutualInformationAB_eq_entropyA_add_entropyB_sub_entropyR]
    ring
  have hbaseProd : (1 / 2 : ℝ) * I + EB - HA = 0 := by
    dsimp [I, EB, HA, HB, HR]
    unfold PureVector.fqswEbitYieldRate
    rw [adhwFQSWMutualInformationAR_eq_entropyA_add_entropyR_sub_entropyB,
      adhwFQSWMutualInformationAB_eq_entropyA_add_entropyB_sub_entropyR]
    ring
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact State.mutualInformation_nonneg ψ.state.coherentTransferReferenceState
  have hq_pos_nat : 0 < Fintype.card q := Fintype.card_pos_iff.mpr inferInstance
  have hq_pos : 0 < (Fintype.card q : ℝ) := by exact_mod_cast hq_pos_nat
  have he_nonneg : 0 ≤ (Fintype.card e : ℝ) := Nat.cast_nonneg _
  have hrtyp_nonneg : 0 ≤ (Fintype.card rtyp : ℝ) := Nat.cast_nonneg _
  have hApu_nonneg : 0 ≤ adhwFQSWAPurity W.source := by
    simpa [adhwFQSWAPurity] using
      hilbertSchmidtSq_nonneg ((adhwFQSWARState W.source).marginalA.matrix)
  have hRpu_nonneg : 0 ≤ adhwFQSWRPurity W.source := by
    simpa [adhwFQSWRPurity] using
      hilbertSchmidtSq_nonneg ((adhwFQSWARState W.source).marginalB.matrix)
  have hARpu_nonneg : 0 ≤ adhwFQSWARPurity W.source := by
    simpa [adhwFQSWARPurity] using
      hilbertSchmidtSq_nonneg (adhwFQSWARState W.source).matrix
  have hQ_upper :
      (Fintype.card q : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) * ((1 / 2 : ℝ) * I + (9 / 4 : ℝ) * δrate)) := by
    have hlog :=
      le_two_rpow_of_log2_le hq_pos
        balancedRateChoice.rateChoice.communication_log_le
    simpa [I, adhwFQSWIidRoundedCommunicationLogUpperTarget,
      PureVector.fqswCommunicationRate] using hlog
  have hE_upper :
      (Fintype.card e : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * EB) := by
    simpa [EB] using balancedRateChoice.ebit_card_upper_for_target
  have hRdim_upper :
      (Fintype.card rtyp : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (HR + δtyp)) := by
    calc
      (Fintype.card rtyp : ℝ) =
          (adhwFQSWSystemRState ψ).typicalSubspaceDimension n T.typicalitySlack :=
            W.typicalRefRegister.card_eq_projector_rank
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ + δtyp)) := T.rankR_upper
      _ = (2 : ℝ) ^ ((n : ℝ) * (HR + δtyp)) := by rfl
  have hscalar :=
    fqsw_mixed_source_fourthRootArgument_scalar_le_skoro
      n I EB HA HB HR δtyp δrate
      (Fintype.card q : ℝ) (Fintype.card e : ℝ) (Fintype.card rtyp : ℝ)
      (adhwFQSWAPurity W.source) (adhwFQSWRPurity W.source)
      (adhwFQSWARPurity W.source)
      hbaseAR hbaseProd hI_nonneg hδrate_nonneg hδtyp_le_eighth hn_large
      he_nonneg hrtyp_nonneg hApu_nonneg hRpu_nonneg hARpu_nonneg
      hQ_upper hE_upper hRdim_upper
      (by simpa [HA] using W.source_a_purity_le)
      (by simpa [HR] using W.source_r_purity_le)
      (by simpa [HB] using W.source_ar_purity_le)
  simpa [adhwFQSWOneShotFourthRootArgument, Fintype.card_prod, I,
    mul_assoc, mul_left_comm, mul_comm] using hscalar

/-- Mixed-slack source-route one-shot tail for the padded compressed source.
This closes the ADHW `skoro` step internally from the compressed source purity
fields and the balanced finite-register choice. -/
theorem ADHWFQSWIidCompressedSourceWitness.oneShotTail_le_mixed
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e]
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δtyp ε T atyp btyp rtyp q e)
    (balancedRateChoice : ADHWFQSWIidBalancedRateChoice ψ n δrate q e)
    (hδrate_nonneg : 0 ≤ δrate)
    (hδtyp_le_eighth : δtyp ≤ δrate / 8)
    (hn_large : 4 ≤ (n : ℝ) * δrate) :
    adhwFQSWOneShotErrorBound W.source q ≤
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δrate / 4)) := by
  have hskoro :
      adhwFQSWOneShotFourthRootArgument W.source q ≤
        4 * (2 : ℝ) ^ ((n : ℝ) *
          (mutualInformation ψ.state.coherentTransferReferenceState + 3 * δrate)) /
          ((Fintype.card q : ℝ) ^ 2) :=
    W.fourthRootArgument_le_iid_skoro_mixed
      balancedRateChoice hδrate_nonneg hδtyp_le_eighth hn_large
  exact
    adhwFQSWOneShotErrorBound_le_iid_entropy_exponent_of_skoro_bound
      ψ W.source q n δrate hskoro
      (by
        simpa [adhwFQSWIidCommunicationLogTarget] using
          balancedRateChoice.rateChoice.communication_card_lower)

/-- Source-route witness for ADHW fqsw.tex lines 1168-1175.  It fixes the
compressed source witness, one-shot bound, and proved one-shot tail used in the
physical double-triangle argument. -/
structure ADHWFQSWIidSourceRouteBlock
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    where
  compressedSourceWitness :
    ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e
  oneShotBound :
    ADHWFQSWOneShotBound compressedSourceWitness.source q e
      (Equiv.refl (Prod q e))
  oneShotTail_le :
    adhwFQSWOneShotErrorBound compressedSourceWitness.source q ≤
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8))

namespace ADHWFQSWIidSourceRouteBlock

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
variable {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
variable {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
variable {q : Type x} {e : Type y}
variable [Fintype atyp] [DecidableEq atyp]
variable [Fintype btyp] [DecidableEq btyp]
variable [Fintype rtyp] [DecidableEq rtyp]
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable (B : ADHWFQSWIidSourceRouteBlock ψ n δ ε T atyp btyp rtyp q e)

/-- The physical full-source protocol fixed by this route witness. -/
def physicalProtocol : FQSWBlockProtocol ψ n q e e := by
  let sourceIndex :=
    Classical.choice B.compressedSourceWitness.unpaddedSource.state.nonempty
  letI : Nonempty atyp := ⟨sourceIndex.1.1⟩
  letI : Nonempty btyp := ⟨sourceIndex.1.2⟩
  exact B.compressedSourceWitness.toFQSWBlockProtocol B.oneShotBound

/-- The computed trace-norm error of the physical protocol is bounded by the
rounded finite-register estimate. -/
theorem physicalProtocol_traceNormError_le_rounded :
    B.physicalProtocol.traceNormError ≤
      adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ := by
  let W := B.compressedSourceWitness
  let H := B.oneShotBound
  let sourceIndex := Classical.choice W.unpaddedSource.state.nonempty
  letI : Nonempty atyp := ⟨sourceIndex.1.1⟩
  letI : Nonempty btyp := ⟨sourceIndex.1.2⟩
  change (W.toFQSWBlockProtocol H).traceNormError ≤
    adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ
  calc
    (W.toFQSWBlockProtocol H).traceNormError ≤
        2 * ε + H.toOneShotProtocol.traceNormError :=
      W.toFQSWBlockProtocol_traceNormError_le_sourceRoute H
    _ ≤ 2 * ε + Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8)) := by
      linarith [H.toOneShotProtocol_traceNormError_le.trans B.oneShotTail_le]
    _ = adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ := rfl

/-- Normalized trace-distance form of the computed rounded error bound. -/
theorem physicalProtocol_normalizedError_le_rounded_half :
    B.physicalProtocol.normalizedError ≤
      (1 / 2 : ℝ) * adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ :=
  B.physicalProtocol.normalizedError_eq_half_traceNormError.trans_le
    (mul_le_mul_of_nonneg_left B.physicalProtocol_traceNormError_le_rounded (by norm_num))

end ADHWFQSWIidSourceRouteBlock

/-- Mixed-slack source-route block for the final no-witness route.  The
typical projectors and compressed source use `δtyp`, while the finite
communication/ebit registers and one-shot exponential tail use `δrate`. -/
structure ADHWFQSWIidMixedSourceRouteBlock
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δtyp δrate ε : ℝ)
    (T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    where
  compressedSourceWitness :
    ADHWFQSWIidCompressedSourceWitness ψ n δtyp ε T atyp btyp rtyp q e
  oneShotBound :
    ADHWFQSWOneShotBound compressedSourceWitness.source q e
      (Equiv.refl (Prod q e))
  oneShotTail_le_mixed :
    adhwFQSWOneShotErrorBound compressedSourceWitness.source q ≤
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δrate / 4))

namespace ADHWFQSWIidMixedSourceRouteBlock

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
variable {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε}
variable {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
variable {q : Type x} {e : Type y}
variable [Fintype atyp] [DecidableEq atyp]
variable [Fintype btyp] [DecidableEq btyp]
variable [Fintype rtyp] [DecidableEq rtyp]
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable (B : ADHWFQSWIidMixedSourceRouteBlock ψ n δtyp δrate ε T atyp btyp rtyp q e)

/-- The physical full-source protocol fixed by this mixed-slack route. -/
def physicalProtocol : FQSWBlockProtocol ψ n q e e := by
  let sourceIndex :=
    Classical.choice B.compressedSourceWitness.unpaddedSource.state.nonempty
  letI : Nonempty atyp := ⟨sourceIndex.1.1⟩
  letI : Nonempty btyp := ⟨sourceIndex.1.2⟩
  exact B.compressedSourceWitness.toFQSWBlockProtocol B.oneShotBound

/-- The computed trace-norm error of the physical mixed-slack protocol obeys
the exact ADHW source bound `2ε + √8 · 2^(-nδrate/4)`. -/
theorem physicalProtocol_traceNormError_le :
    B.physicalProtocol.traceNormError ≤
      adhwFQSWIidPostCompressionTraceErrorBound ε n δrate := by
  let W := B.compressedSourceWitness
  let H := B.oneShotBound
  let sourceIndex := Classical.choice W.unpaddedSource.state.nonempty
  letI : Nonempty atyp := ⟨sourceIndex.1.1⟩
  letI : Nonempty btyp := ⟨sourceIndex.1.2⟩
  change (W.toFQSWBlockProtocol H).traceNormError ≤
    adhwFQSWIidPostCompressionTraceErrorBound ε n δrate
  calc
    (W.toFQSWBlockProtocol H).traceNormError ≤
        2 * ε + H.toOneShotProtocol.traceNormError :=
      W.toFQSWBlockProtocol_traceNormError_le_sourceRoute H
    _ ≤ 2 * ε + Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δrate / 4)) := by
      linarith [H.toOneShotProtocol_traceNormError_le.trans B.oneShotTail_le_mixed]
    _ = adhwFQSWIidPostCompressionTraceErrorBound ε n δrate := rfl

/-- Normalized trace-distance form of the exact physical source bound. -/
theorem physicalProtocol_normalizedError_le :
    B.physicalProtocol.normalizedError ≤
      (1 / 2 : ℝ) * adhwFQSWIidPostCompressionTraceErrorBound ε n δrate :=
  B.physicalProtocol.normalizedError_eq_half_traceNormError.trans_le
    (mul_le_mul_of_nonneg_left B.physicalProtocol_traceNormError_le (by norm_num))

end ADHWFQSWIidMixedSourceRouteBlock

/-- Assemble a source-route block from its fixed compressed source witness,
one-shot bound, and proved one-shot tail estimate. -/
theorem exists_adhwFQSWIidSourceRouteBlock
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δ ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e)))
    (honeShotBound :
      adhwFQSWOneShotErrorBound W.source q ≤
        Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 8))) :
    Nonempty (ADHWFQSWIidSourceRouteBlock ψ n δ ε T atyp btyp rtyp q e) :=
  ⟨{ compressedSourceWitness := W
     oneShotBound := H
     oneShotTail_le := honeShotBound }⟩

/-- Assemble a mixed-slack source-route block from the fixed compressed source
witness, one-shot bound, and proved rate-slack tail estimate. -/
theorem exists_adhwFQSWIidMixedSourceRouteBlock
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
    {T : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (W : ADHWFQSWIidCompressedSourceWitness ψ n δtyp ε T atyp btyp rtyp q e)
    (H : ADHWFQSWOneShotBound W.source q e (Equiv.refl (Prod q e)))
    (honeShotBound :
      adhwFQSWOneShotErrorBound W.source q ≤
        Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δrate / 4))) :
    Nonempty
      (ADHWFQSWIidMixedSourceRouteBlock
        ψ n δtyp δrate ε T atyp btyp rtyp q e) :=
  ⟨{ compressedSourceWitness := W
     oneShotBound := H
     oneShotTail_le_mixed := honeShotBound }⟩

/-- One finite i.i.d. ADHW FQSW block produced by the simultaneous typicality,
padded-embedding, one-shot, and rounded-rate route of fqsw.tex lines
1093-1180. -/
structure ADHWFQSWIidBlockConstruction
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] where
  typicalProjectors : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε
  paddedAtypEmbedding :
    ADHWFQSWPaddedAtypEmbedding ψ n typicalProjectors.typicalitySlack atyp q e
  typicalBobRegister :
    ADHWFQSWIidTypicalBobRegister ψ n δ ε typicalProjectors btyp
  typicalRefRegister :
    ADHWFQSWIidTypicalRefRegister ψ n δ ε typicalProjectors rtyp
  rateChoice : ADHWFQSWIidRateChoice ψ n δ q e
  oneShotCardinalitySideConditions :
    ADHWFQSWIidOneShotCardinalitySideConditions atyp btyp rtyp q e
  sourceRouteBlock :
    ADHWFQSWIidSourceRouteBlock ψ n δ ε typicalProjectors atyp btyp rtyp q e

/-- Assemble one finite ADHW i.i.d. block from the already constructed
typicality, padding, rounded-rate, one-shot, compression, and post-compression
error records. -/
theorem exists_adhwFQSWIidBlockConstruction
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (typicalProjectors : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    (paddedAtypEmbedding :
      ADHWFQSWPaddedAtypEmbedding ψ n typicalProjectors.typicalitySlack atyp q e)
    (typicalBobRegister :
      ADHWFQSWIidTypicalBobRegister ψ n δ ε typicalProjectors btyp)
    (typicalRefRegister :
      ADHWFQSWIidTypicalRefRegister ψ n δ ε typicalProjectors rtyp)
    (rateChoice : ADHWFQSWIidRateChoice ψ n δ q e)
    (oneShotCardinalitySideConditions :
      ADHWFQSWIidOneShotCardinalitySideConditions atyp btyp rtyp q e)
    (sourceRouteBlock :
      ADHWFQSWIidSourceRouteBlock ψ n δ ε typicalProjectors atyp btyp rtyp q e) :
    Nonempty (ADHWFQSWIidBlockConstruction ψ n δ ε atyp btyp rtyp q e) :=
  ⟨{ typicalProjectors := typicalProjectors
     paddedAtypEmbedding := paddedAtypEmbedding
     typicalBobRegister := typicalBobRegister
     typicalRefRegister := typicalRefRegister
     rateChoice := rateChoice
     oneShotCardinalitySideConditions := oneShotCardinalitySideConditions
     sourceRouteBlock := sourceRouteBlock }⟩

/-- Assemble one finite ADHW i.i.d. block through the source-route
post-compression bridge instead of supplying the final post-compression trace
bound as a free hypothesis. -/
theorem exists_adhwFQSWIidBlockConstruction_of_sourceRoutePostCompression
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (typicalProjectors : ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε)
    (paddedAtypEmbedding :
      ADHWFQSWPaddedAtypEmbedding ψ n typicalProjectors.typicalitySlack atyp q e)
    (typicalBobRegister :
      ADHWFQSWIidTypicalBobRegister ψ n δ ε typicalProjectors btyp)
    (typicalRefRegister :
      ADHWFQSWIidTypicalRefRegister ψ n δ ε typicalProjectors rtyp)
    (rateChoice : ADHWFQSWIidRateChoice ψ n δ q e)
    (oneShotCardinalitySideConditions :
      ADHWFQSWIidOneShotCardinalitySideConditions atyp btyp rtyp q e)
    (sourceRouteBlock :
      ADHWFQSWIidSourceRouteBlock ψ n δ ε typicalProjectors atyp btyp rtyp q e) :
    Nonempty (ADHWFQSWIidBlockConstruction ψ n δ ε atyp btyp rtyp q e) :=
  exists_adhwFQSWIidBlockConstruction
    ψ n δ ε atyp btyp rtyp q e
    typicalProjectors paddedAtypEmbedding typicalBobRegister typicalRefRegister
    rateChoice oneShotCardinalitySideConditions sourceRouteBlock

namespace ADHWFQSWIidBlockConstruction

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δ ε : ℝ}
variable {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
variable {q : Type x} {e : Type y}
variable [Fintype atyp] [DecidableEq atyp]
variable [Fintype btyp] [DecidableEq btyp]
variable [Fintype rtyp] [DecidableEq rtyp]
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]

/-- The concrete physical protocol selected by an IID block construction.
Its communication and ebit registers are the finite `q` and `e` chosen by
the ADHW rounding argument. -/
def physicalProtocol
    (B : ADHWFQSWIidBlockConstruction ψ n δ ε atyp btyp rtyp q e) :
    FQSWBlockProtocol ψ n q e e :=
  B.sourceRouteBlock.physicalProtocol

/-- The physical block's computed trace-norm error obeys the rounded source
route estimate. -/
theorem physicalProtocol_traceNormError_le_rounded
    (B : ADHWFQSWIidBlockConstruction ψ n δ ε atyp btyp rtyp q e) :
    B.physicalProtocol.traceNormError ≤
      adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ :=
  B.sourceRouteBlock.physicalProtocol_traceNormError_le_rounded

/-- The physical block's computed normalized error obeys half the rounded
source-route estimate. -/
theorem physicalProtocol_normalizedError_le_rounded_half
    (B : ADHWFQSWIidBlockConstruction ψ n δ ε atyp btyp rtyp q e) :
    B.physicalProtocol.normalizedError ≤
      (1 / 2 : ℝ) * adhwFQSWIidRoundedPostCompressionTraceErrorBound ε n δ :=
  B.sourceRouteBlock.physicalProtocol_normalizedError_le_rounded_half

/-- The finite-register communication bound for the concrete physical block.
The `9δ/4` term is the explicit ceiling slack in the existing ADHW rate
choice. -/
theorem physicalProtocol_communicationRate_le
    (B : ADHWFQSWIidBlockConstruction ψ n δ ε atyp btyp rtyp q e)
    (hn : 0 < n) :
    FQSWBlockProtocol.communicationRate B.physicalProtocol ≤
      ψ.fqswCommunicationRate + (9 / 4 : ℝ) * δ :=
  B.rateChoice.communicationRate_le B.physicalProtocol hn

/-- The finite-register ebit-yield bound for the concrete physical block. -/
theorem physicalProtocol_ebitYieldRate_ge
    (B : ADHWFQSWIidBlockConstruction ψ n δ ε atyp btyp rtyp q e)
    (hn : 0 < n) :
    ψ.fqswEbitYieldRate - 3 * δ ≤
      FQSWBlockProtocol.ebitYieldRate B.physicalProtocol :=
  B.rateChoice.ebitYieldRate_ge B.physicalProtocol hn

/-- Reparameterizing the finite construction with rate slack `δ/3` gives the
source-facing communication window `I(A;R)/2 + δ`. -/
theorem physicalProtocol_communicationRate_le_slack
    {δTarget : ℝ}
    (B : ADHWFQSWIidBlockConstruction
      ψ n (δTarget / 3) ε atyp btyp rtyp q e)
    (hn : 0 < n) (hδ : 0 ≤ δTarget) :
    FQSWBlockProtocol.communicationRate B.physicalProtocol ≤
      ψ.fqswCommunicationRate + δTarget := by
  have hrate := B.physicalProtocol_communicationRate_le hn
  nlinarith

/-- Reparameterizing the finite construction with rate slack `δ/3` gives the
source-facing ebit-yield window `I(A;B)/2 - δ`. -/
theorem physicalProtocol_ebitYieldRate_ge_slack
    {δTarget : ℝ}
    (B : ADHWFQSWIidBlockConstruction
      ψ n (δTarget / 3) ε atyp btyp rtyp q e)
    (hn : 0 < n) :
    ψ.fqswEbitYieldRate - δTarget ≤
      FQSWBlockProtocol.ebitYieldRate B.physicalProtocol := by
  have hyield := B.physicalProtocol_ebitYieldRate_ge hn
  convert hyield using 1
  ring

end ADHWFQSWIidBlockConstruction

/-- One finite mixed-slack ADHW i.i.d. FQSW block.  The simultaneous typical
support and compressed source use `δtyp`; the rounded communication and ebit
registers use `δrate`, which is the slack exposed to the public rate and error
estimates. -/
structure ADHWFQSWIidMixedBlockConstruction
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δtyp δrate ε : ℝ)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] where
  typicalProjectors : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε
  paddedAtypEmbedding :
    ADHWFQSWPaddedAtypEmbedding ψ n typicalProjectors.typicalitySlack atyp q e
  typicalBobRegister :
    ADHWFQSWIidTypicalBobRegister ψ n δtyp ε typicalProjectors btyp
  typicalRefRegister :
    ADHWFQSWIidTypicalRefRegister ψ n δtyp ε typicalProjectors rtyp
  balancedRateChoice : ADHWFQSWIidBalancedRateChoice ψ n δrate q e
  oneShotCardinalitySideConditions :
    ADHWFQSWIidOneShotCardinalitySideConditions atyp btyp rtyp q e
  sourceRouteBlock :
    ADHWFQSWIidMixedSourceRouteBlock
      ψ n δtyp δrate ε typicalProjectors atyp btyp rtyp q e

/-- Assemble one finite mixed-slack ADHW block from the already constructed
typicality, padding, rounded-rate, one-shot, compression, and source-route
records. -/
theorem exists_adhwFQSWIidMixedBlockConstruction
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δtyp δrate ε : ℝ)
    (atyp : Type p) (btyp : Type u1) (rtyp : Type v1)
    (q : Type x) (e : Type y)
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (typicalProjectors : ADHWFQSWSimultaneousTypicalProjectors ψ n δtyp ε)
    (paddedAtypEmbedding :
      ADHWFQSWPaddedAtypEmbedding ψ n typicalProjectors.typicalitySlack atyp q e)
    (typicalBobRegister :
      ADHWFQSWIidTypicalBobRegister ψ n δtyp ε typicalProjectors btyp)
    (typicalRefRegister :
      ADHWFQSWIidTypicalRefRegister ψ n δtyp ε typicalProjectors rtyp)
    (balancedRateChoice : ADHWFQSWIidBalancedRateChoice ψ n δrate q e)
    (oneShotCardinalitySideConditions :
      ADHWFQSWIidOneShotCardinalitySideConditions atyp btyp rtyp q e)
    (sourceRouteBlock :
      ADHWFQSWIidMixedSourceRouteBlock
        ψ n δtyp δrate ε typicalProjectors atyp btyp rtyp q e) :
    Nonempty
      (ADHWFQSWIidMixedBlockConstruction
        ψ n δtyp δrate ε atyp btyp rtyp q e) :=
  ⟨{ typicalProjectors := typicalProjectors
     paddedAtypEmbedding := paddedAtypEmbedding
     typicalBobRegister := typicalBobRegister
     typicalRefRegister := typicalRefRegister
     balancedRateChoice := balancedRateChoice
     oneShotCardinalitySideConditions := oneShotCardinalitySideConditions
     sourceRouteBlock := sourceRouteBlock }⟩

theorem ADHWFQSWIidMixedBlockConstruction.rateChoice
    {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
    {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
    {q : Type x} {e : Type y}
    [Fintype atyp] [DecidableEq atyp]
    [Fintype btyp] [DecidableEq btyp]
    [Fintype rtyp] [DecidableEq rtyp]
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (B : ADHWFQSWIidMixedBlockConstruction ψ n δtyp δrate ε atyp btyp rtyp q e) :
    ADHWFQSWIidRateChoice ψ n δrate q e :=
  B.balancedRateChoice.rateChoice

namespace ADHWFQSWIidMixedBlockConstruction

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ} {δtyp δrate ε : ℝ}
variable {atyp : Type p} {btyp : Type u1} {rtyp : Type v1}
variable {q : Type x} {e : Type y}
variable [Fintype atyp] [DecidableEq atyp]
variable [Fintype btyp] [DecidableEq btyp]
variable [Fintype rtyp] [DecidableEq rtyp]
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]

/-- The concrete physical protocol selected by the mixed-slack IID route. -/
def physicalProtocol
    (B : ADHWFQSWIidMixedBlockConstruction
      ψ n δtyp δrate ε atyp btyp rtyp q e) :
    FQSWBlockProtocol ψ n q e e :=
  B.sourceRouteBlock.physicalProtocol

/-- The actual physical block obeys the exact ADHW full-source trace-norm
bound. -/
theorem physicalProtocol_traceNormError_le
    (B : ADHWFQSWIidMixedBlockConstruction
      ψ n δtyp δrate ε atyp btyp rtyp q e) :
    B.physicalProtocol.traceNormError ≤
      adhwFQSWIidPostCompressionTraceErrorBound ε n δrate :=
  B.sourceRouteBlock.physicalProtocol_traceNormError_le

/-- The actual physical block's normalized error obeys half the exact ADHW
full-source bound. -/
theorem physicalProtocol_normalizedError_le
    (B : ADHWFQSWIidMixedBlockConstruction
      ψ n δtyp δrate ε atyp btyp rtyp q e) :
    B.physicalProtocol.normalizedError ≤
      (1 / 2 : ℝ) * adhwFQSWIidPostCompressionTraceErrorBound ε n δrate :=
  B.sourceRouteBlock.physicalProtocol_normalizedError_le

/-- Concrete communication-rate bound for a mixed-slack IID block. -/
theorem physicalProtocol_communicationRate_le
    (B : ADHWFQSWIidMixedBlockConstruction
      ψ n δtyp δrate ε atyp btyp rtyp q e)
    (hn : 0 < n) :
    FQSWBlockProtocol.communicationRate B.physicalProtocol ≤
      ψ.fqswCommunicationRate + (9 / 4 : ℝ) * δrate :=
  B.rateChoice.communicationRate_le B.physicalProtocol hn

/-- Concrete ebit-yield bound for a mixed-slack IID block. -/
theorem physicalProtocol_ebitYieldRate_ge
    (B : ADHWFQSWIidMixedBlockConstruction
      ψ n δtyp δrate ε atyp btyp rtyp q e)
    (hn : 0 < n) :
    ψ.fqswEbitYieldRate - 3 * δrate ≤
      FQSWBlockProtocol.ebitYieldRate B.physicalProtocol :=
  B.rateChoice.ebitYieldRate_ge B.physicalProtocol hn

/-- A mixed construction with rate slack `δ/3` meets the source-facing
communication window `I(A;R)/2 + δ`, independently of its typicality slack. -/
theorem physicalProtocol_communicationRate_le_slack
    {δTarget : ℝ}
    (B : ADHWFQSWIidMixedBlockConstruction
      ψ n δtyp (δTarget / 3) ε atyp btyp rtyp q e)
    (hn : 0 < n) (hδ : 0 ≤ δTarget) :
    FQSWBlockProtocol.communicationRate B.physicalProtocol ≤
      ψ.fqswCommunicationRate + δTarget := by
  have hrate := B.physicalProtocol_communicationRate_le hn
  nlinarith

/-- A mixed construction with rate slack `δ/3` meets the source-facing
ebit-yield window `I(A;B)/2 - δ`. -/
theorem physicalProtocol_ebitYieldRate_ge_slack
    {δTarget : ℝ}
    (B : ADHWFQSWIidMixedBlockConstruction
      ψ n δtyp (δTarget / 3) ε atyp btyp rtyp q e)
    (hn : 0 < n) :
    ψ.fqswEbitYieldRate - δTarget ≤
      FQSWBlockProtocol.ebitYieldRate B.physicalProtocol := by
  have hyield := B.physicalProtocol_ebitYieldRate_ge hn
  convert hyield using 1
  ring

end ADHWFQSWIidMixedBlockConstruction

/-- Mixed-slack no-witness assembly of one finite ADHW i.i.d. block.  It reuses
the existing simultaneous-typicality, balanced-cardinality, compressed-source,
and one-shot APIs, then closes the tail with the source-route mixed `skoro`
estimate. -/
theorem exists_adhwFQSWIidMixedBlockConstruction_eventually
    (ψ : PureVector (Prod (Prod a b) r)) {δtyp δrate ε : ℝ}
    (hδtyp : 0 < δtyp) (hδrate : 0 < δrate) (hε : 0 < ε)
    (hδtyp_le_eighth : δtyp ≤ δrate / 8) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (atyp : Type u), ∃ (_ : Fintype atyp), ∃ (_ : DecidableEq atyp),
        ∃ (btyp : Type v), ∃ (_ : Fintype btyp), ∃ (_ : DecidableEq btyp),
          ∃ (rtyp : Type w), ∃ (_ : Fintype rtyp), ∃ (_ : DecidableEq rtyp),
            ∃ (q : Type x), ∃ (_ : Fintype q), ∃ (_ : DecidableEq q),
              ∃ (_ : Nonempty q), ∃ (e : Type y), ∃ (_ : Fintype e),
                ∃ (_ : DecidableEq e), ∃ (_ : Nonempty e),
                  Nonempty
                    (ADHWFQSWIidMixedBlockConstruction
                      ψ n δtyp δrate ε atyp btyp rtyp q e) := by
  obtain ⟨Ndata, hdata⟩ :=
    exists_adhwFQSWIidBalancedCardinalityChoice_mixed_eventually
      (ψ := ψ) hδtyp hδrate hε (by linarith)
  let Nlarge : ℕ := Nat.ceil (4 / δrate)
  refine ⟨max Ndata Nlarge, ?_⟩
  intro n hn
  have hn_data : n ≥ Ndata := le_trans (Nat.le_max_left _ _) hn
  have hn_large_nat : n ≥ Nlarge := le_trans (Nat.le_max_right _ _) hn
  have hn_large : 4 ≤ (n : ℝ) * δrate := by
    have hceil : 4 / δrate ≤ (Nlarge : ℝ) := by
      simpa [Nlarge] using Nat.le_ceil (4 / δrate)
    have hnLargeR : (Nlarge : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_large_nat
    have hbound : 4 / δrate ≤ (n : ℝ) := hceil.trans hnLargeR
    have hmul := mul_le_mul_of_nonneg_right hbound hδrate.le
    have hcancel : (4 / δrate) * δrate = (4 : ℝ) := by
      field_simp [ne_of_gt hδrate]
    nlinarith
  obtain ⟨T, atyp, hatypF, hatypD, btyp, hbtypF, hbtypD,
      rtyp, hrtypF, hrtypD, q, hqF, hqD, hqN, e, heF, heD, heN,
      hatypDim, hbtypReg, hrtypReg, hbalancedRate, hbalancedCardinality⟩ :=
    hdata n hn_data
  let _ : Fintype atyp := hatypF
  let _ : DecidableEq atyp := hatypD
  let _ : Fintype btyp := hbtypF
  let _ : DecidableEq btyp := hbtypD
  let _ : Fintype rtyp := hrtypF
  let _ : DecidableEq rtyp := hrtypD
  let _ : Fintype q := hqF
  let _ : DecidableEq q := hqD
  let _ : Nonempty q := hqN
  let _ : Fintype e := heF
  let _ : DecidableEq e := heD
  let _ : Nonempty e := heN
  obtain ⟨Btyp⟩ := hbtypReg
  obtain ⟨Rtyp⟩ := hrtypReg
  obtain ⟨Rbalanced⟩ := hbalancedRate
  obtain ⟨Bcard⟩ := hbalancedCardinality
  obtain ⟨P, hside⟩ :=
    Bcard.to_padded_and_sideConditions (δtyp := T.typicalitySlack) hatypDim
  obtain ⟨Sside⟩ := hside
  obtain ⟨W⟩ := exists_adhwFQSWIidCompressedSourceWitness T P Btyp Rtyp
  obtain ⟨H⟩ := exists_adhwFQSWIidCompressedOneShotBound W.source Sside
  have honeShotTail :
      adhwFQSWOneShotErrorBound W.source q ≤
        Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δrate / 4)) :=
    W.oneShotTail_le_mixed Rbalanced hδrate.le hδtyp_le_eighth hn_large
  obtain ⟨Route⟩ :=
    exists_adhwFQSWIidMixedSourceRouteBlock W H honeShotTail
  obtain ⟨Bmixed⟩ :=
    exists_adhwFQSWIidMixedBlockConstruction
      ψ n δtyp δrate ε atyp btyp rtyp q e
      T P Btyp Rtyp Rbalanced Sside Route
  refine ⟨atyp, hatypF, hatypD, btyp, hbtypF, hbtypD,
    rtyp, hrtypF, hrtypD, q, hqF, hqD, hqN, e, heF, heD, heN, ?_⟩
  exact ⟨Bmixed⟩

/-- ADHW i.i.d. FQSW construction record: the typical-subspace and Schumacher
compression route of fqsw.tex lines 1093-1180 supplies the block protocols
used by the asymptotic direct theorem. -/
structure ADHWFQSWIidConstruction (ψ : PureVector (Prod (Prod a b) r)) where
  typical_rate_blocks :
    ∀ δ : ℝ, 0 < δ → ∀ εerr : ℝ, 0 < εerr →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ (atyp : Type u), ∃ (_ : Fintype atyp), ∃ (_ : DecidableEq atyp),
          ∃ (btyp : Type v), ∃ (_ : Fintype btyp), ∃ (_ : DecidableEq btyp),
            ∃ (rtyp : Type w), ∃ (_ : Fintype rtyp), ∃ (_ : DecidableEq rtyp),
              ∃ (q : Type x), ∃ (_ : Fintype q), ∃ (_ : DecidableEq q),
                ∃ (_ : Nonempty q), ∃ (e : Type y), ∃ (_ : Fintype e),
                  ∃ (_ : DecidableEq e), ∃ (_ : Nonempty e),
                    Nonempty
                      (ADHWFQSWIidMixedBlockConstruction
                        ψ n (δ / 8) δ εerr atyp btyp rtyp q e)

/-- No-witness ADHW i.i.d. FQSW construction record.  The source route uses
`δtyp = δrate / 8`, which restores the exact ADHW `2^(-nδrate/4)` tail after
the finite-register rounding estimates. -/
theorem exists_adhwFQSWIidConstruction
    (ψ : PureVector (Prod (Prod a b) r)) :
    Nonempty (ADHWFQSWIidConstruction.{u, v, w, x, y} ψ) := by
  refine ⟨{ typical_rate_blocks := ?_ }⟩
  intro δ hδ εerr hεerr
  exact
    exists_adhwFQSWIidMixedBlockConstruction_eventually
      (ψ := ψ) (δtyp := δ / 8) (δrate := δ) (ε := εerr)
      (by positivity) hδ hεerr le_rfl

namespace PureVector

variable (ψ : PureVector (Prod (Prod a b) r))

/-- The ADHW i.i.d. construction supplies concrete physical block protocols
with the source communication rate, ebit-yield rate, and vanishing computed
trace-distance error; see fqsw.tex lines 1093-1180. -/
theorem fqsw_direct_achievable_of_iidConstruction
    (h : ADHWFQSWIidConstruction.{u, v, w, x, y} ψ) :
    PureVector.IsAchievableFQSW.{u, v, w, x, y, y} ψ := by
  intro δ hδ εerr hεerr
  have hδ3_pos : 0 < δ / 3 := by positivity
  have hε4_pos : 0 < εerr / 4 := by positivity
  obtain ⟨Nblocks, hblocks⟩ := h.typical_rate_blocks (δ / 3) hδ3_pos (εerr / 4) hε4_pos
  obtain ⟨Nerr, hNerr⟩ :=
    eventually_half_adhwFQSWIidPostCompressionTraceErrorBound_le
      (δ := δ / 3) (ε := εerr) hδ3_pos hεerr
  refine ⟨max (max Nblocks Nerr) 1, fun n hn => ?_⟩
  have hn_blocks : n ≥ Nblocks := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn_err : n ≥ Nerr := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn_pos : 0 < n := by
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hn)
  obtain ⟨atyp, hatypF, hatypD, btyp, hbtypF, hbtypD, rtyp, hrtypF, hrtypD,
      q, hqF, hqD, hqN, e, heF, heD, heN, hBnonempty⟩ :=
    hblocks n hn_blocks
  let _ : Fintype atyp := hatypF
  let _ : DecidableEq atyp := hatypD
  let _ : Fintype btyp := hbtypF
  let _ : DecidableEq btyp := hbtypD
  let _ : Fintype rtyp := hrtypF
  let _ : DecidableEq rtyp := hrtypD
  let _ : Fintype q := hqF
  let _ : DecidableEq q := hqD
  let _ : Nonempty q := hqN
  let _ : Fintype e := heF
  let _ : DecidableEq e := heD
  let _ : Nonempty e := heN
  obtain ⟨B⟩ := hBnonempty
  refine ⟨q, hqF, hqD, e, heF, heD, heN, e, heF, heD, B.physicalProtocol, ?_, ?_, ?_⟩
  · exact B.physicalProtocol_communicationRate_le_slack hn_pos hδ.le
  · exact B.physicalProtocol_ebitYieldRate_ge_slack hn_pos
  · exact B.physicalProtocol_normalizedError_le.trans (hNerr n hn_err)

/-- Source-faithful ADHW FQSW direct achievability: every finite-dimensional
pure tripartite source admits concrete physical block protocols with quantum
communication rate approaching `I(A;R)/2`, ebit-yield rate approaching
`I(A;B)/2`, and vanishing computed trace-distance error, following fqsw.tex
lines 1093-1180. -/
theorem fqsw_direct_achievable :
    PureVector.IsAchievableFQSW.{u, v, w, x, y, y} ψ :=
  Nonempty.elim (exists_adhwFQSWIidConstruction ψ)
    (fqsw_direct_achievable_of_iidConstruction ψ)

end PureVector

end

end QIT
