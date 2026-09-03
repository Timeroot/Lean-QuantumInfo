/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Purification.Conditioning
public import QIT.Information.Renyi.Renyi

/-!
# Fixed-reference conditional Petz Renyi entropy

Matrix-level fixed-side conditional Petz Renyi entropy candidate

`H_α(A|B)_{ρ|σ} = (1 / (1 - α)) log₂ Tr(ρ_AB^α (I_A ⊗ σ_B)^(1-α))`.

This file deliberately defines the per-`σ_B` candidate only. The optimized
conditional Petz entropy and tensor-power AEP limits are downstream structure.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v w x

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

namespace State

/-- The matrix `I_A ⊗ σ_B` is positive semidefinite. -/
theorem identityTensorStateMatrix_posSemidef_of_state (σ : State b) :
    (identityTensorStateMatrix (a := a) σ).PosSemidef := by
  change (Matrix.kronecker (1 : CMatrix a) σ.matrix).PosSemidef
  exact Matrix.PosSemidef.one.kronecker σ.pos

/-- The matrix `I_A ⊗ σ_B` is positive definite whenever `σ_B` is. -/
theorem identityTensorStateMatrix_posDef_of_posDef
    (σ : State b) (hσ : σ.matrix.PosDef) :
    (identityTensorStateMatrix (a := a) σ).PosDef := by
  change (Matrix.kronecker (1 : CMatrix a) σ.matrix).PosDef
  exact Matrix.PosDef.one.kronecker hσ

/-- The fixed-side conditional Petz Renyi entropy candidate.

This is the matrix-level, non-optimized quantity with reference side state
`σ_B`, matching the FQAEP kernel
`(1 / (1 - α)) log₂ Tr(ρ_AB^α (I_A ⊗ σ_B)^(1-α))`. The positivity witnesses
record the usual full-rank domain; they are not computationally inspected by
`CFC.rpow`. -/
def conditionalPetzRenyiEntropyCandidate
    (ρ : State (Prod a b)) (_hρ : ρ.matrix.PosDef)
    (σ : State b) (_hσ : σ.matrix.PosDef)
    (α : ℝ) (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let A := CFC.rpow ρ.matrix α
  let B := CFC.rpow τ (1 - α)
  (1 / (1 - α)) * log2 ((A * B).trace.re)

@[simp]
theorem conditionalPetzRenyiEntropyCandidate_eq
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α hα_pos hα_ne_one =
      let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
      let A := CFC.rpow ρ.matrix α
      let B := CFC.rpow τ (1 - α)
      (1 / (1 - α)) * log2 ((A * B).trace.re) :=
  rfl

/-- The trace term inside the fixed-side conditional Petz candidate. -/
def conditionalPetzRenyiTraceTerm
    (ρ : State (Prod a b)) (σ : State b) (α : ℝ) : ℝ :=
  ((CFC.rpow ρ.matrix α *
    CFC.rpow (identityTensorStateMatrix (a := a) σ) (1 - α)).trace).re

/-- The fixed-side conditional Petz Renyi entropy with arbitrary state `ρ_AB`
and full-rank reference `σ_B`.

The source proof of TCR 2008, Theorem `thm:entropy-ineq`, only needs the
reference side to be full-rank: the positive power `ρ_AB^α` is well-defined for
singular positive semidefinite states by the CFC zero-on-kernel convention. -/
def conditionalPetzRenyiEntropyCandidateFullReference
    (ρ : State (Prod a b)) (σ : State b) (_hσ : σ.matrix.PosDef)
    (α : ℝ) (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  (1 / (1 - α)) * log2 (ρ.conditionalPetzRenyiTraceTerm σ α)

@[simp]
theorem conditionalPetzRenyiEntropyCandidateFullReference_eq
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one =
      (1 / (1 - α)) * log2 (ρ.conditionalPetzRenyiTraceTerm σ α) :=
  rfl

theorem conditionalPetzRenyiEntropyCandidate_eq_fullReference
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α hα_pos hα_ne_one =
      ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α hα_pos hα_ne_one := by
  rfl

/-- The fixed-reference Petz trace term is nonnegative for arbitrary finite
states, using the CFC zero-on-kernel convention for powers. -/
theorem conditionalPetzRenyiTraceTerm_nonneg
    (ρ : State (Prod a b)) (σ : State b) (α : ℝ) :
    0 ≤ ρ.conditionalPetzRenyiTraceTerm σ α := by
  dsimp [conditionalPetzRenyiTraceTerm]
  exact cMatrix_trace_mul_posSemidef_re_nonneg
    (cMatrix_rpow_posSemidef (A := ρ.matrix) (s := α) ρ.pos)
    (cMatrix_rpow_posSemidef
      (A := identityTensorStateMatrix (a := a) σ) (s := 1 - α)
      (identityTensorStateMatrix_posSemidef_of_state (a := a) σ))

/-- With a full-rank reference, the fixed-reference Petz trace term is strictly
positive for every normalized left state. -/
theorem conditionalPetzRenyiTraceTerm_pos_of_fullReference
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) (α : ℝ) :
    0 < ρ.conditionalPetzRenyiTraceTerm σ α := by
  dsimp [conditionalPetzRenyiTraceTerm]
  let M : CMatrix (Prod a b) := CFC.rpow ρ.matrix α
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  have hM : M.PosSemidef := cMatrix_rpow_posSemidef (A := ρ.matrix) (s := α) ρ.pos
  have hτ : τ.PosSemidef :=
    (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ).posSemidef
  have hMne : M ≠ 0 := by
    have hpow_pos : 0 < psdTracePower ρ.matrix ρ.pos (p := α) :=
      psdTracePower_pos_of_ne_zero ρ.matrix ρ.pos ρ.matrix_ne_zero
    intro hzero
    have htrace_zero : psdTracePower ρ.matrix ρ.pos (p := α) = 0 := by
      simpa [psdTracePower, M] using congrArg (fun X : CMatrix (Prod a b) => X.trace.re) hzero
    linarith
  have hsupport : Matrix.Supports M τ :=
    Matrix.Supports.of_right_posDef M τ
      (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)
  simpa [M, τ] using
    trace_mul_cMatrix_rpow_pos_of_support
      (M := M) (N := τ) hM hτ hMne hsupport (1 - α)

private theorem referenceIsometry_applyMatrixRight_eq_kronecker_conj
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (V : ReferenceIsometry b bPlus) (X : CMatrix (Prod a b)) :
    V.applyMatrixRight X =
      Matrix.kronecker (1 : CMatrix a) V.matrix * X *
        Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a) V.matrix) := by
  ext x y
  simp [ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.conjTranspose_kronecker, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_ite_eq', apply_ite,
    mul_assoc, mul_comm]

private theorem trace_isometry_conj
    {r : Type*} [Fintype r] [DecidableEq r]
    (V : Matrix r a ℂ) (hV : Matrix.conjTranspose V * V = (1 : CMatrix a))
    (X : CMatrix a) :
    (V * X * Matrix.conjTranspose V).trace = X.trace := by
  calc
    (V * X * Matrix.conjTranspose V).trace =
        ((V * X) * Matrix.conjTranspose V).trace := by
          simp [Matrix.mul_assoc]
    _ = (Matrix.conjTranspose V * (V * X)).trace := by
          rw [Matrix.trace_mul_comm]
    _ = ((Matrix.conjTranspose V * V) * X).trace := by
          simp [Matrix.mul_assoc]
    _ = X.trace := by
          rw [hV, Matrix.one_mul]

/-- Tensoring a PSD right-reference by an identity matrix commutes with all
real powers.  The identity factor contributes eigenvalue `1`, so no full-rank
assumption is needed on the right reference. -/
theorem cMatrix_rpow_identity_kronecker
    (N : CMatrix b) (hN : N.PosSemidef) (s : ℝ) :
    CFC.rpow (Matrix.kronecker (1 : CMatrix a) N) s =
      Matrix.kronecker (1 : CMatrix a) (CFC.rpow N s) := by
  classical
  let U₁ : Matrix.unitaryGroup a ℂ := 1
  let U₂ : Matrix.unitaryGroup b ℂ := hN.isHermitian.eigenvectorUnitary
  let U : Matrix.unitaryGroup (Prod a b) ℂ :=
    ⟨Matrix.kronecker (U₁ : CMatrix a) (U₂ : CMatrix b),
      Matrix.kronecker_mem_unitary U₁.2 U₂.2⟩
  let d : b → ℝ := hN.isHermitian.eigenvalues
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    exact hN.eigenvalues_nonneg i
  have hN_spec :
      N = (U₂ : CMatrix b) *
          (Matrix.diagonal fun i => ((d i : ℝ) : ℂ)) *
            star (U₂ : CMatrix b) := by
    simpa [U₂, d, Matrix.IsHermitian.spectral_theorem,
      Unitary.conjStarAlgAut_apply] using hN.isHermitian.spectral_theorem
  have hleft_arg :
      Matrix.kronecker (1 : CMatrix a) N =
        (U : CMatrix (Prod a b)) *
          (Matrix.diagonal fun i : Prod a b => ((d i.2 : ℝ) : ℂ)) *
            star (U : CMatrix (Prod a b)) := by
    rw [hN_spec]
    ext x y
    by_cases hxy : x.1 = y.1
    · simp [U, U₁, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Matrix.diagonal, Fintype.sum_prod_type,
        Finset.mul_sum, Finset.sum_ite_eq', apply_ite,
        hxy, mul_assoc, mul_left_comm, mul_comm]
    · simp [U, U₁, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Matrix.diagonal, Fintype.sum_prod_type,
        Finset.mul_sum, Finset.sum_ite_eq', apply_ite,
        hxy, mul_assoc, mul_left_comm, mul_comm]
  have hleft_pow :
      CFC.rpow (Matrix.kronecker (1 : CMatrix a) N) s =
        (U : CMatrix (Prod a b)) *
          (Matrix.diagonal fun i : Prod a b => ((d i.2 ^ s : ℝ) : ℂ)) *
            star (U : CMatrix (Prod a b)) := by
    rw [hleft_arg]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal
      U (fun i : Prod a b => d i.2) (fun i => hd i.2) s
  have hN_pow :
      CFC.rpow N s =
        (U₂ : CMatrix b) *
          (Matrix.diagonal fun i => ((d i ^ s : ℝ) : ℂ)) *
            star (U₂ : CMatrix b) := by
    rw [hN_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U₂ d hd s
  rw [hleft_pow, hN_pow]
  ext x y
  by_cases hxy : x.1 = y.1
  · simp [U, U₁, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Matrix.diagonal, Fintype.sum_prod_type,
      Finset.mul_sum, Finset.sum_ite_eq', apply_ite,
      hxy, mul_assoc, mul_left_comm, mul_comm]
  · simp [U, U₁, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Matrix.diagonal, Fintype.sum_prod_type,
      Finset.mul_sum, Finset.sum_ite_eq', apply_ite,
      hxy, mul_assoc, mul_left_comm, mul_comm]

/-- Compressing the conditioning register to the support of the canonical
reference preserves the fixed-reference Petz trace term.

The positive joint-state power is transported through the support isometry by
`cMatrix_rpow_isometry_conj`; the possibly negative reference power is
transported only through the support-specific reconstruction lemma for the
side marginal. -/
theorem conditionalPetzRenyiTraceTerm_conditioningSupportCompressedState
    (ρ : State (Prod a b)) (α : ℝ) (hα_pos : 0 < α) (h_one_sub_ne : 1 - α ≠ 0) :
    ρ.conditioningSupportCompressedState.conditionalPetzRenyiTraceTerm
      ρ.conditioningSupportCompressedState.marginalB α =
    ρ.conditionalPetzRenyiTraceTerm ρ.marginalB α := by
  classical
  let ρc : State (Prod a (psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos)) :=
    ρ.conditioningSupportCompressedState
  let N : CMatrix b := ρ.marginalB.matrix
  let hN : N.PosSemidef := ρ.marginalB.pos
  let Vb : Matrix b (psdSupportIndex N hN) ℂ := psdSupportIsometry N hN
  let Vref : ReferenceIsometry (psdSupportIndex N hN) b :=
    psdSupportReferenceIsometry N hN
  let W : Matrix (Prod a b) (Prod a (psdSupportIndex N hN)) ℂ :=
    Matrix.kronecker (1 : CMatrix a) Vb
  let τc : CMatrix (Prod a (psdSupportIndex N hN)) :=
    identityTensorStateMatrix (a := a) ρc.marginalB
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) ρ.marginalB
  have hVb : Matrix.conjTranspose Vb * Vb =
      (1 : CMatrix (psdSupportIndex N hN)) := by
    simpa [Vb] using psdSupportIsometry_isometry N hN
  have hW : Matrix.conjTranspose W * W =
      (1 : CMatrix (Prod a (psdSupportIndex N hN))) := by
    rw [show Matrix.conjTranspose W =
        Matrix.kronecker (1 : CMatrix a) (Matrix.conjTranspose Vb) by
          simp [W, Matrix.conjTranspose_kronecker]]
    rw [show W = Matrix.kronecker (1 : CMatrix a) Vb by rfl]
    calc
      Matrix.kronecker (1 : CMatrix a) (Matrix.conjTranspose Vb) *
          Matrix.kronecker (1 : CMatrix a) Vb =
          Matrix.kronecker ((1 : CMatrix a) * (1 : CMatrix a))
            (Matrix.conjTranspose Vb * Vb) := by
            simpa using
              (Matrix.mul_kronecker_mul (1 : CMatrix a) (1 : CMatrix a)
                (Matrix.conjTranspose Vb) Vb).symm
      _ = 1 := by
            rw [hVb]
            simp
  have hρ_embed :
      ρ.matrix = W * ρc.matrix * Matrix.conjTranspose W := by
    have hstate :
        ρc.conditioningIsometryApply Vref = ρ := by
      simpa [ρc, Vref, N, hN] using
        ρ.conditioningSupportCompressedState_conditioningIsometryApply
    have hmat := congrArg State.matrix hstate
    rw [← hmat, conditioningIsometryApply_matrix]
    simpa [W, Vref, Vb, psdSupportReferenceIsometry] using
      referenceIsometry_applyMatrixRight_eq_kronecker_conj
        (a := a) Vref ρc.matrix
  have hρ_pow :
      CFC.rpow ρ.matrix α =
        W * CFC.rpow ρc.matrix α * Matrix.conjTranspose W := by
    rw [hρ_embed]
    exact cMatrix_rpow_isometry_conj W ρc.pos hW hα_pos
  have hρcB_matrix :
      ρc.marginalB.matrix = psdSupportCompress N hN N := by
    simpa [ρc, N, hN] using
      ρ.conditioningSupportCompressedState_marginalB_matrix
  have hB_pow :
      Vb * CFC.rpow ρc.marginalB.matrix (1 - α) *
          Matrix.conjTranspose Vb =
        CFC.rpow N (1 - α) := by
    rw [hρcB_matrix]
    simpa [Vb] using
      cMatrix_rpow_psdSupportCompress_reconstruct_self N hN h_one_sub_ne
  have hτc_pow :
      CFC.rpow τc (1 - α) =
        Matrix.kronecker (1 : CMatrix a)
          (CFC.rpow ρc.marginalB.matrix (1 - α)) := by
    simpa [τc, identityTensorStateMatrix] using
      cMatrix_rpow_identity_kronecker
        (a := a) ρc.marginalB.matrix ρc.marginalB.pos (1 - α)
  have hτ_pow :
      CFC.rpow τ (1 - α) =
        W * CFC.rpow τc (1 - α) * Matrix.conjTranspose W := by
    rw [hτc_pow]
    have hτ_orig :
        CFC.rpow τ (1 - α) =
          Matrix.kronecker (1 : CMatrix a) (CFC.rpow N (1 - α)) := by
      simpa [τ, N, identityTensorStateMatrix] using
        cMatrix_rpow_identity_kronecker
          (a := a) N hN (1 - α)
    rw [hτ_orig, ← hB_pow]
    rw [show Matrix.conjTranspose W =
        Matrix.kronecker (1 : CMatrix a) (Matrix.conjTranspose Vb) by
          simp [W, Matrix.conjTranspose_kronecker]]
    rw [show W = Matrix.kronecker (1 : CMatrix a) Vb by rfl]
    let R : CMatrix (psdSupportIndex N hN) :=
      CFC.rpow ρc.marginalB.matrix (1 - α)
    calc
      Matrix.kronecker (1 : CMatrix a) (Vb * R * Matrix.conjTranspose Vb) =
          Matrix.kronecker ((1 : CMatrix a) * (1 : CMatrix a))
            (Vb * (R * Matrix.conjTranspose Vb)) := by
            simp [R, Matrix.mul_assoc]
      _ = Matrix.kronecker (1 : CMatrix a) Vb *
          Matrix.kronecker (1 : CMatrix a) (R * Matrix.conjTranspose Vb) := by
            simpa using
              Matrix.mul_kronecker_mul (1 : CMatrix a) (1 : CMatrix a)
                Vb (R * Matrix.conjTranspose Vb)
      _ = Matrix.kronecker (1 : CMatrix a) Vb *
          (Matrix.kronecker (1 : CMatrix a) R *
            Matrix.kronecker (1 : CMatrix a) (Matrix.conjTranspose Vb)) := by
            congr 1
            simpa using
              Matrix.mul_kronecker_mul (1 : CMatrix a) (1 : CMatrix a)
                R (Matrix.conjTranspose Vb)
      _ = Matrix.kronecker (1 : CMatrix a) Vb *
          Matrix.kronecker (1 : CMatrix a)
            (CFC.rpow ρc.marginalB.matrix (1 - α)) *
          Matrix.kronecker (1 : CMatrix a) (Matrix.conjTranspose Vb) := by
            simpa [R] using (Matrix.mul_assoc
              (Matrix.kronecker (1 : CMatrix a) Vb)
              (Matrix.kronecker (1 : CMatrix a) R)
              (Matrix.kronecker (1 : CMatrix a) (Matrix.conjTranspose Vb))).symm
  dsimp [conditionalPetzRenyiTraceTerm]
  change
    ((CFC.rpow ρc.matrix α * CFC.rpow τc (1 - α)).trace).re =
      ((CFC.rpow ρ.matrix α * CFC.rpow τ (1 - α)).trace).re
  rw [hρ_pow, hτ_pow]
  have htrace :
      ((W * CFC.rpow ρc.matrix α * Matrix.conjTranspose W) *
          (W * CFC.rpow τc (1 - α) * Matrix.conjTranspose W)).trace =
        (CFC.rpow ρc.matrix α * CFC.rpow τc (1 - α)).trace := by
    calc
      ((W * CFC.rpow ρc.matrix α * Matrix.conjTranspose W) *
          (W * CFC.rpow τc (1 - α) * Matrix.conjTranspose W)).trace =
          (W * (CFC.rpow ρc.matrix α * CFC.rpow τc (1 - α)) *
            Matrix.conjTranspose W).trace := by
            let A : CMatrix (Prod a (psdSupportIndex N hN)) :=
              CFC.rpow ρc.matrix α
            let B : CMatrix (Prod a (psdSupportIndex N hN)) :=
              CFC.rpow τc (1 - α)
            have halg :
                (W * A * Matrix.conjTranspose W) *
                    (W * B * Matrix.conjTranspose W) =
                  W * (A * B) * Matrix.conjTranspose W := by
              calc
                (W * A * Matrix.conjTranspose W) *
                    (W * B * Matrix.conjTranspose W) =
                    W * A * (Matrix.conjTranspose W * W) * B *
                      Matrix.conjTranspose W := by
                      simp [Matrix.mul_assoc]
                _ = W * A * (1 : CMatrix (Prod a (psdSupportIndex N hN))) *
                    B * Matrix.conjTranspose W := by
                      rw [hW]
                _ = W * (A * B) * Matrix.conjTranspose W := by
                      simp [Matrix.mul_assoc]
            simpa [A, B] using congrArg Matrix.trace halg
      _ = (CFC.rpow ρc.matrix α * CFC.rpow τc (1 - α)).trace :=
            trace_isometry_conj W hW _
  exact congrArg Complex.re htrace.symm

/-- Regroup two bipartite product systems from `(A × B) × (C × D)` to
`(A × C) × (B × D)`.

This is the finite basis permutation needed to read the Kronecker product of
two `AB`/`CD` states as one grouped conditional state on `AC|BD`. -/
def conditionalPetzRenyiProductGroupingEquiv
    (a : Type u) (b : Type v) (c : Type w) (d : Type x) :
    Prod (Prod a b) (Prod c d) ≃ Prod (Prod a c) (Prod b d) where
  toFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  invFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  left_inv := by
    intro z
    cases z with
    | mk ab cd =>
        cases ab
        cases cd
        rfl
  right_inv := by
    intro z
    cases z with
    | mk ac bd =>
        cases ac
        cases bd
        rfl

omit [Fintype a] [Fintype c] in
/-- Under the product-grouping basis permutation, the unshuffled product
reference `(I_A ⊗ σ_B) ⊗ (I_C ⊗ σ_D)` is exactly the grouped reference
`I_(A×C) ⊗ (σ_B ⊗ σ_D)`. -/
theorem identityTensorStateMatrix_prod_grouping
    (σ₁ : State b) (σ₂ : State d) :
    identityTensorStateMatrix (a := Prod a c) (σ₁.prod σ₂) =
      (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
        (identityTensorStateMatrix (a := c) σ₂)).submatrix
          (conditionalPetzRenyiProductGroupingEquiv a b c d).symm
          (conditionalPetzRenyiProductGroupingEquiv a b c d).symm := by
  ext x y
  rcases x with ⟨⟨i, k⟩, ⟨j, l⟩⟩
  rcases y with ⟨⟨i', k'⟩, ⟨j', l'⟩⟩
  by_cases hi : i = i'
  · subst i'
    by_cases hk : k = k'
    · subst k'
      simp [identityTensorStateMatrix, State.prod, Matrix.kronecker,
        Matrix.kroneckerMap_apply, conditionalPetzRenyiProductGroupingEquiv]
    · simp [identityTensorStateMatrix, State.prod, Matrix.kronecker,
        Matrix.kroneckerMap_apply, conditionalPetzRenyiProductGroupingEquiv,
        hk]
  · simp [identityTensorStateMatrix, State.prod, Matrix.kronecker,
      Matrix.kroneckerMap_apply, conditionalPetzRenyiProductGroupingEquiv,
      hi]

/-- Trace pairings are invariant under simultaneous finite basis relabeling. -/
theorem trace_mul_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M U : CMatrix κ) :
    ((M.submatrix e e) * (U.submatrix e e)).trace = (M * U).trace := by
  rw [Matrix.trace]
  rw [Matrix.trace]
  apply Fintype.sum_equiv e
    (fun x : ι => ((M.submatrix e e) * (U.submatrix e e)) x x)
    (fun y : κ => (M * U) y y)
  intro x
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Fintype.sum_equiv e
    (fun z : ι => M (e x) (e z) * U (e z) (e x))
    (fun y : κ => M (e x) y * U y (e x))
    (by intro z; rfl)

/-- Matrix trace is invariant under simultaneous finite basis relabeling. -/
theorem trace_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (M : CMatrix κ) :
    (M.submatrix e e).trace = M.trace := by
  simpa [Matrix.submatrix_one_equiv] using
    (trace_mul_submatrix_equiv e M (1 : CMatrix κ))

private def conditionalPetzRenyiCMatrixReindexStarAlgEquiv
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) : CMatrix κ ≃⋆ₐ[ℂ] CMatrix ι where
  __ := Matrix.reindexAlgEquiv ℂ ℂ e.symm
  map_smul' r M := by
    ext i j
    simp [Matrix.reindex_apply]
  map_star' M := by
    ext i j
    simp [Matrix.reindex_apply]

/-- Nonnegative real powers commute with finite basis relabeling for positive
semidefinite complex matrices. -/
theorem cMatrix_rpow_submatrix_equiv_nonneg
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : CMatrix κ) (hM : M.PosSemidef) (e : ι ≃ κ)
    {s : ℝ} (hs0 : 0 ≤ s) :
    CFC.rpow (M.submatrix e e) s = (CFC.rpow M s).submatrix e e := by
  change (M.submatrix e e) ^ s = (M ^ s).submatrix e e
  have hsub_nonneg : 0 ≤ M.submatrix e e :=
    Matrix.nonneg_iff_posSemidef.mpr (hM.submatrix e)
  have hM_nonneg : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM
  rw [CFC.rpow_eq_cfc_real (a := M.submatrix e e) (y := s) hsub_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := M) (y := s) hM_nonneg]
  simpa [conditionalPetzRenyiCMatrixReindexStarAlgEquiv, Matrix.reindexAlgEquiv_apply] using
    (StarAlgHomClass.map_cfc
      (conditionalPetzRenyiCMatrixReindexStarAlgEquiv e)
      (fun x : ℝ => x ^ s) M
      (hf := (Real.continuous_rpow_const hs0).continuousOn)
      (hφ := by
        change Continuous fun A : CMatrix κ => A.submatrix e e
        fun_prop)).symm

/-- Multiplicativity of the fixed-side Petz trace kernel under unshuffled
Kronecker products.

The full source-shaped product additivity for
`H_α(A₁A₂|B₁B₂)_{ρ₁⊗ρ₂|σ₁⊗σ₂}` additionally needs a reindexing bridge between
`(A₁×B₁)×(A₂×B₂)` and `(A₁×A₂)×(B₁×B₂)` commuting with `CFC.rpow`. This lemma is
the matrix multiplicativity core before that permutation layer. -/
theorem conditionalPetzRenyiTraceTerm_prod_kroneckerReference
    (ρ₁ : State (Prod a b)) (σ₁ : State b)
    (ρ₂ : State (Prod c d)) (σ₂ : State d)
    (hρ₁ : ρ₁.matrix.PosDef) (hσ₁ : σ₁.matrix.PosDef)
    (hρ₂ : ρ₂.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) :
    ((CFC.rpow (ρ₁.prod ρ₂).matrix α *
      CFC.rpow
        (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
          (identityTensorStateMatrix (a := c) σ₂)) (1 - α)).trace).re =
      conditionalPetzRenyiTraceTerm ρ₁ σ₁ α *
        conditionalPetzRenyiTraceTerm ρ₂ σ₂ α := by
  have htraceC :
      (CFC.rpow (ρ₁.prod ρ₂).matrix α *
        CFC.rpow
          (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
            (identityTensorStateMatrix (a := c) σ₂)) (1 - α)).trace =
        (CFC.rpow ρ₁.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := a) σ₁) (1 - α)).trace *
        (CFC.rpow ρ₂.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := c) σ₂) (1 - α)).trace := by
    rw [State.prod_matrix_kronecker ρ₁ ρ₂]
    rw [cMatrix_rpow_kronecker_posDef hρ₁ hρ₂ α]
    rw [cMatrix_rpow_kronecker_posDef
      (identityTensorStateMatrix_posDef_of_posDef (a := a) σ₁ hσ₁)
      (identityTensorStateMatrix_posDef_of_posDef (a := c) σ₂ hσ₂) (1 - α)]
    change
      (Matrix.kroneckerMap (fun x y => x * y)
          (CFC.rpow ρ₁.matrix α) (CFC.rpow ρ₂.matrix α) *
        Matrix.kroneckerMap (fun x y => x * y)
          (CFC.rpow (identityTensorStateMatrix (a := a) σ₁) (1 - α))
          (CFC.rpow (identityTensorStateMatrix (a := c) σ₂) (1 - α))).trace =
        (CFC.rpow ρ₁.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := a) σ₁) (1 - α)).trace *
        (CFC.rpow ρ₂.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := c) σ₂) (1 - α)).trace
    rw [← Matrix.mul_kronecker_mul]
    rw [Matrix.trace_kronecker]
  have h_im1 :
      ((CFC.rpow ρ₁.matrix α *
        CFC.rpow (identityTensorStateMatrix (a := a) σ₁) (1 - α)).trace).im = 0 :=
    trace_mul_posSemidef_im_eq_zero
      (ρ₁.rpowMatrix_posSemidef α)
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.rpow_nonneg
          (a := identityTensorStateMatrix (a := a) σ₁) (y := 1 - α)))
  have h_im2 :
      ((CFC.rpow ρ₂.matrix α *
        CFC.rpow (identityTensorStateMatrix (a := c) σ₂) (1 - α)).trace).im = 0 :=
    trace_mul_posSemidef_im_eq_zero
      (ρ₂.rpowMatrix_posSemidef α)
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.rpow_nonneg
          (a := identityTensorStateMatrix (a := c) σ₂) (y := 1 - α)))
  rw [htraceC, Complex.mul_re, h_im1, h_im2]
  simp [conditionalPetzRenyiTraceTerm]

/-- Multiplicativity of the fixed-side Petz trace kernel under unshuffled
Kronecker products with arbitrary left states and full-rank references.

The positive power on the left only needs positive semidefiniteness, while the
reference power may have negative exponent and is discharged from full rank. -/
theorem conditionalPetzRenyiTraceTerm_prod_kroneckerReference_fullReference
    (ρ₁ : State (Prod a b)) (σ₁ : State b)
    (ρ₂ : State (Prod c d)) (σ₂ : State d)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_nonneg : 0 ≤ α) :
    ((CFC.rpow (ρ₁.prod ρ₂).matrix α *
      CFC.rpow
        (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
          (identityTensorStateMatrix (a := c) σ₂)) (1 - α)).trace).re =
      conditionalPetzRenyiTraceTerm ρ₁ σ₁ α *
        conditionalPetzRenyiTraceTerm ρ₂ σ₂ α := by
  have htraceC :
      (CFC.rpow (ρ₁.prod ρ₂).matrix α *
        CFC.rpow
          (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
            (identityTensorStateMatrix (a := c) σ₂)) (1 - α)).trace =
        (CFC.rpow ρ₁.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := a) σ₁) (1 - α)).trace *
        (CFC.rpow ρ₂.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := c) σ₂) (1 - α)).trace := by
    rw [State.prod_matrix_kronecker ρ₁ ρ₂]
    rw [cMatrix_rpow_kronecker_nonneg ρ₁.pos ρ₂.pos hα_nonneg]
    rw [cMatrix_rpow_kronecker_posDef
      (identityTensorStateMatrix_posDef_of_posDef (a := a) σ₁ hσ₁)
      (identityTensorStateMatrix_posDef_of_posDef (a := c) σ₂ hσ₂) (1 - α)]
    change
      (Matrix.kroneckerMap (fun x y => x * y)
          (CFC.rpow ρ₁.matrix α) (CFC.rpow ρ₂.matrix α) *
        Matrix.kroneckerMap (fun x y => x * y)
          (CFC.rpow (identityTensorStateMatrix (a := a) σ₁) (1 - α))
          (CFC.rpow (identityTensorStateMatrix (a := c) σ₂) (1 - α))).trace =
        (CFC.rpow ρ₁.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := a) σ₁) (1 - α)).trace *
        (CFC.rpow ρ₂.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := c) σ₂) (1 - α)).trace
    rw [← Matrix.mul_kronecker_mul]
    rw [Matrix.trace_kronecker]
  have h_im1 :
      ((CFC.rpow ρ₁.matrix α *
        CFC.rpow (identityTensorStateMatrix (a := a) σ₁) (1 - α)).trace).im = 0 :=
    trace_mul_posSemidef_im_eq_zero
      (ρ₁.rpowMatrix_posSemidef α)
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.rpow_nonneg
          (a := identityTensorStateMatrix (a := a) σ₁) (y := 1 - α)))
  have h_im2 :
      ((CFC.rpow ρ₂.matrix α *
        CFC.rpow (identityTensorStateMatrix (a := c) σ₂) (1 - α)).trace).im = 0 :=
    trace_mul_posSemidef_im_eq_zero
      (ρ₂.rpowMatrix_posSemidef α)
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.rpow_nonneg
          (a := identityTensorStateMatrix (a := c) σ₂) (y := 1 - α)))
  rw [htraceC, Complex.mul_re, h_im1, h_im2]
  simp [conditionalPetzRenyiTraceTerm]

/-- Additivity of the fixed-side Petz entropy kernel for the unshuffled
Kronecker-product reference matrix.

See `conditionalPetzRenyiTraceTerm_prod_kroneckerReference` for the remaining
permutation/reindexing bridge needed to turn this into the fully grouped
`A₁A₂|B₁B₂` statement. -/
theorem conditionalPetzRenyiEntropyCandidate_prod_kroneckerReference
    (ρ₁ : State (Prod a b)) (σ₁ : State b)
    (ρ₂ : State (Prod c d)) (σ₂ : State d)
    (hρ₁ : ρ₁.matrix.PosDef) (hσ₁ : σ₁.matrix.PosDef)
    (hρ₂ : ρ₂.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    (1 / (1 - α)) *
        log2
          ((CFC.rpow (ρ₁.prod ρ₂).matrix α *
            CFC.rpow
              (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
                (identityTensorStateMatrix (a := c) σ₂)) (1 - α)).trace).re =
      ρ₁.conditionalPetzRenyiEntropyCandidate hρ₁ σ₁ hσ₁ α hα_pos hα_ne_one +
        ρ₂.conditionalPetzRenyiEntropyCandidate hρ₂ σ₂ hσ₂ α hα_pos hα_ne_one := by
  have htrace :=
    conditionalPetzRenyiTraceTerm_prod_kroneckerReference
      (ρ₁ := ρ₁) (σ₁ := σ₁) (ρ₂ := ρ₂) (σ₂ := σ₂)
      hρ₁ hσ₁ hρ₂ hσ₂ α
  have hxpos : 0 < conditionalPetzRenyiTraceTerm ρ₁ σ₁ α := by
    dsimp [conditionalPetzRenyiTraceTerm]
    haveI : Nonempty (Prod a b) := ρ₁.nonempty
    exact trace_mul_posDef_re_pos
      (ρ₁.rpowMatrix_posDef_of_posDef hρ₁ α)
      (cMatrix_rpow_posDef_of_posDef
        (identityTensorStateMatrix_posDef_of_posDef (a := a) σ₁ hσ₁) (1 - α))
  have hypos : 0 < conditionalPetzRenyiTraceTerm ρ₂ σ₂ α := by
    dsimp [conditionalPetzRenyiTraceTerm]
    haveI : Nonempty (Prod c d) := ρ₂.nonempty
    exact trace_mul_posDef_re_pos
      (ρ₂.rpowMatrix_posDef_of_posDef hρ₂ α)
      (cMatrix_rpow_posDef_of_posDef
        (identityTensorStateMatrix_posDef_of_posDef (a := c) σ₂ hσ₂) (1 - α))
  rw [htrace]
  rw [log2_mul (ne_of_gt hxpos) (ne_of_gt hypos)]
  simp [conditionalPetzRenyiEntropyCandidate, conditionalPetzRenyiTraceTerm]
  ring

/-- Grouped product additivity for the fixed-side Petz trace kernel, assuming
the two remaining CFC real-power reindexing obligations.

The hypotheses `hρpow` and `hrefpow` are the precise missing functional-calculus
facts: `CFC.rpow` must commute with the simultaneous finite basis permutation
used to regroup `(A×B)×(C×D)` as `(A×C)×(B×D)`. The reference matrix itself is
identified unconditionally by `identityTensorStateMatrix_prod_grouping`. -/
theorem conditionalPetzRenyiTraceTerm_prod_grouped_of_rpow_reindex
    (ρ₁ : State (Prod a b)) (σ₁ : State b)
    (ρ₂ : State (Prod c d)) (σ₂ : State d)
    (hρ₁ : ρ₁.matrix.PosDef) (hσ₁ : σ₁.matrix.PosDef)
    (hρ₂ : ρ₂.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ)
    (hρpow :
      CFC.rpow
          ((ρ₁.prod ρ₂).matrix.submatrix
            (conditionalPetzRenyiProductGroupingEquiv a b c d).symm
            (conditionalPetzRenyiProductGroupingEquiv a b c d).symm) α =
        (CFC.rpow (ρ₁.prod ρ₂).matrix α).submatrix
          (conditionalPetzRenyiProductGroupingEquiv a b c d).symm
          (conditionalPetzRenyiProductGroupingEquiv a b c d).symm)
    (hrefpow :
      CFC.rpow (identityTensorStateMatrix (a := Prod a c) (σ₁.prod σ₂)) (1 - α) =
        (CFC.rpow
          (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
            (identityTensorStateMatrix (a := c) σ₂)) (1 - α)).submatrix
          (conditionalPetzRenyiProductGroupingEquiv a b c d).symm
          (conditionalPetzRenyiProductGroupingEquiv a b c d).symm) :
    conditionalPetzRenyiTraceTerm
        ((ρ₁.prod ρ₂).reindex (conditionalPetzRenyiProductGroupingEquiv a b c d))
        (σ₁.prod σ₂) α =
      conditionalPetzRenyiTraceTerm ρ₁ σ₁ α *
        conditionalPetzRenyiTraceTerm ρ₂ σ₂ α := by
  dsimp [conditionalPetzRenyiTraceTerm]
  change
    ((CFC.rpow
          ((ρ₁.prod ρ₂).matrix.submatrix
            (conditionalPetzRenyiProductGroupingEquiv a b c d).symm
            (conditionalPetzRenyiProductGroupingEquiv a b c d).symm) α *
        CFC.rpow (identityTensorStateMatrix (a := Prod a c) (σ₁.prod σ₂)) (1 - α)).trace).re =
      ((CFC.rpow ρ₁.matrix α *
        CFC.rpow (identityTensorStateMatrix (a := a) σ₁) (1 - α)).trace).re *
        ((CFC.rpow ρ₂.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := c) σ₂) (1 - α)).trace).re
  rw [hρpow, hrefpow]
  rw [trace_mul_submatrix_equiv
    (conditionalPetzRenyiProductGroupingEquiv a b c d).symm]
  exact conditionalPetzRenyiTraceTerm_prod_kroneckerReference
    (ρ₁ := ρ₁) (σ₁ := σ₁) (ρ₂ := ρ₂) (σ₂ := σ₂)
    hρ₁ hσ₁ hρ₂ hσ₂ α

/-- Grouped product additivity for the fixed-side Petz trace kernel.  The
`CFC.rpow` reindexing obligations are discharged from positive definiteness. -/
theorem conditionalPetzRenyiTraceTerm_prod_grouped_posDef
    (ρ₁ : State (Prod a b)) (σ₁ : State b)
    (ρ₂ : State (Prod c d)) (σ₂ : State d)
    (hρ₁ : ρ₁.matrix.PosDef) (hσ₁ : σ₁.matrix.PosDef)
    (hρ₂ : ρ₂.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) :
    conditionalPetzRenyiTraceTerm
        ((ρ₁.prod ρ₂).reindex (conditionalPetzRenyiProductGroupingEquiv a b c d))
        (σ₁.prod σ₂) α =
      conditionalPetzRenyiTraceTerm ρ₁ σ₁ α *
        conditionalPetzRenyiTraceTerm ρ₂ σ₂ α := by
  let e := conditionalPetzRenyiProductGroupingEquiv a b c d
  have hρpow :
      CFC.rpow
          ((ρ₁.prod ρ₂).matrix.submatrix e.symm e.symm) α =
        (CFC.rpow (ρ₁.prod ρ₂).matrix α).submatrix e.symm e.symm := by
    simpa [e] using
      cMatrix_rpow_submatrix_equiv_posDef
        (ρ₁.prod ρ₂).matrix (State.prod_posDef hρ₁ hρ₂) e.symm α
  have hrefpow :
      CFC.rpow (identityTensorStateMatrix (a := Prod a c) (σ₁.prod σ₂)) (1 - α) =
        (CFC.rpow
          (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
            (identityTensorStateMatrix (a := c) σ₂)) (1 - α)).submatrix e.symm e.symm := by
    rw [identityTensorStateMatrix_prod_grouping]
    exact cMatrix_rpow_submatrix_equiv_posDef
      (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
        (identityTensorStateMatrix (a := c) σ₂))
      ((identityTensorStateMatrix_posDef_of_posDef (a := a) σ₁ hσ₁).kronecker
        (identityTensorStateMatrix_posDef_of_posDef (a := c) σ₂ hσ₂))
      e.symm (1 - α)
  exact conditionalPetzRenyiTraceTerm_prod_grouped_of_rpow_reindex
    (ρ₁ := ρ₁) (σ₁ := σ₁) (ρ₂ := ρ₂) (σ₂ := σ₂)
    hρ₁ hσ₁ hρ₂ hσ₂ α hρpow hrefpow

/-- Grouped product additivity for the fixed-side Petz trace kernel with
arbitrary left states and full-rank references.

The grouped left-state `CFC.rpow` reindexing is discharged in the PSD domain
from `0 <= α`; the grouped reference still uses full rank because `1 - α` may
be negative. -/
theorem conditionalPetzRenyiTraceTerm_prod_grouped_fullReference
    (ρ₁ : State (Prod a b)) (σ₁ : State b)
    (ρ₂ : State (Prod c d)) (σ₂ : State d)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_nonneg : 0 ≤ α) :
    conditionalPetzRenyiTraceTerm
        ((ρ₁.prod ρ₂).reindex (conditionalPetzRenyiProductGroupingEquiv a b c d))
        (σ₁.prod σ₂) α =
      conditionalPetzRenyiTraceTerm ρ₁ σ₁ α *
        conditionalPetzRenyiTraceTerm ρ₂ σ₂ α := by
  let e := conditionalPetzRenyiProductGroupingEquiv a b c d
  have hρpow :
      CFC.rpow
          ((ρ₁.prod ρ₂).matrix.submatrix e.symm e.symm) α =
        (CFC.rpow (ρ₁.prod ρ₂).matrix α).submatrix e.symm e.symm := by
    simpa [e] using
      cMatrix_rpow_submatrix_equiv_nonneg
        (ρ₁.prod ρ₂).matrix (ρ₁.prod ρ₂).pos e.symm hα_nonneg
  have hrefpow :
      CFC.rpow (identityTensorStateMatrix (a := Prod a c) (σ₁.prod σ₂)) (1 - α) =
        (CFC.rpow
          (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
            (identityTensorStateMatrix (a := c) σ₂)) (1 - α)).submatrix e.symm e.symm := by
    rw [identityTensorStateMatrix_prod_grouping]
    exact cMatrix_rpow_submatrix_equiv_posDef
      (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
        (identityTensorStateMatrix (a := c) σ₂))
      ((identityTensorStateMatrix_posDef_of_posDef (a := a) σ₁ hσ₁).kronecker
        (identityTensorStateMatrix_posDef_of_posDef (a := c) σ₂ hσ₂))
      e.symm (1 - α)
  dsimp [conditionalPetzRenyiTraceTerm]
  change
    ((CFC.rpow
          ((ρ₁.prod ρ₂).matrix.submatrix e.symm e.symm) α *
        CFC.rpow (identityTensorStateMatrix (a := Prod a c) (σ₁.prod σ₂)) (1 - α)).trace).re =
      ((CFC.rpow ρ₁.matrix α *
        CFC.rpow (identityTensorStateMatrix (a := a) σ₁) (1 - α)).trace).re *
        ((CFC.rpow ρ₂.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := c) σ₂) (1 - α)).trace).re
  rw [hρpow, hrefpow]
  rw [trace_mul_submatrix_equiv e.symm]
  exact conditionalPetzRenyiTraceTerm_prod_kroneckerReference_fullReference
    (ρ₁ := ρ₁) (σ₁ := σ₁) (ρ₂ := ρ₂) (σ₂ := σ₂)
    hσ₁ hσ₂ α hα_nonneg

/-- Grouped product additivity for the fixed-side Petz entropy candidate,
conditional on the same CFC real-power reindexing obligations as the trace
kernel theorem. -/
theorem conditionalPetzRenyiEntropyCandidate_prod_grouped_of_rpow_reindex
    (ρ₁ : State (Prod a b)) (σ₁ : State b)
    (ρ₂ : State (Prod c d)) (σ₂ : State d)
    (hρ₁ : ρ₁.matrix.PosDef) (hσ₁ : σ₁.matrix.PosDef)
    (hρ₂ : ρ₂.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (hρgroup :
      (((ρ₁.prod ρ₂).reindex
        (conditionalPetzRenyiProductGroupingEquiv a b c d)).matrix).PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hρpow :
      CFC.rpow
          ((ρ₁.prod ρ₂).matrix.submatrix
            (conditionalPetzRenyiProductGroupingEquiv a b c d).symm
            (conditionalPetzRenyiProductGroupingEquiv a b c d).symm) α =
        (CFC.rpow (ρ₁.prod ρ₂).matrix α).submatrix
          (conditionalPetzRenyiProductGroupingEquiv a b c d).symm
          (conditionalPetzRenyiProductGroupingEquiv a b c d).symm)
    (hrefpow :
      CFC.rpow (identityTensorStateMatrix (a := Prod a c) (σ₁.prod σ₂)) (1 - α) =
        (CFC.rpow
          (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
            (identityTensorStateMatrix (a := c) σ₂)) (1 - α)).submatrix
          (conditionalPetzRenyiProductGroupingEquiv a b c d).symm
          (conditionalPetzRenyiProductGroupingEquiv a b c d).symm) :
    (((ρ₁.prod ρ₂).reindex
        (conditionalPetzRenyiProductGroupingEquiv a b c d)).conditionalPetzRenyiEntropyCandidate
          hρgroup (σ₁.prod σ₂) (State.prod_posDef hσ₁ hσ₂)
          α hα_pos hα_ne_one) =
      ρ₁.conditionalPetzRenyiEntropyCandidate hρ₁ σ₁ hσ₁ α hα_pos hα_ne_one +
        ρ₂.conditionalPetzRenyiEntropyCandidate hρ₂ σ₂ hσ₂ α hα_pos hα_ne_one := by
  have htrace :=
    conditionalPetzRenyiTraceTerm_prod_grouped_of_rpow_reindex
      (ρ₁ := ρ₁) (σ₁ := σ₁) (ρ₂ := ρ₂) (σ₂ := σ₂)
      hρ₁ hσ₁ hρ₂ hσ₂ α hρpow hrefpow
  have hxpos : 0 < conditionalPetzRenyiTraceTerm ρ₁ σ₁ α := by
    dsimp [conditionalPetzRenyiTraceTerm]
    haveI : Nonempty (Prod a b) := ρ₁.nonempty
    exact trace_mul_posDef_re_pos
      (ρ₁.rpowMatrix_posDef_of_posDef hρ₁ α)
      (cMatrix_rpow_posDef_of_posDef
        (identityTensorStateMatrix_posDef_of_posDef (a := a) σ₁ hσ₁) (1 - α))
  have hypos : 0 < conditionalPetzRenyiTraceTerm ρ₂ σ₂ α := by
    dsimp [conditionalPetzRenyiTraceTerm]
    haveI : Nonempty (Prod c d) := ρ₂.nonempty
    exact trace_mul_posDef_re_pos
      (ρ₂.rpowMatrix_posDef_of_posDef hρ₂ α)
      (cMatrix_rpow_posDef_of_posDef
        (identityTensorStateMatrix_posDef_of_posDef (a := c) σ₂ hσ₂) (1 - α))
  simp [conditionalPetzRenyiEntropyCandidate, conditionalPetzRenyiTraceTerm] at htrace ⊢
  rw [htrace]
  change (1 - α)⁻¹ *
      log2
        (((CFC.rpow ρ₁.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := a) σ₁) (1 - α)).trace).re *
          ((CFC.rpow ρ₂.matrix α *
            CFC.rpow (identityTensorStateMatrix (a := c) σ₂) (1 - α)).trace).re) =
    (1 - α)⁻¹ *
        log2 (((CFC.rpow ρ₁.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := a) σ₁) (1 - α)).trace).re) +
      (1 - α)⁻¹ *
        log2 (((CFC.rpow ρ₂.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := c) σ₂) (1 - α)).trace).re)
  have hxne :
      ((CFC.rpow ρ₁.matrix α *
        CFC.rpow (identityTensorStateMatrix (a := a) σ₁) (1 - α)).trace).re ≠ 0 := by
    simpa [conditionalPetzRenyiTraceTerm] using ne_of_gt hxpos
  have hyne :
      ((CFC.rpow ρ₂.matrix α *
        CFC.rpow (identityTensorStateMatrix (a := c) σ₂) (1 - α)).trace).re ≠ 0 := by
    simpa [conditionalPetzRenyiTraceTerm] using ne_of_gt hypos
  rw [log2_mul hxne hyne]
  ring

/-- Grouped product additivity for the fixed-side Petz entropy candidate.  The
`CFC.rpow` reindexing obligations are discharged from positive definiteness. -/
theorem conditionalPetzRenyiEntropyCandidate_prod_grouped_posDef
    (ρ₁ : State (Prod a b)) (σ₁ : State b)
    (ρ₂ : State (Prod c d)) (σ₂ : State d)
    (hρ₁ : ρ₁.matrix.PosDef) (hσ₁ : σ₁.matrix.PosDef)
    (hρ₂ : ρ₂.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    (((ρ₁.prod ρ₂).reindex
        (conditionalPetzRenyiProductGroupingEquiv a b c d)).conditionalPetzRenyiEntropyCandidate
          (State.reindex_posDef_of_posDef
            (ρ₁.prod ρ₂) (State.prod_posDef hρ₁ hρ₂)
            (conditionalPetzRenyiProductGroupingEquiv a b c d))
          (σ₁.prod σ₂) (State.prod_posDef hσ₁ hσ₂)
          α hα_pos hα_ne_one) =
      ρ₁.conditionalPetzRenyiEntropyCandidate hρ₁ σ₁ hσ₁ α hα_pos hα_ne_one +
        ρ₂.conditionalPetzRenyiEntropyCandidate hρ₂ σ₂ hσ₂ α hα_pos hα_ne_one := by
  let e := conditionalPetzRenyiProductGroupingEquiv a b c d
  have hρpow :
      CFC.rpow
          ((ρ₁.prod ρ₂).matrix.submatrix e.symm e.symm) α =
        (CFC.rpow (ρ₁.prod ρ₂).matrix α).submatrix e.symm e.symm := by
    simpa [e] using
      cMatrix_rpow_submatrix_equiv_posDef
        (ρ₁.prod ρ₂).matrix (State.prod_posDef hρ₁ hρ₂) e.symm α
  have hrefpow :
      CFC.rpow (identityTensorStateMatrix (a := Prod a c) (σ₁.prod σ₂)) (1 - α) =
        (CFC.rpow
          (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
            (identityTensorStateMatrix (a := c) σ₂)) (1 - α)).submatrix e.symm e.symm := by
    rw [identityTensorStateMatrix_prod_grouping]
    exact cMatrix_rpow_submatrix_equiv_posDef
      (Matrix.kronecker (identityTensorStateMatrix (a := a) σ₁)
        (identityTensorStateMatrix (a := c) σ₂))
      ((identityTensorStateMatrix_posDef_of_posDef (a := a) σ₁ hσ₁).kronecker
        (identityTensorStateMatrix_posDef_of_posDef (a := c) σ₂ hσ₂))
      e.symm (1 - α)
  simpa [e] using
    conditionalPetzRenyiEntropyCandidate_prod_grouped_of_rpow_reindex
      (ρ₁ := ρ₁) (σ₁ := σ₁) (ρ₂ := ρ₂) (σ₂ := σ₂)
      hρ₁ hσ₁ hρ₂ hσ₂
      (State.reindex_posDef_of_posDef
        (ρ₁.prod ρ₂) (State.prod_posDef hρ₁ hρ₂) e)
      α hα_pos hα_ne_one hρpow hrefpow

/-- Full-reference grouped product additivity for arbitrary left states.

This is the source-aligned product rule needed downstream for general-state
finite AEP: only the references are required to be full rank. -/
theorem conditionalPetzRenyiEntropyCandidateFullReference_prod_grouped
    (ρ₁ : State (Prod a b)) (σ₁ : State b)
    (ρ₂ : State (Prod c d)) (σ₂ : State d)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    conditionalPetzRenyiEntropyCandidateFullReference
      ((ρ₁.prod ρ₂).reindex
        (conditionalPetzRenyiProductGroupingEquiv a b c d))
        (σ₁.prod σ₂) (State.prod_posDef hσ₁ hσ₂)
        α hα_pos hα_ne_one =
      ρ₁.conditionalPetzRenyiEntropyCandidateFullReference
          σ₁ hσ₁ α hα_pos hα_ne_one +
        ρ₂.conditionalPetzRenyiEntropyCandidateFullReference
          σ₂ hσ₂ α hα_pos hα_ne_one := by
  have htrace :=
    conditionalPetzRenyiTraceTerm_prod_grouped_fullReference
      (ρ₁ := ρ₁) (σ₁ := σ₁) (ρ₂ := ρ₂) (σ₂ := σ₂)
      hσ₁ hσ₂ α hα_pos.le
  have hxpos : 0 < conditionalPetzRenyiTraceTerm ρ₁ σ₁ α :=
    conditionalPetzRenyiTraceTerm_pos_of_fullReference ρ₁ σ₁ hσ₁ α
  have hypos : 0 < conditionalPetzRenyiTraceTerm ρ₂ σ₂ α :=
    conditionalPetzRenyiTraceTerm_pos_of_fullReference ρ₂ σ₂ hσ₂ α
  simp [conditionalPetzRenyiEntropyCandidateFullReference] at htrace ⊢
  rw [htrace]
  rw [log2_mul (ne_of_gt hxpos) (ne_of_gt hypos)]
  ring

end State

end

end QIT
