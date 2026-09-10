/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Protocols.FQSW.OneShot
public import QuantumLib.QIT.Asymptotic.AEP
public import QuantumLib.QIT.Coding.Source.SchumacherDirect
public import QuantumLib.QIT.Util.MatrixInstances

/-!
# Typical subspaces for the i.i.d. FQSW source

The asymptotic FQSW theorem applies the one-shot bound to `ψ^{⊗n}`, and the one-shot error is
governed by dimensions and purities, which for `n` copies are controlled by typical subspaces.
This module builds that layer: `adhwFQSWIidKet` regroups `ψ^{⊗n}` as `(A^n × B^n) × R^n`, the three
one-copy marginals `adhwFQSWSystemAState`, `adhwFQSWSystemBState`, `adhwFQSWSystemRState` give the
entropies, and purity of the source turns `I(A;R)` and `I(A;B)` into sums and differences of
`H(A)`, `H(B)` and `H(R)`.

`ADHWFQSWSimultaneousTypicalProjectors` collects projectors `Π_A`, `Π_B`, `Π_R` that are typical at
once, together with the compressed source they cut out and the rank, weight, and marginal-purity
bounds it satisfies.  The projectors are taken at the internal window `δ / 2` while the bounds are
advertised at `δ`; the slack is what
`MState.eventually_two_pow_sub_le_typicalSubspaceDimension` needs in order to give a dimension
bound at the advertised window.  `exists_adhwFQSWSimultaneousTypicalProjectors` produces the record
for all large enough `n`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder QIT.MatrixL2

namespace QIT

universe u v w x y z p u1 v1 w1

noncomputable section

variable {a : Type u} {b : Type v} {r : Type w}
variable {q : Type x} {e : Type y} {et : Type z}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable [Fintype et] [DecidableEq et]

/-- The `n`-fold i.i.d. source regrouped as `(A^n × B^n) × R^n`, matching
the source notation `ψ' = (φ^{ABR})^{⊗ n}` in ADHW fqsw.tex lines 1093-1101. -/
def adhwFQSWIidKet (ψ : Ket ((a × b) × r)) (n : ℕ) :
    Ket ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
  (ψ.tensorPower n).reindex (tensorPowerProdProdEquiv a b r n)

/-- The density state of the regrouped i.i.d. source `ψ'` from ADHW fqsw.tex
lines 1093-1101. -/
def adhwFQSWIidSourceState (ψ : Ket ((a × b) × r)) (n : ℕ) :
    MState ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
  (adhwFQSWIidKet ψ n).state

/-- Alice's one-copy marginal used for the `Π_A` typical projector in ADHW
fqsw.tex lines 1110-1120. -/
def adhwFQSWSystemAState (ψ : Ket ((a × b) × r)) : MState a :=
  ψ.state.traceRight.traceRight

/-- Bob's one-copy marginal used for the `Π_B` typical projector in ADHW
fqsw.tex lines 1110-1120. -/
def adhwFQSWSystemBState (ψ : Ket ((a × b) × r)) : MState b :=
  ψ.state.traceRight.traceLeft

/-- Reference one-copy marginal used for the `Π_R` typical projector in ADHW
fqsw.tex lines 1110-1120. -/
def adhwFQSWSystemRState (ψ : Ket ((a × b) × r)) : MState r :=
  ψ.state.traceLeft

/-- Entropy `H(A)` in the i.i.d. FQSW source route of ADHW fqsw.tex
lines 1110-1120. -/
def adhwFQSWEntropyA (ψ : Ket ((a × b) × r)) : ℝ :=
  (adhwFQSWSystemAState ψ).vonNeumann

/-- Entropy `H(B)` in the i.i.d. FQSW source route of ADHW fqsw.tex
lines 1110-1120. -/
def adhwFQSWEntropyB (ψ : Ket ((a × b) × r)) : ℝ :=
  (adhwFQSWSystemBState ψ).vonNeumann

/-- Entropy `H(R)` in the i.i.d. FQSW source route of ADHW fqsw.tex
lines 1110-1120. -/
def adhwFQSWEntropyR (ψ : Ket ((a × b) × r)) : ℝ :=
  (adhwFQSWSystemRState ψ).vonNeumann

/-- The `A` marginal of the source-route `AR` state is the original source
`A` marginal. -/
theorem adhwFQSWARState_traceRight_eq_systemA
    (ψ : Ket ((a × b) × r)) :
    (adhwFQSWARState ψ).traceRight = adhwFQSWSystemAState ψ := by
  apply MState.ext
  ext i j
  simp [adhwFQSWARState, adhwFQSWSystemAState, MState.coherentTransferReferenceState,
    Matrix.traceRight]
  rw [Finset.sum_comm]

/-- The `R` marginal of the source-route `AR` state is the original reference
marginal. -/
theorem adhwFQSWARState_traceLeft_eq_systemR
    (ψ : Ket ((a × b) × r)) :
    (adhwFQSWARState ψ).traceLeft = adhwFQSWSystemRState ψ := by
  apply MState.ext
  ext i j
  simp [adhwFQSWARState, adhwFQSWSystemRState, MState.coherentTransferReferenceState,
    Matrix.traceLeft, Fintype.sum_prod_type]

/-- The `AR` marginal in the ADHW FQSW source route has the same entropy as
the complementary source `B` system. -/
theorem adhwFQSWARState_vonNeumann_eq_entropyB
    (ψ : Ket ((a × b) × r)) :
    (adhwFQSWARState ψ).vonNeumann = adhwFQSWEntropyB ψ := by
  let Ω : Ket ((a × r) × b) :=
    ψ.reindex (prodABCToACBEquiv a b r)
  have hΩA : Ω.state.traceRight = adhwFQSWARState ψ := by
    apply MState.ext
    ext i j
    simp [Ω, adhwFQSWARState, MState.coherentTransferReferenceState,
      prodABCToACBEquiv, Ket.reindex_state,
      Matrix.traceRight, Ket.state_matrix, rankOneMatrix_apply]
  have hΩB : Ω.state.traceLeft = adhwFQSWSystemBState ψ := by
    apply MState.ext
    ext i j
    simp [Ω, adhwFQSWSystemBState, prodABCToACBEquiv,
      Ket.reindex_state,
      Matrix.traceLeft, Matrix.traceRight, Ket.state_matrix,
      rankOneMatrix_apply, Fintype.sum_prod_type]
  have hdual := MState.ket_traceRight_vonNeumann_eq_traceLeft Ω
  rw [hΩA, hΩB] at hdual
  simpa [adhwFQSWEntropyB] using hdual

/-- The source `AB` marginal has the same entropy as the complementary
reference system `R`. -/
theorem adhwFQSWSourceAB_vonNeumann_eq_entropyR
    (ψ : Ket ((a × b) × r)) :
    ψ.state.traceRight.vonNeumann = adhwFQSWEntropyR ψ := by
  simpa [adhwFQSWEntropyR, adhwFQSWSystemRState] using
    MState.ket_traceRight_vonNeumann_eq_traceLeft ψ

/-- Source-route mutual information identity
`I(A;R) = H(A) + H(R) - H(B)`. -/
theorem adhwFQSWMutualInformationAR_eq_entropyA_add_entropyR_sub_entropyB
    (ψ : Ket ((a × b) × r)) :
    mutualInformation ψ.state.coherentTransferReferenceState =
      adhwFQSWEntropyA ψ + adhwFQSWEntropyR ψ - adhwFQSWEntropyB ψ := by
  rw [← adhwFQSWARState]
  rw [mutualInformation]
  rw [adhwFQSWARState_traceRight_eq_systemA,
    adhwFQSWARState_traceLeft_eq_systemR,
    adhwFQSWARState_vonNeumann_eq_entropyB]
  rfl

/-- Source-route mutual information identity
`I(A;B) = H(A) + H(B) - H(R)`. -/
theorem adhwFQSWMutualInformationAB_eq_entropyA_add_entropyB_sub_entropyR
    (ψ : Ket ((a × b) × r)) :
    mutualInformation ψ.state.traceRight =
      adhwFQSWEntropyA ψ + adhwFQSWEntropyB ψ - adhwFQSWEntropyR ψ := by
  rw [mutualInformation]
  rw [adhwFQSWSourceAB_vonNeumann_eq_entropyR]
  rfl

/-- Lift an `A^n` projector to the grouped i.i.d. source register
`A^nB^nR^n`. -/
private def adhwFQSWIidLiftProjectorA
    (n : ℕ) (PA : CMatrix (TensorPower a n)) :
    CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
  Matrix.kronecker
    (Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
    (1 : CMatrix (TensorPower r n))

/-- Lift a `B^n` projector to the grouped i.i.d. source register
`A^nB^nR^n`. -/
private def adhwFQSWIidLiftProjectorB
    (n : ℕ) (PB : CMatrix (TensorPower b n)) :
    CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
  Matrix.kronecker
    (Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB)
    (1 : CMatrix (TensorPower r n))

/-- Lift an `R^n` projector to the grouped i.i.d. source register
`A^nB^nR^n`. -/
private def adhwFQSWIidLiftProjectorR
    (n : ℕ) (PR : CMatrix (TensorPower r n)) :
    CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
  Matrix.kronecker (1 : CMatrix (TensorPower a n × TensorPower b n)) PR

/-- The simultaneous lifted `A^nB^nR^n` projector
`Π_A ⊗ Π_B ⊗ Π_R`. -/
def adhwFQSWIidLiftProjectorTriple
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
  Matrix.kronecker (Matrix.kronecker PA PB) PR

/-- The simultaneously projected i.i.d. source matrix
`Π_A Π_B Π_R ρ Π_A Π_B Π_R`. -/
def adhwFQSWIidProjectedSourceMatrix
    (ψ : Ket ((a × b) × r)) (n : ℕ)
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  Pi * (adhwFQSWIidSourceState ψ n).m * Pi

-- Algebraic decomposition behind the simultaneous-projector union bound.
omit [Fintype a] [Fintype b] [Fintype r] in
private theorem adhwFQSWIidLiftProjector_union_decomp
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    ((1 - adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA) +
        (1 - adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB) +
          (1 - adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR)) -
        (1 - adhwFQSWIidLiftProjectorTriple
          (a := a) (b := b) (r := r) n PA PB PR) =
      Matrix.kronecker (Matrix.kronecker (1 - PA) (1 - PB))
          (1 : CMatrix (TensorPower r n)) +
        Matrix.kronecker (1 - Matrix.kronecker PA PB) (1 - PR) := by
  ext x y
  rcases x with ⟨⟨xa, xb⟩, xr⟩
  rcases y with ⟨⟨ya, yb⟩, yr⟩
  by_cases ha : xa = ya
  · subst ya
    by_cases hb : xb = yb
    · subst yb
      by_cases hr : xr = yr
      · subst yr
        simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply]
        try ring
      · simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, hr]
        try ring
    · by_cases hr : xr = yr
      · subst yr
        simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, hb]
        try ring
      · simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, hb, hr]
        try ring
  · by_cases hb : xb = yb
    · subst yb
      by_cases hr : xr = yr
      · subst yr
        simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, ha]
        try ring
      · simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, ha, hr]
        try ring
    · by_cases hr : xr = yr
      · subst yr
        simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, ha, hb]
        try ring
      · simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, ha, hb, hr]
        try ring

/-- Simultaneous-projector union bound on the grouped i.i.d. source register. -/
private theorem adhwFQSWIidLiftProjector_union_bound
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n))
    (hPA : PA.PosSemidef) (hPB : PB.PosSemidef) (hPR : PR.PosSemidef)
    (hPAid : PA * PA = PA) (hPBid : PB * PB = PB) (hPRid : PR * PR = PR) :
    (1 - adhwFQSWIidLiftProjectorTriple
        (a := a) (b := b) (r := r) n PA PB PR) ≤
      (1 - adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA) +
        (1 - adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB) +
          (1 - adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR) := by
  rw [Matrix.le_iff]
  rw [adhwFQSWIidLiftProjector_union_decomp]
  have hAcomp := MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent PA hPA hPAid
  have hBcomp := MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent PB hPB hPBid
  have hRcomp := MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent PR hPR hPRid
  have hAB : (Matrix.kronecker PA PB).PosSemidef := hPA.kronecker hPB
  have hABid : Matrix.kronecker PA PB * Matrix.kronecker PA PB =
      Matrix.kronecker PA PB := by
    simpa [hPAid, hPBid] using (Matrix.mul_kronecker_mul PA PA PB PB).symm
  have hABcomp := MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent (Matrix.kronecker PA PB) hAB hABid
  exact (hAcomp.kronecker hBcomp).kronecker Matrix.PosSemidef.one |>.add
    (hABcomp.kronecker hRcomp)

/-- The `A^n` marginal of the grouped FQSW i.i.d. source is the tensor power
of the one-copy `A` marginal. -/
private theorem adhwFQSWIidSourceState_traceRight_eq_tensorPower
    (ψ : Ket ((a × b) × r)) (n : ℕ) :
    (adhwFQSWIidSourceState ψ n).traceRight.traceRight =
      (adhwFQSWSystemAState ψ).tensorPower n := by
  have hAB :
      (adhwFQSWIidSourceState ψ n).traceRight =
        ψ.state.traceRight.tensorPowerBipartite n := by
    simpa [adhwFQSWIidSourceState, adhwFQSWIidKet,
      tensorPowerProdProdEquiv, Ket.tensorPowerTripartiteGrouped,
      Ket.reindex_state,
      Ket.tensorPower_state] using
      Ket.tensorPowerTripartiteGrouped_marginalAB (a := a) (b := b) (c := r) ψ n
  rw [hAB]
  simpa [adhwFQSWSystemAState] using
    MState.tensorPowerBipartite_traceRight (rho := ψ.state.traceRight) n

/-- The `B^n` marginal of the grouped FQSW i.i.d. source is the tensor power
of the one-copy `B` marginal. -/
private theorem adhwFQSWIidSourceState_traceLeft_eq_tensorPower
    (ψ : Ket ((a × b) × r)) (n : ℕ) :
    (adhwFQSWIidSourceState ψ n).traceRight.traceLeft =
      (adhwFQSWSystemBState ψ).tensorPower n := by
  have hAB :
      (adhwFQSWIidSourceState ψ n).traceRight =
        ψ.state.traceRight.tensorPowerBipartite n := by
    simpa [adhwFQSWIidSourceState, adhwFQSWIidKet,
      tensorPowerProdProdEquiv, Ket.tensorPowerTripartiteGrouped,
      Ket.reindex_state,
      Ket.tensorPower_state] using
      Ket.tensorPowerTripartiteGrouped_marginalAB (a := a) (b := b) (c := r) ψ n
  rw [hAB]
  simpa [adhwFQSWSystemBState] using
    MState.tensorPowerBipartite_traceLeft (rho := ψ.state.traceRight) n

/-- The `R^n` marginal of the grouped FQSW i.i.d. source is the tensor power
of the one-copy reference marginal. -/
private theorem adhwFQSWIidSourceState_marginalR_eq_tensorPower
    (ψ : Ket ((a × b) × r)) (n : ℕ) :
    (adhwFQSWIidSourceState ψ n).traceLeft =
      (adhwFQSWSystemRState ψ).tensorPower n := by
  let ρ := adhwFQSWIidSourceState ψ n
  have hAC :
      ρ.marginalAC = ψ.state.marginalAC.tensorPowerBipartite n := by
    simpa [ρ, adhwFQSWIidSourceState, adhwFQSWIidKet,
      tensorPowerProdProdEquiv, Ket.tensorPowerTripartiteGrouped,
      Ket.reindex_state,
      Ket.tensorPower_state] using
      Ket.tensorPowerTripartiteGrouped_marginalAC (a := a) (b := b) (c := r) ψ n
  calc
    ρ.traceLeft = ρ.marginalAC.traceLeft := by
      exact (MState.marginalAC_traceLeft_eq_traceLeft ρ).symm
    _ = (ψ.state.marginalAC.tensorPowerBipartite n).traceLeft := by
      rw [hAC]
    _ = (ψ.state.marginalAC.traceLeft).tensorPower n := by
      exact MState.tensorPowerBipartite_traceLeft (rho := ψ.state.marginalAC) n
    _ = (adhwFQSWSystemRState ψ).tensorPower n := by
      have hR := MState.marginalAC_traceLeft_eq_traceLeft ψ.state
      simpa [adhwFQSWSystemRState] using congrArg (fun σ : MState r => σ.tensorPower n) hR

/-- Acceptance identity for the lifted `A^n` typical projector. -/
private theorem adhwFQSWIid_acceptanceA
    (ψ : Ket ((a × b) × r)) (n : ℕ) (δ : ℝ) :
    (((adhwFQSWIidLiftProjectorA (b := b) (r := r) n
        ((adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).m).trace).re =
      (adhwFQSWSystemAState ψ).typicalSubspaceSpectralWeight n δ := by
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ
  have htraceR :
      (((adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA) *
          ρ.m).trace).re =
        (((Matrix.kronecker PA (1 : CMatrix (TensorPower b n))) *
            ρ.traceRight.m).trace).re := by
    have h := trace_kronecker_one_right_mul_eq_trace_mul_traceRight
      (a := TensorPower a n × TensorPower b n) (b := TensorPower r n)
      (M := ρ.m)
      (T := Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
    simpa [adhwFQSWIidLiftProjectorA, ρ, PA, MState.traceRight_m] using
      congrArg Complex.re h
  have htraceB :
      (((Matrix.kronecker PA (1 : CMatrix (TensorPower b n))) *
            ρ.traceRight.m).trace).re =
        ((PA * ρ.traceRight.traceRight.m).trace).re := by
    have h := trace_kronecker_one_right_mul_eq_trace_mul_traceRight
      (a := TensorPower a n) (b := TensorPower b n)
      (M := ρ.traceRight.m) (T := PA)
    simpa [MState.traceRight_m] using congrArg Complex.re h
  have hmarg := congrArg (fun σ : MState (TensorPower a n) => σ.m)
    (adhwFQSWIidSourceState_traceRight_eq_tensorPower ψ n)
  have hmarg' :
      ρ.traceRight.traceRight.m =
        ((adhwFQSWSystemAState ψ).tensorPower n).m := by
    simpa [ρ] using hmarg
  calc
    (((adhwFQSWIidLiftProjectorA (b := b) (r := r) n
        ((adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).m).trace).re =
        ((PA * ρ.traceRight.traceRight.m).trace).re := by
          rw [htraceR, htraceB]
    _ = (((adhwFQSWSystemAState ψ).tensorPower n).m * PA).trace.re := by
          rw [hmarg']
          rw [Matrix.trace_mul_comm]
    _ = (adhwFQSWSystemAState ψ).typicalSubspaceSpectralWeight n δ := by
          simpa [PA] using
            (adhwFQSWSystemAState ψ).typicalSubspaceProjector_trace_mul_re n δ

/-- Acceptance identity for the lifted `B^n` typical projector. -/
private theorem adhwFQSWIid_acceptanceB
    (ψ : Ket ((a × b) × r)) (n : ℕ) (δ : ℝ) :
    (((adhwFQSWIidLiftProjectorB (a := a) (r := r) n
        ((adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).m).trace).re =
      (adhwFQSWSystemBState ψ).typicalSubspaceSpectralWeight n δ := by
  let ρ := adhwFQSWIidSourceState ψ n
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ
  have htraceR :
      (((adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB) *
          ρ.m).trace).re =
        (((Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB) *
            ρ.traceRight.m).trace).re := by
    have h := trace_kronecker_one_right_mul_eq_trace_mul_traceRight
      (a := TensorPower a n × TensorPower b n) (b := TensorPower r n)
      (M := ρ.m)
      (T := Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB)
    simpa [adhwFQSWIidLiftProjectorB, ρ, PB, MState.traceRight_m] using
      congrArg Complex.re h
  have htraceA :
      (((Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB) *
            ρ.traceRight.m).trace).re =
        ((PB * ρ.traceRight.traceLeft.m).trace).re := by
    have h := trace_kronecker_one_mul_eq_trace_mul_traceLeft
      (a := TensorPower a n) (b := TensorPower b n)
      (M := ρ.traceRight.m) (T := PB)
    simpa [MState.traceLeft_m] using congrArg Complex.re h
  have hmarg := congrArg (fun σ : MState (TensorPower b n) => σ.m)
    (adhwFQSWIidSourceState_traceLeft_eq_tensorPower ψ n)
  have hmarg' :
      ρ.traceRight.traceLeft.m =
        ((adhwFQSWSystemBState ψ).tensorPower n).m := by
    simpa [ρ] using hmarg
  calc
    (((adhwFQSWIidLiftProjectorB (a := a) (r := r) n
        ((adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).m).trace).re =
        ((PB * ρ.traceRight.traceLeft.m).trace).re := by
          rw [htraceR, htraceA]
    _ = (((adhwFQSWSystemBState ψ).tensorPower n).m * PB).trace.re := by
          rw [hmarg']
          rw [Matrix.trace_mul_comm]
    _ = (adhwFQSWSystemBState ψ).typicalSubspaceSpectralWeight n δ := by
          simpa [PB] using
            (adhwFQSWSystemBState ψ).typicalSubspaceProjector_trace_mul_re n δ

/-- Acceptance identity for the lifted `R^n` typical projector. -/
private theorem adhwFQSWIid_acceptanceR
    (ψ : Ket ((a × b) × r)) (n : ℕ) (δ : ℝ) :
    (((adhwFQSWIidLiftProjectorR (a := a) (b := b) n
        ((adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).m).trace).re =
      (adhwFQSWSystemRState ψ).typicalSubspaceSpectralWeight n δ := by
  let ρ := adhwFQSWIidSourceState ψ n
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ
  have htraceAB :
      (((adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR) *
          ρ.m).trace).re =
        ((PR * ρ.traceLeft.m).trace).re := by
    have h := trace_kronecker_one_mul_eq_trace_mul_traceLeft
      (a := TensorPower a n × TensorPower b n) (b := TensorPower r n)
      (M := ρ.m) (T := PR)
    simpa [adhwFQSWIidLiftProjectorR, ρ, PR, MState.traceLeft_m] using
      congrArg Complex.re h
  have hmarg := congrArg (fun σ : MState (TensorPower r n) => σ.m)
    (adhwFQSWIidSourceState_marginalR_eq_tensorPower ψ n)
  have hmarg' :
      ρ.traceLeft.m =
        ((adhwFQSWSystemRState ψ).tensorPower n).m := by
    simpa [ρ] using hmarg
  calc
    (((adhwFQSWIidLiftProjectorR (a := a) (b := b) n
        ((adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).m).trace).re =
        ((PR * ρ.traceLeft.m).trace).re := by
          rw [htraceAB]
    _ = (((adhwFQSWSystemRState ψ).tensorPower n).m * PR).trace.re := by
          rw [hmarg']
          rw [Matrix.trace_mul_comm]
    _ = (adhwFQSWSystemRState ψ).typicalSubspaceSpectralWeight n δ := by
          simpa [PR] using
            (adhwFQSWSystemRState ψ).typicalSubspaceProjector_trace_mul_re n δ

/-- Selectively projecting the right register cannot increase the left
marginal in Loewner order. -/
private theorem adhwFQSW_traceRight_selective_projector_le
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (X : CMatrix (α × β)) (hX : X.PosSemidef)
    (Q : CMatrix β) (hQ : Q.PosSemidef) (hQid : Q * Q = Q) :
    Matrix.traceRight
        (Matrix.kronecker (1 : CMatrix α) Q * X *
          Matrix.kronecker (1 : CMatrix α) Q) ≤
      Matrix.traceRight X := by
  rw [Matrix.le_iff]
  let D : CMatrix α :=
    Matrix.traceRight X -
      Matrix.traceRight
        (Matrix.kronecker (1 : CMatrix α) Q * X *
          Matrix.kronecker (1 : CMatrix α) Q)
  change D.PosSemidef
  have hbranch_psd :
      (Matrix.kronecker (1 : CMatrix α) Q * X *
        Matrix.kronecker (1 : CMatrix α) Q).PosSemidef := by
    let K : CMatrix (α × β) := Matrix.kronecker (1 : CMatrix α) Q
    have hK : K.PosSemidef := Matrix.PosSemidef.one.kronecker hQ
    have h := hX.mul_mul_conjTranspose_same K
    rw [hK.isHermitian.eq] at h
    simpa [K, Matrix.mul_assoc] using h
  have hDherm : D.IsHermitian := by
    dsimp [D]
    exact (Matrix.IsHermitian.traceRight hX.isHermitian).sub
      (Matrix.IsHermitian.traceRight hbranch_psd.isHermitian)
  rw [cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg hDherm]
  intro W hW
  have hQcomp := MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent Q hQ hQid
  have hWQcomp : (Matrix.kronecker W (1 - Q)).PosSemidef :=
    hW.kronecker hQcomp
  have hnonneg :
      0 ≤ ((Matrix.kronecker W (1 - Q) * X).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hWQcomp hX
  have htrace_full :
      ((W * Matrix.traceRight X).trace).re =
        ((Matrix.kronecker W (1 : CMatrix β) * X).trace).re := by
    exact congrArg Complex.re
      (trace_kronecker_one_right_mul_eq_trace_mul_traceRight
        (a := α) (b := β) X W).symm
  have htrace_branch :
      ((W * Matrix.traceRight
          (Matrix.kronecker (1 : CMatrix α) Q * X *
            Matrix.kronecker (1 : CMatrix α) Q)).trace).re =
        ((Matrix.kronecker W Q * X).trace).re := by
    have hpair := congrArg Complex.re
      (trace_kronecker_one_right_mul_eq_trace_mul_traceRight
        (a := α) (b := β)
        (Matrix.kronecker (1 : CMatrix α) Q * X *
          Matrix.kronecker (1 : CMatrix α) Q) W).symm
    rw [hpair]
    congr 1
    let K : CMatrix (α × β) := Matrix.kronecker (1 : CMatrix α) Q
    let L : CMatrix (α × β) := Matrix.kronecker W (1 : CMatrix β)
    have hKLK : K * L * K = Matrix.kronecker W Q := by
      have hKL : K * L = Matrix.kronecker W Q := by
        simpa [K, L, Matrix.one_mul, Matrix.mul_one] using
          (Matrix.mul_kronecker_mul (1 : CMatrix α) W Q (1 : CMatrix β)).symm
      calc
        K * L * K = (Matrix.kronecker W Q) * Matrix.kronecker (1 : CMatrix α) Q := by
          rw [hKL]
        _ = Matrix.kronecker W (Q * Q) := by
          simpa [Matrix.mul_one] using
            (Matrix.mul_kronecker_mul W (1 : CMatrix α) Q Q).symm
        _ = Matrix.kronecker W Q := by rw [hQid]
    calc
      (Matrix.kronecker W (1 : CMatrix β) *
          (Matrix.kronecker (1 : CMatrix α) Q * X *
            Matrix.kronecker (1 : CMatrix α) Q)).trace =
          ((K * L * K) * X).trace := by
            have hassoc :
                Matrix.kronecker W (1 : CMatrix β) *
                    (Matrix.kronecker (1 : CMatrix α) Q * X *
                      Matrix.kronecker (1 : CMatrix α) Q) =
                  L * K * X * K := by
              simp [K, L]
              noncomm_ring
            rw [hassoc]
            rw [Matrix.trace_mul_cycle]
            congr 1
            noncomm_ring
      _ = (Matrix.kronecker W Q * X).trace := by
            rw [hKLK]
  have htrace_decomp :
      ((W * D).trace).re =
        ((Matrix.kronecker W (1 - Q) * X).trace).re := by
    dsimp [D]
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [htrace_full]
    have htrace_branch_expanded := htrace_branch
    simp only [Matrix.kronecker] at htrace_branch_expanded
    rw [htrace_branch_expanded]
    have hsplit :
        Matrix.kronecker W (1 : CMatrix β) - Matrix.kronecker W Q =
          Matrix.kronecker W (1 - Q) := by
      ext x y
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply]
      ring
    have hsplit_expanded := hsplit
    simp only [Matrix.kronecker] at hsplit_expanded
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul]
    simp only [Matrix.kronecker]
    rw [hsplit_expanded]
  rw [Matrix.trace_mul_comm]
  rw [htrace_decomp]
  exact hnonneg

/-- Selectively projecting the left register cannot increase the right
marginal in Loewner order. -/
private theorem adhwFQSW_traceLeft_selective_projector_le
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (X : CMatrix (α × β)) (hX : X.PosSemidef)
    (Q : CMatrix α) (hQ : Q.PosSemidef) (hQid : Q * Q = Q) :
    Matrix.traceLeft
        (Matrix.kronecker Q (1 : CMatrix β) * X *
          Matrix.kronecker Q (1 : CMatrix β)) ≤
      Matrix.traceLeft X := by
  rw [Matrix.le_iff]
  let D : CMatrix β :=
    Matrix.traceLeft X -
      Matrix.traceLeft
        (Matrix.kronecker Q (1 : CMatrix β) * X *
          Matrix.kronecker Q (1 : CMatrix β))
  change D.PosSemidef
  have hbranch_psd :
      (Matrix.kronecker Q (1 : CMatrix β) * X *
        Matrix.kronecker Q (1 : CMatrix β)).PosSemidef := by
    let K : CMatrix (α × β) := Matrix.kronecker Q (1 : CMatrix β)
    have hK : K.PosSemidef := hQ.kronecker Matrix.PosSemidef.one
    have h := hX.mul_mul_conjTranspose_same K
    rw [hK.isHermitian.eq] at h
    simpa [K, Matrix.mul_assoc] using h
  have hDherm : D.IsHermitian := by
    dsimp [D]
    exact (Matrix.IsHermitian.traceLeft hX.isHermitian).sub
      (Matrix.IsHermitian.traceLeft hbranch_psd.isHermitian)
  rw [cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg hDherm]
  intro W hW
  have hQcomp := MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent Q hQ hQid
  have hQcompW : (Matrix.kronecker (1 - Q) W).PosSemidef :=
    hQcomp.kronecker hW
  have hnonneg :
      0 ≤ ((Matrix.kronecker (1 - Q) W * X).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hQcompW hX
  have htrace_full :
      ((W * Matrix.traceLeft X).trace).re =
        ((Matrix.kronecker (1 : CMatrix α) W * X).trace).re := by
    exact congrArg Complex.re
      (trace_kronecker_one_mul_eq_trace_mul_traceLeft
        (a := α) (b := β) X W).symm
  have htrace_branch :
      ((W * Matrix.traceLeft
          (Matrix.kronecker Q (1 : CMatrix β) * X *
            Matrix.kronecker Q (1 : CMatrix β))).trace).re =
        ((Matrix.kronecker Q W * X).trace).re := by
    have hpair := congrArg Complex.re
      (trace_kronecker_one_mul_eq_trace_mul_traceLeft
        (a := α) (b := β)
        (Matrix.kronecker Q (1 : CMatrix β) * X *
          Matrix.kronecker Q (1 : CMatrix β)) W).symm
    rw [hpair]
    congr 1
    let K : CMatrix (α × β) := Matrix.kronecker Q (1 : CMatrix β)
    let L : CMatrix (α × β) := Matrix.kronecker (1 : CMatrix α) W
    have hKLK : K * L * K = Matrix.kronecker Q W := by
      have hKL : K * L = Matrix.kronecker Q W := by
        simpa [K, L, Matrix.one_mul, Matrix.mul_one] using
          (Matrix.mul_kronecker_mul Q (1 : CMatrix α) (1 : CMatrix β) W).symm
      calc
        K * L * K = (Matrix.kronecker Q W) * Matrix.kronecker Q (1 : CMatrix β) := by
          rw [hKL]
        _ = Matrix.kronecker (Q * Q) W := by
          simpa [Matrix.mul_one] using
            (Matrix.mul_kronecker_mul Q Q W (1 : CMatrix β)).symm
        _ = Matrix.kronecker Q W := by rw [hQid]
    calc
      (Matrix.kronecker (1 : CMatrix α) W *
          (Matrix.kronecker Q (1 : CMatrix β) * X *
            Matrix.kronecker Q (1 : CMatrix β))).trace =
          ((K * L * K) * X).trace := by
            have hassoc :
                Matrix.kronecker (1 : CMatrix α) W *
                    (Matrix.kronecker Q (1 : CMatrix β) * X *
                      Matrix.kronecker Q (1 : CMatrix β)) =
                  L * K * X * K := by
              simp [K, L]
              noncomm_ring
            rw [hassoc]
            rw [Matrix.trace_mul_cycle]
            congr 1
            noncomm_ring
      _ = (Matrix.kronecker Q W * X).trace := by
            rw [hKLK]
  have htrace_decomp :
      ((W * D).trace).re =
        ((Matrix.kronecker (1 - Q) W * X).trace).re := by
    dsimp [D]
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [htrace_full]
    have htrace_branch_expanded := htrace_branch
    simp only [Matrix.kronecker] at htrace_branch_expanded
    rw [htrace_branch_expanded]
    have hsplit :
        Matrix.kronecker (1 : CMatrix α) W - Matrix.kronecker Q W =
          Matrix.kronecker (1 - Q) W := by
      ext x y
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply]
      ring
    have hsplit_expanded := hsplit
    simp only [Matrix.kronecker] at hsplit_expanded
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul]
    simp only [Matrix.kronecker]
    rw [hsplit_expanded]
  rw [Matrix.trace_mul_comm]
  rw [htrace_decomp]
  exact hnonneg

private theorem adhwFQSW_complex_smul_smul
    {α : Type u} (c d : ℂ) (M : CMatrix α) :
    c • (d • M) = (c * d) • M := by
  ext i j
  simp [Matrix.smul_apply, smul_eq_mul, mul_assoc]

private theorem adhwFQSW_sum_four_comm
    {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : α → β → γ → δ → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d)
        = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := by
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]

private theorem adhwFQSW_sum_five_comm
    {α β γ δ ε M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [Fintype ε] [AddCommMonoid M]
    (f : α → β → γ → δ → ε → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ c, ∑ e, ∑ a, ∑ b, ∑ d, f a b c d e := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e)
        = ∑ a, ∑ c, ∑ b, ∑ d, ∑ e, f a b c d e := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, ∑ e, f a b c d e := by
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ e, ∑ d, f a b c d e := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ e, ∑ b, ∑ d, f a b c d e := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ e, ∑ a, ∑ b, ∑ d, f a b c d e := by
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]

private theorem adhwFQSW_sum_five_comm_leftPair
    {α β γ δ ε M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [Fintype ε] [AddCommMonoid M]
    (f : α → β → γ → δ → ε → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ b, ∑ d, ∑ a, ∑ c, ∑ e, f a b c d e := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e)
        = ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, f a b c d e := by
          rw [Finset.sum_comm]
    _ = ∑ b, ∑ a, ∑ d, ∑ c, ∑ e, f a b c d e := by
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ b, ∑ d, ∑ a, ∑ c, ∑ e, f a b c d e := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]

private theorem adhwFQSWIidLiftProjectorA_traceRight_traceRight
    (n : ℕ)
    (ρ : MState ((TensorPower a n × TensorPower b n) × TensorPower r n))
    (PA : CMatrix (TensorPower a n)) :
    Matrix.traceRight
      (Matrix.traceRight
        (adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA * ρ.m *
          adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA)) =
      PA * ρ.traceRight.traceRight.m * PA := by
  ext x y
  simp [adhwFQSWIidLiftProjectorA, Matrix.traceRight,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa using
    (adhwFQSW_sum_four_comm
      (fun b0 r0 v0 u0 =>
        PA x u0 * (ρ.m ((u0, b0), r0) ((v0, b0), r0) * PA v0 y)))

private theorem adhwFQSWIidLiftProjectorB_traceRight_traceLeft
    (n : ℕ)
    (ρ : MState ((TensorPower a n × TensorPower b n) × TensorPower r n))
    (PB : CMatrix (TensorPower b n)) :
    Matrix.traceLeft
      (Matrix.traceRight
        (adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB * ρ.m *
          adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB)) =
      PB * ρ.traceRight.traceLeft.m * PB := by
  ext x y
  simp [adhwFQSWIidLiftProjectorB,
    Matrix.traceLeft, Matrix.traceRight, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa using
    (adhwFQSW_sum_four_comm
      (fun a0 r0 v0 u0 =>
        PB x u0 * (ρ.m ((a0, u0), r0) ((a0, v0), r0) * PB v0 y)))

private theorem adhwFQSWIidLiftProjectorR_traceLeft
    (n : ℕ)
    (ρ : MState ((TensorPower a n × TensorPower b n) × TensorPower r n))
    (PR : CMatrix (TensorPower r n)) :
    Matrix.traceLeft
        (adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * ρ.m *
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR) =
      PR * ρ.traceLeft.m * PR := by
  ext x y
  simp [adhwFQSWIidLiftProjectorR, Matrix.traceLeft,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa using
    (adhwFQSW_sum_four_comm
      (fun a0 b0 v0 u0 =>
        PR x u0 * (ρ.m ((a0, b0), u0) ((a0, b0), v0) * PR v0 y)))

omit [DecidableEq a] in
private theorem adhwFQSWIidLiftProjectorA_posSemidef
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (hPA : PA.PosSemidef) :
    (adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA).PosSemidef :=
  (hPA.kronecker Matrix.PosSemidef.one).kronecker Matrix.PosSemidef.one

omit [DecidableEq b] in
private theorem adhwFQSWIidLiftProjectorB_posSemidef
    (n : ℕ) (PB : CMatrix (TensorPower b n)) (hPB : PB.PosSemidef) :
    (adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB).PosSemidef :=
  (Matrix.PosSemidef.one.kronecker hPB).kronecker Matrix.PosSemidef.one

omit [DecidableEq r] in
private theorem adhwFQSWIidLiftProjectorR_posSemidef
    (n : ℕ) (PR : CMatrix (TensorPower r n)) (hPR : PR.PosSemidef) :
    (adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR).PosSemidef :=
  Matrix.PosSemidef.one.kronecker hPR

omit [DecidableEq a] [DecidableEq b] [DecidableEq r] in
private theorem adhwFQSWIidLiftProjectorTriple_posSemidef
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n))
    (hPA : PA.PosSemidef) (hPB : PB.PosSemidef) (hPR : PR.PosSemidef) :
    (adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR).PosSemidef :=
  (hPA.kronecker hPB).kronecker hPR

omit [DecidableEq a] in
private theorem adhwFQSWIidLiftProjectorA_idempotent
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (hPAid : PA * PA = PA) :
    adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA *
      adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA =
        adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA := by
  have hAB :
      Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) *
          Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) =
        Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) := by
    simpa [hPAid] using
      (Matrix.mul_kronecker_mul PA PA (1 : CMatrix (TensorPower b n))
        (1 : CMatrix (TensorPower b n))).symm
  calc
    adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA *
        adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA =
      Matrix.kronecker
        (Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) *
          Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
        ((1 : CMatrix (TensorPower r n)) * (1 : CMatrix (TensorPower r n))) := by
          simpa [adhwFQSWIidLiftProjectorA] using
            (Matrix.mul_kronecker_mul
              (Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
              (Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
              (1 : CMatrix (TensorPower r n)) (1 : CMatrix (TensorPower r n))).symm
    _ = adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA := by
          rw [hAB]
          simp [adhwFQSWIidLiftProjectorA]

omit [DecidableEq a] [DecidableEq b] [DecidableEq r] in
theorem adhwFQSWIidLiftProjectorTriple_idempotent
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n))
    (hPAid : PA * PA = PA) (hPBid : PB * PB = PB) (hPRid : PR * PR = PR) :
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
      adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
        adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR := by
  have hAB :
      Matrix.kronecker PA PB * Matrix.kronecker PA PB =
        Matrix.kronecker PA PB := by
    simpa [hPAid, hPBid] using (Matrix.mul_kronecker_mul PA PA PB PB).symm
  calc
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
        adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
      Matrix.kronecker
        (Matrix.kronecker PA PB * Matrix.kronecker PA PB) (PR * PR) := by
          simpa [adhwFQSWIidLiftProjectorTriple] using
            (Matrix.mul_kronecker_mul (Matrix.kronecker PA PB) (Matrix.kronecker PA PB)
              PR PR).symm
    _ = adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR := by
          rw [hAB, hPRid]
          simp [adhwFQSWIidLiftProjectorTriple]

private theorem adhwFQSW_rejection_trace_eq_one_sub_acceptance
    (ρ : MState a) (P : CMatrix a) :
    ((ρ.m * (1 - P)).trace).re = 1 - ((P * ρ.m).trace).re := by
  have hmul : ρ.m * (1 - P) = ρ.m - ρ.m * P := by
    noncomm_ring
  rw [hmul, Matrix.trace_sub, Complex.sub_re, ρ.tr', Complex.one_re]
  rw [Matrix.trace_mul_comm]

private theorem adhwFQSWIidLiftProjectorTriple_acceptance_of_single
    (n : ℕ)
    (ρ : MState ((TensorPower a n × TensorPower b n) × TensorPower r n))
    (η : ℝ)
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n))
    (hPA : PA.PosSemidef) (hPB : PB.PosSemidef) (hPR : PR.PosSemidef)
    (hPAid : PA * PA = PA) (hPBid : PB * PB = PB) (hPRid : PR * PR = PR)
    (haccA :
      1 - η / 3 ≤
        ((adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA * ρ.m).trace).re)
    (haccB :
      1 - η / 3 ≤
        ((adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB * ρ.m).trace).re)
    (haccR :
      1 - η / 3 ≤
        ((adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * ρ.m).trace).re) :
    1 - η ≤
      ((adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
        ρ.m).trace).re := by
  let PiA := adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA
  let PiB := adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  have hunion : (1 - Pi) ≤ (1 - PiA) + (1 - PiB) + (1 - PiR) := by
    simpa [Pi, PiA, PiB, PiR] using
      adhwFQSWIidLiftProjector_union_bound (a := a) (b := b) (r := r) n PA PB PR
        hPA hPB hPR hPAid hPBid hPRid
  have htrace_le :=
    cMatrix_trace_mul_le_of_le_posSemidef_left (W := ρ.m) ρ.psd hunion
  have hsum :
      ((ρ.m * ((1 - PiA) + (1 - PiB) + (1 - PiR))).trace).re =
        (1 - ((PiA * ρ.m).trace).re) +
          (1 - ((PiB * ρ.m).trace).re) +
            (1 - ((PiR * ρ.m).trace).re) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
      Complex.add_re, Complex.add_re]
    rw [adhwFQSW_rejection_trace_eq_one_sub_acceptance ρ PiA]
    rw [adhwFQSW_rejection_trace_eq_one_sub_acceptance ρ PiB]
    rw [adhwFQSW_rejection_trace_eq_one_sub_acceptance ρ PiR]
  have hrejection :
      ((ρ.m * (1 - Pi)).trace).re ≤ η := by
    calc
      ((ρ.m * (1 - Pi)).trace).re
          ≤ ((ρ.m * ((1 - PiA) + (1 - PiB) + (1 - PiR))).trace).re := htrace_le
      _ = (1 - ((PiA * ρ.m).trace).re) +
            (1 - ((PiB * ρ.m).trace).re) +
              (1 - ((PiR * ρ.m).trace).re) := hsum
      _ ≤ η := by linarith
  have hrej_eq := adhwFQSW_rejection_trace_eq_one_sub_acceptance ρ Pi
  linarith

private theorem adhwFQSW_partialTraceR_liftAB_sandwich_eq_liftB_sandwich_partialTraceR
    (n : ℕ)
    (ρ : MState ((TensorPower a n × TensorPower b n) × TensorPower r n))
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n)) :
    Matrix.traceRight
        (Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) *
          ρ.m *
          Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))) =
      Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB *
        Matrix.traceRight
          (adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA * ρ.m *
            adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA) *
        Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB := by
  ext x y
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  simp [adhwFQSWIidLiftProjectorA, Matrix.traceRight, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (adhwFQSW_sum_five_comm
      (fun r0 aR bR aL bL =>
        PA xa aL *
          (PA aR ya *
            (PB xb bL *
              (PB bR yb * ρ.m ((aL, bL), r0) ((aR, bR), r0))))))

private theorem adhwFQSW_partialTraceR_liftAB_sandwich_eq_liftA_sandwich_partialTraceR
    (n : ℕ)
    (ρ : MState ((TensorPower a n × TensorPower b n) × TensorPower r n))
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n)) :
    Matrix.traceRight
        (Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) *
          ρ.m *
          Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))) =
      Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) *
        Matrix.traceRight
          (adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB * ρ.m *
            adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB) *
        Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) := by
  ext x y
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  simp [adhwFQSWIidLiftProjectorB, Matrix.traceRight, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (adhwFQSW_sum_five_comm_leftPair
      (fun r0 aR bR aL bL =>
        PA xa aL *
          (PA aR ya *
            (PB xb bL *
              (PB bR yb * ρ.m ((aL, bL), r0) ((aR, bR), r0))))))

private theorem adhwFQSW_triple_sandwich_eq_liftR_select_liftAB_sandwich
    (n : ℕ)
    (ρ : MState ((TensorPower a n × TensorPower b n) × TensorPower r n))
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
        ρ.m *
        adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
      adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR *
        (Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) *
          ρ.m *
          Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))) *
        adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR := by
  let K : CMatrix (TensorPower a n × TensorPower b n) := Matrix.kronecker PA PB
  let PiAB : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    Matrix.kronecker K (1 : CMatrix (TensorPower r n))
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  have hleft : PiR * PiAB = Pi := by
    simpa [PiR, PiAB, Pi, K, adhwFQSWIidLiftProjectorR,
      adhwFQSWIidLiftProjectorTriple] using
      (Matrix.mul_kronecker_mul (1 : CMatrix (TensorPower a n × TensorPower b n))
        K PR (1 : CMatrix (TensorPower r n))).symm
  have hright : PiAB * PiR = Pi := by
    simpa [PiR, PiAB, Pi, K, adhwFQSWIidLiftProjectorR,
      adhwFQSWIidLiftProjectorTriple] using
      (Matrix.mul_kronecker_mul K (1 : CMatrix (TensorPower a n × TensorPower b n))
        (1 : CMatrix (TensorPower r n)) PR).symm
  calc
    Pi * ρ.m * Pi = PiR * PiAB * ρ.m * (PiAB * PiR) := by
      rw [hleft, hright]
    _ = PiR * (PiAB * ρ.m * PiAB) * PiR := by
      noncomm_ring

private theorem adhwFQSW_triple_sandwich_eq_liftAB_select_liftR_sandwich
    (n : ℕ)
    (ρ : MState ((TensorPower a n × TensorPower b n) × TensorPower r n))
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
        ρ.m *
        adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
      Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) *
        (adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * ρ.m *
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR) *
        Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) := by
  let K : CMatrix (TensorPower a n × TensorPower b n) := Matrix.kronecker PA PB
  let PiAB : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    Matrix.kronecker K (1 : CMatrix (TensorPower r n))
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  have hleft : PiAB * PiR = Pi := by
    simpa [PiR, PiAB, Pi, K, adhwFQSWIidLiftProjectorR,
      adhwFQSWIidLiftProjectorTriple] using
      (Matrix.mul_kronecker_mul K (1 : CMatrix (TensorPower a n × TensorPower b n))
        (1 : CMatrix (TensorPower r n)) PR).symm
  have hright : PiR * PiAB = Pi := by
    simpa [PiR, PiAB, Pi, K, adhwFQSWIidLiftProjectorR,
      adhwFQSWIidLiftProjectorTriple] using
      (Matrix.mul_kronecker_mul (1 : CMatrix (TensorPower a n × TensorPower b n))
        K PR (1 : CMatrix (TensorPower r n))).symm
  calc
    Pi * ρ.m * Pi = PiAB * PiR * ρ.m * (PiR * PiAB) := by
      rw [hleft, hright]
    _ = PiAB * (PiR * ρ.m * PiR) * PiAB := by
      noncomm_ring

private theorem adhwFQSW_normalizedTripleSandwich_traceRight_le_envelope
    (ψ : Ket ((a × b) × r)) (n : ℕ) (δ' : ℝ) :
    let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
    let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
    let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
    let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
    let τM := Pi * (adhwFQSWIidSourceState ψ n).m * Pi
    0 < τM.trace.re →
      Matrix.traceRight
        (Matrix.traceRight
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM)) ≤
        (((((τM.trace.re)⁻¹ : ℝ) : ℂ) *
          (((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ'))) : ℝ) : ℂ)) • PA) := by
  dsimp only
  intro htrace_pos
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  let PiAB : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))
  let PiA := adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA
  let τM : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    Pi * ρ.m * Pi
  let τAB : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    PiAB * ρ.m * PiAB
  let τA : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    PiA * ρ.m * PiA
  have hPA_stmt :=
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPB_stmt :=
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPR_stmt :=
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement_proved n δ'
  rcases hPA_stmt with ⟨hPApsd, _hPAherm, hPAid, hPAle⟩
  rcases hPB_stmt with ⟨hPBpsd, _hPBherm, hPBid, _hPBle⟩
  rcases hPR_stmt with ⟨hPRpsd, _hPRherm, hPRid, _hPRle⟩
  have hPiABpsd : PiAB.PosSemidef := by
    exact (hPApsd.kronecker hPBpsd).kronecker Matrix.PosSemidef.one
  have hτABpsd : τAB.PosSemidef := by
    simpa [τAB, PiAB] using projector_sandwich_posSemidef PiAB hPiABpsd ρ
  have hR :
      Matrix.traceRight τM ≤
        Matrix.traceRight τAB := by
    have hsel :=
      adhwFQSW_traceRight_selective_projector_le
        (X := τAB) hτABpsd PR hPRpsd hPRid
    have hτeq :
        τM =
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * τAB *
            adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR := by
      simpa [τM, τAB, Pi, PiAB, Matrix.mul_assoc] using
        adhwFQSW_triple_sandwich_eq_liftR_select_liftAB_sandwich
          (a := a) (b := b) (r := r) n ρ PA PB PR
    simpa [τAB, hτeq, adhwFQSWIidLiftProjectorR] using hsel
  have hApsd : τA.PosSemidef := by
    have hPiApsd := adhwFQSWIidLiftProjectorA_posSemidef (b := b) (r := r) n PA hPApsd
    simpa [τA, PiA] using projector_sandwich_posSemidef PiA hPiApsd ρ
  have hB :
      Matrix.traceRight
          (Matrix.traceRight τAB) ≤
        Matrix.traceRight
          (Matrix.traceRight τA) := by
    have hτA_R_psd :
        (Matrix.traceRight τA).PosSemidef :=
      traceRight_posSemidef (a := TensorPower a n × TensorPower b n)
        (b := TensorPower r n) hApsd
    have hsel :=
      adhwFQSW_traceRight_selective_projector_le
        (X := Matrix.traceRight τA)
        hτA_R_psd PB hPBpsd hPBid
    have heq :
        Matrix.traceRight τAB =
          Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB *
            Matrix.traceRight τA *
            Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB := by
      simpa [τAB, τA, PiAB, PiA] using
        adhwFQSW_partialTraceR_liftAB_sandwich_eq_liftB_sandwich_partialTraceR
          (a := a) (b := b) (r := r) n ρ PA PB
    simpa [heq] using hsel
  have hcore₀ :
      Matrix.traceRight
          (Matrix.traceRight τM) ≤
        PA * ρ.traceRight.traceRight.m * PA := by
    calc
      Matrix.traceRight
          (Matrix.traceRight τM)
          ≤ Matrix.traceRight
              (Matrix.traceRight τAB) :=
              traceRight_mono
                (a := TensorPower a n) (b := TensorPower b n) hR
      _ ≤ Matrix.traceRight
              (Matrix.traceRight τA) := hB
      _ = PA * ρ.traceRight.traceRight.m * PA := by
            simpa [τA, PiA] using
              adhwFQSWIidLiftProjectorA_traceRight_traceRight
                (a := a) (b := b) (r := r) n ρ PA
  have hmarg :
      ρ.traceRight.traceRight.m =
        ((adhwFQSWSystemAState ψ).tensorPower n).m := by
    simpa [ρ] using congrArg (fun σ : MState (TensorPower a n) => σ.m)
      (adhwFQSWIidSourceState_traceRight_eq_tensorPower ψ n)
  have hcompress :
      PA * ρ.traceRight.traceRight.m * PA ≤
        (((((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ')))) : ℝ) : ℂ) • PA) := by
    have htyp :=
      MState.typicalSubspaceProjector_tensorPower_compress_le
        (adhwFQSWSystemAState ψ) n δ'
    have hexp :
        -((n : ℝ) * (adhwFQSWEntropyA ψ - δ')) =
          -((n : ℝ) * (adhwFQSWSystemAState ψ).vonNeumann - (n : ℝ) * δ') := by
      simp [adhwFQSWEntropyA]
      ring
    rw [hmarg]
    simpa [PA, hexp] using htyp
  have hcore := hcore₀.trans hcompress
  let c : ℝ := (τM.trace.re)⁻¹
  let d : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ')))
  have hinv_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr htrace_pos.le
  have hscaled :=
    cMatrix_ofReal_smul_le_smul
      (a := TensorPower a n)
      (A := Matrix.traceRight
        (Matrix.traceRight τM))
      (B := (((d : ℝ) : ℂ) • PA))
      hinv_nonneg hcore
  have hscaled_prod :
      (((c : ℝ) : ℂ) •
          Matrix.traceRight
            (Matrix.traceRight τM)) ≤
        (((((c : ℝ) : ℂ) * (((d : ℝ) : ℂ)) : ℂ) • PA)) := by
    have hnested :
        (((c : ℝ) : ℂ) •
            Matrix.traceRight
              (Matrix.traceRight τM)) ≤
          (((c : ℝ) : ℂ) • (((d : ℝ) : ℂ) • PA)) := by
      simpa using hscaled
    rw [adhwFQSW_complex_smul_smul (((c : ℝ) : ℂ)) (((d : ℝ) : ℂ)) PA] at hnested
    exact hnested
  simpa [c, d, τM, Pi, ρ, PA, PB, PR, Matrix.traceRight_smul, Matrix.mul_assoc] using hscaled_prod

private theorem adhwFQSW_normalizedTripleSandwich_traceLeft_le_envelope
    (ψ : Ket ((a × b) × r)) (n : ℕ) (δ' : ℝ) :
    let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
    let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
    let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
    let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
    let τM := Pi * (adhwFQSWIidSourceState ψ n).m * Pi
    0 < τM.trace.re →
      Matrix.traceLeft
        (Matrix.traceRight
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM)) ≤
        (((((τM.trace.re)⁻¹ : ℝ) : ℂ) *
          (((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ'))) : ℝ) : ℂ)) • PB) := by
  dsimp only
  intro htrace_pos
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  let PiAB : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))
  let PiB := adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB
  let τM : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    Pi * ρ.m * Pi
  let τAB : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    PiAB * ρ.m * PiAB
  let τB : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    PiB * ρ.m * PiB
  have hPA_stmt :=
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPB_stmt :=
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPR_stmt :=
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement_proved n δ'
  rcases hPA_stmt with ⟨hPApsd, _hPAherm, hPAid, _hPAle⟩
  rcases hPB_stmt with ⟨hPBpsd, _hPBherm, hPBid, hPBle⟩
  rcases hPR_stmt with ⟨hPRpsd, _hPRherm, hPRid, _hPRle⟩
  have hPiABpsd : PiAB.PosSemidef := by
    exact (hPApsd.kronecker hPBpsd).kronecker Matrix.PosSemidef.one
  have hτABpsd : τAB.PosSemidef := by
    simpa [τAB, PiAB] using projector_sandwich_posSemidef PiAB hPiABpsd ρ
  have hR :
      Matrix.traceRight τM ≤
        Matrix.traceRight τAB := by
    have hsel :=
      adhwFQSW_traceRight_selective_projector_le
        (X := τAB) hτABpsd PR hPRpsd hPRid
    have hτeq :
        τM =
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * τAB *
            adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR := by
      simpa [τM, τAB, Pi, PiAB, Matrix.mul_assoc] using
        adhwFQSW_triple_sandwich_eq_liftR_select_liftAB_sandwich
          (a := a) (b := b) (r := r) n ρ PA PB PR
    simpa [τAB, hτeq, adhwFQSWIidLiftProjectorR] using hsel
  have hBpsd : τB.PosSemidef := by
    have hPiBpsd := adhwFQSWIidLiftProjectorB_posSemidef (a := a) (r := r) n PB hPBpsd
    simpa [τB, PiB] using projector_sandwich_posSemidef PiB hPiBpsd ρ
  have hA :
      Matrix.traceLeft
          (Matrix.traceRight τAB) ≤
        Matrix.traceLeft
          (Matrix.traceRight τB) := by
    have hτB_R_psd :
        (Matrix.traceRight τB).PosSemidef :=
      traceRight_posSemidef (a := TensorPower a n × TensorPower b n)
        (b := TensorPower r n) hBpsd
    have hsel :=
      adhwFQSW_traceLeft_selective_projector_le
        (X := Matrix.traceRight τB)
        hτB_R_psd PA hPApsd hPAid
    have heq :
        Matrix.traceRight τAB =
          Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) *
            Matrix.traceRight τB *
            Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) := by
      simpa [τAB, τB, PiAB, PiB] using
        adhwFQSW_partialTraceR_liftAB_sandwich_eq_liftA_sandwich_partialTraceR
          (a := a) (b := b) (r := r) n ρ PA PB
    simpa [heq] using hsel
  have hcore₀ :
      Matrix.traceLeft
          (Matrix.traceRight τM) ≤
        PB * ρ.traceRight.traceLeft.m * PB := by
    calc
      Matrix.traceLeft
          (Matrix.traceRight τM)
          ≤ Matrix.traceLeft
              (Matrix.traceRight τAB) :=
              traceLeft_mono
                (a := TensorPower a n) (b := TensorPower b n) hR
      _ ≤ Matrix.traceLeft
              (Matrix.traceRight τB) := hA
      _ = PB * ρ.traceRight.traceLeft.m * PB := by
            simpa [τB, PiB] using
              adhwFQSWIidLiftProjectorB_traceRight_traceLeft
                (a := a) (b := b) (r := r) n ρ PB
  have hmarg :
      ρ.traceRight.traceLeft.m =
        ((adhwFQSWSystemBState ψ).tensorPower n).m := by
    simpa [ρ] using congrArg (fun σ : MState (TensorPower b n) => σ.m)
      (adhwFQSWIidSourceState_traceLeft_eq_tensorPower ψ n)
  have hcompress :
      PB * ρ.traceRight.traceLeft.m * PB ≤
        (((((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ')))) : ℝ) : ℂ) • PB) := by
    have htyp :=
      MState.typicalSubspaceProjector_tensorPower_compress_le
        (adhwFQSWSystemBState ψ) n δ'
    have hexp :
        -((n : ℝ) * (adhwFQSWEntropyB ψ - δ')) =
          -((n : ℝ) * (adhwFQSWSystemBState ψ).vonNeumann - (n : ℝ) * δ') := by
      simp [adhwFQSWEntropyB]
      ring
    rw [hmarg]
    simpa [PB, hexp] using htyp
  have hcore := hcore₀.trans hcompress
  let c : ℝ := (τM.trace.re)⁻¹
  let d : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ')))
  have hinv_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr htrace_pos.le
  have hscaled :=
    cMatrix_ofReal_smul_le_smul
      (a := TensorPower b n)
      (A := Matrix.traceLeft
        (Matrix.traceRight τM))
      (B := (((d : ℝ) : ℂ) • PB))
      hinv_nonneg hcore
  have hscaled_prod :
      (((c : ℝ) : ℂ) •
          Matrix.traceLeft
            (Matrix.traceRight τM)) ≤
        (((((c : ℝ) : ℂ) * (((d : ℝ) : ℂ)) : ℂ) • PB)) := by
    have hnested :
        (((c : ℝ) : ℂ) •
            Matrix.traceLeft
              (Matrix.traceRight τM)) ≤
          (((c : ℝ) : ℂ) • (((d : ℝ) : ℂ) • PB)) := by
      simpa using hscaled
    rw [adhwFQSW_complex_smul_smul (((c : ℝ) : ℂ)) (((d : ℝ) : ℂ)) PB] at hnested
    exact hnested
  simpa [c, d, τM, Pi, ρ, PA, PB, PR, Matrix.traceLeft_smul, Matrix.traceRight_smul,
    Matrix.mul_assoc] using hscaled_prod

private theorem adhwFQSW_normalizedTripleSandwich_marginalR_le_envelope
    (ψ : Ket ((a × b) × r)) (n : ℕ) (δ' : ℝ) :
    let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
    let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
    let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
    let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
    let τM := Pi * (adhwFQSWIidSourceState ψ n).m * Pi
    0 < τM.trace.re →
      Matrix.traceLeft
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM) ≤
        (((((τM.trace.re)⁻¹ : ℝ) : ℂ) *
          (((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ'))) : ℝ) : ℂ)) • PR) := by
  dsimp only
  intro htrace_pos
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  let PiAB : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  let τM : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    Pi * ρ.m * Pi
  let τR : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    PiR * ρ.m * PiR
  have hPA_stmt :=
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPB_stmt :=
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPR_stmt :=
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement_proved n δ'
  rcases hPA_stmt with ⟨hPApsd, _hPAherm, hPAid, _hPAle⟩
  rcases hPB_stmt with ⟨hPBpsd, _hPBherm, hPBid, _hPBle⟩
  rcases hPR_stmt with ⟨hPRpsd, _hPRherm, _hPRid, hPRle⟩
  have hQpsd : (Matrix.kronecker PA PB).PosSemidef := hPApsd.kronecker hPBpsd
  have hQid : Matrix.kronecker PA PB * Matrix.kronecker PA PB = Matrix.kronecker PA PB := by
    calc
      Matrix.kronecker PA PB * Matrix.kronecker PA PB =
          Matrix.kronecker (PA * PA) (PB * PB) := by
            exact (Matrix.mul_kronecker_mul PA PA PB PB).symm
      _ = Matrix.kronecker PA PB := by rw [hPAid, hPBid]
  have hRpsd : τR.PosSemidef := by
    have hPiRpsd := adhwFQSWIidLiftProjectorR_posSemidef (a := a) (b := b) n PR hPRpsd
    simpa [τR, PiR] using projector_sandwich_posSemidef PiR hPiRpsd ρ
  have hAB :
      Matrix.traceLeft τM ≤
        Matrix.traceLeft τR := by
    have hsel :=
      adhwFQSW_traceLeft_selective_projector_le
        (X := τR) hRpsd (Matrix.kronecker PA PB) hQpsd hQid
    have hτeq :
        τM = PiAB * τR * PiAB := by
      simpa [τM, τR, Pi, PiAB, PiR, Matrix.mul_assoc] using
        adhwFQSW_triple_sandwich_eq_liftAB_select_liftR_sandwich
          (a := a) (b := b) (r := r) n ρ PA PB PR
    simpa [τR, hτeq, PiAB] using hsel
  have hcore₀ :
      Matrix.traceLeft τM ≤
        PR * ρ.traceLeft.m * PR := by
    calc
      Matrix.traceLeft τM
          ≤ Matrix.traceLeft τR := hAB
      _ = PR * ρ.traceLeft.m * PR := by
            simpa [τR, PiR] using
              adhwFQSWIidLiftProjectorR_traceLeft
                (a := a) (b := b) (r := r) n ρ PR
  have hmarg :
      ρ.traceLeft.m =
        ((adhwFQSWSystemRState ψ).tensorPower n).m := by
    simpa [ρ] using congrArg (fun σ : MState (TensorPower r n) => σ.m)
      (adhwFQSWIidSourceState_marginalR_eq_tensorPower ψ n)
  have hcompress :
      PR * ρ.traceLeft.m * PR ≤
        (((((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ')))) : ℝ) : ℂ) • PR) := by
    have htyp :=
      MState.typicalSubspaceProjector_tensorPower_compress_le
        (adhwFQSWSystemRState ψ) n δ'
    have hexp :
        -((n : ℝ) * (adhwFQSWEntropyR ψ - δ')) =
          -((n : ℝ) * (adhwFQSWSystemRState ψ).vonNeumann - (n : ℝ) * δ') := by
      simp [adhwFQSWEntropyR]
      ring
    rw [hmarg]
    simpa [PR, hexp] using htyp
  have hcore := hcore₀.trans hcompress
  let c : ℝ := (τM.trace.re)⁻¹
  let d : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ')))
  have hinv_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr htrace_pos.le
  have hscaled :=
    cMatrix_ofReal_smul_le_smul
      (a := TensorPower r n)
      (A := Matrix.traceLeft τM)
      (B := (((d : ℝ) : ℂ) • PR))
      hinv_nonneg hcore
  have hscaled_prod :
      (((c : ℝ) : ℂ) •
          Matrix.traceLeft τM) ≤
        (((((c : ℝ) : ℂ) * (((d : ℝ) : ℂ)) : ℂ) • PR)) := by
    have hnested :
        (((c : ℝ) : ℂ) •
            Matrix.traceLeft τM) ≤
          (((c : ℝ) : ℂ) • (((d : ℝ) : ℂ) • PR)) := by
      simpa using hscaled
    rw [adhwFQSW_complex_smul_smul (((c : ℝ) : ℂ)) (((d : ℝ) : ℂ)) PR] at hnested
    exact hnested
  simpa [c, d, τM, Pi, ρ, PA, PB, PR, Matrix.traceLeft_smul, Matrix.mul_assoc] using
    hscaled_prod

/-- AEP high-weight form for one typical projector spectral weight. -/
private theorem adhwFQSW_eventually_one_sub_le_typicalSubspaceSpectralWeight
    (ρ : MState a) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      1 - η ≤ ρ.typicalSubspaceSpectralWeight n δ := by
  have hlim := ρ.tendsto_typicalSubspaceSpectralWeight hδ
  have hball :
      ∀ᶠ n : ℕ in Filter.atTop,
        ρ.typicalSubspaceSpectralWeight n δ ∈ Metric.ball (1 : ℝ) η :=
    hlim.eventually (Metric.ball_mem_nhds _ hη)
  have hev :
      ∀ᶠ n : ℕ in Filter.atTop,
        1 - η ≤ ρ.typicalSubspaceSpectralWeight n δ := by
    filter_upwards [hball] with n hn
    rw [Metric.mem_ball, Real.dist_eq] at hn
    have hlt := abs_lt.mp hn
    linarith
  exact Filter.eventually_atTop.mp hev

/-- Small scalar split used to turn eventual high-weight estimates into an
ADHW-style final trace-error budget. -/
private def adhwFQSWTypicalEta (ε : ℝ) : ℝ :=
  min ((ε / 4) ^ 2) (min (ε / 4) (1 / 2))

private theorem adhwFQSWTypicalEta_pos {ε : ℝ} (hε : 0 < ε) :
    0 < adhwFQSWTypicalEta ε := by
  dsimp [adhwFQSWTypicalEta]
  positivity

private theorem adhwFQSWTypicalEta_error_split {ε : ℝ} (hε : 0 < ε) :
    2 * (Real.sqrt (adhwFQSWTypicalEta ε) + adhwFQSWTypicalEta ε) ≤ ε := by
  have hη_nonneg : 0 ≤ adhwFQSWTypicalEta ε := (adhwFQSWTypicalEta_pos hε).le
  have hη_sq : adhwFQSWTypicalEta ε ≤ (ε / 4) ^ 2 := by
    dsimp [adhwFQSWTypicalEta]
    exact min_le_left _ _
  have hη_quarter : adhwFQSWTypicalEta ε ≤ ε / 4 := by
    dsimp [adhwFQSWTypicalEta]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hsqrt : Real.sqrt (adhwFQSWTypicalEta ε) ≤ ε / 4 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, hη_sq⟩
  linarith

private theorem adhwFQSW_inv_trace_mul_typicalitySlack_envelope_le
    {t η H δ δtyp : ℝ} (n : ℕ)
    (htrace : 1 - η ≤ t)
    (hη_le_half : η ≤ (1 / 2 : ℝ))
    (hδtyp : δtyp = δ / 2)
    (hn_absorb : 1 ≤ (n : ℝ) * δ / 2) :
    t⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (H - δtyp))) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (H - δ))) := by
  have ht_half : (1 / 2 : ℝ) ≤ t := by linarith
  have ht_pos : 0 < t := by linarith
  have hinv_le_two : t⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ ht_pos]
    nlinarith
  have hpow_nonneg :
      0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (H - δtyp))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  calc
    t⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (H - δtyp)))
        ≤ 2 * (2 : ℝ) ^ (-((n : ℝ) * (H - δtyp))) := by
          exact mul_le_mul_of_nonneg_right hinv_le_two hpow_nonneg
    _ = (2 : ℝ) ^ (1 + -((n : ℝ) * (H - δtyp))) := by
          nth_rw 1 [← Real.rpow_one (2 : ℝ)]
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 : ℝ) ^ (-((n : ℝ) * (H - δ))) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
          rw [hδtyp]
          nlinarith

private theorem adhwFQSW_real_smul_one_le_smul_one
    {α : Type u} [Fintype α] [DecidableEq α]
    {c d : ℝ} (hcd : c ≤ d) :
    (((c : ℝ) : ℂ) • (1 : CMatrix α)) ≤
      (((d : ℝ) : ℂ) • (1 : CMatrix α)) := by
  rw [Matrix.le_iff]
  have hdiff :
      (((d : ℝ) : ℂ) • (1 : CMatrix α) -
          ((c : ℝ) : ℂ) • (1 : CMatrix α)) =
        ((((d - c : ℝ) : ℂ)) • (1 : CMatrix α)) := by
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply, Complex.ofReal_sub, sub_mul]
  rw [hdiff]
  exact Matrix.PosSemidef.smul Matrix.PosSemidef.one
    (by exact_mod_cast sub_nonneg.mpr hcd)

private theorem adhwFQSW_hilbertSchmidtSq_le_of_projector_envelope
    {α : Type u} [Fintype α] [DecidableEq α]
    (ρ : MState α) {P : CMatrix α} {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hP_le : P ≤ (1 : CMatrix α))
    (hcd : c ≤ d) (henv : ρ.m ≤ (((c : ℝ) : ℂ) • P)) :
    hilbertSchmidtSq ρ.m ≤ d := by
  have hPenv : (((c : ℝ) : ℂ) • P) ≤ (((c : ℝ) : ℂ) • (1 : CMatrix α)) :=
    cMatrix_ofReal_smul_le_smul hc hP_le
  have hdenv : (((c : ℝ) : ℂ) • (1 : CMatrix α)) ≤
      (((d : ℝ) : ℂ) • (1 : CMatrix α)) :=
    adhwFQSW_real_smul_one_le_smul_one hcd
  exact MState.hilbertSchmidtSq_matrix_le_of_le_smul_one ρ hd
    (henv.trans (hPenv.trans hdenv))

private theorem adhwFQSW_traceNormDistance_le_of_normalizedTraceDistance_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (ρ σ : MState α) {η ε : ℝ}
    (hdist : ρ.normalizedTraceDistance σ ≤ Real.sqrt η + η)
    (hsplit : 2 * (Real.sqrt η + η) ≤ ε) :
    traceNormDistance ρ.m σ.m ≤ ε := by
  have hnorm : (1 / 2 : ℝ) * traceNormDistance ρ.m σ.m ≤
      Real.sqrt η + η := by
    simpa [MState.normalizedTraceDistance, normalizedTraceDistance] using hdist
  have hnonneg : 0 ≤ traceNormDistance ρ.m σ.m :=
    traceNormDistance_nonneg ρ.m σ.m
  nlinarith

/-- Simultaneous ADHW i.i.d. typical projectors `Π_A`, `Π_B`, and `Π_R`,
with the no-witness spectral construction, source estimates, marginal purity
bounds, and item iii rank bounds from fqsw.tex lines 1110-1129.

The projectors use the internal typicality window `δ / 2`.  This is the
standard slack split needed by `MState.eventually_two_pow_sub_le_typicalSubspaceDimension`:
the constructed projectors are typical at the smaller window while the public
ADHW rank and purity bounds are stated with the advertised `±δ` slack. -/
structure ADHWFQSWSimultaneousTypicalProjectors
    (ψ : Ket ((a × b) × r)) (n : ℕ) (δ ε : ℝ) where
  /-- The internal typicality window, smaller than the advertised slack `δ`. -/
  typicalitySlack : ℝ
  /-- The internal window is half the advertised slack. -/
  typicalitySlack_eq : typicalitySlack = δ / 2
  /-- The internal window is positive. -/
  typicalitySlack_pos : 0 < typicalitySlack
  /-- The internal window is strictly smaller than the advertised slack. -/
  typicalitySlack_lt_delta : typicalitySlack < δ
  /-- Alice's typical projector. -/
  projectorA : CMatrix (TensorPower a n)
  /-- Bob's typical projector. -/
  projectorB : CMatrix (TensorPower b n)
  /-- The reference typical projector. -/
  projectorR : CMatrix (TensorPower r n)
  /-- Alice's projector is the typical-subspace projector at the internal window. -/
  projectorA_eq :
    projectorA = (adhwFQSWSystemAState ψ).typicalSubspaceProjector n typicalitySlack
  /-- Bob's projector is the typical-subspace projector at the internal window. -/
  projectorB_eq :
    projectorB = (adhwFQSWSystemBState ψ).typicalSubspaceProjector n typicalitySlack
  /-- The reference projector is the typical-subspace projector at the internal window. -/
  projectorR_eq :
    projectorR = (adhwFQSWSystemRState ψ).typicalSubspaceProjector n typicalitySlack
  /-- The defining typicality properties of Alice's projector. -/
  projectorA_statement :
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement n typicalitySlack
  /-- The defining typicality properties of Bob's projector. -/
  projectorB_statement :
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement n typicalitySlack
  /-- The defining typicality properties of the reference projector. -/
  projectorR_statement :
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement n typicalitySlack
  /-- The Schumacher-compressed source. -/
  compressedSource :
    MState ((TensorPower a n × TensorPower b n) × TensorPower r n)
  /-- The source projected onto all three typical subspaces and renormalized. -/
  normalizedTypicalSource :
    MState ((TensorPower a n × TensorPower b n) × TensorPower r n)
  /-- The projected source has nonzero trace, so it can be renormalized. -/
  normalizedTypicalSource_projected_trace_pos :
    0 < (adhwFQSWIidProjectedSourceMatrix
      (a := a) (b := b) (r := r) ψ n projectorA projectorB projectorR).trace.re
  /-- The normalized typical source is the renormalized projected source. -/
  normalizedTypicalSource_matrix_eq :
    normalizedTypicalSource.m =
      ((((adhwFQSWIidProjectedSourceMatrix
        (a := a) (b := b) (r := r) ψ n projectorA projectorB projectorR).trace.re)⁻¹ :
          ℝ) : ℂ) •
        adhwFQSWIidProjectedSourceMatrix
          (a := a) (b := b) (r := r) ψ n projectorA projectorB projectorR
  /-- Compression moves the source by at most `ε` in trace distance. -/
  schumacher_traceNorm_le :
    traceNormDistance compressedSource.m (adhwFQSWIidSourceState ψ n).m ≤ ε
  /-- The compressed and normalized typical sources are within `ε`. -/
  schumacher_traceNorm_le_normalizedTypical :
    traceNormDistance compressedSource.m normalizedTypicalSource.m ≤ ε
  /-- Typical projection moves the source by at most `ε` in trace distance. -/
  normalized_traceNorm_le :
    traceNormDistance normalizedTypicalSource.m (adhwFQSWIidSourceState ψ n).m ≤ ε
  /-- Alice's marginal purity is exponentially small in her entropy. -/
  purityA_le :
    hilbertSchmidtSq normalizedTypicalSource.traceRight.traceRight.m ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ)))
  /-- Bob's marginal purity is exponentially small in his entropy. -/
  purityB_le :
    hilbertSchmidtSq normalizedTypicalSource.traceRight.traceLeft.m ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ)))
  /-- The reference marginal purity is exponentially small in its entropy. -/
  purityR_le :
    hilbertSchmidtSq normalizedTypicalSource.traceLeft.m ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ)))
  /-- Alice's typical subspace has rank at least `2 ^ (n (S(A) - δ))`. -/
  rankA_lower :
    (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyA ψ - δ)) ≤
      (adhwFQSWSystemAState ψ).typicalSubspaceDimension n typicalitySlack
  /-- Alice's typical subspace has rank at most `2 ^ (n (S(A) + δ))`. -/
  rankA_upper :
    (adhwFQSWSystemAState ψ).typicalSubspaceDimension n typicalitySlack ≤
      (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyA ψ + δ))
  /-- Bob's typical subspace has rank at least `2 ^ (n (S(B) - δ))`. -/
  rankB_lower :
    (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyB ψ - δ)) ≤
      (adhwFQSWSystemBState ψ).typicalSubspaceDimension n typicalitySlack
  /-- Bob's typical subspace has rank at most `2 ^ (n (S(B) + δ))`. -/
  rankB_upper :
    (adhwFQSWSystemBState ψ).typicalSubspaceDimension n typicalitySlack ≤
      (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyB ψ + δ))
  /-- The reference typical subspace has rank at least `2 ^ (n (S(R) - δ))`. -/
  rankR_lower :
    (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ - δ)) ≤
      (adhwFQSWSystemRState ψ).typicalSubspaceDimension n typicalitySlack
  /-- The reference typical subspace has rank at most `2 ^ (n (S(R) + δ))`. -/
  rankR_upper :
    (adhwFQSWSystemRState ψ).typicalSubspaceDimension n typicalitySlack ≤
      (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ + δ))

/-- Upper rank bound after splitting the advertised ADHW slack `δ` into an
internal typicality window `δ / 2`. -/
private theorem adhwFQSW_typicalSubspaceDimension_le_two_pow_halfSlack
    (ρ : MState a) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ρ.typicalSubspaceDimension n (δ / 2) ≤
      (2 : ℝ) ^ ((n : ℝ) * (ρ.vonNeumann + δ)) := by
  have hbase : (1 : ℝ) ≤ 2 := by norm_num
  have hdim := ρ.typicalSubspaceDimension_le_two_pow n (δ / 2)
  have hexp :
      (n : ℝ) * (ρ.vonNeumann + δ / 2) ≤
        (n : ℝ) * (ρ.vonNeumann + δ) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    nlinarith
  exact hdim.trans (Real.rpow_le_rpow_of_exponent_le hbase hexp)

/-- Construct the simultaneous typical-projector record from local spectral
typical projectors, with no external proof witnesses.

For every positive advertised slack `δ` and tolerance `ε`, all sufficiently
large `n` have the three internal-window projectors, the normalized source
estimates, the three marginal purity estimates, and the ADHW item iii rank
bounds. -/
theorem exists_adhwFQSWSimultaneousTypicalProjectors
    (ψ : Ket ((a × b) × r)) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      Nonempty (ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε) := by
  have hhalf_pos : 0 < δ / 2 := by linarith
  have hhalf_lt : δ / 2 < δ := by linarith
  let η : ℝ := adhwFQSWTypicalEta (ε / 2)
  have hε_half_pos : 0 < ε / 2 := by positivity
  have hε_half_le : ε / 2 ≤ ε := by linarith
  have hη_pos : 0 < η := by
    simpa [η] using adhwFQSWTypicalEta_pos hε_half_pos
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hη_le_half : η ≤ (1 / 2 : ℝ) := by
    dsimp [η, adhwFQSWTypicalEta]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hη_lt_one : η < 1 := by linarith
  have hη_third_pos : 0 < η / 3 := by linarith
  have hη_error := adhwFQSWTypicalEta_error_split hε_half_pos
  obtain ⟨NA, hNA⟩ :=
    (adhwFQSWSystemAState ψ).eventually_two_pow_sub_le_typicalSubspaceDimension
      hhalf_pos hhalf_lt
  obtain ⟨NB, hNB⟩ :=
    (adhwFQSWSystemBState ψ).eventually_two_pow_sub_le_typicalSubspaceDimension
      hhalf_pos hhalf_lt
  obtain ⟨NR, hNR⟩ :=
    (adhwFQSWSystemRState ψ).eventually_two_pow_sub_le_typicalSubspaceDimension
      hhalf_pos hhalf_lt
  obtain ⟨NwA, hW_A⟩ :=
    adhwFQSW_eventually_one_sub_le_typicalSubspaceSpectralWeight
      (adhwFQSWSystemAState ψ) hhalf_pos hη_third_pos
  obtain ⟨NwB, hW_B⟩ :=
    adhwFQSW_eventually_one_sub_le_typicalSubspaceSpectralWeight
      (adhwFQSWSystemBState ψ) hhalf_pos hη_third_pos
  obtain ⟨NwR, hW_R⟩ :=
    adhwFQSW_eventually_one_sub_le_typicalSubspaceSpectralWeight
      (adhwFQSWSystemRState ψ) hhalf_pos hη_third_pos
  let Nabs : ℕ := Nat.ceil (2 / δ)
  let N : ℕ := max NA (max NB (max NR (max NwA (max NwB (max NwR Nabs)))))
  refine ⟨N, ?_⟩
  intro n hn
  have hnA : n ≥ NA := by dsimp [N] at hn; omega
  have hnB : n ≥ NB := by dsimp [N] at hn; omega
  have hnR : n ≥ NR := by dsimp [N] at hn; omega
  have hnWA : n ≥ NwA := by dsimp [N] at hn; omega
  have hnWB : n ≥ NwB := by dsimp [N] at hn; omega
  have hnWR : n ≥ NwR := by dsimp [N] at hn; omega
  have hnAbs : n ≥ Nabs := by dsimp [N] at hn; omega
  have hn_absorb : 1 ≤ (n : ℝ) * δ / 2 := by
    have hceil : 2 / δ ≤ (Nabs : ℝ) := by
      simpa [Nabs] using Nat.le_ceil (2 / δ)
    have hnAbs_real : (Nabs : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnAbs
    have htwo_div_le : 2 / δ ≤ (n : ℝ) := hceil.trans hnAbs_real
    have hmul := mul_le_mul_of_nonneg_right htwo_div_le hδ.le
    have hdiv_mul : (2 / δ) * δ = (2 : ℝ) := by field_simp [hδ.ne']
    nlinarith
  let δtyp : ℝ := δ / 2
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δtyp
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δtyp
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δtyp
  let PiA := adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  let τA : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    PiA * ρ.m * PiA
  let τM : CMatrix ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    Pi * ρ.m * Pi
  have hPAstmt :
      (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement n δtyp :=
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement_proved n δtyp
  have hPBstmt :
      (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement n δtyp :=
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement_proved n δtyp
  have hPRstmt :
      (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement n δtyp :=
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement_proved n δtyp
  have hPAstmt_parts := hPAstmt
  have hPBstmt_parts := hPBstmt
  have hPRstmt_parts := hPRstmt
  rcases hPAstmt_parts with ⟨hPApsd, _hPAherm, hPAid, hPAle⟩
  rcases hPBstmt_parts with ⟨hPBpsd, _hPBherm, hPBid, hPBle⟩
  rcases hPRstmt_parts with ⟨hPRpsd, _hPRherm, hPRid, hPRle⟩
  have hPiApsd : PiA.PosSemidef := by
    simpa [PiA, PA] using
      adhwFQSWIidLiftProjectorA_posSemidef (b := b) (r := r) n PA hPApsd
  have hPiAid : PiA * PiA = PiA := by
    simpa [PiA, PA] using
      adhwFQSWIidLiftProjectorA_idempotent (b := b) (r := r) n PA hPAid
  have hPipsd : Pi.PosSemidef := by
    simpa [Pi, PA, PB, PR] using
      adhwFQSWIidLiftProjectorTriple_posSemidef (a := a) (b := b) (r := r)
        n PA PB PR hPApsd hPBpsd hPRpsd
  have hPiid : Pi * Pi = Pi := by
    simpa [Pi, PA, PB, PR] using
      adhwFQSWIidLiftProjectorTriple_idempotent (a := a) (b := b) (r := r)
        n PA PB PR hPAid hPBid hPRid
  have hτApsd : τA.PosSemidef := by
    simpa [τA] using projector_sandwich_posSemidef PiA hPiApsd ρ
  have hτMpsd : τM.PosSemidef := by
    simpa [τM] using projector_sandwich_posSemidef Pi hPipsd ρ
  have haccA3 :
      1 - η / 3 ≤ ((PiA * ρ.m).trace).re := by
    calc
      1 - η / 3 ≤
          (adhwFQSWSystemAState ψ).typicalSubspaceSpectralWeight n δtyp :=
            hW_A n hnWA
      _ = ((PiA * ρ.m).trace).re := by
            simpa [PiA, PA, ρ, δtyp] using
              (adhwFQSWIid_acceptanceA (a := a) (b := b) (r := r) ψ n δtyp).symm
  let PiB := adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  have haccB3 :
      1 - η / 3 ≤ ((PiB * ρ.m).trace).re := by
    calc
      1 - η / 3 ≤
          (adhwFQSWSystemBState ψ).typicalSubspaceSpectralWeight n δtyp :=
            hW_B n hnWB
      _ = ((PiB * ρ.m).trace).re := by
            simpa [PiB, PB, ρ, δtyp] using
              (adhwFQSWIid_acceptanceB (a := a) (b := b) (r := r) ψ n δtyp).symm
  have haccR3 :
      1 - η / 3 ≤ ((PiR * ρ.m).trace).re := by
    calc
      1 - η / 3 ≤
          (adhwFQSWSystemRState ψ).typicalSubspaceSpectralWeight n δtyp :=
            hW_R n hnWR
      _ = ((PiR * ρ.m).trace).re := by
            simpa [PiR, PR, ρ, δtyp] using
              (adhwFQSWIid_acceptanceR (a := a) (b := b) (r := r) ψ n δtyp).symm
  have haccA : 1 - η ≤ ((PiA * ρ.m).trace).re := by
    linarith
  have haccTriple : 1 - η ≤ ((Pi * ρ.m).trace).re := by
    simpa [Pi, PiA, PiB, PiR, PA, PB, PR] using
      adhwFQSWIidLiftProjectorTriple_acceptance_of_single
        (a := a) (b := b) (r := r) n ρ η PA PB PR
        hPApsd hPBpsd hPRpsd hPAid hPBid hPRid haccA3 haccB3 haccR3
  have htrA : τA.trace.re ≠ 0 := by
    simpa [τA] using
      projector_sandwich_trace_re_ne_zero_of_acceptance PiA hPiAid ρ hη_lt_one haccA
  have htrM : τM.trace.re ≠ 0 := by
    simpa [τM] using
      projector_sandwich_trace_re_ne_zero_of_acceptance Pi hPiid ρ hη_lt_one haccTriple
  have htraceM_lower : 1 - η ≤ τM.trace.re := by
    calc
      1 - η ≤ ((Pi * ρ.m).trace).re := haccTriple
      _ = τM.trace.re := by
            simpa [τM] using
              (projector_sandwich_trace_re_eq_acceptance Pi hPiid ρ).symm
  have htraceM_pos : 0 < τM.trace.re :=
    lt_of_lt_of_le (by linarith : 0 < 1 - η) htraceM_lower
  let compressedSource :
      MState ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    MState.normalizePSD τA hτApsd htrA
  let normalizedTypicalSource :
      MState ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
    MState.normalizePSD τM hτMpsd htrM
  have hdistCompressed_norm :
      compressedSource.normalizedTraceDistance ρ ≤ Real.sqrt η + η := by
    simpa [compressedSource, τA, MState.normalizedTraceDistance, normalizedTraceDistance,
      MState.normalizePSD_matrix] using
      normalizedTraceDistance_normalize_projector_sandwich_le
        (P := PiA) hPiApsd hPiAid ρ hη_nonneg hη_lt_one haccA
  have hdistNormalized_norm :
      normalizedTypicalSource.normalizedTraceDistance ρ ≤ Real.sqrt η + η := by
    simpa [normalizedTypicalSource, τM, MState.normalizedTraceDistance, normalizedTraceDistance,
      MState.normalizePSD_matrix] using
      normalizedTraceDistance_normalize_projector_sandwich_le
        (P := Pi) hPipsd hPiid ρ hη_nonneg hη_lt_one haccTriple
  have hdistCompressed_half :
      traceNormDistance compressedSource.m ρ.m ≤ ε / 2 :=
    adhwFQSW_traceNormDistance_le_of_normalizedTraceDistance_le
      compressedSource ρ hdistCompressed_norm (by simpa [η] using hη_error)
  have hdistNormalized_half :
      traceNormDistance normalizedTypicalSource.m ρ.m ≤ ε / 2 :=
    adhwFQSW_traceNormDistance_le_of_normalizedTraceDistance_le
      normalizedTypicalSource ρ hdistNormalized_norm (by simpa [η] using hη_error)
  have hdistCompressed :
      traceNormDistance compressedSource.m ρ.m ≤ ε :=
    hdistCompressed_half.trans hε_half_le
  have hdistNormalized :
      traceNormDistance normalizedTypicalSource.m ρ.m ≤ ε :=
    hdistNormalized_half.trans hε_half_le
  have hdistCompressedNormalized :
      traceNormDistance compressedSource.m normalizedTypicalSource.m ≤ ε := by
    have hdistNormalized_half_comm :
        traceNormDistance ρ.m normalizedTypicalSource.m ≤ ε / 2 := by
      rw [traceNormDistance_comm]
      exact hdistNormalized_half
    calc
      traceNormDistance compressedSource.m normalizedTypicalSource.m
          ≤ traceNormDistance compressedSource.m ρ.m +
              traceNormDistance ρ.m normalizedTypicalSource.m :=
            traceNormDistance_triangle compressedSource.m ρ.m normalizedTypicalSource.m
      _ ≤ ε / 2 + ε / 2 := by
            exact add_le_add hdistCompressed_half hdistNormalized_half_comm
      _ = ε := by ring
  let cA : ℝ :=
    τM.trace.re⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δtyp)))
  let cB : ℝ :=
    τM.trace.re⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δtyp)))
  let cR : ℝ :=
    τM.trace.re⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δtyp)))
  have hcA_nonneg : 0 ≤ cA := by
    dsimp [cA]
    exact mul_nonneg (inv_nonneg.mpr htraceM_pos.le)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hcB_nonneg : 0 ≤ cB := by
    dsimp [cB]
    exact mul_nonneg (inv_nonneg.mpr htraceM_pos.le)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hcR_nonneg : 0 ≤ cR := by
    dsimp [cR]
    exact mul_nonneg (inv_nonneg.mpr htraceM_pos.le)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have htargetA_nonneg :
      0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have htargetB_nonneg :
      0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have htargetR_nonneg :
      0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hcA_le :
      cA ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))) := by
    change τM.trace.re⁻¹ *
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δtyp))) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ)))
    exact
      adhwFQSW_inv_trace_mul_typicalitySlack_envelope_le
        (n := n) (t := τM.trace.re) (η := η)
        (H := adhwFQSWEntropyA ψ) (δ := δ) (δtyp := δtyp)
        htraceM_lower hη_le_half rfl hn_absorb
  have hcB_le :
      cB ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) := by
    change τM.trace.re⁻¹ *
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δtyp))) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ)))
    exact
      adhwFQSW_inv_trace_mul_typicalitySlack_envelope_le
        (n := n) (t := τM.trace.re) (η := η)
        (H := adhwFQSWEntropyB ψ) (δ := δ) (δtyp := δtyp)
        htraceM_lower hη_le_half rfl hn_absorb
  have hcR_le :
      cR ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))) := by
    change τM.trace.re⁻¹ *
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δtyp))) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ)))
    exact
      adhwFQSW_inv_trace_mul_typicalitySlack_envelope_le
        (n := n) (t := τM.trace.re) (η := η)
        (H := adhwFQSWEntropyR ψ) (δ := δ) (δtyp := δtyp)
        htraceM_lower hη_le_half rfl hn_absorb
  have henvA :
      normalizedTypicalSource.traceRight.traceRight.m ≤ (((cA : ℝ) : ℂ) • PA) := by
    have henv :=
      adhwFQSW_normalizedTripleSandwich_traceRight_le_envelope
        (a := a) (b := b) (r := r) ψ n δtyp htraceM_pos
    simp only [normalizedTypicalSource, MState.traceRight_m, MState.normalizePSD_matrix]
    change
      Matrix.traceRight
        (Matrix.traceRight
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM)) ≤ (((cA : ℝ) : ℂ) • PA)
    rw [Matrix.traceRight_smul, Matrix.traceRight_smul]
    have henv' := henv
    rw [Matrix.traceRight_smul, Matrix.traceRight_smul] at henv'
    simpa only [τM, Pi, ρ, PA, PB, PR, cA, Matrix.mul_assoc, Complex.ofReal_mul] using henv'
  have henvB :
      normalizedTypicalSource.traceRight.traceLeft.m ≤ (((cB : ℝ) : ℂ) • PB) := by
    have henv :=
      adhwFQSW_normalizedTripleSandwich_traceLeft_le_envelope
        (a := a) (b := b) (r := r) ψ n δtyp htraceM_pos
    simp only [normalizedTypicalSource, MState.traceRight_m, MState.traceLeft_m,
      MState.normalizePSD_matrix]
    change
      Matrix.traceLeft
        (Matrix.traceRight
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM)) ≤ (((cB : ℝ) : ℂ) • PB)
    rw [Matrix.traceRight_smul, Matrix.traceLeft_smul]
    have henv' := henv
    rw [Matrix.traceRight_smul, Matrix.traceLeft_smul] at henv'
    simpa only [τM, Pi, ρ, PA, PB, PR, cB, Matrix.mul_assoc, Complex.ofReal_mul] using henv'
  have henvR :
      normalizedTypicalSource.traceLeft.m ≤ (((cR : ℝ) : ℂ) • PR) := by
    have henv :=
      adhwFQSW_normalizedTripleSandwich_marginalR_le_envelope
        (a := a) (b := b) (r := r) ψ n δtyp htraceM_pos
    simp only [normalizedTypicalSource, MState.traceLeft_m, MState.normalizePSD_matrix]
    change
      Matrix.traceLeft
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM) ≤
        (((((τM.trace.re)⁻¹ *
            (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δtyp)))) : ℝ) : ℂ) • PR)
    rw [Complex.ofReal_mul]
    simpa only [τM, Pi, ρ, PA, PB, PR, Matrix.mul_assoc] using henv
  have hpurityA :
      hilbertSchmidtSq normalizedTypicalSource.traceRight.traceRight.m ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))) :=
    adhwFQSW_hilbertSchmidtSq_le_of_projector_envelope
      (c := cA)
      (d := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))))
      normalizedTypicalSource.traceRight.traceRight
      hcA_nonneg htargetA_nonneg hPAle hcA_le henvA
  have hpurityB :
      hilbertSchmidtSq normalizedTypicalSource.traceRight.traceLeft.m ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) :=
    adhwFQSW_hilbertSchmidtSq_le_of_projector_envelope
      (c := cB)
      (d := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))))
      normalizedTypicalSource.traceRight.traceLeft
      hcB_nonneg htargetB_nonneg hPBle hcB_le henvB
  have hpurityR :
      hilbertSchmidtSq normalizedTypicalSource.traceLeft.m ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))) :=
    adhwFQSW_hilbertSchmidtSq_le_of_projector_envelope
      (c := cR)
      (d := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))))
      normalizedTypicalSource.traceLeft
      hcR_nonneg htargetR_nonneg hPRle hcR_le henvR
  exact
    ⟨{ typicalitySlack := δtyp
       typicalitySlack_eq := rfl
       typicalitySlack_pos := hhalf_pos
       typicalitySlack_lt_delta := hhalf_lt
       projectorA := PA
       projectorB := PB
       projectorR := PR
       projectorA_eq := rfl
       projectorB_eq := rfl
       projectorR_eq := rfl
       projectorA_statement := hPAstmt
       projectorB_statement := hPBstmt
       projectorR_statement := hPRstmt
       compressedSource := compressedSource
       normalizedTypicalSource := normalizedTypicalSource
       normalizedTypicalSource_projected_trace_pos := by
        change 0 < τM.trace.re
        exact htraceM_pos
       normalizedTypicalSource_matrix_eq := by
        change normalizedTypicalSource.m =
          (((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM
        exact MState.normalizePSD_matrix τM hτMpsd htrM
       schumacher_traceNorm_le := by
        simpa [ρ] using hdistCompressed
       schumacher_traceNorm_le_normalizedTypical := by
        simpa using hdistCompressedNormalized
       normalized_traceNorm_le := by
        simpa [ρ] using hdistNormalized
       purityA_le := hpurityA
       purityB_le := hpurityB
       purityR_le := hpurityR
       rankA_lower := by
        simpa [δtyp, adhwFQSWEntropyA] using hNA n hnA
       rankA_upper := by
        simpa [δtyp, adhwFQSWEntropyA] using
          adhwFQSW_typicalSubspaceDimension_le_two_pow_halfSlack
            (adhwFQSWSystemAState ψ) n hδ
       rankB_lower := by
        simpa [δtyp, adhwFQSWEntropyB] using hNB n hnB
       rankB_upper := by
        simpa [δtyp, adhwFQSWEntropyB] using
          adhwFQSW_typicalSubspaceDimension_le_two_pow_halfSlack
            (adhwFQSWSystemBState ψ) n hδ
       rankR_lower := by
        simpa [δtyp, adhwFQSWEntropyR] using hNR n hnR
       rankR_upper := by
        simpa [δtyp, adhwFQSWEntropyR] using
          adhwFQSW_typicalSubspaceDimension_le_two_pow_halfSlack
            (adhwFQSWSystemRState ψ) n hδ }⟩

end

end QIT
