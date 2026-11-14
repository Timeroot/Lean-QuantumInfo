/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Classical.Ensemble
public import QIT.States.TraceNorm.Distance
public import QIT.Util.Matrix

/-!
# Classical-quantum states from ensembles

A classical-quantum (cq) state rho_XQ = Sum_x p_x |x><x|_X (x) rho_x is built
from a finite ensemble by block-diagonal embedding of each member state in the
classical register, instantiating the cq-state decomposition in the source
material [Tomamichel2015FiniteResources, prelim.tex:617-624].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v

noncomputable section

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a]
variable [DecidableEq ι] [DecidableEq a]

namespace Ensemble

/-- The classical-quantum state rho_XQ = Sum_x p_x |x><x|_X (x) rho_x. -/
def cqState (E : Ensemble ι a) : State (Prod ι a) where
  matrix := ∑ x, (E.probs x) • Matrix.kronecker (Matrix.single x x (1 : ℂ)) (E.states x).matrix
  pos := by
    exact Matrix.posSemidef_sum Finset.univ fun x _ =>
      ((posSemidef_single x).kronecker (E.states x).pos).smul (NNReal.coe_nonneg (E.probs x))
  trace_eq_one := by
    have hkr : ∀ x, (Matrix.kronecker (Matrix.single x x (1 : ℂ)) (E.states x).matrix).trace =
        (Matrix.single x x (1 : ℂ)).trace * (E.states x).matrix.trace := fun x =>
      Matrix.trace_kronecker _ _
    simp only [Matrix.trace_sum, Matrix.trace_smul]
    rw [Finset.sum_congr rfl fun x _ => by rw [hkr x, trace_single_one, if_pos rfl, one_mul,
      (E.states x).trace_eq_one]]
    rw [Finset.sum_congr rfl fun x _ => (Algebra.algebraMap_eq_smul_one _).symm]
    rw [← map_sum (algebraMap ℝ≥0 ℂ) E.probs Finset.univ, E.weights_sum, map_one]

/-- The cq state's matrix is the weighted Kronecker sum. -/
@[simp]
theorem cqState_matrix (E : Ensemble ι a) :
    E.cqState.matrix =
      ∑ x, (E.probs x) • Matrix.kronecker (Matrix.single x x (1 : ℂ)) (E.states x).matrix := by
  rfl

/-- Tracing out the classical register gives the ensemble's average state. -/
theorem partialTraceA_cqState (E : Ensemble ι a) :
    partialTraceA (E.cqState.matrix) = E.averageState.matrix := by
  ext j j'
  simp only [cqState_matrix, averageState_matrix, partialTraceA, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)
      fun x _ hx => by
        simp only [Matrix.single_apply, hx, if_false, and_self_iff, if_false, zero_mul,
          smul_zero]]
  simp only [Matrix.single_apply, and_self_iff, if_true, one_mul]

/-- The quantum marginal of an ensemble cq-state is the ensemble average state. -/
theorem cqState_marginalB_eq_averageState (E : Ensemble ι a) :
    E.cqState.marginalB = E.averageState := by
  apply State.ext
  exact partialTraceA_cqState E

/-- Tracing out the quantum system gives the classical distribution diag(p). -/
theorem partialTraceB_cqState (E : Ensemble ι a) :
    partialTraceB (E.cqState.matrix) = Matrix.diagonal (fun x => ((E.probs x : ℂ))) := by
  ext x x'
  simp only [cqState_matrix, partialTraceB, Matrix.sum_apply, Matrix.diagonal_apply,
    Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  by_cases h : x = x'
  · subst h
    rw [if_pos rfl]
    have key : ∀ (i : a),
        (∑ c : ι, (E.probs c • (Matrix.single c c (1 : ℂ) x x * (E.states c).matrix i i) : ℂ)) =
          (E.probs x • (E.states x).matrix i i : ℂ) := by
      intro i
      rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _)
          fun c _ hc => by
            have hz : Matrix.single c c (1 : ℂ) x x = 0 := by
              rw [Matrix.single_apply, if_neg fun hcc => hc hcc.1]
            rw [hz, zero_mul, smul_zero]]
      simp only [Matrix.single_apply, and_self_iff, if_true, one_mul]
    simp only [key]
    rw [← Finset.smul_sum]
    show (E.probs x) • ((E.states x).matrix.trace) = ↑↑(E.probs x)
    rw [(E.states x).trace_eq_one, Algebra.smul_def, mul_one]
    rfl
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    have hz : Matrix.single j j (1 : ℂ) x x' = 0 := by
      rw [Matrix.single_apply, if_neg fun hcc => h (hcc.1.symm.trans hcc.2)]
    rw [hz, zero_mul, smul_zero]

end Ensemble

namespace Classical

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [DecidableEq ι]

/-- Extract the `(x, x')` classical block of a matrix on a classical-quantum product. -/
def block (X : CMatrix (Prod ι a)) (x x' : ι) : CMatrix a := fun i j => X (x, i) (x', j)

/-- Reconstruct a block-diagonal classical-quantum matrix from quantum blocks. -/
def blockDiagonal (blocks : ι → CMatrix a) : CMatrix (Prod ι a) :=
  ∑ x, Matrix.kronecker (Matrix.single x x (1 : ℂ)) (blocks x)

/-- Extracting a diagonal block from a block-diagonal matrix recovers that block. -/
@[simp]
theorem blockDiagonal_block_self (blocks : ι → CMatrix a) (x : ι) :
    block (blockDiagonal blocks) x x = blocks x := by
  ext i j
  simp only [block, blockDiagonal, Matrix.sum_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _)
      fun y _ hy => by
        have hz : Matrix.single y y (1 : ℂ) x x = 0 := by
          rw [Matrix.single_apply, if_neg fun hyy => hy hyy.1]
        rw [hz, zero_mul]]
  simp only [Matrix.single_apply, and_self_iff, if_true, one_mul]

/-- Off-diagonal classical blocks of a block-diagonal matrix vanish. -/
@[simp]
theorem blockDiagonal_block_ne (blocks : ι → CMatrix a) {x x' : ι} (h : x ≠ x') :
    block (blockDiagonal blocks) x x' = 0 := by
  ext i j
  simp only [block, blockDiagonal, Matrix.sum_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hz : Matrix.single y y (1 : ℂ) x x' = 0 := by
    rw [Matrix.single_apply, if_neg fun hyy => h (hyy.1.symm.trans hyy.2)]
  rw [hz, zero_mul]

/-- Block-diagonal reconstruction commutes with blockwise subtraction. -/
theorem blockDiagonal_sub (blocks blocks' : ι → CMatrix a) :
    blockDiagonal (fun x => blocks x - blocks' x) =
      blockDiagonal blocks - blockDiagonal blocks' := by
  classical
  unfold blockDiagonal
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ext xi xj
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

/-- Block-diagonal reconstruction commutes with scalar multiplication. -/
theorem blockDiagonal_smul (c : ℂ) (blocks : ι → CMatrix a) :
    blockDiagonal (fun x => c • blocks x) =
      c • blockDiagonal blocks := by
  classical
  unfold blockDiagonal
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ext xi xj
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

/-- A side operator tensored with the classical identity is the constant
block-diagonal matrix with that side operator in each diagonal block. -/
theorem identityTensor_eq_blockDiagonal (T : CMatrix a) :
    Matrix.kronecker (1 : CMatrix ι) T =
      blockDiagonal (fun _ : ι => T) := by
  classical
  ext xi xj
  rcases xi with ⟨x, i⟩
  rcases xj with ⟨x', j⟩
  by_cases hxx' : x = x'
  · subst x'
    have hblock :=
      congrFun (congrFun
        (blockDiagonal_block_self (fun _ : ι => T) x) i) j
    simpa [block, Matrix.kronecker, Matrix.kroneckerMap_apply] using hblock.symm
  · have hblock :=
      congrFun (congrFun
        (blockDiagonal_block_ne (fun _ : ι => T) hxx') i) j
    simpa [block, Matrix.kronecker, Matrix.kroneckerMap_apply, hxx'] using hblock.symm

variable [Fintype a] [DecidableEq a]

omit [DecidableEq a] in
/-- A block-diagonal classical-quantum matrix is positive semidefinite when
all diagonal blocks are positive semidefinite. -/
theorem blockDiagonal_posSemidef (blocks : ι → CMatrix a)
    (hblocks : ∀ x, (blocks x).PosSemidef) :
    (blockDiagonal blocks).PosSemidef := by
  classical
  unfold blockDiagonal
  exact Matrix.posSemidef_sum Finset.univ fun x _ =>
    (posSemidef_single x).kronecker (hblocks x)

omit [DecidableEq a] in
/-- The trace of a block-diagonal classical-quantum matrix is the sum of the
traces of its diagonal blocks. -/
@[simp]
theorem blockDiagonal_trace (blocks : ι → CMatrix a) :
    (blockDiagonal blocks).trace = ∑ x, (blocks x).trace := by
  classical
  unfold blockDiagonal
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hkr :
      ((Matrix.kronecker (Matrix.single x x (1 : ℂ)) (blocks x)).trace) =
        (Matrix.single x x (1 : ℂ)).trace * (blocks x).trace :=
    Matrix.trace_kronecker _ _
  rw [hkr, trace_single_one, if_pos rfl]
  simp

omit [Fintype a] [DecidableEq a] in
/-- Block-diagonal reconstruction commutes with conjugate transpose. -/
theorem blockDiagonal_conjTranspose (blocks : ι → CMatrix a) :
    Matrix.conjTranspose (blockDiagonal blocks) =
      blockDiagonal (fun x => Matrix.conjTranspose (blocks x)) := by
  classical
  ext xi xj
  rcases xi with ⟨x, i⟩
  rcases xj with ⟨y, j⟩
  by_cases hxy : y = x
  · subst y
    calc
      Matrix.conjTranspose (blockDiagonal blocks) (x, i) (x, j) =
          star (blockDiagonal blocks (x, j) (x, i)) := rfl
      _ = star (blocks x j i) := by
            have hblock :=
              congrFun (congrFun (blockDiagonal_block_self blocks x) j) i
            simp [block] at hblock
            rw [hblock]
      _ = Matrix.conjTranspose (blocks x) i j := rfl
      _ = blockDiagonal (fun x => Matrix.conjTranspose (blocks x)) (x, i) (x, j) := by
            have hblock :=
              congrFun (congrFun
                (blockDiagonal_block_self (fun x => Matrix.conjTranspose (blocks x)) x) i) j
            simpa [block] using hblock.symm
  · have hxy' : x ≠ y := fun h => hxy h.symm
    calc
      Matrix.conjTranspose (blockDiagonal blocks) (x, i) (y, j) =
          star (blockDiagonal blocks (y, j) (x, i)) := rfl
      _ = 0 := by
            have hblock :=
              congrFun (congrFun (blockDiagonal_block_ne blocks hxy) j) i
            simp [block] at hblock
            simp [hblock]
      _ = blockDiagonal (fun x => Matrix.conjTranspose (blocks x)) (x, i) (y, j) := by
            have hblock :=
              congrFun (congrFun
                (blockDiagonal_block_ne (fun x => Matrix.conjTranspose (blocks x)) hxy') i) j
            simpa [block] using hblock.symm

omit [DecidableEq a] in
/-- Block-diagonal reconstruction commutes with blockwise multiplication. -/
theorem blockDiagonal_mul (blocks₁ blocks₂ : ι → CMatrix a) :
    blockDiagonal blocks₁ * blockDiagonal blocks₂ =
      blockDiagonal (fun x => blocks₁ x * blocks₂ x) := by
  classical
  ext xi xj
  rcases xi with ⟨x, i⟩
  rcases xj with ⟨y, j⟩
  by_cases hxy : x = y
  · subst y
    calc
      (blockDiagonal blocks₁ * blockDiagonal blocks₂) (x, i) (x, j) =
          ∑ z : ι, ∑ k : a,
            blockDiagonal blocks₁ (x, i) (z, k) *
              blockDiagonal blocks₂ (z, k) (x, j) := by
            rw [Matrix.mul_apply, Fintype.sum_prod_type]
      _ =
          ∑ k : a,
            blockDiagonal blocks₁ (x, i) (x, k) *
              blockDiagonal blocks₂ (x, k) (x, j) := by
            rw [Finset.sum_eq_single x]
            · intro z _ hz
              apply Finset.sum_eq_zero
              intro k _
              have hxz : x ≠ z := fun h => hz h.symm
              have hleft :=
                congrFun (congrFun (blockDiagonal_block_ne blocks₁ hxz) i) k
              simp [block] at hleft
              simp [hleft]
            · simp
      _ = ∑ k : a, blocks₁ x i k * blocks₂ x k j := by
            refine Finset.sum_congr rfl fun k _ => ?_
            have hleft :=
              congrFun (congrFun (blockDiagonal_block_self blocks₁ x) i) k
            have hright :=
              congrFun (congrFun (blockDiagonal_block_self blocks₂ x) k) j
            simpa [block] using congrArg₂ (fun u v => u * v) hleft hright
      _ = (blocks₁ x * blocks₂ x) i j := by
            rw [Matrix.mul_apply]
      _ = blockDiagonal (fun x => blocks₁ x * blocks₂ x) (x, i) (x, j) := by
            have hblock :=
              congrFun (congrFun
                (blockDiagonal_block_self (fun x => blocks₁ x * blocks₂ x) x) i) j
            simpa [block] using hblock.symm
  · calc
      (blockDiagonal blocks₁ * blockDiagonal blocks₂) (x, i) (y, j) =
          ∑ z : ι, ∑ k : a,
            blockDiagonal blocks₁ (x, i) (z, k) *
              blockDiagonal blocks₂ (z, k) (y, j) := by
            rw [Matrix.mul_apply, Fintype.sum_prod_type]
      _ = 0 := by
            apply Finset.sum_eq_zero
            intro z _
            by_cases hzx : z = x
            · subst z
              apply Finset.sum_eq_zero
              intro k _
              have hright :=
                congrFun (congrFun (blockDiagonal_block_ne blocks₂ hxy) k) j
              simp [block] at hright
              simp [hright]
            · apply Finset.sum_eq_zero
              intro k _
              have hxz : x ≠ z := fun h => hzx h.symm
              have hleft :=
                congrFun (congrFun (blockDiagonal_block_ne blocks₁ hxz) i) k
              simp [block] at hleft
              simp [hleft]
      _ = blockDiagonal (fun x => blocks₁ x * blocks₂ x) (x, i) (y, j) := by
            have hblock :=
              congrFun (congrFun
                (blockDiagonal_block_ne (fun x => blocks₁ x * blocks₂ x) hxy) i) j
            simpa [block] using hblock.symm

/-- The positive square root of a classical block-diagonal PSD matrix is the
block diagonal of the positive square roots. -/
theorem blockDiagonal_psdSqrt (blocks : ι → CMatrix a)
    (hblocks : ∀ x, (blocks x).PosSemidef) :
    psdSqrt (blockDiagonal blocks) =
      blockDiagonal (fun x => psdSqrt (blocks x)) := by
  classical
  let S : CMatrix (Prod ι a) := blockDiagonal (fun x => psdSqrt (blocks x))
  have hSpos : S.PosSemidef := by
    dsimp [S]
    exact blockDiagonal_posSemidef (fun x => psdSqrt (blocks x))
      (fun x => psdSqrt_pos (blocks x))
  have hSsq : S * S = blockDiagonal blocks := by
    dsimp [S]
    rw [blockDiagonal_mul]
    apply congrArg blockDiagonal
    funext x
    exact psdSqrt_mul_self_of_posSemidef (hblocks x)
  simpa [S, psdSqrt] using
    (CFC.sqrt_unique (a := blockDiagonal blocks) (b := S) hSsq hSpos.nonneg)

/-- The trace norm of a classical block-diagonal matrix is the sum of the trace
norms of its diagonal blocks. -/
theorem traceNorm_blockDiagonal (blocks : ι → CMatrix a) :
    traceNorm (blockDiagonal blocks) = ∑ x, traceNorm (blocks x) := by
  classical
  have hgram :
      Matrix.conjTranspose (blockDiagonal blocks) * blockDiagonal blocks =
        blockDiagonal (fun x => Matrix.conjTranspose (blocks x) * blocks x) := by
    rw [blockDiagonal_conjTranspose, blockDiagonal_mul]
  rw [traceNorm, hgram,
    blockDiagonal_psdSqrt (fun x => Matrix.conjTranspose (blocks x) * blocks x)
      (fun x => Matrix.posSemidef_conjTranspose_mul_self (blocks x)),
    blockDiagonal_trace]
  simp [traceNorm]

/-- The trace-norm term in fidelity decomposes over classical block-diagonal
positive semidefinite matrices. -/
theorem traceNorm_psdSqrt_blockDiagonal_mul_psdSqrt_blockDiagonal
    (blocks₁ blocks₂ : ι → CMatrix a)
    (hblocks₁ : ∀ x, (blocks₁ x).PosSemidef)
    (hblocks₂ : ∀ x, (blocks₂ x).PosSemidef) :
    traceNorm (psdSqrt (blockDiagonal blocks₁) * psdSqrt (blockDiagonal blocks₂)) =
      ∑ x, traceNorm (psdSqrt (blocks₁ x) * psdSqrt (blocks₂ x)) := by
  rw [blockDiagonal_psdSqrt blocks₁ hblocks₁,
    blockDiagonal_psdSqrt blocks₂ hblocks₂,
    blockDiagonal_mul, traceNorm_blockDiagonal]

omit [DecidableEq ι] [DecidableEq a] in
/-- The trace of a matrix on a classical-quantum product is the sum of the
traces of its diagonal classical blocks. -/
theorem sum_block_trace (X : CMatrix (Prod ι a)) :
    (∑ x, (block X x x).trace) = X.trace := by
  rw [Matrix.trace]
  rw [Fintype.sum_prod_type]
  rfl

/-- The cq-state matrix is reconstructed from the weighted diagonal quantum blocks. -/
theorem cqState_eq_blockDiagonal (E : Ensemble ι a) :
    E.cqState.matrix = blockDiagonal fun x => (E.probs x : ℂ) • (E.states x).matrix := by
  ext xi xj
  simp only [Ensemble.cqState_matrix, blockDiagonal, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Algebra.smul_def]
  rw [show (algebraMap ℝ≥0 ℂ) (E.probs x) = (E.probs x : ℂ) by rfl]
  ring

/-- The `(x, x)` block of a cq-state is the weighted quantum state for `x`. -/
@[simp]
theorem cqState_block_self (E : Ensemble ι a) (x : ι) :
    block E.cqState.matrix x x = (E.probs x : ℂ) • (E.states x).matrix := by
  rw [cqState_eq_blockDiagonal]
  exact blockDiagonal_block_self (fun y => (E.probs y : ℂ) • (E.states y).matrix) x

/-- Distinct classical labels have zero off-diagonal cq-state blocks. -/
@[simp]
theorem cqState_block_ne (E : Ensemble ι a) {x x' : ι} (h : x ≠ x') :
    block E.cqState.matrix x x' = 0 := by
  rw [cqState_eq_blockDiagonal]
  exact blockDiagonal_block_ne (fun y => (E.probs y : ℂ) • (E.states y).matrix) h

/-- A cq-state is reconstructed by placing its extracted diagonal blocks on the diagonal. -/
theorem cqState_eq_blockDiagonal_blocks (E : Ensemble ι a) :
    E.cqState.matrix = blockDiagonal fun x => block E.cqState.matrix x x := by
  rw [cqState_eq_blockDiagonal]
  apply congrArg blockDiagonal
  funext x
  symm
  exact blockDiagonal_block_self (fun y => (E.probs y : ℂ) • (E.states y).matrix) x

/-- Local classical bridge alias for the cq-state construction. -/
abbrev cqState (E : Ensemble ι a) : State (Prod ι a) := Ensemble.cqState E

/-- The cq-state matrix is the weighted Kronecker sum. -/
@[simp]
theorem cqState_matrix (E : Ensemble ι a) :
    E.cqState.matrix =
      ∑ x, (E.probs x) • Matrix.kronecker (Matrix.single x x (1 : ℂ)) (E.states x).matrix := by
  rfl

/-- Tracing out the classical register gives the ensemble's average state. -/
theorem partialTraceA_cqState (E : Ensemble ι a) :
    partialTraceA (E.cqState.matrix) = E.averageState.matrix := by
  simpa [cqState] using Ensemble.partialTraceA_cqState E

/-- Tracing out the quantum system gives the classical distribution diag(p). -/
theorem partialTraceB_cqState (E : Ensemble ι a) :
    partialTraceB (E.cqState.matrix) = Matrix.diagonal (fun x => ((E.probs x : ℂ))) := by
  simpa [cqState] using Ensemble.partialTraceB_cqState E

end Classical

end

end QIT
