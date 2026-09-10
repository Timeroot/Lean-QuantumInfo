/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.State
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank-one kernels of kets

Rank-one vector kernels provide pure-state infrastructure for the purification
route registered from [Wilde2011Qst, qit-notes.tex:10238-10290] and
[Gour2024Resources, BookQRT.tex:2051-2069].

A `Ket a` is normalized by `∑ x, ‖ψ x‖ ^ 2 = 1`; the same condition says that the rank-one
kernel `|ψ⟩⟨ψ|` has unit trace, which is the form the purification development uses. The two
directions are `QIT.trace_rankOneMatrix_eq_one_iff`, `Ket.ofRankOne` and
`Ket.trace_rankOne_eq_one`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QIT

universe u v

noncomputable section

variable {a : Type u}

/-- The rank-one matrix kernel `|ψ⟩⟨ψ|` associated to an amplitude vector. -/
def rankOneMatrix (ψ : a → ℂ) : CMatrix a :=
  Matrix.vecMulVec ψ (fun i => star (ψ i))

@[simp]
theorem rankOneMatrix_apply (ψ : a → ℂ) (i j : a) :
    rankOneMatrix ψ i j = ψ i * star (ψ j) := by
  simp [rankOneMatrix, Matrix.vecMulVec_apply]

/-- The rank-one kernel is Hermitian. -/
@[simp]
theorem rankOneMatrix_conjTranspose (ψ : a → ℂ) :
    (rankOneMatrix ψ)ᴴ = rankOneMatrix ψ := by
  rw [rankOneMatrix, Matrix.conjTranspose_vecMulVec]
  ext i j
  simp [Matrix.vecMulVec_apply]

/-- The rank-one kernel is Hermitian, as a predicate. -/
theorem rankOneMatrix_isHermitian (ψ : a → ℂ) :
    (rankOneMatrix ψ).IsHermitian :=
  rankOneMatrix_conjTranspose ψ

variable [Fintype a]

/-- The rank-one kernel is positive semidefinite. -/
theorem rankOneMatrix_pos (ψ : a → ℂ) :
    (rankOneMatrix ψ).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star ψ

/-- The trace of `|ψ⟩⟨ψ|` is the squared norm dot product. -/
@[simp]
theorem rankOneMatrix_trace (ψ : a → ℂ) :
    (rankOneMatrix ψ).trace = ψ ⬝ᵥ (fun i => star (ψ i)) := by
  simp [rankOneMatrix]

/-- Rank-one kernels have matrix rank at most one. -/
theorem rankOneMatrix_rank_le_one (ψ : a → ℂ) :
    (rankOneMatrix ψ).rank ≤ 1 := by
  simpa [rankOneMatrix] using Matrix.rank_vecMulVec_le ψ (fun i => star (ψ i))

/-- Unit trace of the rank-one kernel, in `ℂ`, is normalization of the amplitudes, in `ℝ`. -/
theorem trace_rankOneMatrix_eq_one_iff (ψ : a → ℂ) :
    (rankOneMatrix ψ).trace = 1 ↔ ∑ x, ‖ψ x‖ ^ 2 = 1 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, rankOneMatrix_apply, ← starRingEnd_apply, Complex.mul_conj']
  exact_mod_cast Iff.rfl

/-- Acting by `|ψ⟩⟨ψ|` rescales `ψ` by the overlap `⟨ψ|φ⟩`. -/
theorem rankOneMatrix_mulVec_eq_dotProduct_smul (ψ φ : a → ℂ) :
    (rankOneMatrix ψ).mulVec φ = dotProduct (star ψ) φ • ψ := by
  ext i
  simp [Matrix.mulVec, rankOneMatrix_apply, dotProduct, Finset.mul_sum,
    mul_comm, mul_left_comm]

/-- Vanishing of a rank-one action forces the corresponding amplitude
pairing to vanish. -/
theorem dotProduct_star_eq_zero_of_rankOne_mulVec_eq_zero (ψ φ : a → ℂ)
    (h : (rankOneMatrix ψ).mulVec φ = 0) :
    dotProduct (star ψ) φ = 0 := by
  rw [rankOneMatrix_mulVec_eq_dotProduct_smul] at h
  by_cases hψ : ψ = 0
  · simp [hψ, dotProduct]
  · obtain ⟨i, hi⟩ : ∃ i, ψ i ≠ 0 := Function.ne_iff.mp hψ
    have hi0 := congrFun h i
    simpa [hi] using (mul_eq_zero.mp hi0).resolve_right hi

/-- Moving a Hermitian square-root weight from a rank-one vector back to the
left-hand weight before tracing out the weighted system. -/
theorem traceLeft_rankOne_kron_left_mulVec_eq_weight_mul {b : Type v} [DecidableEq a]
    [Fintype b] [DecidableEq b] (S : CMatrix a) (hS : S.IsHermitian) (ψ : a × b → ℂ) :
    Matrix.traceLeft (rankOneMatrix (Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b)) ψ)) =
      Matrix.traceLeft (Matrix.kronecker (S * S) (1 : CMatrix b) * rankOneMatrix ψ) := by
  ext j j'
  have hstar : ∀ x y : a, (starRingEnd ℂ) (S x y) = S y x := by
    intro x y
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hS.eq y) x
  simp [Matrix.traceLeft, rankOneMatrix_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simp_rw [hstar]
  conv_lhs =>
    rw [Finset.sum_comm]
    enter [2, z]
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  ring_nf

/-- Rank-one kernels transform by conjugation under a matrix-vector product. -/
theorem rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose
    {β : Type v} [Fintype β] [DecidableEq β]
    (M : Matrix β a ℂ) (v : a → ℂ) :
    rankOneMatrix (M.mulVec v) = M * rankOneMatrix v * Matrix.conjTranspose M := by
  rw [rankOneMatrix, rankOneMatrix]
  rw [Matrix.mul_vecMulVec]
  rw [Matrix.vecMulVec_mul]
  congr
  ext i
  simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose, mul_comm]

/-- Coordinate form of a left tensor factor acting on a bipartite vector. -/
theorem kronecker_left_one_mulVec_apply {c : Type v} [Fintype c] [DecidableEq c]
    (W : CMatrix a) (ψ : a × c → ℂ) (i : a) (k : c) :
    (Matrix.kronecker W (1 : CMatrix c)).mulVec ψ (i, k) =
      W.mulVec (fun j => ψ (j, k)) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Matrix.one_apply]

/-- Coordinate form of a right tensor factor acting on a bipartite vector. -/
theorem kronecker_right_one_mulVec_apply [DecidableEq a] {c : Type v} [Fintype c]
    (W : CMatrix c) (ψ : a × c → ℂ) (i : a) (k : c) :
    (Matrix.kronecker (1 : CMatrix a) W).mulVec ψ (i, k) =
      W.mulVec (fun l => ψ (i, l)) k := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Matrix.one_apply]

/-- Applying `W ⊗ I` to a bipartite rank-one kernel and tracing out the second system
sandwiches the original first-system marginal by `W`. -/
theorem traceRight_rankOne_kron_left_mulVec_eq {c : Type v} [Fintype c] [DecidableEq c]
    (W : CMatrix a) (ψ : a × c → ℂ) :
    Matrix.traceRight (rankOneMatrix ((Matrix.kronecker W (1 : CMatrix c)).mulVec ψ)) =
      W * Matrix.traceRight (rankOneMatrix ψ) * Matrix.conjTranspose W := by
  ext x y
  have hmulVec :
      (Matrix.kronecker W (1 : CMatrix c)).mulVec ψ =
        fun p : a × c => W.mulVec (fun i => ψ (i, p.2)) p.1 := by
    ext p
    exact kronecker_left_one_mulVec_apply W ψ p.1 p.2
  rw [hmulVec]
  let F : c → a → a → ℂ := fun k i j =>
    W x i * (ψ (i, k) * (star (W y j) * star (ψ (j, k))))
  calc
    Matrix.traceRight
        (rankOneMatrix (fun p : a × c => W.mulVec (fun i => ψ (i, p.2)) p.1)) x y =
        ∑ k : c, ∑ j : a, ∑ i : a, F k i j := by
          simp [F, Matrix.traceRight, rankOneMatrix_apply, Matrix.mulVec, dotProduct,
            Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = ∑ j : a, ∑ k : c, ∑ i : a, F k i j := by
          rw [Finset.sum_comm]
    _ = ∑ j : a, ∑ i : a, ∑ k : c, F k i j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ j : a, star (W y j) *
          ∑ i : a, W x i * ∑ k : c, ψ (i, k) * star (ψ (j, k)) := by
          simp [F, Finset.mul_sum, mul_left_comm]
    _ = (W * Matrix.traceRight (rankOneMatrix ψ) * Matrix.conjTranspose W) x y := by
          simp [Matrix.traceRight, rankOneMatrix_apply, Matrix.mul_apply,
            Matrix.conjTranspose_apply, mul_comm]

end
end QIT

namespace Ket

noncomputable section

open QIT
universe u v
variable {a : Type u}
variable [Fintype a]

/-- The ket with the given amplitudes, normalized by unit trace of the rank-one kernel. -/
@[reducible]
def ofRankOne (v : a → ℂ) (h : (rankOneMatrix v).trace = 1) : Ket a where
  vec := v
  normalized' := (trace_rankOneMatrix_eq_one_iff v).mp h

@[simp]
theorem ofRankOne_vec (v : a → ℂ) (h : (rankOneMatrix v).trace = 1) :
    (ofRankOne v h).vec = v :=
  rfl

@[simp]
theorem ofRankOne_apply (v : a → ℂ) (h : (rankOneMatrix v).trace = 1) (i : a) :
    ofRankOne v h i = v i :=
  rfl

/-- The rank-one kernel of a ket has unit trace. -/
theorem trace_rankOne_eq_one (ψ : Ket a) : (rankOneMatrix ψ.vec).trace = 1 :=
  (trace_rankOneMatrix_eq_one_iff _).mpr ψ.normalized'

/-- Normalize a nonzero amplitude vector to a ket using the trace of its rank-one kernel. -/
def normalizeRankOne (v : a → ℂ) (hpos : 0 < (rankOneMatrix v).trace.re) : Ket a :=
  ofRankOne (fun x => (((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * v x) <| by
    classical
    let t : ℝ := (rankOneMatrix v).trace.re
    have htpos : 0 < t := hpos
    have ht_nonneg : 0 ≤ t := le_of_lt htpos
    have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htpos)
    have htrace_im : (rankOneMatrix v).trace.im = 0 :=
      (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos v)).2.symm
    have htrace_complex : (rankOneMatrix v).trace = (t : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using htrace_im
    have hcoeff :
        (((((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
              ((((Real.sqrt t)⁻¹ : ℝ) : ℂ))) * (t : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt ht_nonneg]
    calc
      (rankOneMatrix
          (fun x => ((((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * v x))).trace =
          (((((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
              ((((Real.sqrt t)⁻¹ : ℝ) : ℂ))) * (rankOneMatrix v).trace) := by
            simp [rankOneMatrix_trace, dotProduct, t, Finset.mul_sum, mul_assoc,
              mul_left_comm, mul_comm]
      _ = (((((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
              ((((Real.sqrt t)⁻¹ : ℝ) : ℂ))) * (t : ℂ)) := by
            rw [htrace_complex]
      _ = 1 := hcoeff

@[simp]
theorem normalizeRankOne_vec (v : a → ℂ) (hpos : 0 < (rankOneMatrix v).trace.re) :
    (normalizeRankOne v hpos).vec =
      fun x => (((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * v x :=
  rfl

variable [DecidableEq a]

variable (ψ : Ket a)

/-- The state represented by a ket. -/
def state : MState a := .ofMatrix
  (matrix := rankOneMatrix ψ.vec)
  (pos := rankOneMatrix_pos ψ.vec)
  (trace_eq_one := ψ.trace_rankOne_eq_one)

@[simp]
theorem state_matrix :
    ψ.state.m = rankOneMatrix ψ.vec :=
  MState.matrix_ofMatrix _ _ _

@[simp]
theorem state_matrix_apply (i j : a) :
    ψ.state.m i j = ψ.vec i * star (ψ.vec j) := by
  simp [state]

theorem state_matrix_rank_le_one :
    ψ.state.m.rank ≤ 1 := by
  simpa using rankOneMatrix_rank_le_one ψ.vec

theorem state_matrix_conjTranspose :
    (ψ.state.m)ᴴ = ψ.state.m := by
  simp [state]

theorem state_matrix_isHermitian :
    ψ.state.m.IsHermitian :=
  state_matrix_conjTranspose ψ

/-- Relabel a ket along a finite basis equivalence. -/
def reindex {β : Type v} [Fintype β] [DecidableEq β]
    (e : a ≃ β) : Ket β :=
  ofRankOne (fun j => ψ.vec (e.symm j)) <| by
    calc
      (rankOneMatrix (fun j : β => ψ.vec (e.symm j))).trace =
          ∑ j : β, ψ.vec (e.symm j) * star (ψ.vec (e.symm j)) := by
            simp [Matrix.trace, rankOneMatrix_apply]
      _ = ∑ i : a, ψ.vec i * star (ψ.vec i) := by
            refine Fintype.sum_equiv e.symm
              (fun j : β => ψ.vec (e.symm j) * star (ψ.vec (e.symm j)))
              (fun i : a => ψ.vec i * star (ψ.vec i)) ?_
            intro j
            simp
      _ = (rankOneMatrix ψ.vec).trace := by
            simp [Matrix.trace, rankOneMatrix_apply]
      _ = 1 := ψ.trace_rankOne_eq_one

omit [DecidableEq a] in
@[simp]
theorem reindex_vec {β : Type v} [Fintype β] [DecidableEq β]
    (e : a ≃ β) (j : β) :
    (ψ.reindex e).vec j = ψ.vec (e.symm j) :=
  rfl

/-- Relabeling a ket and then forming its state agrees with relabeling
the associated rank-one state. -/
theorem reindex_state {β : Type v} [Fintype β] [DecidableEq β]
    (e : a ≃ β) :
    (ψ.reindex e).state = ψ.state.reindex e := by
  apply MState.ext
  ext i j
  simp [Ket.state, rankOneMatrix_apply]

variable {b : Type v} [Fintype b] [DecidableEq b]

omit [DecidableEq a] [DecidableEq b] in
@[simp]
theorem prod_vec (ψ : Ket a) (φ : Ket b) (x : a × b) :
    (ψ.prod φ).vec x = ψ.vec x.1 * φ.vec x.2 := rfl

/-- Product kets induce product density states. -/
theorem prod_state (ψ : Ket a) (φ : Ket b) :
    (ψ.prod φ).state = ψ.state.prod φ.state := by
  apply MState.ext
  ext i j
  simp [Ket.state, Matrix.kroneckerMap_apply,
    rankOneMatrix_apply, mul_assoc, mul_left_comm, mul_comm]

/-- IID tensor power of a ket. -/
def tensorPower (ψ : Ket a) : (n : ℕ) → Ket (QIT.TensorPower a n)
  | 0 =>
      ofRankOne (fun _ => 1) <| by
        rw [rankOneMatrix_trace]
        change (∑ _ : PUnit, (1 : ℂ) * star (1 : ℂ)) = 1
        simp
  | n + 1 => ψ.prod (tensorPower ψ n)

omit [DecidableEq a] in
@[simp]
theorem tensorPower_zero (ψ : Ket a) :
    ψ.tensorPower 0 =
      ofRankOne (fun _ : QIT.TensorPower a 0 => 1) (by
        rw [rankOneMatrix_trace]
        change (∑ _ : PUnit, (1 : ℂ) * star (1 : ℂ)) = 1
        simp) := rfl

omit [DecidableEq a] in
@[simp]
theorem tensorPower_succ (ψ : Ket a) (n : ℕ) :
    ψ.tensorPower (n + 1) = ψ.prod (ψ.tensorPower n) := rfl

theorem tensorPower_state (ψ : Ket a) :
    (n : ℕ) → (ψ.tensorPower n).state = ψ.state.tensorPower n
  | 0 =>
      have : Subsingleton (QIT.TensorPower a 0) := inferInstanceAs (Subsingleton PUnit)
      MState.eq_of_subsingleton _ _
  | n + 1 => by
      rw [Ket.tensorPower_succ, MState.tensorPower_succ]
      calc
        (ψ.prod (ψ.tensorPower n)).state =
            ψ.state.prod (ψ.tensorPower n).state := Ket.prod_state ψ (ψ.tensorPower n)
        _ = ψ.state.prod (ψ.state.tensorPower n) := by rw [tensorPower_state ψ n]

/-- The rank-one state of a ket is its pure state. -/
theorem state_eq_pure : ψ.state = MState.pure ψ :=
  DensityOp.ext_m <| by
    ext i j
    simp [Ket.apply]

/-- The density matrix of a ket is idempotent. -/
theorem state_matrix_mul_self :
    ψ.state.m * ψ.state.m = ψ.state.m := by
  have hdot : (fun i => star (ψ.vec i)) ⬝ᵥ ψ.vec = 1 := by
    have htrace := ψ.trace_rankOne_eq_one
    rw [rankOneMatrix_trace] at htrace
    rw [dotProduct_comm]
    exact htrace
  rw [state_matrix, rankOneMatrix, Matrix.vecMulVec_mul_vecMulVec, hdot]
  simp

/-- The density matrix of a normalized amplitude vector is the trace-normalized
rank-one kernel. -/
theorem normalizeRankOne_state_matrix
    (v : a → ℂ) (hpos : 0 < (rankOneMatrix v).trace.re) :
    (normalizeRankOne v hpos).state.m =
      ((((rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) • rankOneMatrix v := by
  classical
  let t : ℝ := (rankOneMatrix v).trace.re
  have htpos : 0 < t := hpos
  have ht_nonneg : 0 ≤ t := le_of_lt htpos
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htpos)
  let c : ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ)
  have hcoeff :
      c * c = (((t⁻¹ : ℝ) : ℂ)) := by
    dsimp [c]
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt ht_nonneg]
  rw [Ket.state_matrix]
  ext i j
  change (c * v i) * star (c * v j) =
    ((((rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * (v i * star (v j))
  calc
    (c * v i) * star (c * v j) = (c * c) * (v i * star (v j)) := by
      dsimp [c]
      simp [mul_assoc, mul_left_comm, mul_comm]
    _ = (((t⁻¹ : ℝ) : ℂ)) * (v i * star (v j)) := by rw [hcoeff]
    _ = ((((rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * (v i * star (v j)) := by
      rfl

section Tripartite

universe w

variable {c : Type w} [Fintype c] [DecidableEq c]

/-- Reading `(A ⊗ B) ⊗ C` as `(A ⊗ C) ⊗ B` turns the `AB` marginal of a pure
state into its `AC` marginal. -/
theorem prodABCToACB_marginalAB (psi : Ket ((a × b) × c)) :
    (psi.reindex (prodABCToACBEquiv a b c)).state.marginalAB =
      psi.state.marginalAC := by
  rw [Ket.reindex_state, MState.prodABCToACB_marginalAB]

/-- Reading `(A ⊗ B) ⊗ C` as `(A ⊗ C) ⊗ B` turns the `AC` marginal of a pure
state into its `AB` marginal. -/
theorem prodABCToACB_marginalAC (psi : Ket ((a × b) × c)) :
    (psi.reindex (prodABCToACBEquiv a b c)).state.marginalAC =
      psi.state.marginalAB := by
  rw [Ket.reindex_state, MState.prodABCToACB_marginalAC]

/-- Reading `(A ⊗ B) ⊗ C` as `(A ⊗ C) ⊗ B` turns the middle-system marginal of
a pure state into the `C` marginal of its `AC` marginal. -/
theorem prodABCToACB_marginalBOfABC (psi : Ket ((a × b) × c)) :
    (psi.reindex (prodABCToACBEquiv a b c)).state.marginalBOfABC =
      psi.state.marginalAC.traceLeft := by
  rw [Ket.reindex_state, MState.prodABCToACB_marginalBOfABC,
    MState.marginalAC_traceLeft_eq_traceLeft]

/-- Reading `(A ⊗ B) ⊗ C` as `(A ⊗ C) ⊗ B` turns the state of a pure state on
the last system into its middle-system marginal. -/
theorem prodABCToACB_traceLeft (psi : Ket ((a × b) × c)) :
    (psi.reindex (prodABCToACBEquiv a b c)).state.traceLeft =
      psi.state.marginalBOfABC := by
  rw [Ket.reindex_state, MState.prodABCToACB_traceLeft]

end Tripartite

end

end Ket
