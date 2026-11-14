/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.State
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Pure vectors and rank-one states

Rank-one vector kernels provide pure-state infrastructure for the purification
route registered from [Wilde2011Qst, qit-notes.tex:10238-10290] and
[Gour2024Resources, BookQRT.tex:2051-2069].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QIT

universe u v

noncomputable section

variable {a : Type u}

/-- The rank-one matrix kernel `|ψ⟩⟨ψ|` associated to an amplitude vector. -/
def rankOneMatrix (ψ : a -> ℂ) : CMatrix a :=
  Matrix.vecMulVec ψ (fun i => star (ψ i))

@[simp]
theorem rankOneMatrix_apply (ψ : a -> ℂ) (i j : a) :
    rankOneMatrix ψ i j = ψ i * star (ψ j) := by
  simp [rankOneMatrix, Matrix.vecMulVec_apply]

/-- The rank-one kernel is Hermitian. -/
@[simp]
theorem rankOneMatrix_conjTranspose (ψ : a -> ℂ) :
    (rankOneMatrix ψ)ᴴ = rankOneMatrix ψ := by
  rw [rankOneMatrix, Matrix.conjTranspose_vecMulVec]
  ext i j
  simp [Matrix.vecMulVec_apply]

/-- The rank-one kernel is Hermitian, as a predicate. -/
theorem rankOneMatrix_isHermitian (ψ : a -> ℂ) :
    (rankOneMatrix ψ).IsHermitian :=
  rankOneMatrix_conjTranspose ψ

variable [Fintype a]

/-- The rank-one kernel is positive semidefinite. -/
theorem rankOneMatrix_pos (ψ : a -> ℂ) :
    (rankOneMatrix ψ).PosSemidef := by
  simpa [rankOneMatrix] using Matrix.posSemidef_vecMulVec_self_star ψ

/-- The trace of `|ψ⟩⟨ψ|` is the squared norm dot product. -/
@[simp]
theorem rankOneMatrix_trace (ψ : a -> ℂ) :
    (rankOneMatrix ψ).trace = ψ ⬝ᵥ (fun i => star (ψ i)) := by
  simp [rankOneMatrix]

/-- Rank-one kernels have matrix rank at most one. -/
theorem rankOneMatrix_rank_le_one (ψ : a -> ℂ) :
    (rankOneMatrix ψ).rank ≤ 1 := by
  simpa [rankOneMatrix] using Matrix.rank_vecMulVec_le ψ (fun i => star (ψ i))

variable [DecidableEq a]

/-- A pure vector is an amplitude vector whose rank-one kernel has trace one. -/
structure PureVector (a : Type u) [Fintype a] [DecidableEq a] where
  amp : a -> ℂ
  trace_rankOne_eq_one : (rankOneMatrix amp).trace = 1

namespace PureVector

variable (ψ : PureVector a)

/-- The state represented by a trace-normalized pure vector. -/
def state : State a where
  matrix := rankOneMatrix ψ.amp
  pos := rankOneMatrix_pos ψ.amp
  trace_eq_one := ψ.trace_rankOne_eq_one

@[simp]
theorem state_matrix :
    ψ.state.matrix = rankOneMatrix ψ.amp :=
  rfl

@[simp]
theorem state_matrix_apply (i j : a) :
    ψ.state.matrix i j = ψ.amp i * star (ψ.amp j) := by
  simp [state]

theorem state_matrix_rank_le_one :
    ψ.state.matrix.rank ≤ 1 := by
  simpa using rankOneMatrix_rank_le_one ψ.amp

@[simp]
theorem state_matrix_conjTranspose :
    (ψ.state.matrix)ᴴ = ψ.state.matrix := by
  simp [state]

theorem state_matrix_isHermitian :
    ψ.state.matrix.IsHermitian :=
  state_matrix_conjTranspose ψ

/-- Relabel a normalized pure vector along a finite basis equivalence. -/
def reindex {β : Type v} [Fintype β] [DecidableEq β]
    (e : a ≃ β) : PureVector β where
  amp := fun j => ψ.amp (e.symm j)
  trace_rankOne_eq_one := by
    calc
      (rankOneMatrix (fun j : β => ψ.amp (e.symm j))).trace =
          ∑ j : β, ψ.amp (e.symm j) * star (ψ.amp (e.symm j)) := by
            simp [Matrix.trace, rankOneMatrix_apply]
      _ = ∑ i : a, ψ.amp i * star (ψ.amp i) := by
            refine Fintype.sum_equiv e.symm
              (fun j : β => ψ.amp (e.symm j) * star (ψ.amp (e.symm j)))
              (fun i : a => ψ.amp i * star (ψ.amp i)) ?_
            intro j
            simp
      _ = (rankOneMatrix ψ.amp).trace := by
            simp [Matrix.trace, rankOneMatrix_apply]
      _ = 1 := ψ.trace_rankOne_eq_one

@[simp]
theorem reindex_amp {β : Type v} [Fintype β] [DecidableEq β]
    (e : a ≃ β) (j : β) :
    (ψ.reindex e).amp j = ψ.amp (e.symm j) :=
  rfl

/-- Relabeling a pure vector and then forming its state agrees with relabeling
the associated rank-one state. -/
theorem reindex_state {β : Type v} [Fintype β] [DecidableEq β]
    (e : a ≃ β) :
    (ψ.reindex e).state = ψ.state.reindex e := by
  apply State.ext
  ext i j
  simp [State.reindex, PureVector.state, rankOneMatrix_apply]

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- Product of normalized pure vectors. -/
def prod (ψ : PureVector a) (φ : PureVector b) : PureVector (Prod a b) where
  amp x := ψ.amp x.1 * φ.amp x.2
  trace_rankOne_eq_one := by
    rw [rankOneMatrix_trace]
    calc
      (fun x : Prod a b => ψ.amp x.1 * φ.amp x.2) ⬝ᵥ
          (fun x : Prod a b => star (ψ.amp x.1 * φ.amp x.2)) =
          (∑ i : a, ψ.amp i * star (ψ.amp i)) *
            (∑ j : b, φ.amp j * star (φ.amp j)) := by
            rw [dotProduct, Fintype.sum_prod_type]
            simp only [star_mul]
            calc
              (∑ x : a, ∑ y : b,
                  ψ.amp x * φ.amp y * (star (φ.amp y) * star (ψ.amp x))) =
                  ∑ x : a, (ψ.amp x * star (ψ.amp x)) *
                    (∑ y : b, φ.amp y * star (φ.amp y)) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    calc
                      (∑ y : b, ψ.amp x * φ.amp y *
                          (star (φ.amp y) * star (ψ.amp x))) =
                          ∑ y : b, (ψ.amp x * star (ψ.amp x)) *
                            (φ.amp y * star (φ.amp y)) := by
                            apply Finset.sum_congr rfl
                            intro y hy
                            ring
                      _ = (ψ.amp x * star (ψ.amp x)) *
                            (∑ y : b, φ.amp y * star (φ.amp y)) := by
                            rw [Finset.mul_sum]
              _ = (∑ i : a, ψ.amp i * star (ψ.amp i)) *
                    (∑ j : b, φ.amp j * star (φ.amp j)) := by
                    rw [Finset.sum_mul]
      _ = (rankOneMatrix ψ.amp).trace * (rankOneMatrix φ.amp).trace := by
            simp [rankOneMatrix_trace, dotProduct]
      _ = 1 := by rw [ψ.trace_rankOne_eq_one, φ.trace_rankOne_eq_one, mul_one]

@[simp]
theorem prod_amp (ψ : PureVector a) (φ : PureVector b) (x : Prod a b) :
    (ψ.prod φ).amp x = ψ.amp x.1 * φ.amp x.2 := rfl

/-- Product pure vectors induce product density states. -/
theorem prod_state (ψ : PureVector a) (φ : PureVector b) :
    (ψ.prod φ).state = ψ.state.prod φ.state := by
  apply State.ext
  ext i j
  simp [PureVector.state, State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply,
    rankOneMatrix_apply, mul_assoc, mul_left_comm, mul_comm]

/-- IID tensor power of a normalized pure vector. -/
def tensorPower (ψ : PureVector a) : (n : ℕ) → PureVector (TensorPower a n)
  | 0 =>
      { amp := fun _ => 1
        trace_rankOne_eq_one := by
          rw [rankOneMatrix_trace]
          change (∑ _ : PUnit, (1 : ℂ) * star (1 : ℂ)) = 1
          simp }
  | n + 1 => ψ.prod (tensorPower ψ n)

@[simp]
theorem tensorPower_zero (ψ : PureVector a) :
    ψ.tensorPower 0 =
      ({ amp := fun _ : PUnit => 1
         trace_rankOne_eq_one := by
          rw [rankOneMatrix_trace]
          change (∑ _ : PUnit, (1 : ℂ) * star (1 : ℂ)) = 1
          simp } : PureVector (TensorPower a 0)) := rfl

@[simp]
theorem tensorPower_succ (ψ : PureVector a) (n : ℕ) :
    ψ.tensorPower (n + 1) = ψ.prod (ψ.tensorPower n) := rfl

theorem tensorPower_state (ψ : PureVector a) :
    (n : ℕ) → (ψ.tensorPower n).state = ψ.state.tensorPower n
  | 0 => by
      apply State.ext
      ext i j
      cases i
      cases j
      simp [PureVector.tensorPower, PureVector.state, State.tensorPower, State.unit,
        rankOneMatrix_apply]
  | n + 1 => by
      rw [PureVector.tensorPower_succ, State.tensorPower_succ]
      calc
        (ψ.prod (ψ.tensorPower n)).state =
            ψ.state.prod (ψ.tensorPower n).state := PureVector.prod_state ψ (ψ.tensorPower n)
        _ = ψ.state.prod (ψ.state.tensorPower n) := by rw [tensorPower_state ψ n]

/-- The density matrix of a normalized pure vector is idempotent. -/
@[simp]
theorem state_matrix_mul_self :
    ψ.state.matrix * ψ.state.matrix = ψ.state.matrix := by
  have hdot : (fun i => star (ψ.amp i)) ⬝ᵥ ψ.amp = 1 := by
    have htrace := ψ.trace_rankOne_eq_one
    rw [rankOneMatrix_trace] at htrace
    rw [dotProduct_comm]
    exact htrace
  change rankOneMatrix ψ.amp * rankOneMatrix ψ.amp = rankOneMatrix ψ.amp
  rw [rankOneMatrix, Matrix.vecMulVec_mul_vecMulVec, hdot]
  simp

end PureVector

/-- Normalize a nonzero amplitude vector to a pure vector using the trace of
its rank-one kernel. -/
def PureVector.normalize (v : a → ℂ) (hpos : 0 < (rankOneMatrix v).trace.re) :
    PureVector a where
  amp := fun x => (((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * v x
  trace_rankOne_eq_one := by
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

/-- The density matrix of a normalized amplitude vector is the trace-normalized
rank-one kernel. -/
theorem PureVector.normalize_state_matrix
    (v : a → ℂ) (hpos : 0 < (rankOneMatrix v).trace.re) :
    (PureVector.normalize v hpos).state.matrix =
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

omit [DecidableEq a] in
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

end

end QIT
