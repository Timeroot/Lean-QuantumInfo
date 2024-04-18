--COPIED FROM https://github.com/dupuisf/LFTCM2024TraceClass/blob/master/LFTCM2024TraceClass/Conway/Main.lean

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Module
import QuantumInfo.InfiniteDim.CFC
import QuantumInfo.InfiniteDim.HilbertBasis

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [InnerProductSpace ℂ E]

noncomputable section

/-!
# Conway, A course in operator theory, Chapter 18
-/

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

namespace TraceClass

/- Definitions of diagonal and cross sums -/

def sum_diag_norm {ι₁ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (f : E →L[ℂ] E) :=
  ∑' (i₁ : ι₁), (‖f (B₁ i₁)‖₊^2 : ENNReal)

def sum_cross {ι₁ ι₂ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (B₂ : HilbertBasis ι₂ ℂ E) (f : E →L[ℂ] E) :=
  ∑' (i₁ : ι₁) (i₂ : ι₂), (‖⟪f (B₁ i₁), B₂ i₂⟫‖₊^2 : ENNReal)

lemma sum_diag_norm_abs {ι₁ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (f : E →L[ℂ] E) :
  sum_diag_norm B₁ (abs f) = sum_diag_norm B₁ f := by
  rw [sum_diag_norm, sum_diag_norm]
  conv =>
    enter [1, 1, i₁, 1, 1]
    rw [abs_vec_norm']

/-- Proposition 18.1 -
For a bounded operator `f` on a Hilbert space `E`, given Hilbert bases `B₁` and `B₂` of `E`,
one has `∑ ‖f e₁‖² = ∑ ∑ |⟪f e₁, e₂⟫|²`. -/
lemma sum_diag_eq_sum_cross
  {ι₁ ι₂ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (B₂ : HilbertBasis ι₂ ℂ E) (f : E →L[ℂ] E) :
  sum_diag_norm B₁ f = sum_cross B₁ B₂ f := by
  have p : ∀ x : E, ∑' (i₂ : ι₂), (‖⟪x, B₂ i₂⟫_ℂ‖₊^2 : ENNReal) = (‖x‖₊^2 : ENNReal) := by
    -- TODO: It should follow from the NNReal version of Parseval's identity
    sorry
  rw [sum_diag_norm, sum_cross]
  conv =>
    enter [1, 1, i₁]
    rw [← p]

/-- The NNNorm of the conjugate is the NNNorm. -/
lemma nnnorm_conj (z : ℂ) : ‖(starRingEnd ℂ) z‖₊ = ‖z‖₊ := by
  apply NNReal.coe_injective
  exact (Complex.abs_conj z)

/-- Corollary 18.2 (generalized version) -
The diagonal sum of norms of a self-adjoint operator is independent of the Hilbert basis -/
lemma sum_diag_norm_independent
  {ι₁ ι₂ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (B₂ : HilbertBasis ι₂ ℂ E) (f : E →L[ℂ] E)
  (h : ContinuousLinearMap.adjoint f = f) :
  sum_diag_norm B₁ f = sum_diag_norm B₂ f := by
  rw [sum_diag_eq_sum_cross B₁ B₂]
  rw [sum_diag_eq_sum_cross B₂ B₁]
  rw [sum_cross, sum_cross]
  rw [ENNReal.tsum_comm]
  conv =>
    enter [1, 1, b, 1, a, 1, 1]
    rw [← ContinuousLinearMap.adjoint_inner_right, h]
    rw [← InnerProductSpace.conj_symm]
    rw [nnnorm_conj]

end TraceClass

/- Trace class -/

open ENNReal

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [InnerProductSpace ℂ E]

class IsTraceClass (f : E →L[ℂ] E) : Prop where
  finite_diag_norm : ∀ {ι : Type u_2} (B : HilbertBasis ι ℂ E), TraceClass.sum_diag_norm B (TraceClass.sqrt_abs f) ≠ ∞

namespace TraceClass

lemma mk_of_exists {ι : Type*} (B : HilbertBasis ι ℂ E)
  (h : TraceClass.sum_diag_norm B (sqrt_abs f) ≠ ∞) : IsTraceClass f where
    finite_diag_norm := by
      intro ι' B'
      rw [sum_diag_norm_independent B' B (sqrt_abs f) (adjoint_sqrt_abs f)]
      exact h

def trace_norm (f : E →L[ℂ] E) := sum_diag_norm (stdHilbertBasis ℂ E) (sqrt_abs f)

lemma sum_diag_eq_trace_norm {ι : Type*} (B : HilbertBasis ι ℂ E) :
  sum_diag_norm B (sqrt_abs f) = trace_norm f := by
  exact sum_diag_norm_independent B (stdHilbertBasis ℂ E) (sqrt_abs f) (adjoint_sqrt_abs f)

/- Hilbert-Schmidt -/

class IsHilbertSchmidt (f : E →L[ℂ] E) : Prop where
  sq_is_trace_class : IsTraceClass (sq (abs f))

def ENNReal.sqrt (x : ENNReal) : ENNReal := match x with
  | ENNReal.ofNNReal y => ENNReal.ofReal (Real.sqrt y)
  | ⊤ => ⊤

/-- The Hilbert-Schmidt norm of the operator. -/
def hs_norm (f : E →L[ℂ] E) := ENNReal.sqrt (trace_norm (sq (abs f)))

/-- Proposition 18.6.a -
The Hilbert-Schmidt norm is the square root of the ∑ ‖f e‖² in any Hilbert basis. -/
lemma hs_norm_eq_sum_basis {ι : Type*} (B : HilbertBasis ι ℂ E) (f : E →L[ℂ] E) :
  hs_norm f = ENNReal.sqrt (sum_diag_norm B f) := by
  rw [hs_norm, trace_norm, sqrt_sq_eq_abs, ← sum_diag_norm_abs B f]
  rw [sum_diag_norm_independent]
  exact adjoint_abs f

/-- Proposition 18.6.b -
The Hilber-Schmidt norm of the adjoint is the same. -/
lemma hs_norm_adjoint (f : E →L[ℂ] E) :
  hs_norm (ContinuousLinearMap.adjoint f) = hs_norm f := by
  rw [hs_norm, abs_adjoint, ← hs_norm]

-- TODO We first need the preliminaries before we move on to here

def sum_diag_inner {ι₁ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (f : E →L[ℂ] E) :=
  ∑' (i₁ : ι₁), ⟪f (B₁ i₁), B₁ i₁⟫

def trace (f : E →L[ℂ] E) : ℂ := sum_diag_inner (stdHilbertBasis ℂ E) f

theorem sum_diag_inner_eq_trace {ι₁ : Type*} (B₁ : HilbertBasis ι₁ ℂ E) (f : E →L[ℂ] E) [IsTraceClass f] :
  HasSum (fun i₁ => ⟪f (B₁ i₁), B₁ i₁⟫) (trace f) := by
  -- The proof is not so easy and seems to require Hilbert-Schmidt and approximation
  sorry

end TraceClass

end
