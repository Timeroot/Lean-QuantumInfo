--COPIED FROM https://github.com/dupuisf/LFTCM2024TraceClass/blob/master/LFTCM2024TraceClass/Conway/HilbertBasis.lean

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Content about Hilbert bases

Could maybe be merged in `Mathlib/Analysis/InnerProductSpace/l2Space`
 -/

noncomputable section

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [CompleteSpace E]
  [InnerProductSpace 𝕜 E]

/- Standard Hilbert basis - TODO Refactor to define and use instead the cardinality of a Hilbert space -/

def stdHilbertIndex := Classical.choose (exists_hilbertBasis 𝕜 E)

lemma stdHilbertIndex_spec : ∃ (b : HilbertBasis (stdHilbertIndex 𝕜 E) 𝕜 E), b = ((↑) : (stdHilbertIndex 𝕜 E) → E) :=
  Classical.choose_spec <| exists_hilbertBasis 𝕜 E

def stdHilbertBasis : HilbertBasis (stdHilbertIndex 𝕜 E) 𝕜 E :=
  Classical.choose <| stdHilbertIndex_spec 𝕜 E

end

section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [CompleteSpace E]
  [InnerProductSpace 𝕜 E]

/-- Parseval identity -/
lemma parseval {ι : Type*} (B : HilbertBasis ι 𝕜 E) (x : E) : ∑' (i : ι), ‖⟪x, B i⟫_𝕜‖^2 = ‖x‖^2 := by
  rw [norm_sq_eq_inner (𝕜 := 𝕜)]
  rw [← HilbertBasis.tsum_inner_mul_inner B]
  rw [RCLike.re_tsum]
  conv =>
    enter [2, 1, a]
    rw [← inner_conj_symm]
    rw [← RCLike.innerProductSpace.proof_1]
    rw [← inner_conj_symm, RCLike.norm_conj]
  apply HilbertBasis.summable_inner_mul_inner B

/-- Parseval identity with non-negative real norms -/
lemma parseval_nnreal {ι : Type*} (B : HilbertBasis ι 𝕜 E) (x : E) :
  ∑' (i : ι), ‖⟪x, B i⟫_𝕜‖₊^2 = ‖x‖₊^2 := by
  -- TODO: Deduce this NNReal version of the previous one
  sorry

end
