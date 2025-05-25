import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Defs.Filter

/-- The minimax theorem, at the level of generality we need. Convex, compact sets,
 and a bilinear function on ℝ. -/
theorem minimax {M : Type*} [AddCommMonoid M] [Module ℝ M] [TopologicalSpace M]
    (f : LinearMap.BilinForm ℝ M) (S : Set M) (T : Set M)
    (hS₁ : IsCompact S) (hT₁ : IsCompact T) (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T)
    :
    ⨆ x ∈ S, ⨅ y ∈ T, f x y =  ⨅ y ∈ T, ⨆ x ∈ S, f x y := by
  sorry
