import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-- The minimax theorem, at the level of generality we need. For convex, compact, nonempty sets `S`
and `T`in a real topological vector space `M`, and a bilinear function `f` on M, we can exchange
the order of minimizing and maximizing. -/
theorem minimax {M : Type*} [AddCommMonoid M] [Module ℝ M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul ℝ M]
  (f : LinearMap.BilinForm ℝ M) (S : Set M) (T : Set M) (hS₁ : IsCompact S) (hT₁ : IsCompact T)
  (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)
    : ⨆ x : S, ⨅ y : T, f x y =  ⨅ y : T, ⨆ x : S, f x y := by
  sorry
