/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Entanglement.Separable

/-!
# Positive partial transpose bipartite states

The PPT predicate uses the `B`/Bob subsystem convention from the local
partial-transpose API: a bipartite state is PPT when its partial transpose on
the second product factor is positive semidefinite. Separable states have this
property by product-state positivity and closure under finite convex mixing,
matching the PPT criterion route in
[Horodecki2007Entanglement, ent-review-last.tex:2234-2290].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v}

private theorem partialTransposeB_smul_nnreal (c : ℝ≥0) (X : CMatrix (Prod a b)) :
    partialTransposeB (a := a) (b := b) (c • X) =
      c • partialTransposeB (a := a) (b := b) X := by
  ext x y
  rfl

private theorem partialTransposeB_sum {ι : Type w} [Fintype ι]
    (f : ι → CMatrix (Prod a b)) :
    partialTransposeB (a := a) (b := b) (∑ i, f i) =
      ∑ i, partialTransposeB (a := a) (b := b) (f i) := by
  ext x y
  change (∑ i, f i) (x.1, y.2) (y.1, x.2) =
    (∑ i, partialTransposeB (a := a) (b := b) (f i)) x y
  rw [show (∑ i, f i) (x.1, y.2) = ∑ i, f i (x.1, y.2) from by
    exact Finset.sum_apply (x.1, y.2) Finset.univ f]
  rw [show (∑ i, f i (x.1, y.2)) (y.1, x.2) =
      ∑ i, f i (x.1, y.2) (y.1, x.2) from by
    exact Finset.sum_apply (y.1, x.2) Finset.univ
      (fun i => f i (x.1, y.2))]
  rw [show (∑ i, partialTransposeB (a := a) (b := b) (f i)) x =
      ∑ i, partialTransposeB (a := a) (b := b) (f i) x from by
    exact Finset.sum_apply x Finset.univ
      (fun i => partialTransposeB (a := a) (b := b) (f i))]
  rw [show (∑ i, partialTransposeB (a := a) (b := b) (f i) x) y =
      ∑ i, partialTransposeB (a := a) (b := b) (f i) x y from by
    exact Finset.sum_apply y Finset.univ
      (fun i => partialTransposeB (a := a) (b := b) (f i) x)]
  rfl

variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A bipartite state is PPT when the partial transpose on the second subsystem
is positive semidefinite. -/
def IsPPT (rho : State (Prod a b)) : Prop :=
  Matrix.PosSemidef (partialTransposeB rho.matrix)

/-- Product states are PPT. -/
theorem isPPT_prod (rho : State a) (sigma : State b) :
    IsPPT (rho.prod sigma) := by
  rw [IsPPT, State.prod, partialTransposeB_kronecker]
  exact rho.pos.kronecker sigma.pos.transpose

/-- PPT states are closed under finite convex mixing. -/
theorem isPPT_averageState {ι : Type w} [Fintype ι]
    (E : Ensemble ι (Prod a b)) (hE : ∀ i, IsPPT (E.states i)) :
    IsPPT E.averageState := by
  rw [IsPPT, Ensemble.averageState_matrix, partialTransposeB_sum]
  simp_rw [partialTransposeB_smul_nnreal]
  exact Matrix.posSemidef_sum Finset.univ fun i _ =>
    (hE i).smul (NNReal.coe_nonneg (E.probs i))

/-- Every separable state is PPT. -/
theorem isPPT_of_isSeparable {rho : State (Prod a b)}
    (hrho : IsSeparable.{u, v, w} rho) : IsPPT rho := by
  induction hrho with
  | product rhoA rhoB =>
      exact isPPT_prod rhoA rhoB
  | @averageState ι _ E hE ih =>
      exact isPPT_averageState E ih

end

end QIT
