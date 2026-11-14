/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Classical.Ensemble

/-!
# Separable bipartite states

Separable states are the finite convex closure of product states. The predicate
uses the existing finite `Ensemble` API: product states are separable, and a
finite ensemble average of separable states is separable. This inductive API is
the local proof interface for finite-dimensional convex product decompositions in
[Horodecki2007Entanglement, ent-review-last.tex:2175-2208],
[Gour2024Resources, BookQRT.tex:3260-3274], and
[Gour2024Resources, BookQRT.tex:20963-20969].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A bipartite state is a product state when it is exactly a tensor product of
local density states. -/
def IsProductState (rho : State (Prod a b)) : Prop :=
  ∃ (rhoA : State a) (rhoB : State b), rho = rhoA.prod rhoB

/-- A bipartite state is separable when it has a finite convex decomposition
generated from product states. -/
inductive IsSeparable : State (Prod a b) → Prop where
  /-- Product states are separable. -/
  | product (rho : State a) (sigma : State b) : IsSeparable (rho.prod sigma)
  /-- Finite convex mixtures of separable states are separable. -/
  | averageState {ι : Type w} [Fintype ι] (E : Ensemble ι (Prod a b))
      (hE : ∀ i, IsSeparable (E.states i)) : IsSeparable E.averageState

/-- A tensor product of local states is a product state. -/
theorem isProductState_prod (rho : State a) (sigma : State b) :
    IsProductState (rho.prod sigma) :=
  ⟨rho, sigma, rfl⟩

/-- Every product state is separable, as a one-point convex mixture. -/
theorem isSeparable_of_isProductState {rho : State (Prod a b)}
    (hrho : IsProductState rho) : IsSeparable rho := by
  rcases hrho with ⟨rhoA, rhoB, rfl⟩
  exact IsSeparable.product rhoA rhoB

/-- A tensor product of local states is separable. -/
theorem isSeparable_prod (rho : State a) (sigma : State b) :
    IsSeparable (rho.prod sigma) :=
  IsSeparable.product rho sigma

/-- Separable states are closed under finite convex mixing. -/
theorem isSeparable_averageState {ι : Type w} [Fintype ι]
    (E : Ensemble ι (Prod a b)) (hE : ∀ i, IsSeparable.{u, v, w} (E.states i)) :
    IsSeparable.{u, v, w} E.averageState :=
  IsSeparable.averageState E hE

end

end QIT
