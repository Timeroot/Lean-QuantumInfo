/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.SmoothEndpoint.Subnormalized

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal Pointwise
open scoped Topology
open Matrix
open Set Filter

namespace QIT

universe u v w x

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace State

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

@[simp]
theorem toSubnormalized_matrix_ne_zero (ρ : State a) :
    ρ.toSubnormalized.matrix ≠ 0 := by
  simpa only [State.toSubnormalized_matrix] using ρ.density_matrix_ne_zero

/-- Embedding a normalized center into the subnormalized state space does not
change its unsmoothed conditional min-entropy. -/
@[simp]
theorem toSubnormalized_conditionalMinEntropy_eq
    (ρ : State (Prod a b)) :
    ρ.toSubnormalized.conditionalMinEntropy = (ρ.conditionalMinEntropy : EReal) := by
  letI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  letI : Nonempty b := ⟨(Classical.choice ρ.nonempty).2⟩
  have hstate :
      SubnormalizedState.ofStateScale ρ 1 (by norm_num) (by norm_num) =
        ρ.toSubnormalized := by
    apply SubnormalizedState.ext
    simp [SubnormalizedState.ofStateScale_matrix]
  have hscale := SubnormalizedState.conditionalMinEntropy_ofStateScale
    (a := a) (b := b) ρ (t := 1) (by norm_num) (by norm_num)
  rw [hstate] at hscale
  rw [SubnormalizedState.conditionalMinEntropy_eq_coe_finite_of_matrix_ne_zero
    ρ.toSubnormalized_matrix_ne_zero]
  congr 1
  simpa [SubnormalizedState.conditionalMinEntropyFinite, log2] using hscale

@[simp]
theorem toSubnormalized_conditionalMinEntropyFinite_eq
    (ρ : State (Prod a b)) :
    ρ.toSubnormalized.conditionalMinEntropyFinite ρ.toSubnormalized_matrix_ne_zero =
      ρ.conditionalMinEntropy := by
  letI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  letI : Nonempty b := ⟨(Classical.choice ρ.nonempty).2⟩
  have hstate :
      SubnormalizedState.ofStateScale ρ 1 (by norm_num) (by norm_num) =
        ρ.toSubnormalized := by
    apply SubnormalizedState.ext
    simp [SubnormalizedState.ofStateScale_matrix]
  have hscale := SubnormalizedState.conditionalMinEntropy_ofStateScale
    (a := a) (b := b) ρ (t := 1) (by norm_num) (by norm_num)
  rw [hstate] at hscale
  simpa [SubnormalizedState.conditionalMinEntropyFinite, log2] using hscale

@[simp]
theorem toSubnormalized_conditionalMinEntropyRaw_eq
    (ρ : State (Prod a b)) :
    ρ.toSubnormalized.conditionalMinEntropyRaw = ρ.conditionalMinEntropy := by
  simpa [SubnormalizedState.conditionalMinEntropyFinite] using
    ρ.toSubnormalized_conditionalMinEntropyFinite_eq (a := a) (b := b)

/-- Embedding a normalized center into the subnormalized state space does not
change its unsmoothed conditional max-entropy. -/
@[simp]
theorem toSubnormalized_conditionalMaxEntropy_eq
    (ρ : State (Prod a b)) :
    ρ.toSubnormalized.conditionalMaxEntropy = (ρ.conditionalMaxEntropy : EReal) := by
  letI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  letI : Nonempty b := ⟨(Classical.choice ρ.nonempty).2⟩
  have hstate :
      SubnormalizedState.ofStateScale ρ 1 (by norm_num) (by norm_num) =
        ρ.toSubnormalized := by
    apply SubnormalizedState.ext
    simp [SubnormalizedState.ofStateScale_matrix]
  have hscale := SubnormalizedState.conditionalMaxEntropy_ofStateScale
    (a := a) (b := b) ρ (t := 1) (by norm_num) (by norm_num)
  rw [hstate] at hscale
  rw [SubnormalizedState.conditionalMaxEntropy_eq_coe_finite_of_matrix_ne_zero
    ρ.toSubnormalized_matrix_ne_zero]
  congr 1
  simpa [SubnormalizedState.conditionalMaxEntropyFinite, log2] using hscale

@[simp]
theorem toSubnormalized_conditionalMaxEntropyFinite_eq
    (ρ : State (Prod a b)) :
    ρ.toSubnormalized.conditionalMaxEntropyFinite ρ.toSubnormalized_matrix_ne_zero =
      ρ.conditionalMaxEntropy := by
  letI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  letI : Nonempty b := ⟨(Classical.choice ρ.nonempty).2⟩
  have hstate :
      SubnormalizedState.ofStateScale ρ 1 (by norm_num) (by norm_num) =
        ρ.toSubnormalized := by
    apply SubnormalizedState.ext
    simp [SubnormalizedState.ofStateScale_matrix]
  have hscale := SubnormalizedState.conditionalMaxEntropy_ofStateScale
    (a := a) (b := b) ρ (t := 1) (by norm_num) (by norm_num)
  rw [hstate] at hscale
  simpa [SubnormalizedState.conditionalMaxEntropyFinite, log2] using hscale

@[simp]
theorem toSubnormalized_conditionalMaxEntropyRaw_eq
    (ρ : State (Prod a b)) :
    ρ.toSubnormalized.conditionalMaxEntropyRaw = ρ.conditionalMaxEntropy := by
  simpa [SubnormalizedState.conditionalMaxEntropyFinite] using
    ρ.toSubnormalized_conditionalMaxEntropyFinite_eq (a := a) (b := b)

/-- Zero-radius source-facing smooth conditional min-entropy is the unsmoothed
conditional min-entropy [Tomamichel2015FiniteResources, calculus.tex:418-442]. -/
theorem smoothConditionalMinEntropy_zero (ρ : State (Prod a b)) :
    ρ.smoothConditionalMinEntropy 0 (le_refl 0) (by norm_num) =
      ρ.conditionalMinEntropy := by
  rw [State.smoothConditionalMinEntropy_zero_eq_toSubnormalized,
    State.toSubnormalized_conditionalMinEntropyFinite_eq]

/-- Zero-radius source-facing smooth conditional max-entropy is the unsmoothed
conditional max-entropy [Tomamichel2015FiniteResources, calculus.tex:418-442]. -/
theorem smoothConditionalMaxEntropy_zero (ρ : State (Prod a b)) :
    ρ.smoothConditionalMaxEntropy 0 (le_refl 0) (by norm_num) =
      ρ.conditionalMaxEntropy := by
  rw [State.smoothConditionalMaxEntropy_zero_eq_toSubnormalized,
    State.toSubnormalized_conditionalMaxEntropyFinite_eq]

end State

namespace PureVector

variable {a : Type u} {b : Type v} {c : Type*}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]
variable {κ : Type x} [Fintype κ] [DecidableEq κ]

private theorem sum_pair_delta {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [AddCommMonoid γ] (p : α) (q : β) (f : α → β → γ) :
    (∑ x : α, ∑ y : β, if x = p ∧ y = q then f x y else 0) = f p q := by
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp
    · intro y _ hy
      simp [hy]
    · intro hnot
      simp at hnot
  · intro x _ hx
    have hxp : x ≠ p := hx
    simp [hxp]
  · intro hnot
    simp at hnot

private theorem sum_pair_delta_rev {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [AddCommMonoid γ] (p : α) (q : β) (f : α → β → γ) :
    (∑ x : α, ∑ y : β, if p = x ∧ q = y then f x y else 0) = f p q := by
  simpa [eq_comm] using sum_pair_delta p q f

private theorem sum_abab_delta {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [AddCommMonoid γ] (p r : α) (q s : β) (f : α → β → α → β → γ) :
    (∑ x₁ : α, ∑ y₁ : β, ∑ x₂ : α, ∑ y₂ : β,
      if x₁ = p ∧ x₂ = r ∧ y₁ = q ∧ y₂ = s then f x₁ y₁ x₂ y₂ else 0) =
      f p q r s := by
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · rw [Finset.sum_eq_single r]
      · rw [Finset.sum_eq_single s]
        · simp
        · intro y _ hy
          simp [hy]
        · intro hnot
          simp at hnot
      · intro x _ hx
        simp [hx]
      · intro hnot
        simp at hnot
    · intro y _ hy
      simp [hy]
    · intro hnot
      simp at hnot
  · intro x _ hx
    simp [hx]
  · intro hnot
    simp at hnot

/-- The dual-effect objective on the `AC` marginal is the same tripartite
bracket obtained by lifting that `AC` operator to the pure `ABC` state.

This is only a representation bridge; it does not use or prove endpoint
duality. -/
theorem dualEffectObjective_eq_tripartiteBracket_liftAC
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c)) :
    ((ψ.state.marginalAC.matrix * M).trace).re =
      (ψ.tripartiteBracket (State.liftACToABC (b := b) M)).re := by
  calc
    ((ψ.state.marginalAC.matrix * M).trace).re =
        ((M * ψ.state.marginalAC.matrix).trace).re := by
      rw [Matrix.trace_mul_comm]
    _ = (ψ.tripartiteBracket (State.liftACToABC (b := b) M)).re := by
      rw [ψ.tripartiteBracket_liftACToABC_eq_trace_marginalAC M]

/-! ### Pure endpoint link-map support -/

def dualEffectKrausSuccessVector [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) (K : κ → Matrix a c ℂ) :
    Prod κ b → ℂ :=
  fun x =>
    ((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ) *
      ∑ i : a, ∑ z : c, K x.1 i z * ψ.amp ((i, x.2), z)

omit [DecidableEq κ] in
private theorem dualEffectTransposeMatrixMap_eq_ofKraus_entry
    {M : CMatrix (Prod a c)} {K : κ → Matrix a c ℂ}
    (hK :
      State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M =
        MatrixMap.ofKraus K)
    (i i' : a) (z z' : c) :
    M (i', z') (i, z) =
      ∑ l : κ, K l i z * star (K l i' z') := by
  have hchoi := congrArg MatrixMap.choi hK
  have hentry := congrFun (congrFun hchoi (z, i)) (z', i')
  rw [State.conditionalMinEntropyDualEffectTransposeMatrixMap,
    MatrixMap.choi_ofChoiMatrix, MatrixMap.choi_ofKraus] at hentry
  simpa [State.conditionalMinEntropyDualEffectTransposeMatrixMap,
    State.conditionalMinEntropyDualEffectTransposeChoiMatrix,
    State.conditionalMinEntropyDualEffectChoiMatrix, Matrix.vecMulVec,
    Matrix.transpose, Matrix.sum_apply] using hentry

/-- Apply the Choi map induced by an `AC` dual effect to the purifying `C`
register of a pure `ABC` state, leaving the `AB` registers untouched.

The output lives on `(A × B) × A'`; the final endpoint proof tests the two
outer `A` registers against a maximally-entangled projector. -/
def dualEffectLinkOutputABA (ψ : PureVector (Prod (Prod a b) c))
    (M : CMatrix (Prod a c)) : CMatrix (Prod (Prod a b) a) :=
  (MatrixMap.kron (LinearMap.id : MatrixMap (Prod a b) (Prod a b))
    (State.conditionalMinEntropyDualEffectMatrixMap (a := a) (b := c) M)) ψ.state.matrix

/-- The same link-map output, written with the adjoint input matrix.  Since
pure-state density matrices are Hermitian this is equal to
`dualEffectLinkOutputABA`, but its matrix-entry expansion has the orientation
that directly matches `Tr(ρ_AC M)`. -/
def dualEffectLinkOutputABAStarInput (ψ : PureVector (Prod (Prod a b) c))
    (M : CMatrix (Prod a c)) : CMatrix (Prod (Prod a b) a) :=
  (MatrixMap.kron (LinearMap.id : MatrixMap (Prod a b) (Prod a b))
    (State.conditionalMinEntropyDualEffectMatrixMap (a := a) (b := c) M)) (star ψ.state.matrix)

/-- Link output using the transpose-Choi orientation of the dual effect.  This
orientation is the one whose maximally-entangled projector expectation unfolds
directly to the dual-effect objective `Tr(ρ_AC M)`. -/
def dualEffectTransposeLinkOutputABA (ψ : PureVector (Prod (Prod a b) c))
    (M : CMatrix (Prod a c)) : CMatrix (Prod (Prod a b) a) :=
  (MatrixMap.kron (LinearMap.id : MatrixMap (Prod a b) (Prod a b))
    (State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M))
      ψ.state.matrix

theorem dualEffectLinkOutputABAStarInput_eq
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c)) :
    dualEffectLinkOutputABAStarInput (a := a) (b := b) (c := c) ψ M =
      dualEffectLinkOutputABA (a := a) (b := b) (c := c) ψ M := by
  have hstar : star ψ.state.matrix = ψ.state.matrix := by
    simp [Matrix.star_eq_conjTranspose]
  rw [dualEffectLinkOutputABAStarInput, dualEffectLinkOutputABA, hstar]

@[simp]
theorem dualEffectLinkOutputABA_apply
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c))
    (ab ab' : Prod a b) (i i' : a) :
    dualEffectLinkOutputABA (a := a) (b := b) (c := c) ψ M (ab, i) (ab', i') =
      ∑ k : c, ∑ k' : c,
        ψ.state.matrix (ab, k) (ab', k') * M (i, k) (i', k') := by
  classical
  rcases ab with ⟨j, b0⟩
  rcases ab' with ⟨j', b1⟩
  simp [dualEffectLinkOutputABA, MatrixMap.kron, MatrixMap.ofChoiMatrix_apply,
    State.conditionalMinEntropyDualEffectMatrixMap,
    State.conditionalMinEntropyDualEffectChoiMatrix, PureVector.state_matrix,
    rankOneMatrix_apply, Matrix.single, Fintype.sum_prod_type,
    sum_pair_delta_rev, sum_abab_delta, and_assoc, and_left_comm]

@[simp]
theorem dualEffectLinkOutputABAStarInput_apply
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c))
    (ab ab' : Prod a b) (i i' : a) :
    dualEffectLinkOutputABAStarInput (a := a) (b := b) (c := c) ψ M (ab, i) (ab', i') =
      ∑ k : c, ∑ k' : c,
        (star ψ.state.matrix) (ab, k) (ab', k') * M (i, k) (i', k') := by
  classical
  rcases ab with ⟨j, b0⟩
  rcases ab' with ⟨j', b1⟩
  simp [dualEffectLinkOutputABAStarInput, MatrixMap.kron, MatrixMap.ofChoiMatrix_apply,
    State.conditionalMinEntropyDualEffectMatrixMap,
    State.conditionalMinEntropyDualEffectChoiMatrix, PureVector.state_matrix,
    rankOneMatrix_apply, Matrix.single, Fintype.sum_prod_type,
    sum_pair_delta_rev, sum_abab_delta, and_assoc, and_left_comm]

@[simp]
theorem dualEffectTransposeLinkOutputABA_apply
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c))
    (ab ab' : Prod a b) (i i' : a) :
    dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M (ab, i) (ab', i') =
      ∑ k : c, ∑ k' : c,
        ψ.state.matrix (ab, k) (ab', k') * M (i', k') (i, k) := by
  classical
  rcases ab with ⟨j, b0⟩
  rcases ab' with ⟨j', b1⟩
  simp [dualEffectTransposeLinkOutputABA, MatrixMap.kron, MatrixMap.ofChoiMatrix_apply,
    State.conditionalMinEntropyDualEffectTransposeMatrixMap,
    State.conditionalMinEntropyDualEffectTransposeChoiMatrix,
    State.conditionalMinEntropyDualEffectChoiMatrix, PureVector.state_matrix,
    rankOneMatrix_apply, Matrix.single, Fintype.sum_prod_type,
    sum_pair_delta_rev, sum_abab_delta, and_assoc, and_left_comm, Matrix.transpose]

private theorem sum_a_a_b_c_c_k_reorder {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → α → β → γ → γ → δ → ℂ) :
    (∑ x : α, ∑ y : α, ∑ j : β, ∑ k : γ, ∑ l : γ, ∑ m : δ,
        f x y j k l m) =
      ∑ m : δ, ∑ j : β, ∑ x : α, ∑ k : γ, ∑ y : α, ∑ l : γ,
        f x y j k l m := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  conv_rhs =>
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
  let e : (((((α × α) × β) × γ) × γ) × δ) ≃ (((((δ × β) × α) × γ) × α) × γ) := {
    toFun := fun t =>
      (((((t.2, t.1.1.1.2), t.1.1.1.1.1), t.1.1.2), t.1.1.1.1.2), t.1.2)
    invFun := fun s =>
      (((((s.1.1.1.2, s.1.2), s.1.1.1.1.2), s.1.1.2), s.2), s.1.1.1.1.1)
    left_inv := by
      intro t
      rcases t with ⟨⟨⟨⟨⟨x, y⟩, j⟩, k⟩, l⟩, m⟩
      rfl
    right_inv := by
      intro s
      rcases s with ⟨⟨⟨⟨⟨m, j⟩, x⟩, k⟩, y⟩, l⟩
      rfl }
  simpa [e] using
    (Finset.sum_equiv e (s := Finset.univ) (t := Finset.univ)
      (fun _ => by simp)
      (fun t _ => by
        rcases t with ⟨⟨⟨⟨⟨x, y⟩, j⟩, k⟩, l⟩, m⟩
        rfl))

private theorem sum_outer_mul_inner_expand {δ : Type*} {β : Type*} {α : Type*} {γ : Type*}
    [Fintype δ] [Fintype β] [Fintype α] [Fintype γ]
    (s : ℂ) (A B : δ → β → α → γ → ℂ)
    (C : δ → β → α → γ → α → γ → ℂ) :
    (∑ m : δ, ∑ j : β, ∑ x : α, ∑ k : γ,
        A m j x k * (s * (B m j x k *
          ∑ y : α, ∑ l : γ, s * C m j x k y l))) =
      ∑ m : δ, ∑ j : β, ∑ x : α, ∑ k : γ, ∑ y : α, ∑ l : γ,
        A m j x k * (s * (s * (B m j x k * C m j x k y l))) := by
  classical
  simp [Finset.mul_sum, mul_left_comm]

private theorem sum_success_norm_expand {δ : Type*} {β : Type*} {α : Type*} {γ : Type*}
    [Fintype δ] [Fintype β] [Fintype α] [Fintype γ]
    (s : ℂ) (hs : star s = s) (K : δ → α → γ → ℂ)
    (A : δ → β → α → γ → ℂ) :
    (∑ m : δ, ∑ j : β, ∑ x : α, ∑ k : γ,
        s * (K m x k * A m j x k) *
          star (∑ y : α, ∑ l : γ, s * (K m y l * A m j y l))) =
      ∑ m : δ, ∑ j : β, ∑ x : α, ∑ k : γ, ∑ y : α, ∑ l : γ,
        K m x k *
          (s * (s * (A m j x k * (star (K m y l) * star (A m j y l))))) := by
  classical
  simp [hs, Finset.mul_sum, mul_assoc, mul_left_comm]

private theorem dotProduct_single_one_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι) (f : ι → ℂ) :
    (fun j => if p = j then 1 else 0) ⬝ᵥ f = f p := by
  classical
  rw [dotProduct]
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj
    have hpj : p ≠ j := fun h => hj h.symm
    simp [hpj]
  · intro hnot
    simp at hnot

private theorem sum_two_delta_collapse {δ : Type*} {α : Type*} {β : Type*} {γ : Type*}
    [Fintype δ] [DecidableEq δ] [Fintype α] [DecidableEq α]
    [Fintype β] [Fintype γ]
    (F : δ → α → α → β → δ → γ → ℂ) :
    (∑ m : δ, ∑ i : α, ∑ i' : α, ∑ j : β, ∑ m' : δ,
        if m = m' ∧ i = i' then ∑ z : γ, F m i i' j m' z else 0) =
      ∑ m : δ, ∑ j : β, ∑ i : α, ∑ z : γ, F m i i j m z := by
  classical
  calc
    (∑ m : δ, ∑ i : α, ∑ i' : α, ∑ j : β, ∑ m' : δ,
        if m = m' ∧ i = i' then ∑ z : γ, F m i i' j m' z else 0) =
        ∑ m : δ, ∑ i : α, ∑ j : β, ∑ z : γ, F m i i j m z := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_eq_single i]
          · rw [Finset.sum_eq_single m]
            · simp
            · intro m' _ hm'
              have hne : m ≠ m' := fun h => hm' h.symm
              simp [hne]
            · intro hnot
              simp at hnot
          · intro i' _ hi'
            have hne : i ≠ i' := fun h => hi' h.symm
            simp [hne]
          · intro hnot
            simp at hnot
    _ = ∑ m : δ, ∑ j : β, ∑ i : α, ∑ z : γ, F m i i j m z := by
      apply Finset.sum_congr rfl
      intro m hm
      exact Finset.sum_comm

omit [DecidableEq κ] in
set_option maxHeartbeats 800000 in
theorem dualEffectTransposeLink_projector_trace_eq_successVector_trace [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    {K : κ → Matrix a c ℂ}
    (hK :
      State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M =
        MatrixMap.ofKraus K) :
    ((dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M *
        State.maximallyEntangledProjectorWithMiddle (a := a) b).trace) =
      (rankOneMatrix (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace := by
  classical
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hsqrt_ne : Real.sqrt (Fintype.card a : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr hcard_pos)
  have hcoeff_success :
      (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) =
        (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) *
          (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← sq, Real.sq_sqrt]
    exact inv_nonneg.mpr (le_of_lt hcard_pos)
  rw [State.trace_mul_maximallyEntangledProjectorWithMiddle]
  rw [rankOneMatrix_trace]
  simp only [dualEffectTransposeLinkOutputABA_apply, dualEffectKrausSuccessVector,
    dotProduct, PureVector.state_matrix, rankOneMatrix_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
    dualEffectTransposeMatrixMap_eq_ofKraus_entry (a := a) (c := c) hK]
  rw [hcoeff_success]
  have hscoeff :
      star ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ)) =
        (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) := by
    simp
  rw [sum_success_norm_expand
    (δ := κ) (β := b) (α := a) (γ := c)
    ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ))
    hscoeff K (fun _ j x k => ψ.amp ((x, j), k))]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    sum_a_a_b_c_c_k_reorder (α := a) (β := b) (γ := c) (δ := κ)
      (fun x y j k l m =>
        K m x k *
          ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) *
            ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) *
              (ψ.amp ((x, j), k) *
                ((starRingEnd ℂ) (K m y l) *
                  (starRingEnd ℂ) (ψ.amp ((y, j), l)))))))

private theorem sum_a_c_a_c_b_reorder {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → α → γ → ℂ) :
    (∑ x : α, ∑ k : γ, ∑ y : α, ∑ l : γ, ∑ j : β,
        f x j k y l) =
      ∑ x : α, ∑ y : α, ∑ j : β, ∑ k : γ, ∑ l : γ,
        f x j k y l := by
  apply Finset.sum_congr rfl
  intro x _
  calc
    (∑ k : γ, ∑ y : α, ∑ l : γ, ∑ j : β, f x j k y l) =
        ∑ y : α, ∑ k : γ, ∑ l : γ, ∑ j : β, f x j k y l := by
      rw [Finset.sum_comm]
    _ = ∑ y : α, ∑ k : γ, ∑ j : β, ∑ l : γ, f x j k y l := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = ∑ y : α, ∑ j : β, ∑ k : γ, ∑ l : γ, f x j k y l := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]

private theorem idChannel_map_eq_linearMap_id {α : Type*} [Fintype α] [DecidableEq α] :
    (Channel.idChannel α).map = (LinearMap.id : MatrixMap α α) := by
  ext X i j
  simp [Channel.idChannel, MatrixMap.ofKraus]

private def contractionDilationReferenceIsometry {r₁ : Type*} {r₂ : Type*}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    (K : Matrix r₂ r₁ ℂ) (hK : Matrix.conjTranspose K * K ≤ (1 : CMatrix r₁)) :
    ReferenceIsometry r₁ (Sum r₁ r₂) where
  matrix := fun x y =>
    match x with
    | Sum.inl i => psdSqrt ((1 : CMatrix r₁) - Matrix.conjTranspose K * K) i y
    | Sum.inr j => K j y
  isometry := by
    classical
    let S : CMatrix r₁ := (1 : CMatrix r₁) - Matrix.conjTranspose K * K
    have hSpos : S.PosSemidef := by
      simpa [S, Matrix.le_iff] using hK
    have hSH : (psdSqrt S).IsHermitian := psdSqrt_isHermitian S
    have hSsq : psdSqrt S * psdSqrt S = S :=
      psdSqrt_mul_self_of_posSemidef hSpos
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [Fintype.sum_sum_type]
    have hleft :
        (∑ x : r₁,
          star (psdSqrt S x i) * psdSqrt S x j) =
          S i j := by
      calc
        (∑ x : r₁, star (psdSqrt S x i) * psdSqrt S x j) =
            (∑ x : r₁, psdSqrt S i x * psdSqrt S x j) := by
              apply Finset.sum_congr rfl
              intro x _
              have hx := congrFun (congrFun hSH.eq i) x
              have hx' : star (psdSqrt S x i) = psdSqrt S i x := by
                simpa [Matrix.conjTranspose_apply] using hx
              rw [hx']
        _ = (psdSqrt S * psdSqrt S) i j := by
              simp [Matrix.mul_apply]
        _ = S i j := by rw [hSsq]
    rw [hleft]
    change S i j + (Matrix.conjTranspose K * K) i j = (1 : CMatrix r₁) i j
    simp [S, Matrix.sub_apply]

private def referenceIsometryRightBlockK {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (V : ReferenceIsometry c (Sum c (Prod κ a))) :
    κ → Matrix a c ℂ :=
  fun k i z => V.matrix (Sum.inr (k, i)) z

private def referenceIsometryLeftBlockMatrix {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (V : ReferenceIsometry c (Sum c (Prod κ a))) :
    CMatrix c :=
  fun z z' => V.matrix (Sum.inl z) z'

private theorem referenceIsometryRightBlockK_contraction {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (V : ReferenceIsometry c (Sum c (Prod κ a))) :
    Matrix.conjTranspose
        (MatrixMap.smoothEndpointKrausStack (referenceIsometryRightBlockK (a := a) V)) *
        MatrixMap.smoothEndpointKrausStack (referenceIsometryRightBlockK (a := a) V) ≤
      (1 : CMatrix c) := by
  classical
  let L : CMatrix c := referenceIsometryLeftBlockMatrix (a := a) V
  let Kstack : Matrix (Prod κ a) c ℂ :=
    MatrixMap.smoothEndpointKrausStack (referenceIsometryRightBlockK (a := a) V)
  have hdecomp :
      (1 : CMatrix c) - Matrix.conjTranspose Kstack * Kstack =
        Matrix.conjTranspose L * L := by
    ext z z'
    have hV := congrFun (congrFun V.isometry z) z'
    simp [L, Kstack, referenceIsometryLeftBlockMatrix, referenceIsometryRightBlockK,
      MatrixMap.smoothEndpointKrausStack, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_sum_type, Fintype.sum_prod_type, Matrix.sub_apply] at hV ⊢
    rw [← hV]
    ring
  have hpos : ((1 : CMatrix c) - Matrix.conjTranspose Kstack * Kstack).PosSemidef := by
    rw [hdecomp]
    exact Matrix.posSemidef_conjTranspose_mul_self L
  simpa [Kstack, Matrix.le_iff] using hpos

theorem dualEffectObjective_eq_card_mul_trace_transposeLink
    [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c)) :
    ((ψ.state.marginalAC.matrix * M).trace) =
      ((Fintype.card a : ℂ) *
        ((dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M *
          State.maximallyEntangledProjectorWithMiddle (a := a) b).trace)) := by
  classical
  rw [State.trace_mul_maximallyEntangledProjectorWithMiddle]
  simpa [dualEffectTransposeLinkOutputABA_apply, State.marginalAC, Matrix.trace,
    Matrix.mul_apply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
    mul_assoc] using
      sum_a_c_a_c_b_reorder (α := a) (β := b) (γ := c)
        (fun x j k y l =>
          ψ.amp ((x, j), k) * ((starRingEnd ℂ) (ψ.amp ((y, j), l)) * M (y, l) (x, k)))

theorem dualEffectTransposeLinkOutputABA_posSemidef
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    (hM : State.ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    (dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M).PosSemidef := by
  classical
  let T : MatrixMap c a :=
    State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M
  have hT : MatrixMap.TraceNonincreasingCP T :=
    State.conditionalMinEntropyDualEffectTransposeMatrixMap_traceNonincreasingCP
      (a := a) (b := c) hM
  have hkron :
      MatrixMap.TraceNonincreasingCP
        (MatrixMap.kron (Channel.idChannel (Prod a b)).map T) :=
    MatrixMap.traceNonincreasingCP_id_kron (a := Prod a b) hT
  have hkron' :
      MatrixMap.TraceNonincreasingCP
        (MatrixMap.kron (LinearMap.id : MatrixMap (Prod a b) (Prod a b)) T) := by
    simpa [idChannel_map_eq_linearMap_id] using hkron
  simpa [dualEffectTransposeLinkOutputABA, T] using
    hkron'.mapsPositive ψ.state.matrix ψ.state.pos

theorem dualEffectTransposeLinkOutputABA_trace_re_le_one
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    (hM : State.ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    (dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M).trace.re ≤ 1 := by
  classical
  let T : MatrixMap c a :=
    State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M
  have hT : MatrixMap.TraceNonincreasingCP T :=
    State.conditionalMinEntropyDualEffectTransposeMatrixMap_traceNonincreasingCP
      (a := a) (b := c) hM
  have hkron :
      MatrixMap.TraceNonincreasingCP
        (MatrixMap.kron (Channel.idChannel (Prod a b)).map T) :=
    MatrixMap.traceNonincreasingCP_id_kron (a := Prod a b) hT
  have hkron' :
      MatrixMap.TraceNonincreasingCP
        (MatrixMap.kron (LinearMap.id : MatrixMap (Prod a b) (Prod a b)) T) := by
    simpa [idChannel_map_eq_linearMap_id] using hkron
  have hle := hkron'.traceNonincreasing ψ.state.matrix ψ.state.pos
  have htrace : (ψ.amp ⬝ᵥ fun i => (starRingEnd ℂ) (ψ.amp i)).re = 1 := by
    simpa [PureVector.state_matrix, Matrix.trace, rankOneMatrix_apply, dotProduct,
      Complex.mul_re, Complex.conj_re, Complex.conj_im] using
      congrArg Complex.re ψ.trace_rankOne_eq_one
  change ((MatrixMap.kron (LinearMap.id : MatrixMap (Prod a b) (Prod a b)) T)
      ψ.state.matrix).trace.re ≤ 1
  simpa [htrace] using hle

theorem dualEffectTransposeLinkOutputABA_projector_trace_re_nonneg [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    (hM : State.ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    0 ≤ ((dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M *
      State.maximallyEntangledProjectorWithMiddle (a := a) b).trace).re := by
  exact cMatrix_trace_mul_posSemidef_re_nonneg
    (ψ.dualEffectTransposeLinkOutputABA_posSemidef (a := a) hM)
    (State.maximallyEntangledProjectorWithMiddle_posSemidef (a := a) (b := b))

theorem dualEffectObjective_re_eq_card_mul_trace_transposeLink [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c)) :
    ((ψ.state.marginalAC.matrix * M).trace).re =
      (Fintype.card a : ℝ) *
        ((dualEffectTransposeLinkOutputABA (a := a) (b := b) (c := c) ψ M *
          State.maximallyEntangledProjectorWithMiddle (a := a) b).trace).re := by
  have h :=
    congrArg Complex.re
      (ψ.dualEffectObjective_eq_card_mul_trace_transposeLink (a := a) (b := b) M)
  simpa [Complex.re_ofReal_mul] using h

omit [DecidableEq κ] in
theorem dualEffectObjective_re_eq_card_mul_successVector_trace [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    {K : κ → Matrix a c ℂ}
    (hK :
      State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M =
        MatrixMap.ofKraus K) :
    ((ψ.state.marginalAC.matrix * M).trace).re =
      (Fintype.card a : ℝ) *
        (rankOneMatrix
          (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re := by
  have hobj :=
    ψ.dualEffectObjective_re_eq_card_mul_trace_transposeLink (a := a) (b := b) M
  have htrace :=
    congrArg Complex.re
      (ψ.dualEffectTransposeLink_projector_trace_eq_successVector_trace
        (a := a) (b := b) hK)
  rw [hobj, htrace]

omit [DecidableEq κ] in
theorem dualEffectKrausSuccessVector_card_mul_trace_le_scaleFeasible_trace
    [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) {K : κ → Matrix a c ℂ}
    {T : CMatrix c}
    (hKstack :
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
        MatrixMap.smoothEndpointKrausStack K ≤ (1 : CMatrix c))
    (hT : State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T) :
    (Fintype.card a : ℝ) *
        (rankOneMatrix
          (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re ≤
      T.trace.re := by
  let M : CMatrix (Prod a c) :=
    State.conditionalMinEntropyDualEffectOfKraus (a := a) (b := c) K
  have hM : State.ConditionalMinEntropyDualEffectFeasible (a := a) M := by
    exact State.conditionalMinEntropyDualEffectOfKraus_feasible
      (a := a) (b := c) K hKstack
  have hK :
      State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M =
        MatrixMap.ofKraus K := by
    exact State.conditionalMinEntropyDualEffectOfKraus_transposeMatrixMap_eq_ofKraus
      (a := a) (b := c) K
  have hweak :
      ((ψ.state.marginalAC.matrix * M).trace).re ≤ T.trace.re :=
    State.conditionalMinEntropyDualEffectValue_le_scaleValue
      (a := a) hM hT
  have hobj :=
    ψ.dualEffectObjective_re_eq_card_mul_successVector_trace
      (a := a) (b := b) hK
  rwa [hobj] at hweak

omit [DecidableEq κ] in
theorem dualEffectObjective_le_card_mul_sSup_fidelityValueSet_of_successVector_trace_le
    [Nonempty a] [Nonempty b]
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    {K : κ → Matrix a c ℂ}
    (hK :
      State.conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := c) M =
        MatrixMap.ofKraus K)
    (hsuccess :
      (rankOneMatrix
        (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re ≤
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ((ψ.state.marginalAC.matrix * M).trace).re ≤
      (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  rw [ψ.dualEffectObjective_re_eq_card_mul_successVector_trace
    (a := a) (b := b) hK]
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card a)
  exact mul_le_mul_of_nonneg_left hsuccess hcard_nonneg

set_option maxHeartbeats 1200000 in
private theorem dualEffectKrausSuccessVector_dilation_overlap_eq_dot
    [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) (K : κ → Matrix a c ℂ)
    (hKstack :
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
        MatrixMap.smoothEndpointKrausStack K ≤ (1 : CMatrix c))
    (η : PureVector (Prod κ b)) :
    let v := dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K
    let Ψ₀ : PureVector (Prod c (Prod a b)) :=
      ψ.reindex (Equiv.prodComm (Prod a b) c)
    let Ψ :=
      (contractionDilationReferenceIsometry
        (MatrixMap.smoothEndpointKrausStack K) hKstack).applyPureVector Ψ₀
    let Φ₀ := State.maxEntangledSidePureVector (a := a) η
    let Φ :=
      (ReferenceIsometry.sumInr c (Prod κ a)).applyPureVector Φ₀
    Ψ.overlap Φ = ∑ x : Prod κ b, star (v x) * η.amp x := by
  classical
  intro v Ψ₀ Ψ Φ₀ Φ
  have hscoeff :
      star ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ)) =
        (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) := by
    simp
  simpa [PureVector.overlap, Ψ, Φ, Ψ₀, Φ₀, v,
    ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
    contractionDilationReferenceIsometry, ReferenceIsometry.sumInr,
    State.maxEntangledSidePureVector, State.pureVectorOfAmplitudeMatrix,
    State.maxEntangledSideAmplitude,
    dualEffectKrausSuccessVector, MatrixMap.smoothEndpointKrausStack,
    Matrix.mulVec, Fintype.sum_sum_type, Fintype.sum_prod_type,
    dotProduct_single_one_left,
    dotProduct, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul, hscoeff,
    mul_assoc, mul_left_comm, mul_comm] using
      sum_two_delta_collapse (δ := κ) (α := a) (β := b) (γ := c)
      (fun m i i' j m' z =>
            (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) *
            (η.amp (m', j) *
              (star (K m i z) * star (ψ.amp ((i', j), z)))))

set_option maxHeartbeats 1200000 in
private theorem referenceIsometryRightBlockK_overlap_eq_dot
    [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c))
    (V : ReferenceIsometry c (Sum c (Prod κ a)))
    (η : PureVector (Prod κ b)) :
    let K := referenceIsometryRightBlockK (a := a) V
    let v := dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K
    let Ψ₀ : PureVector (Prod c (Prod a b)) :=
      ψ.reindex (Equiv.prodComm (Prod a b) c)
    let Ψ := V.applyPureVector Ψ₀
    let Φ₀ := State.maxEntangledSidePureVector (a := a) η
    let Φ :=
      (ReferenceIsometry.sumInr c (Prod κ a)).applyPureVector Φ₀
    Ψ.overlap Φ = ∑ x : Prod κ b, star (v x) * η.amp x := by
  classical
  intro K v Ψ₀ Ψ Φ₀ Φ
  have hscoeff :
      star ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ)) =
        (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) := by
    simp
  simpa [PureVector.overlap, Ψ, Φ, Ψ₀, Φ₀, v, K,
    ReferenceIsometry.applyPureVector_amp, ReferenceIsometry.applyAmp,
    ReferenceIsometry.sumInr, State.maxEntangledSidePureVector,
    State.pureVectorOfAmplitudeMatrix, State.maxEntangledSideAmplitude,
    referenceIsometryRightBlockK, dualEffectKrausSuccessVector,
    Matrix.mulVec, Fintype.sum_sum_type, Fintype.sum_prod_type,
    dotProduct_single_one_left, dotProduct, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul, hscoeff,
    mul_assoc, mul_left_comm, mul_comm] using
      sum_two_delta_collapse (δ := κ) (α := a) (β := b) (γ := c)
        (fun m i i' j m' z =>
            (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) *
            (η.amp (m', j) *
              (star (V.matrix (Sum.inr (m, i)) z) *
                star (ψ.amp ((i', j), z)))))

private theorem referenceIsometryRightBlockK_card_mul_overlapSq_le_scaleFeasible_trace
    [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c))
    (V : ReferenceIsometry c (Sum c (Prod κ a)))
    (η : PureVector (Prod κ b))
    {T : CMatrix c}
    (hT : State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T) :
    (Fintype.card a : ℝ) *
        ((V.applyPureVector
          (ψ.reindex (Equiv.prodComm (Prod a b) c))).overlapSq
            ((ReferenceIsometry.sumInr c (Prod κ a)).applyPureVector
              (State.maxEntangledSidePureVector (a := a) η))) ≤
      T.trace.re := by
  classical
  let K := referenceIsometryRightBlockK (a := a) V
  let v := dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K
  have hoverlap :=
    referenceIsometryRightBlockK_overlap_eq_dot
      (a := a) (b := b) (c := c) ψ V η
  have hcauchy :
      Complex.normSq (∑ x : Prod κ b, star (v x) * η.amp x) ≤
        (rankOneMatrix v).trace.re :=
    PureVector.normSq_sum_star_mul_le_rankOne_trace v η
  have hsuccess :
      (Fintype.card a : ℝ) * (rankOneMatrix v).trace.re ≤ T.trace.re :=
    ψ.dualEffectKrausSuccessVector_card_mul_trace_le_scaleFeasible_trace
      (a := a) (b := b) (K := K)
      (referenceIsometryRightBlockK_contraction (a := a) V) hT
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card a)
  have hmul :
      (Fintype.card a : ℝ) *
          Complex.normSq (∑ x : Prod κ b, star (v x) * η.amp x) ≤
        (Fintype.card a : ℝ) * (rankOneMatrix v).trace.re :=
    mul_le_mul_of_nonneg_left hcauchy hcard_nonneg
  rw [PureVector.overlapSq_eq_normSq, hoverlap]
  exact hmul.trans hsuccess

theorem fidelity_forward_bound_by_scaleFeasible
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) (σ : State b) (T : CMatrix c)
    (hT : State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T) :
    (Fintype.card a : ℝ) *
        ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
      T.trace.re := by
  classical
  let η : PureVector (Prod b b) := σ.canonicalPurification
  let τ : State (Prod a b) := (State.maximallyMixed a).prod σ
  let Ψ₀ : PureVector (Prod c (Prod a b)) :=
    ψ.reindex (Equiv.prodComm (Prod a b) c)
  let Φ₀ : PureVector (Prod (Prod b a) (Prod a b)) :=
    State.maxEntangledSidePureVector (a := a) η
  let Φ : PureVector (Prod (Sum c (Prod b a)) (Prod a b)) :=
    (ReferenceIsometry.sumInr c (Prod b a)).applyPureVector Φ₀
  have hη : η.state.marginalB = σ := by
    apply State.ext
    have hp : η.Purifies σ := by
      simpa [η] using σ.canonicalPurification_purifies
    simpa [η, State.marginalB_matrix] using hp
  have hΦ₀ : Φ₀.Purifies τ := by
    simpa [Φ₀, τ, hη] using State.maxEntangledSidePureVector_purifies (a := a) η
  have hΦ : Φ.Purifies τ := by
    simpa [Φ] using
      ((ReferenceIsometry.sumInr c (Prod b a)).applyPureVector_purifies hΦ₀)
  have hcardTarget :
      Fintype.card (Prod a b) ≤ Fintype.card (Sum c (Prod b a)) := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod]
    calc
      Fintype.card a * Fintype.card b = Fintype.card b * Fintype.card a :=
        Nat.mul_comm _ _
      _ ≤ Fintype.card c + Fintype.card b * Fintype.card a :=
        Nat.le_add_left _ _
  obtain ⟨Ψ, hΨ, hoverlap⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (Ψ := Φ) (ρ := τ) (σ := ψ.state.marginalAB) hΦ hcardTarget
  have hΨ₀ : Ψ₀.Purifies ψ.state.marginalAB := by
    simpa [Ψ₀] using ψ.reindex_prodComm_purifies_marginalA
  have hcardIso :
      Fintype.card c ≤ Fintype.card (Sum c (Prod b a)) := by
    rw [Fintype.card_sum]
    exact Nat.le_add_right _ _
  obtain ⟨V, hV⟩ :=
    PureVector.exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
      hΨ₀ hΨ hcardIso
  have hscale :=
    referenceIsometryRightBlockK_card_mul_overlapSq_le_scaleFeasible_trace
      (a := a) (b := b) (c := c) ψ V η hT
  have hfid :
      ψ.state.marginalAB.squaredFidelity τ =
        (V.applyPureVector Ψ₀).overlapSq Φ := by
    rw [hV] at hoverlap
    calc
      ψ.state.marginalAB.squaredFidelity τ =
          τ.squaredFidelity ψ.state.marginalAB := State.squaredFidelity_comm _ _
      _ = Φ.overlapSq (V.applyPureVector Ψ₀) := hoverlap.symm
      _ = (V.applyPureVector Ψ₀).overlapSq Φ := PureVector.overlapSq_comm_endpoint _ _
  rw [hfid]
  simpa [Ψ₀, Φ, τ] using hscale

private theorem dualEffectKrausSuccessVector_dilation_overlap_eq_sqrt_trace
    [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) (K : κ → Matrix a c ℂ)
    (hKstack :
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
        MatrixMap.smoothEndpointKrausStack K ≤ (1 : CMatrix c))
    (hpos :
      0 < (rankOneMatrix
        (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re) :
    let v := dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K
    let η := State.pureVectorNormalize v hpos
    let Ψ₀ : PureVector (Prod c (Prod a b)) :=
      ψ.reindex (Equiv.prodComm (Prod a b) c)
    let Ψ :=
      (contractionDilationReferenceIsometry
        (MatrixMap.smoothEndpointKrausStack K) hKstack).applyPureVector Ψ₀
    let Φ₀ := State.maxEntangledSidePureVector (a := a) η
    let Φ :=
      (ReferenceIsometry.sumInr c (Prod κ a)).applyPureVector Φ₀
    Ψ.overlap Φ =
      (((Real.sqrt
        (rankOneMatrix
          (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re) : ℝ) : ℂ) := by
  classical
  intro v η Ψ₀ Ψ Φ₀ Φ
  let t : ℝ := (rankOneMatrix v).trace.re
  have htpos : 0 < t := hpos
  have ht_nonneg : 0 ≤ t := le_of_lt htpos
  have htrace_im : (rankOneMatrix v).trace.im = 0 :=
    (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos v)).2.symm
  have htrace_complex : (rankOneMatrix v).trace = (t : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using htrace_im
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htpos)
  have hsqrt_inv_mul_trace :
      ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (rankOneMatrix v).trace) =
        ((Real.sqrt t : ℝ) : ℂ) := by
    rw [htrace_complex]
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt ht_nonneg]
  have hscoeff :
      star ((((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ)) =
        (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) := by
    simp
  have hnorm :
      (∑ x : Prod κ b, star (v x) * v x) = (rankOneMatrix v).trace := by
    simp [rankOneMatrix_trace, dotProduct, mul_comm]
  have hv_dot_re : (v ⬝ᵥ fun i => star (v i)).re = t := by
    simp [t, rankOneMatrix_trace, dotProduct]
  have hpsi_dot_re :
      ((dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K) ⬝ᵥ
          fun i => star (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K i)).re = t := by
    simpa [v] using hv_dot_re
  have hpsi_dot_re' :
      ((dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K) ⬝ᵥ
          fun i => (starRingEnd ℂ)
            (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K i)).re = t := by
    simpa using hpsi_dot_re
  have hsqrtdot :
      ((Real.sqrt
        (((dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K) ⬝ᵥ
          fun i => (starRingEnd ℂ)
            (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K i)).re) : ℂ)⁻¹) =
        ((Real.sqrt t : ℂ)⁻¹) := by
    exact congrArg (fun x : ℝ => ((Real.sqrt x : ℂ)⁻¹)) hpsi_dot_re'
  calc
    Ψ.overlap Φ =
        (((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
          (∑ x : Prod κ b, star (v x) * v x) := by
      rw [dualEffectKrausSuccessVector_dilation_overlap_eq_dot
        (a := a) (b := b) (c := c) ψ K hKstack η]
      simp [η, State.pureVectorNormalize_amp, v, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [hsqrtdot, mul_assoc, mul_comm]
    _ = (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (rankOneMatrix v).trace := by
      rw [hnorm]
    _ = ((Real.sqrt
          (rankOneMatrix
            (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re : ℝ) : ℂ) := by
      simpa [v, t] using hsqrt_inv_mul_trace

theorem dualEffectKrausSuccessVector_trace_le_sSup_fidelityValueSet
    [Nonempty a] [Nonempty b]
    (ψ : PureVector (Prod (Prod a b) c)) {K : κ → Matrix a c ℂ}
    (hKstack :
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
        MatrixMap.smoothEndpointKrausStack K ≤ (1 : CMatrix c)) :
    (rankOneMatrix
      (dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K)).trace.re ≤
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  classical
  let v := dualEffectKrausSuccessVector (a := a) (b := b) (c := c) ψ K
  let t : ℝ := (rankOneMatrix v).trace.re
  have ht_nonneg : 0 ≤ t := by
    simpa [t] using
      (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos v)).1
  by_cases hpos : 0 < t
  · let η : PureVector (Prod κ b) := State.pureVectorNormalize v (by simpa [t, v] using hpos)
    let Ψ₀ : PureVector (Prod c (Prod a b)) :=
      ψ.reindex (Equiv.prodComm (Prod a b) c)
    let Ψ :=
      (contractionDilationReferenceIsometry
        (MatrixMap.smoothEndpointKrausStack K) hKstack).applyPureVector Ψ₀
    let Φ₀ := State.maxEntangledSidePureVector (a := a) η
    let Φ :=
      (ReferenceIsometry.sumInr c (Prod κ a)).applyPureVector Φ₀
    have hΨ₀ : Ψ₀.Purifies ψ.state.marginalAB := by
      simpa [Ψ₀] using ψ.reindex_prodComm_purifies_marginalA
    have hΨ : Ψ.Purifies ψ.state.marginalAB := by
      simpa [Ψ] using
        ((contractionDilationReferenceIsometry
          (MatrixMap.smoothEndpointKrausStack K) hKstack).applyPureVector_purifies hΨ₀)
    have hΦ₀ :
        Φ₀.Purifies ((State.maximallyMixed a).prod η.state.marginalB) := by
      simpa [Φ₀] using State.maxEntangledSidePureVector_purifies (a := a) η
    have hΦ :
        Φ.Purifies ((State.maximallyMixed a).prod η.state.marginalB) := by
      simpa [Φ] using
        ((ReferenceIsometry.sumInr c (Prod κ a)).applyPureVector_purifies hΦ₀)
    have hoverlap :
        Ψ.overlap Φ = (((Real.sqrt t : ℝ) : ℂ)) := by
      simpa [v, t, η, Ψ₀, Ψ, Φ₀, Φ] using
        (dualEffectKrausSuccessVector_dilation_overlap_eq_sqrt_trace
          (a := a) (b := b) (c := c) ψ K hKstack
          (by simpa [v, t] using hpos))
    have habs_le :
        Complex.abs (Ψ.overlap Φ) ≤
          ψ.state.marginalAB.fidelity ((State.maximallyMixed a).prod η.state.marginalB) :=
      State.pureVector_abs_overlap_le_fidelity hΨ hΦ
    have hsqrt_le :
        Real.sqrt t ≤
          ψ.state.marginalAB.fidelity ((State.maximallyMixed a).prod η.state.marginalB) := by
      simpa [hoverlap, abs_of_nonneg (Real.sqrt_nonneg t)] using habs_le
    have ht_le_sq :
        t ≤ ψ.state.marginalAB.squaredFidelity
          ((State.maximallyMixed a).prod η.state.marginalB) := by
      rw [State.squaredFidelity_eq_fidelity_sq]
      have hfid_nonneg :
          0 ≤ ψ.state.marginalAB.fidelity
            ((State.maximallyMixed a).prod η.state.marginalB) := traceNorm_nonneg _
      have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg t) hfid_nonneg).mpr hsqrt_le
      simpa [sq, Real.sq_sqrt ht_nonneg, mul_comm] using hsquare
    have hmem :
        ψ.state.marginalAB.squaredFidelity
            ((State.maximallyMixed a).prod η.state.marginalB) ∈
          ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a) := by
      exact ⟨η.state.marginalB, rfl⟩
    have hsup :
        ψ.state.marginalAB.squaredFidelity
            ((State.maximallyMixed a).prod η.state.marginalB) ≤
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) :=
      le_csSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet_bddAbove (a := a)) hmem
    exact le_trans (by simpa [t, v] using ht_le_sq) hsup
  · have ht_le_zero : t ≤ 0 := le_of_not_gt hpos
    have hzero_le_sup :
        0 ≤ sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
      let σ₀ : State b := State.maximallyMixed b
      have hmem :
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ₀) ∈
            ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a) := by
        exact ⟨σ₀, rfl⟩
      have hle_sup :
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ₀) ≤
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) :=
        le_csSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet_bddAbove (a := a)) hmem
      exact le_trans (State.squaredFidelity_nonneg _ _) hle_sup
    exact le_trans (by simpa [t, v] using ht_le_zero) hzero_le_sup

theorem dualEffectObjective_le_card_mul_sSup_fidelityValueSet
    [Nonempty a] [Nonempty b]
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    (hM : State.ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    ((ψ.state.marginalAC.matrix * M).trace).re ≤
      (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  classical
  rcases State.exists_krausStack_contraction_conditionalMinEntropyDualEffectTransposeMatrixMap
      (a := a) (b := c) hM with ⟨K, hK, hKstack⟩
  exact ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet_of_successVector_trace_le
    (a := a) (b := b) hK
    (ψ.dualEffectKrausSuccessVector_trace_le_sSup_fidelityValueSet
      (a := a) (b := b) hKstack)

theorem dualEffectObjective_re_nonneg [Nonempty a]
    (ψ : PureVector (Prod (Prod a b) c)) {M : CMatrix (Prod a c)}
    (hM : State.ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    0 ≤ ((ψ.state.marginalAC.matrix * M).trace).re := by
  rw [ψ.dualEffectObjective_re_eq_card_mul_trace_transposeLink (a := a) (b := b)]
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card a)
  have hproj :=
    ψ.dualEffectTransposeLinkOutputABA_projector_trace_re_nonneg
      (a := a) (b := b) hM
  exact mul_nonneg hcard_nonneg hproj

theorem dualEffectObjective_le_card_mul_sSup_fidelityValueSet_of_scaled_le
    [Nonempty a] [Nonempty b]
    (ψ : PureVector (Prod (Prod a b) c)) (M : CMatrix (Prod a c))
    (σ : State b) {t : ℝ} (ht : 0 ≤ t)
    (hobj :
      ((ψ.state.marginalAC.matrix * M).trace).re = (Fintype.card a : ℝ) * t)
    (hle :
      (((t : ℝ) : ℂ) • ((State.maximallyMixed a).prod σ).matrix) ≤
        ψ.state.marginalAB.matrix) :
    ((ψ.state.marginalAC.matrix * M).trace).re ≤
      (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  let X : CMatrix (Prod a b) :=
    (((Real.sqrt t : ℝ) : ℂ) • ((State.maximallyMixed a).prod σ).matrix)
  have hfeas :
      State.ConditionalMaxFidelityBlockFeasible
        (a := a) ψ.state.marginalAB σ X := by
    exact State.ConditionalMaxFidelityBlockFeasible.of_scaled_le
      (a := a) (ρ := ψ.state.marginalAB) (σ := σ) ht hle
  have hval :
      State.conditionalMaxFidelityBlockExponentValue (a := a) X =
        (Fintype.card a : ℝ) * t := by
    simpa [X] using
      (State.ConditionalMaxFidelityBlockFeasible.of_scaled_le_blockExponentValue
        (a := a) (σ := σ) ht)
  have hmem :
      (Fintype.card a : ℝ) * t ∈
        ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet (a := a) := by
    refine ⟨σ, X, hfeas, ?_⟩
    exact hval.symm
  have hbdd :
      BddAbove
        (ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet (a := a)) :=
    ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet_bddAbove (a := a)
  calc
    ((ψ.state.marginalAC.matrix * M).trace).re =
        (Fintype.card a : ℝ) * t := hobj
    _ ≤ sSup (ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet
          (a := a)) := le_csSup hbdd hmem
    _ = (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
          rw [← State.card_mul_sSup_fidelityValueSet_eq_sSup_conditionalMaxFidelityBlockExponentValueSet
            (a := a) ψ.state.marginalAB]


theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_endpoint_scale
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hscale :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        ψ.state.marginalAC.conditionalMinEntropyScale (a := a)) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.state.marginalAB
    |>.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_card_mul_sSup_fidelity_eq_scale
      (a := a) ψ.state.marginalAC hscale

theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_endpoint_scale
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hscale :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        ψ.state.marginalAC.conditionalMinEntropyScale (a := a)) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_endpoint_scale
    (a := a) hscale

/-- Pure endpoint assembly after identifying the max-fidelity endpoint with
the min-entropy dual-effect endpoint.

This packages the conic strong-duality result
`conditionalMinEntropyScale_eq_sSup_dualEffectValueSet`: the only remaining
source-shaped pure-state obligation is the equality between the dual-effect
supremum and the fidelity supremum. -/
theorem card_mul_sSup_fidelityValueSet_eq_conditionalMinEntropyScale_marginalAC_of_dualEffect
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
      ψ.state.marginalAC.conditionalMinEntropyScale (a := a) := by
  rw [hdual]
  exact (State.conditionalMinEntropyScale_eq_sSup_dualEffectValueSet
    (a := a) ψ.state.marginalAC).symm

/-- Pure endpoint assembly from the single remaining SDP equality:
the block-SDP endpoint for the `AB` marginal equals the dual-effect endpoint
for the complementary `AC` marginal. -/
theorem card_mul_sSup_fidelityValueSet_eq_conditionalMinEntropyScale_marginalAC_of_blockDual
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual :
      sSup (ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet (a := a)) =
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
      ψ.state.marginalAC.conditionalMinEntropyScale (a := a) := by
  refine ψ.card_mul_sSup_fidelityValueSet_eq_conditionalMinEntropyScale_marginalAC_of_dualEffect
    (a := a) ?_
  rw [State.card_mul_sSup_fidelityValueSet_eq_sSup_conditionalMaxFidelityBlockExponentValueSet
    (a := a) ψ.state.marginalAB]
  exact hdual

/-- Endpoint min/max entropy duality once the pure-state dual-effect/fidelity
bridge is proved. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_endpoint_scale
    (a := a)
    (ψ.card_mul_sSup_fidelityValueSet_eq_conditionalMinEntropyScale_marginalAC_of_dualEffect
      (a := a) hdual)

theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect
    (a := a) hdual

/-- Endpoint min/max entropy duality once the pure-state block/dual-effect SDP
equality is proved. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockDual
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual :
      sSup (ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet (a := a)) =
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_endpoint_scale
    (a := a)
    (ψ.card_mul_sSup_fidelityValueSet_eq_conditionalMinEntropyScale_marginalAC_of_blockDual
      (a := a) hdual)

theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockDual
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual :
      sSup (ψ.state.marginalAB.conditionalMaxFidelityBlockExponentValueSet (a := a)) =
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockDual
    (a := a) hdual

theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_endpoint_bounds
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤ T.trace.re)
    (hreverse : ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        T.trace.re ≤
          (Fintype.card a : ℝ) *
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.state.marginalAB
    |>.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_fidelity_endpoint_bounds
      (a := a) ψ.state.marginalAC hforward hreverse

theorem conditionalMaxEntropyPositive_marginalAB_le_neg_conditionalMinEntropy_marginalAC_of_endpoint_forward_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤ T.trace.re) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive ≤
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.state.marginalAB
    |>.conditionalMaxEntropyPositive_le_neg_conditionalMinEntropy_of_cross_fidelity_forward_bound
      (a := a) ψ.state.marginalAC hforward

/-- Pure-state forward endpoint order bridge through the dual-effect SDP.

This is the source-faithful form for the remaining forward weak-duality
obligation: it is enough to lower-bound the dual-effect optimum by each
max-fidelity candidate.  The conic strong-duality theorem
`conditionalMinEntropyScale_eq_sSup_dualEffectValueSet` then converts that
dual-effect optimum into the min-entropy scale. -/
theorem conditionalMaxEntropyPositive_marginalAB_le_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hlower : ∀ σ : State b,
      (Fintype.card a : ℝ) *
        ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
          sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive ≤
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropyPositive_eq_log2_card_mul_sSup_fidelityValueSet
      (a := a),
    ψ.state.marginalAC.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hle_sup :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) ≤
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a)) := by
    have hcard_pos : 0 < (Fintype.card a : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    rw [← mul_sSup_image_eq
      (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet_nonempty (a := a))
      (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet_bddAbove (a := a)) hcard_pos]
    refine csSup_le ?_ ?_
    · exact Set.Nonempty.image _
        (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet_nonempty (a := a))
    · intro x hx
      rcases hx with ⟨y, ⟨σ, rfl⟩, rfl⟩
      exact hlower σ
  have hle :
      (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) ≤
        ψ.state.marginalAC.conditionalMinEntropyScale (a := a) := by
    rwa [ψ.state.marginalAC.conditionalMinEntropyScale_eq_sSup_dualEffectValueSet (a := a)]
  have hleft_pos :
      0 < (Fintype.card a : ℝ) *
          sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [← ψ.state.marginalAB.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
      (a := a)]
    exact ψ.state.marginalAB.conditionalMaxEntropyExponent_pos (a := a)
  have hscale_pos : 0 < ψ.state.marginalAC.conditionalMinEntropyScale (a := a) := by
    rw [ψ.state.marginalAC.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ψ.state.marginalAC.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  unfold log2
  simpa using div_le_div_of_nonneg_right (Real.log_le_log hleft_pos hle)
    (le_of_lt (Real.log_pos one_lt_two))

/-- It suffices to exhibit a concrete feasible dual effect for every
max-fidelity side state.  This is the most useful proof obligation for the
remaining pure endpoint forward bridge. -/
theorem dualEffect_lower_bound_of_exists_feasible_objective
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hexists : ∀ σ : State b, ∃ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M ∧
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            ((ψ.state.marginalAC.matrix * M).trace).re) :
    ∀ σ : State b,
      (Fintype.card a : ℝ) *
        ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
          sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a)) := by
  intro σ
  rcases hexists σ with ⟨M, hM, hleM⟩
  have hmem :
      ((ψ.state.marginalAC.matrix * M).trace).re ∈
        ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a) :=
    ⟨M, hM, rfl⟩
  have hle_sup :
      ((ψ.state.marginalAC.matrix * M).trace).re ≤
        sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a)) :=
    le_csSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet_bddAbove
      (a := a)) hmem
  exact hleM.trans hle_sup

/-- Endpoint equality from concrete feasible dual-effect witnesses for every
max-fidelity side state. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_exists_dualEffect_lower_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hexists : ∀ σ : State b, ∃ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M ∧
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            ((ψ.state.marginalAC.matrix * M).trace).re) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  le_antisymm
    (ψ.conditionalMaxEntropyPositive_marginalAB_le_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound
      (a := a)
      (ψ.dualEffect_lower_bound_of_exists_feasible_objective (a := a) hexists))
    (ψ.state.marginalAB
      |>.neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_dualEffect_bound
        (a := a) ψ.state.marginalAC
        (fun _ hM => ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet
          (a := a) (b := b) hM))

/-- Non-positive-candidate endpoint equality from concrete feasible dual-effect
witnesses. -/
theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_exists_dualEffect_lower_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hexists : ∀ σ : State b, ∃ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M ∧
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            ((ψ.state.marginalAC.matrix * M).trace).re) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_exists_dualEffect_lower_bound
    (a := a) hexists

/-- Pure complementary-marginal endpoint equality from the value-set forward
dual-effect lower bound and the already-proved reverse dual-effect upper
bound. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hlower : ∀ σ : State b,
      (Fintype.card a : ℝ) *
        ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
          sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  le_antisymm
    (ψ.conditionalMaxEntropyPositive_marginalAB_le_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound
      (a := a) hlower)
    (ψ.state.marginalAB
      |>.neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_dualEffect_bound
        (a := a) ψ.state.marginalAC
        (fun _ hM => ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet
          (a := a) (b := b) hM))

/-- Non-positive-candidate version of
`conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound`. -/
theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hlower : ∀ σ : State b,
      (Fintype.card a : ℝ) *
        ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
          sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_dualEffect_lower_bound
    (a := a) hlower

/-- Pure-state version of the strong pointwise side-operator reverse wrapper.

For the source-faithful endpoint SDP bridge, prefer
`neg_conditionalMinEntropy_marginalAC_le_conditionalMaxEntropyPositive_marginalAB_of_dualEffect_bound`. -/
theorem neg_conditionalMinEntropy_marginalAC_le_conditionalMaxEntropyPositive_marginalAB_of_endpoint_reverse_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hreverse : ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        T.trace.re ≤
          (Fintype.card a : ℝ) *
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    -ψ.state.marginalAC.conditionalMinEntropy ≤
      ψ.state.marginalAB.conditionalMaxEntropyPositive :=
  ψ.state.marginalAB
    |>.neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_fidelity_reverse_bound
      (a := a) ψ.state.marginalAC hreverse

/-- Pure-state reverse endpoint order bridge through the correct dual-effect
objective.

This is the normalized finite-dimensional form of the remaining endpoint
link-map obligation: for every `AC` dual effect `M`, bound
`Tr(ρ_AC M)` by the max-fidelity endpoint on the complementary `AB` marginal. -/
theorem neg_conditionalMinEntropy_marginalAC_le_conditionalMaxEntropyPositive_marginalAB_of_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual : ∀ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ψ.state.marginalAC.matrix * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    -ψ.state.marginalAC.conditionalMinEntropy ≤
      ψ.state.marginalAB.conditionalMaxEntropyPositive :=
  ψ.state.marginalAB
    |>.neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_dualEffect_bound
      (a := a) ψ.state.marginalAC hdual

theorem neg_conditionalMinEntropy_marginalAC_le_conditionalMaxEntropyPositive_marginalAB
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) :
    -ψ.state.marginalAC.conditionalMinEntropy ≤
      ψ.state.marginalAB.conditionalMaxEntropyPositive :=
  ψ.neg_conditionalMinEntropy_marginalAC_le_conditionalMaxEntropyPositive_marginalAB_of_dualEffect_bound
    (a := a)
    (fun _ hM => ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet
      (a := a) (b := b) hM)

/-- Pure-state value-set form of the reverse endpoint bound through dual
effects. -/
theorem sSup_conditionalMinEntropyDualEffectValueSet_marginalAC_le_card_mul_sSup_fidelityValueSet_marginalAB_of_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hdual : ∀ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ψ.state.marginalAC.matrix * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a)) ≤
      (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) :=
  ψ.state.marginalAB
    |>.sSup_conditionalMinEntropyDualEffectValueSet_le_card_mul_sSup_fidelityValueSet_of_dualEffect_bound
      (a := a) ψ.state.marginalAC hdual

theorem sSup_conditionalMinEntropyDualEffectValueSet_marginalAC_le_card_mul_sSup_fidelityValueSet_marginalAB
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) :
    sSup (ψ.state.marginalAC.conditionalMinEntropyDualEffectValueSet (a := a)) ≤
      (Fintype.card a : ℝ) *
        sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a)) :=
  ψ.sSup_conditionalMinEntropyDualEffectValueSet_marginalAC_le_card_mul_sSup_fidelityValueSet_marginalAB_of_dualEffect_bound
    (a := a)
    (fun _ hM => ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet
      (a := a) (b := b) hM)

/-- Pure complementary-marginal endpoint equality from the two correct
one-sided source obligations: a forward fidelity/scale bound and a reverse
dual-effect bound. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_fidelity_forward_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            T.trace.re)
    (hdual : ∀ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ψ.state.marginalAC.matrix * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.state.marginalAB
    |>.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_fidelity_forward_dualEffect_bound
      (a := a) ψ.state.marginalAC hforward hdual

theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_fidelity_forward_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            T.trace.re)
    (hdual : ∀ M : CMatrix (Prod a c),
      State.ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ψ.state.marginalAC.matrix * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ψ.state.marginalAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_fidelity_forward_dualEffect_bound
    (a := a) hforward hdual

/-- The user-facing block-SDP weak-duality statement follows immediately from
the fidelity forward bound, because every block-feasible `X` is bounded by the
corresponding fidelity candidate. -/
theorem blockFeasible_trace_bound_by_scaleFeasible_of_fidelity_forward_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            T.trace.re) :
    ∀ σ : State b, ∀ T : CMatrix c, ∀ X : CMatrix (Prod a b),
      State.ConditionalMaxFidelityBlockFeasible (a := a) ψ.state.marginalAB σ X →
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        State.conditionalMaxFidelityBlockExponentValue (a := a) X ≤ T.trace.re := by
  intro σ T X hX hT
  exact (hX.blockExponentValue_le_exponentCandidate (a := a)).trans (by
    rw [State.conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity]
    exact hforward σ T hT)

/-- A block-SDP trace bound implies the source-shaped fidelity forward bound.

This is the purely order-theoretic handoff from a future pointwise weak-duality
lemma for block feasible `X` to the fidelity value used in the conditional
max-entropy endpoint. -/
theorem fidelity_forward_bound_of_blockFeasible_trace_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hblock : ∀ σ : State b, ∀ T : CMatrix c, ∀ X : CMatrix (Prod a b),
      State.ConditionalMaxFidelityBlockFeasible (a := a) ψ.state.marginalAB σ X →
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        State.conditionalMaxFidelityBlockExponentValue (a := a) X ≤ T.trace.re) :
    ∀ σ : State b, ∀ T : CMatrix c,
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        (Fintype.card a : ℝ) *
          ψ.state.marginalAB.squaredFidelity ((State.maximallyMixed a).prod σ) ≤
            T.trace.re := by
  intro σ T hT
  rcases ψ.state.marginalAB.exists_ConditionalMaxFidelityBlockFeasible_trace_re_eq_fidelity
      (a := a) σ with ⟨X, hX, hval⟩
  have hle := hblock σ T X hX hT
  rw [State.conditionalMaxFidelityBlockExponentValue_eq] at hle
  rw [State.squaredFidelity_eq_fidelity_sq]
  have htrace :
      X.trace.re =
        ψ.state.marginalAB.fidelity ((State.maximallyMixed a).prod σ) := by
    simpa [State.conditionalMaxFidelityBlockValue] using hval
  simpa [htrace] using hle

/-- A block-SDP trace bound plus the already-proved dual-effect reverse bound
gives the endpoint positive max/min entropy equality for pure complementary
marginals.

The remaining mathematical work is exactly the block feasible trace bound
appearing as `hblock`; all value-set, logarithm and reverse-duality assembly is
handled here. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockFeasible_trace_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hblock : ∀ σ : State b, ∀ T : CMatrix c, ∀ X : CMatrix (Prod a b),
      State.ConditionalMaxFidelityBlockFeasible (a := a) ψ.state.marginalAB σ X →
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        State.conditionalMaxFidelityBlockExponentValue (a := a) X ≤ T.trace.re) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_fidelity_forward_dualEffect_bound
    (a := a)
    (ψ.fidelity_forward_bound_of_blockFeasible_trace_bound (a := a) hblock)
    (fun _ hM => ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet
      (a := a) (b := b) hM)

/-- Non-positive-candidate version of
`conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockFeasible_trace_bound`. -/
theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockFeasible_trace_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c))
    (hblock : ∀ σ : State b, ∀ T : CMatrix c, ∀ X : CMatrix (Prod a b),
      State.ConditionalMaxFidelityBlockFeasible (a := a) ψ.state.marginalAB σ X →
      State.ConditionalMinEntropyScaleFeasible (a := a) ψ.state.marginalAC T →
        State.conditionalMaxFidelityBlockExponentValue (a := a) X ≤ T.trace.re) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_blockFeasible_trace_bound
    (a := a) hblock

/-- Endpoint conditional min/max duality for normalized finite-dimensional
pure complementary marginals, in the positive-candidate convention for
conditional max-entropy. -/
theorem conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) :
    ψ.state.marginalAB.conditionalMaxEntropyPositive =
      -ψ.state.marginalAC.conditionalMinEntropy :=
  ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_fidelity_forward_dualEffect_bound
    (a := a)
    (fun σ T hT => ψ.fidelity_forward_bound_by_scaleFeasible (a := a) σ T hT)
    (fun _ hM => ψ.dualEffectObjective_le_card_mul_sSup_fidelityValueSet
      (a := a) (b := b) hM)

/-- Endpoint conditional min/max duality for normalized finite-dimensional
pure complementary marginals. -/
theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) :
    ψ.state.marginalAB.conditionalMaxEntropy =
      -ψ.state.marginalAC.conditionalMinEntropy := by
  rw [ψ.state.marginalAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ψ.conditionalMaxEntropyPositive_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
    (a := a)

end PureVector

namespace SubnormalizedState

variable {c : Type x} [Fintype c] [DecidableEq c]

/-- Explicit scaled-pure subnormalized endpoint duality, obtained by shifting
the normalized complementary-marginal equality through the common scale. -/
theorem conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_scaled_pure
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ψ : PureVector (Prod (Prod a b) c)) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (abMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
      ψ t ht.le ht1).conditionalMaxEntropyRaw =
      - (acMarginalFromScaledTripartitePure (a := a) (b := b) (c := c)
        ψ t ht.le ht1).conditionalMinEntropyRaw := by
  rw [abMarginalFromScaledTripartitePure, acMarginalFromScaledTripartitePure,
    conditionalMaxEntropy_ofStateScale (a := a) (b := b) ψ.state.marginalAB ht ht1,
    conditionalMinEntropy_ofStateScale (a := a) (b := c) ψ.state.marginalAC ht ht1]
  rw [PureVector.conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
    (a := a) (b := b) (c := c) ψ]
  ring

/-- Relation-level subnormalized unsmoothed min/max entropy duality on
complementary scaled-pure marginals. -/
theorem conditionalMinMaxEntropyDualOn_complementaryPureMarginals
    {a : Type u} {b : Type v} {c : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty a] [Nonempty b] [Nonempty c] :
    ConditionalMinMaxEntropyDualOn (a := a) (b := b) (c := c)
      (ComplementaryPureMarginalRel (a := a) (b := b) (c := c)) := by
  intro ρAB ρAC hrel
  rcases hrel with ⟨ψ, t, ht, ht1, hAB, hAC⟩
  rw [hAB, hAC]
  exact conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC_of_scaled_pure
    (a := a) (b := b) (c := c) ψ ht ht1

end SubnormalizedState

namespace State

/-- Unsmoothed conditional min/max entropy duality on complementary pure
marginals.

This is the relation-parametric `hdual` input required by the smooth
min/max-duality bridge in `QIT.OneShot.Smooth`. -/
theorem conditionalMinMaxEntropyDualOn_complementaryPureMarginals
    {a : Type u} {b : Type v} {c : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty a] [Nonempty b] [Nonempty c] :
    ConditionalMinMaxEntropyDualOn (a := a) (b := b) (c := c)
      (ComplementaryPureMarginalRel (a := a) (b := b) (c := c)) := by
  intro ρAB ρAC hrel
  rcases hrel with ⟨Ψ, hpur, hAC⟩
  let Ω : PureVector (Prod (Prod a b) c) :=
    Ψ.reindex (Equiv.prodComm c (Prod a b))
  have hAB : Ω.state.marginalAB = ρAB := by
    apply State.ext
    simpa [Ω, State.marginalAB_eq_marginalA, PureVector.reindex_state, State.reindex,
      State.marginalA, State.marginalB, partialTraceA, partialTraceB,
      PureVector.state_matrix, rankOneMatrix_apply] using hpur
  have hAC' : Ω.state.marginalAC = ρAC := by
    subst hAC
    apply State.ext
    ext ac ac'
    simp [Ω, acMarginalFromABPurification, State.marginalAC_matrix, State.marginalB_matrix,
      PureVector.reindex_state, State.reindex, partialTraceA,
      PureVector.state_matrix, rankOneMatrix_apply, abToACReferenceEquiv]
  rw [← hAB, ← hAC']
  exact PureVector.conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
    (a := a) (b := b) (c := c) Ω

/-- A normalized finite-dimensional conditional max-entropy is bounded below by
minus the logarithm of the conditioned register dimension. -/
theorem neg_log2_card_left_le_conditionalMaxEntropy
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    -log2 (Fintype.card a : ℝ) ≤ ρ.conditionalMaxEntropy := by
  obtain ⟨Ψ, hΨ⟩ :=
    State.exists_purification_on_reference_of_card_le
      (r := Prod a b) ρ (Nat.le_refl _)
  let Ω : PureVector (Prod (Prod a b) (Prod a b)) :=
    Ψ.reindex (Equiv.prodComm (Prod a b) (Prod a b))
  have hAB : Ω.state.marginalAB = ρ := by
    apply State.ext
    simpa [Ω, State.marginalAB_eq_marginalA, PureVector.reindex_state, State.reindex,
      State.marginalA, State.marginalB, partialTraceA, partialTraceB,
      PureVector.state_matrix, rankOneMatrix_apply] using hΨ
  have hdual :
      Ω.state.marginalAB.conditionalMaxEntropy =
        -Ω.state.marginalAC.conditionalMinEntropy :=
    PureVector.conditionalMaxEntropy_marginalAB_eq_neg_conditionalMinEntropy_marginalAC
      (a := a) (b := b) (c := Prod a b) Ω
  have hmin :
      Ω.state.marginalAC.conditionalMinEntropy ≤ log2 (Fintype.card a : ℝ) :=
    Ω.state.marginalAC.conditionalMinEntropy_le_log2_card_left
      (a := a) (b := Prod a b)
  rw [← hAB, hdual]
  exact neg_le_neg hmin

/-- Fuchs--van de Graaf converts an `ε` trace-distance bound into the
smoothing radius `sqrt (2ε - ε^2)`. -/
theorem purifiedDistance_le_sqrt_two_mul_sub_sq_of_normalizedTraceDistance_le
    (ρ σ : State a) {ε : ℝ}
    (hε1 : ε ≤ 1)
    (hD : ρ.normalizedTraceDistance σ ≤ ε) :
    ρ.purifiedDistance σ ≤ Real.sqrt (2 * ε - ε ^ 2) := by
  have hlower := State.fuchs_van_de_graaf_lower ρ σ
  have hfidelity_ge : 1 - ε ≤ ρ.fidelity σ := by
    linarith
  have hleft_nonneg : 0 ≤ 1 - ε := by linarith
  have hfid_nonneg : 0 ≤ ρ.fidelity σ := State.fidelity_nonneg ρ σ
  have hsquare_ge :
      (1 - ε) ^ 2 ≤ (ρ.fidelity σ) ^ 2 :=
    (sq_le_sq₀ hleft_nonneg hfid_nonneg).mpr hfidelity_ge
  have hinside :
      1 - ρ.squaredFidelity σ ≤ 2 * ε - ε ^ 2 := by
    rw [State.squaredFidelity_eq_fidelity_sq]
    nlinarith
  rw [State.purifiedDistance_eq]
  exact Real.sqrt_le_sqrt hinside

/-- Normalized smooth conditional min-entropy candidates are bounded above by
the logarithm of the conditioned register dimension. -/
theorem SmoothConditionalMinEntropyCandidate_bddAbove
    (ρ : State (Prod a b)) (ε : ℝ) :
    BddAbove {h : ℝ | State.SmoothConditionalMinEntropyCandidate (a := a) ρ ε h} := by
  refine ⟨log2 (Fintype.card a : ℝ), ?_⟩
  intro h hh
  rcases hh with ⟨ρ', _hball, rfl⟩
  rw [State.conditionalMinEntropy_eq]
  by_cases hne :
      ({lam : ℝ | ∃ τ : State b,
        ConditionalMinEntropyFeasible (a := a) ρ' τ lam}).Nonempty
  · exact csSup_le hne fun lam hlam =>
      let ⟨_, hτ⟩ := hlam
      conditionalMinEntropyFeasible_le_log2_card_left (a := a) hτ
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    haveI : Nonempty a := ⟨(Classical.choice ρ'.nonempty).1⟩
    have hcard_one : 1 ≤ (Fintype.card a : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr inferInstance))
    exact div_nonneg (Real.log_nonneg hcard_one)
      (le_of_lt (Real.log_pos one_lt_two))

/-- A smooth min-entropy candidate contributes a lower bound to the smooth
conditional min-entropy supremum. -/
theorem le_smoothConditionalMinEntropyNormalizedCandidates_of_candidate
    {ρ : State (Prod a b)} {ε h : ℝ}
    (hcand : State.SmoothConditionalMinEntropyCandidate (a := a) ρ ε h) :
    h ≤ ρ.smoothConditionalMinEntropyNormalizedCandidates ε := by
  rw [State.smoothConditionalMinEntropyNormalizedCandidates_eq_sSup_candidates]
  exact le_csSup (State.SmoothConditionalMinEntropyCandidate_bddAbove (a := a) ρ ε) hcand

end State
end

end QIT
