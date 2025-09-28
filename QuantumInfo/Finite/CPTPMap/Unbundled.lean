import QuantumInfo.Finite.CPTPMap.MatrixMap

/-! # Properties of Matrix Maps

Building on `MatrixMap`s, this defines the properties: `IsTracePreserving`, `Unital`,
`IsHermitianPreserving`, `IsPositive` and `IsCompletelyPositive`. They have basic facts
such as closure under composition, addition, and scaling.

These are the *unbundled* versions, which just state the relevant properties of a given `MatrixMap`.
The bundled versions are `HPMap`, `UnitalMap`, `TPMap`, `PMap`, and `CPMap` respectively, given
in Bundled.lean.
-/

namespace MatrixMap

section tp
variable [Fintype A] [DecidableEq A] [Fintype B] [Fintype C] [Semiring R]

/-- A linear matrix map is *trace preserving* if trace of the output equals trace of the input. -/
def IsTracePreserving (M : MatrixMap A B R) : Prop :=
  ∀ (x : Matrix A A R), (M x).trace = x.trace

namespace IsTracePreserving

variable {A : Type*} [Fintype A] in
/-- Simp lemma: the trace of the image of a IsTracePreserving map is the same as the original trace. -/
@[simp]
theorem apply_trace {M : MatrixMap A B R} (h : M.IsTracePreserving) (ρ : Matrix A A R)
    : (M ρ).trace = ρ.trace :=
  h ρ

variable {A : Type*} [Fintype A] in
/-- The composition of IsTracePreserving maps is also trace preserving. -/
theorem comp {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R} (h₁ : M₁.IsTracePreserving) (h₂ : M₂.IsTracePreserving) :
    IsTracePreserving (M₂ ∘ₗ M₁) := by
  intro x
  simp [h₂ _, h₁ _]

variable {A : Type*} [Fintype A] in
/-- The identity MatrixMap IsTracePreserving. -/
@[simp]
theorem id : (id A R).IsTracePreserving := by
  simp [IsTracePreserving, MatrixMap.id]

variable {A R : Type*} [CommSemiring R] [Fintype A] in
/-- Unit linear combinations of IsTracePreserving maps are IsTracePreserving. -/
theorem unit_linear {M₁ M₂ : MatrixMap A B R} {x y : R}
    (h₁ : M₁.IsTracePreserving) (h₂ : M₂.IsTracePreserving) (hxy : x + y = 1) :
    (x • M₁ + y • M₂).IsTracePreserving := by
  rw [IsTracePreserving] at h₁ h₂ ⊢
  simp [h₁, h₂, ← add_mul, hxy]

variable {D R : Type*} [CommSemiring R] [DecidableEq C] [Fintype D] in
/-- The kronecker product of IsTracePreserving maps is also trace preserving. -/
theorem kron {M₁ : MatrixMap A B R} {M₂ : MatrixMap C D R} (h₁ : M₁.IsTracePreserving) (h₂ : M₂.IsTracePreserving) :
    (M₁ ⊗ₖₘ M₂).IsTracePreserving := by
  unfold MatrixMap.kron
  intro x
  simp
  sorry

variable [CommSemiring S] [Star S] [SMulCommClass S S S] in
/-- The channel X ↦ ∑ k : κ, (M k) * X * (N k)ᴴ formed by Kraus operators M, N : κ → Matrix B A R
is trace-preserving if ∑ k : κ, (N k)ᴴ * (M k) = 1 -/
theorem of_kraus_isTracePreserving {κ : Type*} [Fintype κ]
  (M N : κ → Matrix B A S)
  (hTP : (∑ k, (N k).conjTranspose * (M k)) = 1) :
  (MatrixMap.of_kraus M N).IsTracePreserving := by
  intro x
  simp only [of_kraus, LinearMap.coeFn_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Matrix.trace_sum]
  conv =>
    enter [1,2,i]
    rw [Matrix.trace_mul_cycle (M i) x (N i).conjTranspose]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hTP, one_mul]

end IsTracePreserving
end tp


section unital

variable [DecidableEq A] [DecidableEq B] [Semiring R]

/-- A linear matrix map is *unital* if it preserves the identity. -/
def Unital (M : MatrixMap A B R) : Prop :=
  M 1 = 1

namespace Unital

variable {M : MatrixMap A B R}

@[simp]
theorem map_1 (h : M.Unital) : M 1 = 1 :=
  h

/-- The identity `MatrixMap` is `Unital`. -/
@[simp]
theorem id : (id A R).Unital := by
  simp [Unital, MatrixMap.id]

--TODO: Closed under composition, kronecker products, it's iff M.choi_matrix.traceLeft = 1...

end Unital
end unital

variable {A B C R : Type*}

open Kronecker
open TensorProduct

open ComplexOrder
variable [RCLike R]

/-- A linear matrix map is *Hermitian preserving* if it maps `IsHermitian` matrices to `IsHermitian`.-/
def IsHermitianPreserving (M : MatrixMap A B R) : Prop :=
  ∀{x}, x.IsHermitian → (M x).IsHermitian

/-- A linear matrix map is *positive* if it maps `PosSemidef` matrices to `PosSemidef`.-/
def IsPositive [Fintype A] [Fintype B] (M : MatrixMap A B R) : Prop :=
  ∀{x}, x.PosSemidef → (M x).PosSemidef

/-- A linear matrix map is *completely positive* if, for any integer n, the tensor product
with `I(n)` is positive. -/
def IsCompletelyPositive [Fintype A] [Fintype B] [DecidableEq A] (M : MatrixMap A B R) : Prop :=
  ∀ (n : ℕ), (M ⊗ₖₘ (LinearMap.id : MatrixMap (Fin n) (Fin n) R)).IsPositive

namespace IsHermitianPreserving

variable {A : Type*} [Fintype A] in
/-- The identity MatrixMap IsHermitianPreserving. -/
theorem id : (id A R).IsPositive :=
  _root_.id

/-- The composition of IsHermitianPreserving maps is also Hermitian preserving. -/
theorem comp {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R}
    (h₁ : M₁.IsHermitianPreserving) (h₂ : M₂.IsHermitianPreserving) : IsHermitianPreserving (M₂ ∘ₗ M₁) :=
  fun h ↦ h₂ (h₁ h)

end IsHermitianPreserving

namespace IsPositive
variable [Fintype A] [Fintype B] [Fintype C]

/- Every `MatrixMap` that `IsPositive` is also `IsHermitianPreserving`. -/
theorem IsHermitianPreserving {M : MatrixMap A B R}
    (hM : IsPositive M) : IsHermitianPreserving M := by
  intro x hx
  let xH : HermitianMat _ _ := ⟨x, hx⟩
  classical --because PosPart requires DecidableEq
  have hMPos := hM (HermitianMat.zero_le_iff.mp xH.zero_le_posPart)
  have hMNeg := hM (HermitianMat.zero_le_iff.mp xH.negPart_le_zero)
  have hSub := hMPos.isHermitian.sub hMNeg.isHermitian
  rw [← map_sub] at hSub
  convert ← hSub
  exact HermitianMat.ext_iff.1 (HermitianMat.posPart_add_negPart xH)

/-- The composition of IsPositive maps is also positive. -/
theorem comp {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R} (h₁ : M₁.IsPositive)
    (h₂ : M₂.IsPositive) : IsPositive (M₂ ∘ₗ M₁) :=
  fun h ↦ h₂ (h₁ h)

variable {A : Type*} [Fintype A] in
/-- The identity MatrixMap IsPositive. -/
@[simp]
theorem id : (id A R).IsPositive :=
  _root_.id

/-- Sums of IsPositive maps are IsPositive. -/
theorem add {M₁ M₂ : MatrixMap A B R} (h₁ : M₁.IsPositive) (h₂ : M₂.IsPositive) :
    (M₁ + M₂).IsPositive :=
  fun x ↦ Matrix.PosSemidef.add (h₁ x) (h₂ x)

/-- Nonnegative scalings of IsPositive maps are IsPositive. -/
theorem smul {M : MatrixMap A B R} (hM : M.IsPositive) {x : R} (hx : 0 ≤ x) :
    (x • M).IsPositive :=
  fun hm ↦ (hM hm).smul hx

end IsPositive

namespace IsCompletelyPositive
variable [Fintype A] [Fintype B] [Fintype C] [DecidableEq A]

/- Every `MatrixMap` that `IsCompletelyPositive` also `IsPositiveMap`. -/
theorem IsPositive [DecidableEq A] {M : MatrixMap A B R}
    (hM : IsCompletelyPositive M) : IsPositive M := by
  intro x hx
  let x' : Matrix (A × Fin 1) (A × Fin 1) R := x ⊗ₖ 1
  let eqA : (A × Fin 1) ≃ A :=
    (Equiv.prodCongrRight (fun _ ↦ finOneEquiv)).trans (Equiv.prodPUnit A)
  let eqB : (B × Fin 1) ≃ B :=
    (Equiv.prodCongrRight (fun _ ↦ finOneEquiv)).trans (Equiv.prodPUnit B)
  specialize @hM 1 (x.submatrix eqA eqA) (Matrix.PosSemidef.submatrix hx _)
  replace hM := Matrix.PosSemidef.submatrix hM eqB.symm
  convert hM
  sorry

/-- The composition of IsCompletelyPositive maps is also completely positive. -/
theorem comp [DecidableEq B] {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R} (h₁ : M₁.IsCompletelyPositive)
    (h₂ : M₂.IsCompletelyPositive) : IsCompletelyPositive (M₂ ∘ₗ M₁) := by
  --sketch: (M₂ ∘ₗ M₁) ⊗ₖₘ id[n] = (M₂ ⊗ₖₘ id[n]) ∘ₗ (M₁ ⊗ₖₘ id[n]), which is a composition of positive maps.
  intro n x hx
  specialize h₁ n hx
  specialize h₂ n h₁
  conv in LinearMap.id =>
    change LinearMap.id ∘ₗ LinearMap.id
  rw [kron_comp_distrib]
  simpa using h₂

/-- The identity MatrixMap IsCompletelyPositive. -/
@[simp]
theorem id : (id A R).IsCompletelyPositive := by
  intro n ρ h
  rwa [show LinearMap.id = MatrixMap.id (Fin n) R from rfl, kron_id_id]

/-- Sums of IsCompletelyPositive maps are IsCompletelyPositive. -/
theorem add {M₁ M₂ : MatrixMap A B R} (h₁ : M₁.IsCompletelyPositive) (h₂ : M₂.IsCompletelyPositive) :
    (M₁ + M₂).IsCompletelyPositive :=
  fun n _ h ↦ by
  simpa only [add_kron] using Matrix.PosSemidef.add (h₁ n h) (h₂ n h)

/-- Nonnegative scalings of `IsCompletelyPositive` maps are `IsCompletelyPositive`. -/
theorem smul {M : MatrixMap A B R} (hM : M.IsCompletelyPositive) {x : R} (hx : 0 ≤ x) :
    (x • M).IsCompletelyPositive :=
  fun n ρ h ↦ by
    rw [MatrixMap.smul_kron]
    exact (hM n h).smul hx

variable (A B) in
/-- The zero map `IsCompletelyPositive`. -/
theorem zero : (0 : MatrixMap A B R).IsCompletelyPositive :=
  fun _ _ _ ↦ by simpa using Matrix.PosSemidef.zero

/-- A finite sum of completely positive maps is completely positive. -/
theorem finset_sum {ι : Type*} [Fintype ι] {m : ι → MatrixMap A B R} (hm : ∀ i, (m i).IsCompletelyPositive) :
    (∑ i, m i).IsCompletelyPositive :=
  Finset.sum_induction m _ (fun _ _ ↦ add) (.zero A B) (by simpa)

variable [Fintype d] [DecidableEq d]
/-- The map that takes M and returns M ⊗ₖ C, where C is positive semidefinite, is a completely positive map. -/
theorem kron_kronecker_const {C : Matrix d d R} (h : C.PosSemidef) {h₁ h₂ : _} : MatrixMap.IsCompletelyPositive
    (⟨⟨fun M => M ⊗ₖ C, h₁⟩, h₂⟩ : MatrixMap A (A × d) R) := by
  sorry

/-- The act of conjugating (not necessarily by a unitary, just by any matrix at all) is completely positive. -/
theorem conj_isCompletelyPositive (M : Matrix B A R) :
  IsCompletelyPositive {
    toFun := fun (x : Matrix A A R) ↦ M * x * M.conjTranspose,
    map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
    map_smul' r x := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
  } := by
  sorry

/-- The channel X ↦ ∑ k : κ, (M k) * X * (M k)ᴴ formed by Kraus operators M : κ → Matrix B A R
is completely positive -/
theorem of_kraus_isCompletelyPositive {κ : Type*} [Fintype κ] (M : κ → Matrix B A R) :
    (MatrixMap.of_kraus M M).IsCompletelyPositive := by
  rw [of_kraus]
  exact finset_sum (fun i ↦ conj_isCompletelyPositive (M i))

def exists_kraus (Φ : MatrixMap A B R) (hCP : Φ.IsCompletelyPositive) :
    ∃ r : ℕ, ∃ (M : Fin r → Matrix B A R), Φ = of_kraus M M :=
  sorry

end IsCompletelyPositive

end MatrixMap
