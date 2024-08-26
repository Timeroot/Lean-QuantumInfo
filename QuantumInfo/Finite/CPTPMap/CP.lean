import QuantumInfo.Finite.CPTPMap.MatrixMap

/-! # Completely Positive maps

Building on `MatrixMap`s, this defines `IsHermitianPreserving`, `IsPositive`
and `IsCompletelyPositive` maps. They have basic facts such as closure under composition,
addition, and scaling.

-/

namespace MatrixMap

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
theorem IsHermitianPreserving (M : MatrixMap A B R)
    (hM : IsPositive M) : IsHermitianPreserving M := by
--sketch: Positive maps are all Hermitian preserving, because positive matrices generate the full
--set of Hermitian matrices (generate as a vector space). Concretely, every pair of elements
-- (i,j) and (j,i) must be conjugate because we can look at the PSD matrices with 1's on (i,i),
-- on (j,j), and on all 4 elements (i or j, i or j).
  sorry

/-- The composition of IsPositive maps is also positive. -/
theorem comp {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R} (h₁ : M₁.IsPositive)
    (h₂ : M₂.IsPositive) : IsPositive (M₂ ∘ₗ M₁) :=
  fun h ↦ h₂ (h₁ h)

variable {A : Type*} [Fintype A] in
/-- The identity MatrixMap IsPositive. -/
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

/-- Definition of a CP map, but with `Fintype T` in the definition instead of a `Fin n`. -/
theorem def_Fintype  {M : MatrixMap A B R} (h : IsCompletelyPositive M)
    (T : Type*) [Fintype T] [DecidableEq T] :
    (M.kron (LinearMap.id : MatrixMap T T R)).IsPositive := by
  sorry

/- Every `MatrixMap` that `IsCompletelyPositive` also `IsPositiveMap`. -/
theorem IsPositive [DecidableEq A] {M : MatrixMap A B R}
    (hM : IsCompletelyPositive M) : IsPositive M := by
  intro x hx
  let x' : Matrix (A × Fin 1) (A × Fin 1) R := x ⊗ₖ 1
  let eqB : (B × Fin 1) ≃ B :=
    (Equiv.prodCongrRight (fun _ ↦ finOneEquiv)).trans (Equiv.prodPUnit B)
  sorry

/-- The composition of IsCompletelyPositive maps is also completely positive. -/
theorem comp [DecidableEq B] {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R} (h₁ : M₁.IsCompletelyPositive)
    (h₂ : M₂.IsCompletelyPositive) : IsCompletelyPositive (M₂ ∘ₗ M₁) := by
--sketch: (M₂ ∘ₗ M₁) ⊗ₖₘ id[n] = (M₂ ⊗ₖₘ id[n]) ∘ₗ (M₁ ⊗ₖₘ id[n]), which is a composition of positive maps.
  sorry

/-- The identity MatrixMap IsCompletelyPositive. -/
theorem id : (id A R).IsCompletelyPositive := by
  intro n ρ h
  rwa [show LinearMap.id = MatrixMap.id (Fin n) R from rfl, kron_id_id]

/-- Sums of IsCompletelyPositive maps are IsCompletelyPositive. -/
theorem add {M₁ M₂ : MatrixMap A B R} (h₁ : M₁.IsCompletelyPositive) (h₂ : M₂.IsCompletelyPositive) :
    (M₁ + M₂).IsCompletelyPositive :=
  fun n _ h ↦ by
  simpa only [add_kron] using Matrix.PosSemidef.add (h₁ n h) (h₂ n h)

/-- Nonnegative scalings of IsPositive maps are IsPositive. -/
theorem smul {M : MatrixMap A B R} (hM : M.IsCompletelyPositive) {x : R} (hx : 0 ≤ x) :
    (x • M).IsCompletelyPositive := by
  sorry

/-- Choi's theorem on completely positive maps: A map `IsCompletelyPositive` iff its Choi Matrix is PSD. -/
theorem _root_.MatrixMap.choi_PSD_iff_CP_map [DecidableEq A] (M : MatrixMap A B ℂ) :
    M.IsCompletelyPositive ↔ M.choi_matrix.PosSemidef :=
  sorry

/-- The Kronecker product of IsCompletelyPositive maps is also completely positive. -/
theorem kron [DecidableEq C] [Fintype D] {M₁ : MatrixMap A B R} {M₂ : MatrixMap C D R}
    (h₁ : M₁.IsCompletelyPositive) (h₂ : M₂.IsCompletelyPositive) : IsCompletelyPositive (M₁ ⊗ₖₘ M₂) := by
--sketch: the Choi matrix of the Kron is the Kron of the Choi matrix, and Kron of PSD matrices is PSD.
/-
      intro n M hM
      let M' : Matrix (dI₁ × (dI₂ × Fin n)) (dI₁ × (dI₂ × Fin n)) ℂ := sorry --reorder indices of M
      have hM' : M'.PosSemidef := sorry --PSD preserved under reordering
      let Λ₁M := ((Λ₁.map.kron LinearMap.id) M')
      have hΛ₁M : Λ₁M.PosSemidef := Λ₁.completely_pos.def_Fintype (dI₂ × Fin n) hM'
      let Λ₁M' : Matrix (dI₂ × (dO₁ × Fin n)) (dI₂ × (dO₁ × Fin n)) ℂ := sorry --reorder Λ₁M
      have hΛ₁M' : Λ₁M'.PosSemidef := sorry --PSD preserved under reordering
      let Λ₂Λ₁M := (Λ₂.map.kron LinearMap.id) Λ₁M'
      have hΛ₂Λ₁M : Λ₂Λ₁M.PosSemidef := Λ₂.completely_pos.def_Fintype (dO₁ × Fin n) hΛ₁M'
      --PSD preserved under reordering to get (((Λ₁.map.MatrixMap_Prod Λ₂.map).MatrixMap_Prod LinearMap.id) M)
      sorry
      -/
  sorry

section piKron

variable {ι : Type u} [DecidableEq ι] [fι : Fintype ι]
variable {dI : ι → Type v} [∀i, Fintype (dI i)] [∀i, DecidableEq (dI i)]
variable {dO : ι → Type w} [∀i, Fintype (dO i)] [∀i, DecidableEq (dO i)]

/-- The `piKron` product of IsCompletelyPositive maps is also completely positive. -/
theorem piKron {Λi : ∀ i, MatrixMap (dI i) (dO i) R} (h₁ : ∀ i, (Λi i).IsCompletelyPositive) :
    IsCompletelyPositive (MatrixMap.piKron Λi) := by
  sorry

end piKron

end IsCompletelyPositive


end MatrixMap
