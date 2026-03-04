/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap.Bundled
import QuantumInfo.Finite.Unitary

/-! # Completely Positive Trace Preserving maps

A `CPTPMap` is a `ℂ`-linear map between matrices (`MatrixMap` is an alias), bundled with the facts that it
`IsCompletelyPositive` and `IsTracePreserving`. CPTP maps are typically regarded as the "most general
quantum operation", as they map density matrices (`MState`s) to density matrices. The type `PTPMap`,
for maps that are positive (but not necessarily completely positive) is also declared.

A large portion of the theory is in terms of the Choi matrix (`MatrixMap.choi_matrix`), as the
positive-definiteness of this matrix corresponds to being a CP map. This is
[Choi's theorem on CP maps](https://en.wikipedia.org/wiki/Choi%27s_theorem_on_completely_positive_maps).

This file also defines several important examples of, classes of, and operations on, CPTPMaps:
 * `compose`: Composition of maps
 * `id`: The identity map
 * `replacement`: The replacement channel that always outputs the same state
 * `prod`: Tensor product of two CPTP maps, with notation M₁ ⊗ M₂
 * `piProd`: Tensor product of finitely many CPTP maps (Pi-type product)
 * `of_unitary`: The CPTP map corresponding to a unitary opeation `U`
 * `IsUnitary`: Predicate whether the map corresponds to any unitary
 * `purify`: Purifying a channel into a unitary on a larger Hilbert space
 * `complementary`: The complementary channel to its purification
 * `IsEntanglementBreaking`, `IsDegradable`, `IsAntidegradable`: Entanglement breaking, degradable
    and antidegradable channels.
 * `SWAP`, `assoc`, `assoc'`, `traceLeft`, `traceRight`: The CPTP maps corresponding to important
    operations on states. These correspond directly to `MState.SWAP`, `MState.assoc`, `MState.assoc'`,
    `MState.traceLeft`, and `MState.traceRight`.
-/

variable {dIn dOut dOut₂ : Type*} [Fintype dIn] [Fintype dOut] [Fintype dOut₂]

namespace CPTPMap
noncomputable section
open scoped Matrix ComplexOrder

variable [DecidableEq dIn]

variable {dM : Type*} [Fintype dM] [DecidableEq dM]
variable {dM₂ : Type*} [Fintype dM₂] [DecidableEq dM₂]
variable (Λ : CPTPMap dIn dOut)

/-- The Choi matrix of a CPTPMap. -/
@[reducible]
def choi := Λ.map.choi_matrix

/-- Two CPTPMaps are equal if their Choi matrices are equal. -/
theorem choi_ext {Λ₁ Λ₂ : CPTPMap dIn dOut} (h : Λ₁.choi = Λ₂.choi) : Λ₁ = Λ₂ := by
  ext1
  exact MatrixMap.choi_equiv.injective h

/-- The Choi matrix of a channel is PSD. -/
theorem choi_PSD_of_CPTP : Λ.map.choi_matrix.PosSemidef :=
  Λ.map.choi_PSD_iff_CP_map.1 Λ.cp

/-- The trace of a Choi matrix of a CPTP map is the cardinality of the input space. -/
@[simp]
theorem Tr_of_choi_of_CPTP : Λ.choi.trace =
    (Finset.univ (α := dIn)).card :=
  Λ.TP.trace_choi

/-- Construct a CPTP map from a PSD Choi matrix with correct partial trace. -/
def CPTP_of_choi_PSD_Tr {M : Matrix (dOut × dIn) (dOut × dIn) ℂ} (h₁ : M.PosSemidef)
    (h₂ : M.traceLeft = 1) : CPTPMap dIn dOut where
  toLinearMap := MatrixMap.of_choi_matrix M
  cp := (MatrixMap.choi_PSD_iff_CP_map (MatrixMap.of_choi_matrix M)).2
      ((MatrixMap.map_choi_inv M).symm ▸ h₁)
  TP := (MatrixMap.of_choi_matrix M).IsTracePreserving_iff_trace_choi.2
    ((MatrixMap.map_choi_inv M).symm ▸ h₂)

@[simp]
theorem choi_of_CPTP_of_choi (M : Matrix (dOut × dIn) (dOut × dIn) ℂ) {h₁} {h₂} :
    (CPTP_of_choi_PSD_Tr (M := M) h₁ h₂).choi = M := by
  simp only [choi, CPTP_of_choi_PSD_Tr]
  rw [MatrixMap.map_choi_inv]

theorem mat_coe_eq_apply_mat [DecidableEq dOut] (ρ : MState dIn) : (Λ ρ).m = Λ.map ρ.m :=
  rfl

@[ext]
theorem funext [DecidableEq dOut] {Λ₁ Λ₂ : CPTPMap dIn dOut} (h : ∀ ρ, Λ₁ ρ = Λ₂ ρ) : Λ₁ = Λ₂ :=
  DFunLike.ext _ _ h

/-- The composition of CPTPMaps, as a CPTPMap. -/
def compose (Λ₂ : CPTPMap dM dOut) (Λ₁ : CPTPMap dIn dM) : CPTPMap dIn dOut where
  toLinearMap := Λ₂.map ∘ₗ Λ₁.map
  cp := Λ₁.cp.comp Λ₂.cp
  TP := Λ₁.TP.comp Λ₂.TP

infixl:75 "∘ₘ" => CPTPMap.compose

/-- Composition of CPTPMaps by `CPTPMap.compose` is compatible with the `instFunLike` action. -/
@[simp]
theorem compose_eq [DecidableEq dOut] {Λ₁ : CPTPMap dIn dM} {Λ₂ : CPTPMap dM dOut} : ∀ρ, (Λ₂ ∘ₘ Λ₁) ρ = Λ₂ (Λ₁ ρ) :=
  fun _ ↦ rfl

/-- Composition of CPTPMaps is associative. -/
theorem compose_assoc [DecidableEq dOut] (Λ₃ : CPTPMap dM₂ dOut) (Λ₂ : CPTPMap dM dM₂)
    (Λ₁ : CPTPMap dIn dM) : (Λ₃ ∘ₘ Λ₂) ∘ₘ Λ₁ = Λ₃ ∘ₘ (Λ₂ ∘ₘ Λ₁) := by
  ext1 ρ
  simp

/-- CPTPMaps have a convex structure from their Choi matrices. -/
instance instMixable : Mixable (Matrix (dOut × dIn) (dOut × dIn) ℂ) (CPTPMap dIn dOut) where
  to_U := CPTPMap.choi
  to_U_inj := choi_ext
  mkT {u} h := ⟨CPTP_of_choi_PSD_Tr (M := u)
    (Exists.recOn h fun t ht => ht ▸ t.choi_PSD_of_CPTP)
    (Exists.recOn h fun t ht => (by
      rw [← ht, ← MatrixMap.IsTracePreserving_iff_trace_choi]
      exact t.TP)),
    by apply choi_of_CPTP_of_choi⟩
  convex := by
    have h_convex : ∀ (M₁ M₂ : Matrix (dOut × dIn) (dOut × dIn) ℂ), M₁.PosSemidef → M₂.PosSemidef → ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → (t • M₁ + (1 - t) • M₂).PosSemidef := by
      intro M₁ M₂ h₁ h₂ t ht₁ ht₂;
      convert Matrix.PosSemidef.add ( h₁.smul ht₁ ) ( h₂.smul ( sub_nonneg.mpr ht₂ ) ) using 1;
    intro M hM N hN a b ha hb hab;
    obtain ⟨Λ₁, hΛ₁⟩ := hM
    obtain ⟨Λ₂, hΛ₂⟩ := hN;
    obtain ⟨Λ, hΛ⟩ : ∃ Λ : MatrixMap dIn dOut ℂ, (a • M + b • N).traceLeft = 1 ∧ (a • M + b • N).PosSemidef ∧ Λ = MatrixMap.of_choi_matrix (a • M + b • N) := by
      refine ⟨_, ?_, ?_, rfl⟩
      · have h_trace_M : M.traceLeft = 1 := by
          convert Λ₁.TP using 1;
          rw [ ← hΛ₁, MatrixMap.IsTracePreserving_iff_trace_choi ]
        have h_trace_N : N.traceLeft = 1 := by
          convert Λ₂.map.IsTracePreserving_iff_trace_choi.1 Λ₂.TP;
          exact hΛ₂.symm;
        convert congr_arg₂ ( fun x y : Matrix dIn dIn ℂ => a • x + b • y ) h_trace_M h_trace_N using 1;
        · ext i j
          simp [ Matrix.traceLeft ]
          simp only [Finset.sum_add_distrib, Finset.mul_sum _ _ _];
        · rw [ ← add_smul, hab, one_smul ];
      · convert h_convex M N ( by simpa [ ← hΛ₁ ] using Λ₁.choi_PSD_of_CPTP ) ( by simpa [ ← hΛ₂ ] using Λ₂.choi_PSD_of_CPTP ) a ha ( by linarith ) using 1 ; rw [ ← hab ]
        ring_nf
    use CPTP_of_choi_PSD_Tr hΛ.2.1 hΛ.1;
    exact MatrixMap.map_choi_inv (a • M + b • N)

/-- The identity channel, which leaves the input unchanged. -/
def id : CPTPMap dIn dIn where
  toLinearMap := .id
  cp := .id
  TP := .id

/-- The map `CPTPMap.id` leaves any matrix unchanged. -/
@[simp]
theorem id_map : (id (dIn := dIn)).map = LinearMap.id := by
  rfl

/-- The map `CPTPMap.id` leaves the input state unchanged. -/
@[simp]
theorem id_MState (ρ : MState dIn) : CPTPMap.id (dIn := dIn) ρ = ρ := by
  apply MState.ext_m
  rw [mat_coe_eq_apply_mat]
  simp

/-- The map `CPTPMap.id` composed with any map is the same map. -/
@[simp]
theorem id_compose [DecidableEq dOut] (Λ : CPTPMap dIn dOut) : id ∘ₘ Λ = Λ := by
  apply funext
  simp

/-- Any map composed with `CPTPMap.id` is the same map. -/
@[simp]
theorem compose_id (Λ : CPTPMap dIn dOut) : Λ ∘ₘ id = Λ := by
  classical ext1
  simp

section equiv
variable [DecidableEq dOut]

/-- Given a equivalence (a bijection) between the types d₁ and d₂, that is, if they're
 the same dimension, then there's a CPTP channel for this. This is what we need for
 defining e.g. the SWAP channel, which is 'unitary' but takes heterogeneous input
 and outputs types (d₁ × d₂) and (d₂ × d₁). -/
def ofEquiv (σ : dIn ≃ dOut) : CPTPMap dIn dOut where
  toLinearMap := MatrixMap.submatrix ℂ σ.symm
  cp := .submatrix σ.symm
  TP x := by rw [MatrixMap.IsTracePreserving.submatrix]

@[simp]
theorem ofEquiv_apply (σ : dIn ≃ dOut) (ρ : MState dIn) :
    ofEquiv σ ρ = ρ.relabel σ.symm := by
  rfl

@[simp]
theorem equiv_inverse (σ : dIn ≃ dOut)  : (ofEquiv σ) ∘ (ofEquiv σ.symm) = id (dIn := dOut) := by
  ext1; simp

variable {d₁ d₂ d₃ : Type*} [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]

--TODO: of_equiv (id) = id
--(of_equiv σ).compose (of_equiv τ) = of_equiv (σ ∘ τ)

/-- The SWAP operation, as a channel. -/
def SWAP : CPTPMap (d₁ × d₂) (d₂ × d₁) :=
  ofEquiv (Equiv.prodComm d₁ d₂)

/-- The associator, as a channel. -/
def assoc : CPTPMap ((d₁ × d₂) × d₃) (d₁ × d₂ × d₃) :=
  ofEquiv (Equiv.prodAssoc d₁ d₂ d₃)

/-- The inverse associator, as a channel. -/
def assoc' : CPTPMap (d₁ × d₂ × d₃) ((d₁ × d₂) × d₃) :=
  ofEquiv (Equiv.prodAssoc d₁ d₂ d₃).symm

@[simp]
theorem SWAP_eq_MState_SWAP (ρ : MState (d₁ × d₂)) : SWAP (d₁ := d₁) (d₂ := d₂) ρ = ρ.SWAP :=
  rfl

@[simp]
theorem assoc_eq_MState_assoc (ρ : MState ((d₁ × d₂) × d₃)) : assoc (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) ρ = ρ.assoc :=
  rfl

@[simp]
theorem assoc'_eq_MState_assoc' (ρ : MState (d₁ × d₂ × d₃)) : assoc' (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) ρ = ρ.assoc' :=
  rfl

@[simp]
theorem assoc_assoc' : (assoc (d₁ := d₁) (d₂ := d₂) (d₃ := d₃)) ∘ₘ assoc' = id := by
  ext1 ρ
  simp

end equiv

section trace
variable {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]

/-- Partial tracing out the left, as a CPTP map. -/
@[simps]
def traceLeft : CPTPMap (d₁ × d₂) d₂ :=
    --TODO: make Matrix.traceLeft a linear map, a `MatrixMap`.
  letI f (d) [Fintype d] [DecidableEq d]: Matrix (d₁ × d) (d₁ × d) ℂ →ₗ[ℂ] Matrix d d ℂ := {
    toFun x := Matrix.traceLeft x
    map_add' := by
      intros; ext
      simp [Matrix.traceLeft, Finset.sum_add_distrib]
    map_smul' := by
      intros; ext
      simp [Matrix.traceLeft, Finset.mul_sum]
  }
  {
    toLinearMap := f d₂
    TP := by intro; simp [f]
    cp := by
      --(traceLeft ⊗ₖₘ I) = traceLeft ∘ₘ (ofEquiv prod_assoc)
      --Both go (A × B) × C → B × C
      --So then it suffices to show both are positive, and we have PosSemidef.traceLeft already.
      intro n
      classical
      suffices MatrixMap.IsPositive
          (f (d₂ × Fin n) ∘ₗ (MatrixMap.submatrix ℂ (Equiv.prodAssoc d₁ d₂ (Fin n)).symm)) by
        convert this
        ext
        rw [MatrixMap.kron_def]
        simp [f, Matrix.submatrix, Matrix.single, ite_and, Matrix.traceLeft, Fintype.sum_prod_type]
      apply MatrixMap.IsPositive.comp
      · exact (MatrixMap.IsCompletelyPositive.submatrix _).IsPositive
      · intro x h
        exact h.traceLeft
  }

/-- Partial tracing out the right, as a CPTP map. -/
def traceRight : CPTPMap (d₁ × d₂) d₁ :=
  traceLeft ∘ₘ SWAP

@[simp]
theorem traceLeft_eq_MState_traceLeft (ρ : MState (d₁ × d₂)) :
    traceLeft (d₁ := d₁) (d₂ := d₂) ρ = ρ.traceLeft := by
  rfl

@[simp]
theorem traceRight_eq_MState_traceRight (ρ : MState (d₁ × d₂)) :
    traceRight (d₁ := d₁) (d₂ := d₂) ρ = ρ.traceRight := by
  rfl --It's actually pretty crazy that this is a definitional equality, cool

end trace

/--The replacement channel that maps all inputs to a given state. -/
def replacement [Nonempty dIn] [DecidableEq dOut] (ρ : MState dOut) : CPTPMap dIn dOut :=
  traceLeft ∘ₘ {
      toFun := fun M => Matrix.kroneckerMap (fun x1 x2 => x1 * x2) M ρ.m
      map_add' := by simp [Matrix.add_kronecker]
      map_smul' := by simp [Matrix.smul_kronecker]
      cp := MatrixMap.kron_kronecker_const ρ.psd
      TP := by intro; simp [Matrix.trace_kronecker]
      }

/-- The output of `replacement ρ` is always that `ρ`. -/
@[simp]
theorem replacement_apply [Nonempty dIn] [DecidableEq dOut] (ρ : MState dOut) (ρ₀ : MState dIn) :
    replacement ρ ρ₀ = ρ := by
  simp [replacement, instMFunLike, PTPMap.instMFunLike, HPMap.instFunLike, HPMap.map,
    MState.traceLeft]
  --This should be simp...
  ext i j
  simp
  rw [HermitianMat.instFun]
  simp [-HermitianMat.mat_apply, Matrix.traceLeft, ← Finset.sum_mul]
  convert one_mul _
  exact ρ₀.tr'

--In principle we can relax the `Nonempty dIn`: for the case where `IsEmpty dIn`, we just take the
-- 0 map, and it's CPTP.
instance [Nonempty dIn] [Nonempty dOut] [DecidableEq dOut] : Inhabited (CPTPMap dIn dOut) :=
  ⟨replacement default⟩

instance [Nonempty dIn] [Nonempty dOut] : Nonempty (CPTPMap dIn dOut) := by
  classical infer_instance

/-- There is a CPTP map that takes a system of any (nonzero) dimension and outputs the
trivial Hilbert space, 1-dimensional, indexed by any `Unique` type. We can think of this
as "destroying" the whole system; tracing out everything. -/
def destroy [Nonempty dIn] [Unique dOut] : CPTPMap dIn dOut :=
  replacement default

/-- Two CPTP maps into the same one-dimensional output space must be equal -/
theorem eq_if_output_unique [Unique dOut] (Λ₁ Λ₂ : CPTPMap dIn dOut) : Λ₁ = Λ₂ :=
  funext fun _ ↦ (Unique.eq_default _).trans (Unique.eq_default _).symm

/-- There is exactly one CPTPMap to a 1-dimensional space. -/
instance instUnique [Nonempty dIn] [Unique dOut] : Unique (CPTPMap dIn dOut) where
  default := destroy
  uniq := fun _ ↦ eq_if_output_unique _ _

@[simp]
theorem destroy_comp {dOut₂ : Type*} [Unique dOut₂] [DecidableEq dOut] [Nonempty dIn] [Nonempty dOut]
  (Λ : CPTPMap dIn dOut) :
    destroy (dOut := dOut₂) ∘ₘ Λ = destroy :=
  Unique.eq_default _

section prod
open Kronecker

variable {dI₁ dI₂ dO₁ dO₂ : Type*} [Fintype dI₁] [Fintype dI₂] [Fintype dO₁] [Fintype dO₂]
variable [DecidableEq dI₁] [DecidableEq dI₂] [DecidableEq dO₁] [DecidableEq dO₂]

set_option maxRecDepth 1000 in -- ??? what the heck is recursing
/-- The tensor product of two CPTPMaps. -/
def prod (Λ₁ : CPTPMap dI₁ dO₁) (Λ₂ : CPTPMap dI₂ dO₂) : CPTPMap (dI₁ × dI₂) (dO₁ × dO₂) where
  toLinearMap := Λ₁.map.kron Λ₂.map
  cp := Λ₁.cp.kron Λ₂.cp
  TP := Λ₁.TP.kron Λ₂.TP

infixl:70 "⊗ᶜᵖ" => CPTPMap.prod

end prod

section finprod

variable {ι : Type u} [DecidableEq ι] [fι : Fintype ι]
variable {dI : ι → Type v} [∀(i :ι), Fintype (dI i)] [∀(i :ι), DecidableEq (dI i)]
variable {dO : ι → Type w} [∀(i :ι), Fintype (dO i)] [∀(i :ι), DecidableEq (dO i)]

/-- Finitely-indexed tensor products of CPTPMaps.  -/
def piProd (Λi : (i:ι) → CPTPMap (dI i) (dO i)) : CPTPMap ((i:ι) → dI i) ((i:ι) → dO i) where
  toLinearMap := MatrixMap.piProd (fun i ↦ (Λi i).map)
  cp := MatrixMap.IsCompletelyPositive.piProd (fun i ↦ (Λi i).cp)
  TP := sorry

theorem fin_1_piProd
  {dI : Fin 1 → Type v} [Fintype (dI 0)] [DecidableEq (dI 0)]
  {dO : Fin 1 → Type w} [Fintype (dO 0)] [DecidableEq (dO 0)]
  (Λi : (i : Fin 1) → CPTPMap (dI 0) (dO 0)) :
    piProd Λi = sorry ∘ₘ ((Λi 1) ∘ₘ sorry) :=
  sorry --TODO: permutations

/--
The tensor product of composed maps is the composition of the tensor products.
-/
theorem piProd_comp
  {d₁ d₂ d₃ : ι → Type*}
  [∀ i, Fintype (d₁ i)] [∀ i, DecidableEq (d₁ i)]
  [∀ i, Fintype (d₂ i)] [∀ i, DecidableEq (d₂ i)]
  [∀ i, Fintype (d₃ i)] [∀ i, DecidableEq (d₃ i)]
  (Λ₁ : ∀ i, CPTPMap (d₁ i) (d₂ i)) (Λ₂ : ∀ i, CPTPMap (d₂ i) (d₃ i)) :
  piProd (fun i => (Λ₂ i) ∘ₘ (Λ₁ i)) = (piProd Λ₂) ∘ₘ (piProd Λ₁) := by
    apply CPTPMap.ext
    convert MatrixMap.piProd_comp _ _;
    infer_instance

end finprod

section unitary

/-- Conjugating density matrices by a unitary as a channel. This is standard unitary evolution. -/
def ofUnitary (U : 𝐔[dIn]) : CPTPMap dIn dIn where
  toLinearMap := MatrixMap.conj U
  cp := MatrixMap.conj_isCompletelyPositive U.val
  TP := by intro; simp [Matrix.trace_mul_cycle U.val, ← Matrix.star_eq_conjTranspose]

/-- The unitary channel U conjugated by U. -/
theorem ofUnitary_eq_conj (U : 𝐔[dIn]) (ρ : MState dIn) :
    (ofUnitary U) ρ = ρ.U_conj U :=
  rfl

/-- A channel is unitary iff it is `ofUnitary U`. -/
def IsUnitary (Λ : CPTPMap dIn dIn) : Prop :=
  ∃ U, Λ = ofUnitary U

/-- A channel is unitary iff it can be written as conjugation by a unitary. -/
theorem IsUnitary_iff_U_conj (Λ : CPTPMap dIn dIn) : IsUnitary Λ ↔ ∃ U, ∀ ρ, Λ ρ = ρ.U_conj U := by
  simp_rw [IsUnitary, ← ofUnitary_eq_conj, CPTPMap.funext_iff]

theorem IsUnitary_equiv (σ : dIn ≃ dIn) : IsUnitary (ofEquiv σ) := by
  have h_unitary : ∃ U : Matrix dIn dIn ℂ, U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1 ∧ ∀ x : dIn, (∀ y : dIn, (U y x = 1) ↔ (y = σ x)) ∧ ∀ y : dIn, (U y x = 0) ↔ (y ≠ σ x) := by
    simp only [Matrix.conjTranspose, RCLike.star_def];
    refine' ⟨ fun y x => if y = σ x then 1 else 0, ?_, ?_, by simp⟩
    · ext y x
      simp [Matrix.mul_apply, Matrix.transpose_apply];
      rw [Finset.sum_eq_single ( σ.symm x )] <;> aesop
    · ext y x
      simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply];
      simp [Matrix.one_apply, eq_comm]
  obtain ⟨U, hU_unitary, hU_eq⟩ := h_unitary;
  use ⟨U, Matrix.mem_unitaryGroup_iff.mpr hU_unitary⟩
  have h_mul : ∀ ρ : Matrix dIn dIn ℂ, U * ρ * Uᴴ = Matrix.submatrix ρ σ.symm σ.symm := by
    intro ρ
    ext i j
    have hU_i_x : ∀ x : dIn, U i x = if x = σ.symm i then 1 else 0 := by grind
    have hU_j_x : ∀ x : dIn, U j x = if x = σ.symm j then 1 else 0 := by grind
    simp [Matrix.mul_apply, Matrix.submatrix, hU_i_x, hU_j_x]
  ext ρ : 3
  exact (h_mul ρ).symm

end unitary

-- /-- A channel is *entanglement breaking* iff its product with the identity channel
--   only outputs separable states. -/
-- def IsEntanglementBreaking (Λ : CPTPMap dIn dOut) : Prop :=
--   ∀ (dR : Type u_1) [Fintype dR] [DecidableEq dR],
--   ∀ (ρ : MState (dR × dIn)), ((CPTPMap.id (dIn := dR) ⊗ₖ Λ) ρ).IsSeparable

--TODO:
--Theorem: entanglement breaking iff it holds for all channels, not just id.
--Theorem: entanglement break iff it breaks a Bell pair (Wilde Exercise 4.6.2)
--Theorem: entanglement break if c-q or q-c, e.g. measurements
--Theorem: eb iff Kraus operators can be written as all unit rank (Wilde Theorem 4.6.1)

section purify
variable [DecidableEq dOut] [Inhabited dOut]

--PULLOUT
omit [DecidableEq dOut] [Inhabited dOut] in
/-
PROBLEM
If a MatrixMap of_kraus K K is trace-preserving, then Σ_k K_k† K_k = 1.

PROVIDED SOLUTION
The TP condition says for all X, trace((of_kraus K K) X) = trace(X).
Unfolding of_kraus: trace(Σ_k K_k X K_k†) = Σ_k trace(K_k† K_k X) (by cycle) = trace((Σ_k K_k† K_k) X).
So trace(A X) = trace(X) for all X where A = Σ_k K_k† K_k, which means A = 1.
Use `Matrix.eq_of_trace_mul_eq` or the fact that trace is a faithful pairing on matrices
to conclude A = 1. The TP condition `Λ.TP` gives us `∀ x, (Λ.map x).trace = x.trace`, and
since `Λ.map = of_kraus K K`, we substitute and simplify.
-/
private lemma kraus_sum_eq_one_of_TP
    {κ : Type*} [Fintype κ]
    {K : κ → Matrix dOut dIn ℂ}
    (hTP : (MatrixMap.of_kraus K K).IsTracePreserving) :
    ∑ k, (K k).conjTranspose * (K k) = 1 := by
  refine' Matrix.ext fun i j => _;
  have := hTP ( Matrix.of fun x y => if x = j then if y = i then 1 else 0 else 0 )
  simp_all +decide [ Matrix.trace, Matrix.mul_apply, Finset.mul_sum _ _ _ ] ;
  convert this using 1
  · simp +decide [ MatrixMap.of_kraus, Matrix.transpose_apply ]
    ring!
    simp +decide [ Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )
  · simp +decide [ Matrix.one_apply, eq_comm ]

/-
PROBLEM
Given an m × n matrix V over ℂ with V†V = 1, and an injection emb : n ↪ m,
there exists a unitary matrix U ∈ unitaryGroup m ℂ such that for all i and j,
U i (emb j) = V i j.

PROVIDED SOLUTION
The columns of V form an orthonormal set in ℂ^m (this follows from V†V = 1).
Using the embedding emb, assign each column V_j to position emb(j) in the larger matrix.
The remaining columns can be filled by extending to an orthonormal basis of ℂ^m.
This extension exists by `Orthonormal.exists_orthonormalBasis_extension` in Mathlib.
The resulting matrix has orthonormal columns spanning ℂ^m, hence it is unitary.

Concretely, define the column vectors of V as an orthonormal family in EuclideanSpace ℂ m,
indexed by the range of emb. Then use `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`
to extend this to a full OrthonormalBasis. The matrix of this basis is unitary.

Alternatively, use V to define a linear isometry on the subspace spanned by the image
of emb, then use `LinearIsometry.extend` to extend to the full space. Since in finite
dimensions a linear isometry from a space to itself is surjective, this gives a
LinearIsometryEquiv, hence a unitary matrix.
-/
set_option maxHeartbeats 1600000 in
private lemma exists_unitary_extending_isometry
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : V.conjTranspose * V = 1)
    (emb : n ↪ m) :
    ∃ U : 𝐔[m], ∀ i j, U.val i (emb j) = V i j := by
  -- Let $u_i$ be the $i$-th column of $V$.
  set u : n → EuclideanSpace ℂ m := fun j => fun i => V i j;
  -- Since $u$ is an orthonormal set, we can extend it to an orthonormal basis of $\mathbb{C}^m$.
  obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis m ℂ (EuclideanSpace ℂ m), ∀ j, b (emb j) = u j := by
    have h_orthonormal : Orthonormal ℂ (fun j => u j) := by
      rw [ orthonormal_iff_ite ];
      intro i j; replace hV := congr_fun ( congr_fun hV i ) j; simp_all +decide [ Matrix.mul_apply, inner_sum ] ;
      simpa only [ mul_comm ] using hV;
    have := @Orthonormal.exists_orthonormalBasis_extension_of_card_eq;
    contrapose! this;
    refine' ⟨ ℂ, inferInstance, EuclideanSpace ℂ m, inferInstance, inferInstance, _, _ ⟩;
    exact inferInstance;
    refine' ⟨ m, inferInstance, _, _ ⟩;
    · simp +decide [ Module.finrank_pi ];
    · refine' ⟨ fun i => if hi : i ∈ Set.range emb then u ( Classical.choose hi ) else 0, Set.range emb, _, _ ⟩ <;> simp_all +decide [ Orthonormal ];
      intro i j hij; split_ifs <;> simp_all +decide [ Pairwise ] ;
      exact h_orthonormal.2 ( by intro h; have := Classical.choose_spec ‹∃ y, emb y = ↑i›; have := Classical.choose_spec ‹∃ y, emb y = ↑j›; aesop );
  refine' ⟨ _, _ ⟩;
  refine' ⟨ _, _ ⟩;
  exact Matrix.of ( fun i j => b j i );
  all_goals simp_all +decide [ Matrix.mem_unitaryGroup_iff ];
  · ext i j; simp +decide [ Matrix.mul_apply, Matrix.one_apply ] ;
    have := b.sum_inner_mul_inner ( EuclideanSpace.single i 1 ) ( EuclideanSpace.single j 1 ) ; simp_all +decide [ inner, Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ] ;
  · exact fun i j => rfl

omit [DecidableEq dOut] [Inhabited dOut] in
/-
PROBLEM
Given Kraus operators K indexed by (dOut × dIn), define the isometry matrix
V : Matrix (dIn × dOut × dOut) dIn ℂ by V_{(a, b, d), a'} = (K (b, a))_{d, a'},
and show that V†V = 1 given that Σ_k K_k† K_k = 1.

PROVIDED SOLUTION
(V†V)_{a₁, a₂} = Σ_{(a,b,d)} conj(V_{(a,b,d), a₁}) * V_{(a,b,d), a₂}
= Σ_{(a,b,d)} conj((K(b,a))_{d,a₁}) * (K(b,a))_{d,a₂}
= Σ_{k=(b,a)} ((K k)† * (K k))_{a₁,a₂}
= (Σ_k (K k)† * (K k))_{a₁,a₂}
= 1_{a₁,a₂}.
Use ext, simp on conjTranspose and mul, reindex the sum over (b,a) as a sum over k,
and apply hTP.
-/
private lemma purify_isometry_condition
    {K : (dOut × dIn) → Matrix dOut dIn ℂ}
    (hTP : ∑ k, (K k).conjTranspose * (K k) = 1) :
    let V : Matrix (dIn × dOut × dOut) dIn ℂ :=
      fun ⟨a, b, d⟩ a' => (K (b, a)) d a'
    V.conjTranspose * V = 1 := by
  convert hTP using 1;
  ext i j;
  simp +decide [ Matrix.mul_apply, Fintype.sum_prod_type ];
  rw [ Finset.sum_comm ];
  simp +decide [ Matrix.sum_apply, Matrix.mul_apply ]

/-
PROBLEM
Show that the composed CPTP map
  traceLeft ∘ₘ traceLeft ∘ₘ ofUnitary U ∘ₘ (id ⊗ᶜᵖ replacement (ρ₀)) ∘ₘ ofEquiv (prodPUnit).symm
equals the map defined by of_kraus K K, given that U's columns at (a', default, default)
match the isometry V defined by the Kraus operators K.

PROVIDED SOLUTION
Use CPTPMap.ext to reduce to showing the underlying MatrixMaps agree.
Then use LinearMap.ext to reduce to showing they agree on all matrices X.
Then use Matrix.ext to show the entries agree at (d₁, d₂).

The RHS composition unfolds as:
1. ofEquiv maps X to X.submatrix (Equiv.prodPUnit dIn) (Equiv.prodPUnit dIn) on dIn × Unit
2. (id ⊗ᶜᵖ replacement ρ₀) applies the Kronecker product of maps; by kron_def,
   the result at ((a₁,(b₁,c₁)), (a₂,(b₂,c₂))) is
   Σ_{α₁,α₂,u₁,u₂} (single α₁ α₂ 1)_{a₁,a₂} * (replacement.map (single u₁ u₂ 1))_{(b₁,c₁),(b₂,c₂)} * step1_{(α₁,u₁),(α₂,u₂)}
   Since Unit is a unique type, u₁ = u₂ = ().
   This simplifies to X_{a₁,a₂} * (ρ₀.m)_{(b₁,c₁),(b₂,c₂)}
   where ρ₀ = MState.pure (Ket.basis default), so
   (ρ₀.m)_{p,q} = if p = (default,default) then (if q = (default,default) then 1 else 0) else 0
3. ofUnitary U conjugates: (U M U†)_{i,j} = Σ_{k,l} U_{i,k} M_{k,l} conj(U_{j,l})
   The non-zero entries of M from step 2 are only at k = (α₁, default, default),
   l = (α₂, default, default). So:
   (U M U†)_{i,j} = Σ_{α₁,α₂} U_{i,(α₁,default,default)} X_{α₁,α₂} conj(U_{j,(α₂,default,default)})
   By hU: U_{i,(α,default,default)} = V i α = K(i.2.1, i.1) i.2.2 α
4. First traceLeft sums over dIn: gives a matrix on dOut × dOut
5. Second traceLeft sums over the first dOut: gives a matrix on dOut
   The result is Σ_{a,b} Σ_{α₁,α₂} (K(b,a))_{d₁,α₁} X_{α₁,α₂} conj((K(b,a))_{d₂,α₂})
   = Σ_k (K k * X * (K k)†)_{d₁,d₂} = (of_kraus K K X)_{d₁,d₂}

The proof strategy: use `ext` at the CPTPMap level to get linear map equality,
then use `ext` to get matrix entry equality, then unfold all definitions
(compose, traceLeft, ofUnitary, prod, replacement, ofEquiv, of_kraus) using simp
with the appropriate lemmas. Key simp lemmas to use:
- MatrixMap.kron_def for unfolding the tensor product of maps
- Matrix.traceLeft for the partial trace
- Matrix.mul_apply for matrix multiplication
- hU for the unitary column condition
- Fintype.sum_prod_type for reindexing sums over product types
The crucial simplification is that the sum over Unit (from step 1) collapses,
and the sum over (b,a) in dOut × dIn matches the Kraus sum.
-/

/-
PROBLEM
Show that the composed CPTP map equals Λ.

PROVIDED SOLUTION
Use CPTPMap.ext to reduce to MatrixMap equality, then LinearMap.ext and funext to get
entry-level equality. On the LHS, use hK to get of_kraus K K entries. On the RHS, unfold
the composition step by step:

Step 1 (append): Maps X to X.submatrix (Equiv.prodPUnit dIn). At entries:
  (append.map X) (a₁,()) (a₂,()) = X a₁ a₂

Step 2 (prep = id ⊗ₖₘ zero_prep): By MatrixMap.kron_map_of_kron_state, since
  append.map X = X ⊗ₖ (1 : Matrix Unit Unit ℂ), we get
  prep.map (append.map X) = id.map X ⊗ₖ zero_prep.map 1 = X ⊗ₖ ρ₀.m
  where ρ₀ = MState.pure (Ket.basis default).

Step 3 (ofUnitary U): Conjugation gives
  (U * (X ⊗ₖ ρ₀.m) * U†) with entries at (i,j):
  Σ_k Σ_l U i k * (X ⊗ₖ ρ₀.m) k l * conj(U j l)
  Since ρ₀.m is only nonzero at (default,default), this collapses to:
  Σ_{α₁,α₂} U i (α₁,default,default) * X α₁ α₂ * conj(U j (α₂,default,default))

Step 4-5 (two traceLeft's): First traces over dIn, then over first dOut:
  result d₁ d₂ = Σ_{a,b} Σ_{α₁,α₂} U (a,b,d₁) (α₁,0,0) * X α₁ α₂ * conj(U (a,b,d₂) (α₂,0,0))
  = Σ_{a,b} Σ_{α₁,α₂} (K(b,a)) d₁ α₁ * X α₁ α₂ * conj((K(b,a)) d₂ α₂)  [by hU]
  = Σ_k (K k * X * (K k)†) d₁ d₂ = (of_kraus K K X) d₁ d₂

The proof approach:
1. Use CPTPMap.ext to reduce to linear map equality.
2. Use LinearMap.ext (ext X) to reduce to matrix equality.
3. Use funext (ext d₁ d₂) to reduce to entry equality.
4. Rewrite LHS with hK to get of_kraus entries.
5. On the RHS, the key rewrite step is to note that
   (prep ∘ₘ append).map X = X ⊗ₖ ρ₀.m  by using MatrixMap.kron_map_of_kron_state.
   This requires showing append.map X = X ⊗ₖ 1 (a submatrix equals a Kronecker product).
6. Then unfold ofUnitary to get U * (X ⊗ₖ ρ₀.m) * U†.
7. Unfold traceLeft to get the sums.
8. Use hU to replace U entries and reindex sums.
9. Show the result equals (of_kraus K K X) d₁ d₂.

Key lemmas: MatrixMap.kron_map_of_kron_state, Matrix.traceLeft, Matrix.mul_apply,
  Matrix.conjTranspose_apply, MatrixMap.of_kraus, MatrixMap.conj, Fintype.sum_prod_type.
-/
set_option maxHeartbeats 1600000 in
private lemma purify_trace_eq
    {K : (dOut × dIn) → Matrix dOut dIn ℂ}
    {Λ : CPTPMap dIn dOut ℂ}
    (hK : Λ.map = MatrixMap.of_kraus K K)
    {U : 𝐔[dIn × dOut × dOut]}
    (hU : ∀ (i : dIn × dOut × dOut) (j : dIn),
      U.val i (j, default, default) =
      (fun ⟨a, b, d⟩ a' => (K (b, a)) d a') i j) :
    Λ = (
      let zero_prep : CPTPMap Unit (dOut × dOut) := replacement (MState.pure (Ket.basis default))
      let prep := (id ⊗ᶜᵖ zero_prep)
      let append : CPTPMap dIn (dIn × Unit) := CPTPMap.ofEquiv (Equiv.prodPUnit dIn).symm
      CPTPMap.traceLeft ∘ₘ CPTPMap.traceLeft ∘ₘ (ofUnitary U) ∘ₘ prep ∘ₘ append) := by
  sorry

theorem exists_purify (Λ : CPTPMap dIn dOut) :
    ∃ (Λ' : CPTPMap (dIn × dOut × dOut) (dIn × dOut × dOut)),
      Λ'.IsUnitary ∧
      Λ = (
      let zero_prep : CPTPMap Unit (dOut × dOut) := replacement (MState.pure (Ket.basis default))
      let prep := (id ⊗ᶜᵖ zero_prep)
      let append : CPTPMap dIn (dIn × Unit) := CPTPMap.ofEquiv (Equiv.prodPUnit dIn).symm
      CPTPMap.traceLeft ∘ₘ CPTPMap.traceLeft ∘ₘ Λ' ∘ₘ prep ∘ₘ append
    ) := by
  obtain ⟨K, hK⟩ := MatrixMap.IsCompletelyPositive.exists_kraus Λ.map Λ.cp
  -- K : (dOut × dIn) → Matrix dOut dIn ℂ
  -- hK : Λ.map = MatrixMap.of_kraus K K
  -- Step 1: Extract Kraus sum condition from trace-preserving
  have hTP_kraus : ∑ k, (K k).conjTranspose * (K k) = 1 :=
    kraus_sum_eq_one_of_TP (hK ▸ Λ.TP)
  -- Step 2: Define the isometry
  let V : Matrix (dIn × dOut × dOut) dIn ℂ :=
    fun ⟨a, b, d⟩ a' => (K (b, a)) d a'
  -- Step 3: Show V†V = 1
  have hV : V.conjTranspose * V = 1 :=
    purify_isometry_condition hTP_kraus
  -- Step 4: Extend V to a unitary using the embedding a ↦ (a, default, default)
  let emb : dIn ↪ (dIn × dOut × dOut) :=
    ⟨fun a => (a, default, default), fun a₁ a₂ h => by simpa using h⟩
  obtain ⟨U, hU⟩ := exists_unitary_extending_isometry V hV emb
  -- Step 5: Construct the purifying channel
  refine ⟨ofUnitary U, ⟨U, rfl⟩, ?_⟩
  -- Step 6: Show the trace property.
  -- We need: Λ = traceLeft ∘ₘ traceLeft ∘ₘ ofUnitary U ∘ₘ prep ∘ₘ append
  exact purify_trace_eq hK hU

/-- Every channel can be written as a unitary channel on a larger system. In general, if
 the original channel was A→B, we may need to go as big as dilating the output system (the
 environment) by a factor of A*B. One way of stating this would be that it forms an
 isometry from A to (B×A×B). So that we can instead talk about the cleaner unitaries, we
 say that this is a unitary on (A×B×B). The defining properties that this is a valid
 purification comes are `purify_IsUnitary` and `purify_trace`. This means the environment
 always has type `dIn × dOut`.

 Furthermore, since we need a canonical "0" state on B in order to add with the input,
 we require a typeclass instance [Inhabited dOut]. -/
def purify (Λ : CPTPMap dIn dOut) : CPTPMap (dIn × dOut × dOut) (dIn × dOut × dOut) :=
  exists_purify Λ |>.choose

--TODO: Constructing this will probably need Kraus operators first.

theorem purify_IsUnitary (Λ : CPTPMap dIn dOut) : Λ.purify.IsUnitary :=
  exists_purify Λ |>.choose_spec.1

/-- With a channel Λ : A → B, a valid purification (A×B×B)→(A×B×B) is such that:
 * Preparing the default ∣0⟩ state on two copies of B
 * Appending these to the input
 * Applying the purified unitary channel
 * Tracing out the two left parts of the output
is equivalent to the original channel. This theorem states that the channel output by `purify`
has this property. -/
theorem purify_trace (Λ : CPTPMap dIn dOut) : Λ = (
    let zero_prep : CPTPMap Unit (dOut × dOut) := replacement (MState.pure (Ket.basis default))
    let prep := (id ⊗ᶜᵖ zero_prep)
    let append : CPTPMap dIn (dIn × Unit) := CPTPMap.ofEquiv (Equiv.prodPUnit dIn).symm
    CPTPMap.traceLeft ∘ₘ CPTPMap.traceLeft ∘ₘ Λ.purify ∘ₘ prep ∘ₘ append
  ) :=
  exists_purify Λ |>.choose_spec.2

--TODO Theorem: `purify` is unique up to unitary equivalence.

--TODO: Best to rewrite the "zero_prep / prep / append" as one CPTPMap.append channel when we
-- define that.

/-- The complementary channel comes from tracing out the other half (the right half) of the purified channel `purify`. -/
def complementary (Λ : CPTPMap dIn dOut) : CPTPMap dIn (dIn × dOut) :=
  let zero_prep : CPTPMap Unit (dOut × dOut) := replacement (MState.pure (Ket.basis default))
  let prep := (id ⊗ᶜᵖ zero_prep)
  let append : CPTPMap dIn (dIn × Unit) := CPTPMap.ofEquiv (Equiv.prodPUnit dIn).symm
  CPTPMap.traceRight ∘ₘ CPTPMap.assoc' ∘ₘ Λ.purify ∘ₘ prep ∘ₘ append

end purify

section degradable
variable [DecidableEq dOut] [Inhabited dOut] [DecidableEq dOut₂] [Inhabited dOut₂]

/-- A channel is *degradable to* another, if the other can be written as a composition of
  a _degrading_ channel D with the original channel. -/
def IsDegradableTo (Λ : CPTPMap dIn dOut) (Λ₂ : CPTPMap dIn dOut₂) : Prop :=
  ∃ (D : CPTPMap dOut (dOut₂)), D ∘ₘ Λ = Λ₂

/-- A channel is *antidegradable to* another, if the other `IsDegradableTo` this one. -/
@[reducible]
def IsAntidegradableTo (Λ : CPTPMap dIn dOut) (Λ₂ : CPTPMap dIn dOut₂) : Prop :=
  IsDegradableTo Λ₂ Λ

/-- A channel is *degradable* if it `IsDegradableTo` its complementary channel. -/
def IsDegradable (Λ : CPTPMap dIn dOut) : Prop :=
  IsDegradableTo Λ Λ.complementary

/-- A channel is *antidegradable* if it `IsAntidegradableTo` its complementary channel. -/
@[reducible]
def IsAntidegradable (Λ : CPTPMap dIn dOut) : Prop :=
  IsAntidegradableTo Λ Λ.complementary

--Theorem (Wilde Exercise 13.5.7): Entanglement breaking channels are antidegradable.
end degradable

/-- `CPTPMap`s inherit a topology from their choi matrices. -/
instance instTop : TopologicalSpace (CPTPMap dIn dOut) :=
  TopologicalSpace.induced (CPTPMap.choi) instTopologicalSpaceMatrix

/-- The projection from `CPTPMap` to the Choi matrix is an embedding -/
theorem choi_IsEmbedding : Topology.IsEmbedding (CPTPMap.choi (dIn := dIn) (dOut := dOut)) where
  eq_induced := rfl
  injective _ _ := choi_ext

instance instT3Space : T3Space (CPTPMap dIn dOut) :=
  Topology.IsEmbedding.t3Space choi_IsEmbedding

end
end CPTPMap
