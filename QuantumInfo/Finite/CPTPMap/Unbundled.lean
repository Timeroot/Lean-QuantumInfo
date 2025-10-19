/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
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

/-- A map is trace preserving iff the partial trace of the Choi matrix is the identity. -/
theorem IsTracePreserving_iff_trace_choi (M : MatrixMap A B R) : M.IsTracePreserving
    ↔ M.choi_matrix.traceLeft = 1 := by
  constructor
  · intro h
    ext a₁ a₂
    replace h := h (Matrix.single a₁ a₂ 1)
    simp_rw [Matrix.trace, Matrix.diag] at h
    simp only [Matrix.traceLeft, choi_matrix, Matrix.of_apply, h]
    simp only [Matrix.single, Matrix.of_apply, Finset.sum_boole, Matrix.one_apply]
    have : (fun x => a₁ = x ∧ a₂ = x) = (fun x => a₁ = a₂ ∧ a₂ = x) := by
      funext x
      rw [eq_iff_iff, and_congr_left_iff]
      rintro rfl
      trivial
    split_ifs with h
    <;> simp [this, h, Finset.filter_eq]
  · intro h X
    replace h := fun (a₁ a₂ : A) ↦ congrFun₂ h a₁ a₂
    simp [Matrix.traceLeft, Matrix.trace] at h ⊢
    rw [← M.choi_map_inv, of_choi_matrix]
    dsimp
    rw [Finset.sum_comm_cycle, Finset.sum_comm_cycle]
    simp_rw [← Finset.mul_sum, h, Matrix.one_apply]
    simp

namespace IsTracePreserving

variable {A : Type*} [Fintype A] in
/-- Simp lemma: the trace of the image of a IsTracePreserving map is the same as the original trace. -/
@[simp]
theorem apply_trace {M : MatrixMap A B R} (h : M.IsTracePreserving) (ρ : Matrix A A R)
    : (M ρ).trace = ρ.trace :=
  h ρ

/-- The trace of a Choi matrix of a TP map is the cardinality of the input space. -/
theorem trace_choi {M : MatrixMap A B R} (h : M.IsTracePreserving) :
    M.choi_matrix.trace = (Finset.univ (α := A)).card := by
  rw [← Matrix.traceLeft_trace, (IsTracePreserving_iff_trace_choi M).mp h,
    Matrix.trace_one, Finset.card_univ]

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
  intro x
  simp_rw [Matrix.trace, Matrix.diag]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [kron_def]
  have h_simp : ∑ x_1, ∑ x_2, ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂,
    M₁ (Matrix.single a₁ a₂ 1) x_1 x_1 * M₂ (Matrix.single c₁ c₂ 1) x_2 x_2 * x (a₁, c₁) (a₂, c₂) =
      ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂, (if a₁ = a₂ then 1 else 0) * (if c₁ = c₂ then 1 else 0) * x (a₁, c₁) (a₂, c₂) := by
    --Sort the sum into AACCBD order
    simp only [@Finset.sum_comm A _ D, @Finset.sum_comm A _ B, @Finset.sum_comm C _ B, @Finset.sum_comm C _ D]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    congr! 8 with a₁ _ a₂ _ c₁ _ c₂ _
    · refine (h₁ _).trans ?_
      split_ifs with h
      · subst h
        exact Matrix.trace_single_eq_same _ _
      · exact Matrix.trace_single_eq_of_ne _ _ _ h
    · refine (h₂ _).trans ?_
      split_ifs with h
      · subst h
        exact Matrix.trace_single_eq_same _ _
      · exact Matrix.trace_single_eq_of_ne _ _ _ h
  simp [h_simp]

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

omit [DecidableEq A] in
/-- `MatrixMap.submatrix` is trace-preserving when the function is an equivalence. -/
theorem submatrix (e : A ≃ B) : (MatrixMap.submatrix R e).IsTracePreserving := by
  intro; simp

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
  ∀⦃x⦄, x.IsHermitian → (M x).IsHermitian

/-- A linear matrix map is *positive* if it maps `PosSemidef` matrices to `PosSemidef`.-/
def IsPositive [Fintype A] [Fintype B] (M : MatrixMap A B R) : Prop :=
  ∀⦃x⦄, x.PosSemidef → (M x).PosSemidef

/-- A linear matrix map is *completely positive* if, for any integer n, the tensor product
with `I(n)` is positive. -/
def IsCompletelyPositive [Fintype A] [Fintype B] [DecidableEq A] (M : MatrixMap A B R) : Prop :=
  ∀ (n : ℕ), (M ⊗ₖₘ (LinearMap.id : MatrixMap (Fin n) (Fin n) R)).IsPositive

namespace IsHermitianPreserving

variable {A : Type*} [Fintype A] in
/-- The identity MatrixMap IsHermitianPreserving. -/
theorem id : (id A R).IsPositive :=
  fun _ h ↦ h

/-- The composition of IsHermitianPreserving maps is also Hermitian preserving. -/
theorem comp {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R}
    (h₁ : M₁.IsHermitianPreserving) (h₂ : M₂.IsHermitianPreserving) : IsHermitianPreserving (M₂ ∘ₗ M₁) :=
  fun _ h ↦ h₂ (h₁ h)

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
  fun _ h ↦ h₂ (h₁ h)

variable {A : Type*} [Fintype A] in
/-- The identity MatrixMap IsPositive. -/
@[simp]
theorem id : (id A R).IsPositive :=
  fun _ h ↦ h

/-- Sums of IsPositive maps are IsPositive. -/
theorem add {M₁ M₂ : MatrixMap A B R} (h₁ : M₁.IsPositive) (h₂ : M₂.IsPositive) :
    (M₁ + M₂).IsPositive :=
  fun _ h ↦ Matrix.PosSemidef.add (h₁ h) (h₂ h)

/-- Nonnegative scalings of IsPositive maps are IsPositive. -/
theorem smul {M : MatrixMap A B R} (hM : M.IsPositive) {x : R} (hx : 0 ≤ x) :
    (x • M).IsPositive :=
  fun _ h ↦ (hM h).smul hx

end IsPositive

namespace IsCompletelyPositive
variable [Fintype A] [Fintype B] [Fintype C] [DecidableEq A]

/-- Definition of a CP map, but with `Fintype T` in the definition instead of a `Fin n`. -/
theorem of_Fintype  {M : MatrixMap A B R} (h : IsCompletelyPositive M)
    (T : Type*) [Fintype T] [DecidableEq T] :
    (M.kron (LinearMap.id : MatrixMap T T R)).IsPositive := by
  sorry

/- Every `MatrixMap` that `IsCompletelyPositive` also `IsPositiveMap`. -/
theorem IsPositive {M : MatrixMap A B R}
    (hM : IsCompletelyPositive M) : IsPositive M := by
  intro x hx
  let x' : Matrix (A × Fin 1) (A × Fin 1) R := x ⊗ₖ 1
  let eqA : (A × Fin 1) ≃ A :=
    (Equiv.prodCongrRight (fun _ ↦ finOneEquiv)).trans (Equiv.prodPUnit A)
  let eqB : (B × Fin 1) ≃ B :=
    (Equiv.prodCongrRight (fun _ ↦ finOneEquiv)).trans (Equiv.prodPUnit B)
  specialize @hM 1 (x.submatrix eqA eqA) (Matrix.PosSemidef.submatrix hx _)
  convert Matrix.PosSemidef.submatrix hM eqB.symm; clear hM
  --TODO Cleanup
  ext i j
  simp only [Matrix.submatrix, Matrix.of_apply]
  rw [MatrixMap.kron_def]
  suffices h : M x = ∑ a₁, ∑ a₂, x a₁ a₂ • M (Matrix.single a₁ a₂ 1) by
    simp [h, Matrix.sum_apply, Matrix.single, eqA, eqB]
    ac_rfl
  simp only [← M.map_smul, ← map_sum]
  congr
  ext k l
  simp [Matrix.sum_apply, Matrix.single]
  rw [Finset.sum_eq_single k]
  · simp
  · simp +contextual
  · simp +contextual

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

variable {d : Type*} [Fintype d]

/-- The map that takes M and returns M ⊗ₖ C, where C is positive semidefinite, is a completely positive map. -/
theorem kron_kronecker_const {C : Matrix d d R} (h : C.PosSemidef) {h₁ h₂ : _} : MatrixMap.IsCompletelyPositive
    (⟨⟨fun M => M ⊗ₖ C, h₁⟩, h₂⟩ : MatrixMap A (A × d) R) := by
  intros n x hx
  have h_kronecker_pos : (x ⊗ₖ C).PosSemidef := by
    -- Since $x$ and $C$ are positive semidefinite, there exist matrices $U$ and $V$ such that $x = U^*U$ and $C = V^*V$.
    obtain ⟨U, hU⟩ : ∃ U : Matrix (A × Fin n) (A × Fin n) R, x = star U * U :=
      Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hx
    obtain ⟨V, hV⟩ : ∃ V : Matrix d d R, C = star V * V :=
      Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp h
    -- $W = (U \otimes V)^* (U \otimes V)$ is positive semidefinite.
    have hW_pos : (U ⊗ₖ V).conjTranspose * (U ⊗ₖ V) = x ⊗ₖ C := by
      rw [Matrix.kroneckerMap_conjTranspose, ← Matrix.mul_kronecker_mul]
      rw [hU, hV, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
    rw [ ← hW_pos ]
    exact Matrix.posSemidef_conjTranspose_mul_self (U ⊗ₖ V)
  --TODO clean up this mess (but, thanks Aristotle)
  convert h_kronecker_pos.submatrix (fun (⟨ ⟨ a, d' ⟩, n' ⟩ : (A × d) × Fin n) => ⟨ ⟨ a, n' ⟩, d' ⟩) using 1;
  ext ⟨⟨a, d⟩, n⟩ ⟨⟨a', d'⟩, n'⟩
  simp [Matrix.kroneckerMap_apply, Matrix.submatrix_apply]
  erw [MatrixMap.kron_def]
  simp [Matrix.single, Matrix.kroneckerMap_apply]
  simp [Finset.sum_ite, Finset.filter_eq', Finset.filter_and]
  rw [ Finset.sum_eq_single a ]
  · simp_all only [RingHom.id_apply, ↓reduceIte, Finset.mem_univ, Finset.inter_singleton_of_mem, Finset.sum_singleton]
    simp_all only
    rw [ Finset.sum_eq_single n ]
    · simp_all only [↓reduceIte, Finset.mem_univ, Finset.inter_singleton_of_mem, Finset.sum_singleton]
      ring
    · intro b a_1 a_2
      simp_all only [Finset.mem_univ, ne_eq, ↓reduceIte, Finset.notMem_empty, not_false_eq_true,
        Finset.inter_singleton_of_notMem, Finset.sum_empty]
    · intro a_1
      simp_all only [Finset.mem_univ, not_true_eq_false]
  · intro b a_1 a_2
    simp_all only [RingHom.id_apply, Finset.mem_univ, ne_eq, ↓reduceIte, Finset.notMem_empty, not_false_eq_true,
      Finset.inter_singleton_of_notMem, Finset.sum_empty]
  · intro a_1
    simp_all only [RingHom.id_apply, Finset.mem_univ, not_true_eq_false]

/-- Choi's theorem on completely positive maps: A map `IsCompletelyPositive` iff its Choi Matrix is PSD. -/
theorem _root_.MatrixMap.choi_PSD_iff_CP_map [DecidableEq A] (M : MatrixMap A B ℂ) :
    M.IsCompletelyPositive ↔ M.choi_matrix.PosSemidef := by
  by_cases hA : Nonempty A
  · constructor
    · intro hcp
      rw [choi_matrix_state_rep]
      apply Matrix.PosSemidef.smul _ (ha := by positivity)
      exact of_Fintype hcp A (MState.pure (Ket.MES A)).pos
    · sorry
  · simp at hA
    have : M = 0 := Subsingleton.elim M 0
    subst M
    have hx (x : B × A → ℂ) : x = 0 := Subsingleton.elim x 0
    simp [Matrix.PosSemidef, Matrix.IsHermitian, IsCompletelyPositive,
      MatrixMap.IsPositive, hx]
    ext
    simp [choi_matrix] --TODO: `choi_matrix 0 = 0` as simp

--TODO: Where to put this definition?
/-- The linear map of conjugating a matrix by another, `x → y * x * yᴴ`. -/
@[simps]
def conj (y : Matrix B A R) : MatrixMap A B R where
  toFun := fun (x : Matrix A A R) ↦ y * x * y.conjTranspose
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

omit [Fintype B] [DecidableEq A] in
theorem conj_eq_mulRightLinearMap_comp_mulRightLinearMap (y : Matrix B A R) :
    conj y = mulRightLinearMap B R y.conjTranspose ∘ₗ mulLeftLinearMap A R y := by
  ext1; simp

/-- The act of conjugating (not necessarily by a unitary, just by any matrix at all) is completely positive. -/
theorem conj_isCompletelyPositive (M : Matrix B A R) : (conj M).IsCompletelyPositive := by
  intro n m h
  classical
  open ComplexOrder in
  open Kronecker in
  suffices ((M ⊗ₖ 1 : Matrix (B × Fin n) (A × Fin n) R) * m * (M.conjTranspose ⊗ₖ 1)).PosSemidef by
    convert this
    --TODO cleanup. Thanks Aristotle
    ext ⟨ b₁, c₁ ⟩ ⟨ b₂, c₂ ⟩
    rw [ MatrixMap.kron_def ];
    simp [Matrix.mul_apply, Matrix.single];
    have h_split : ∑ x, ∑ x_1, ∑ x_2, ∑ x_3, (if x_2 = c₁ ∧ x_3 = c₂ then (∑ x_4, (∑ x_5, if x = x_5 ∧ x_1 = x_4 then M b₁ x_5 else 0) * (starRingEnd R) (M b₂ x_4)) * m (x, x_2) (x_1, x_3) else 0) = ∑ x, ∑ x_1, (∑ x_4, (∑ x_5, if x = x_5 ∧ x_1 = x_4 then M b₁ x_5 else 0) * (starRingEnd R) (M b₂ x_4)) * m (x, c₁) (x_1, c₂) := by
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ Finset.sum_eq_single c₁ ] <;> aesop;
    convert h_split using 1;
    rw [ Matrix.mul_assoc ];
    simp [ Matrix.mul_apply, Finset.mul_sum _ _ _, Finset.sum_mul ];
    simp [ Matrix.one_apply, Finset.sum_ite, Finset.filter_eq, Finset.filter_and ];
    have h_reindex : ∑ x ∈ {x | c₁ = x.2}, ∑ x_1 ∈ {x | x.2 = c₂}, M b₁ x.1 * (m x x_1 * (starRingEnd R) (M b₂ x_1.1)) = ∑ x ∈ Finset.univ, ∑ x_1 ∈ Finset.univ, M b₁ x * (m (x, c₁) (x_1, c₂) * (starRingEnd R) (M b₂ x_1)) := by
      rw [ show ( Finset.univ.filter fun x : A × Fin n => c₁ = x.2 ) = Finset.image ( fun x : A => ( x, c₁ ) ) Finset.univ from ?_, show ( Finset.univ.filter fun x : A × Fin n => x.2 = c₂ ) = Finset.image ( fun x : A => ( x, c₂ ) ) Finset.univ from ?_ ];
      · simp [ Finset.sum_image ];
      · ext ⟨ x, y ⟩ ; simp ;
        exact eq_comm;
      · ext ⟨ x, y ⟩ ; simp [ eq_comm ];
    have h_inner : ∀ x x_1, ∑ x_2, ∑ x_3 ∈ {x} ∩ if x_1 = x_2 then Finset.univ else ∅, M b₁ x_3 * (starRingEnd R) (M b₂ x_2) * m (x, c₁) (x_1, c₂) = M b₁ x * (starRingEnd R) (M b₂ x_1) * m (x, c₁) (x_1, c₂) := by
      intro x x_1
      rw [ Finset.sum_eq_single x_1 ] <;> simp +contextual;
      simp +contextual [ eq_comm ];
    simp only [ h_inner ];
    simpa only [ mul_assoc, mul_comm, mul_left_comm ] using h_reindex

  obtain ⟨m', rfl⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp h
  convert Matrix.posSemidef_conjTranspose_mul_self (m' * (M ⊗ₖ 1 : Matrix (B × Fin n) (A × Fin n) R).conjTranspose) using 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  congr
  ext
  simp +contextual [Matrix.one_apply, apply_ite]
  tauto

--TODO: PULLOUT and then use this to rewrite `Matrix.reindex_eq_conj` too.
theorem _root_.Matrix.submatrix_eq_mul_mul {d₂ d₃ : Type*} [DecidableEq d] (A : Matrix d d R) (e : d₂ → d) (f : d₃ → d) :
    A.submatrix e f = (Matrix.submatrix (α := R) 1 e _root_.id : Matrix d₂ d R) * A *
      (Matrix.submatrix (α := R) 1 _root_.id f) := by
  rw [show _root_.id = Equiv.refl d by rfl, Matrix.mul_submatrix_one, Matrix.one_submatrix_mul]
  simp

/-- `MatrixMap.submatrix` is completely positive -/
theorem submatrix (f : B → A) : (MatrixMap.submatrix R f).IsCompletelyPositive := by
  convert conj_isCompletelyPositive (Matrix.submatrix (α := R) 1 f _root_.id : Matrix B A R)
  ext1 m
  simp [m.submatrix_eq_mul_mul]

/-- The channel X ↦ ∑ k : κ, (M k) * X * (M k)ᴴ formed by Kraus operators M : κ → Matrix B A R
is completely positive -/
theorem of_kraus_isCompletelyPositive {κ : Type*} [Fintype κ] (M : κ → Matrix B A R) :
    (MatrixMap.of_kraus M M).IsCompletelyPositive := by
  rw [of_kraus]
  exact finset_sum (fun i ↦ conj_isCompletelyPositive (M i))

theorem exists_kraus (Φ : MatrixMap A B R) (hCP : Φ.IsCompletelyPositive) :
    ∃ r : ℕ, ∃ (M : Fin r → Matrix B A R), Φ = of_kraus M M :=
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
