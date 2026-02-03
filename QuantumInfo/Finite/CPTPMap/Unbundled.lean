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
  obtain ⟨n, ⟨e⟩⟩ : ∃ n : ℕ, Nonempty (T ≃ Fin n) :=
    Finite.exists_equiv_fin T
  convert h n using 1
  have h_submatrix : (M ⊗ₖₘ (LinearMap.id : MatrixMap T T R)) = (MatrixMap.submatrix R (fun p : B × T => (p.1, e p.2)) ∘ₗ (M ⊗ₖₘ (LinearMap.id : MatrixMap (Fin n) (Fin n) R)) ∘ₗ MatrixMap.submatrix R (fun p : A × Fin n => (p.1, e.symm p.2))) := by
    ext
    simp only [submatrix, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Matrix.submatrix_apply]
    rw [MatrixMap.kron_def, MatrixMap.kron_def]
    simp only [Matrix.single, LinearMap.id_coe, id_eq, Matrix.of_apply, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Matrix.submatrix];
    congr! 4
    rw [← Equiv.sum_comp e]
    congr! 2
    rw [← Equiv.sum_comp e]
    simp only [EmbeddingLike.apply_eq_iff_eq, Equiv.symm_apply_apply]
  constructor
  · intro h₂
    simp [MatrixMap.IsPositive]
    exact h n
  · intro h x hx
    specialize h (hx.submatrix (fun p : A × Fin n => (p.1, e.symm p.2)))
    rw [h_submatrix]
    simp only [LinearMap.coe_comp, Function.comp_apply, submatrix_apply]
    exact h.submatrix _

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

noncomputable section AristotleLemmas

omit [Fintype B] in
theorem choi_of_kraus {κ : Type*} [Fintype κ] (K : κ → Matrix B A ℂ) :
  (MatrixMap.of_kraus K K).choi_matrix = ∑ k, Matrix.vecMulVec (fun (x : B × A) => K k x.1 x.2) (fun (x : B × A) => star (K k x.1 x.2)) := by
    -- By definition of Choi matrix, we can expand the left-hand side using the linearity of the map and the properties of the Choi matrix.
    ext ⟨b₁, a₁⟩ ⟨b₂, a₂⟩
    simp [MatrixMap.choi_matrix, MatrixMap.of_kraus];
    -- By definition of the sum, the entry (b₁, b₂) of the sum of the Choi matrices of each Kraus operator is the sum of the entries (b₁, b₂) of each individual Choi matrix.
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.single];
    -- Since the inner sum over `x_2` will only contribute when `x_2 = a₁` and `x_1 = a₂`, we can simplify the expression.
    have h_inner : ∀ x : κ, ∑ x_1 : A, (∑ x_2 : A, if a₁ = x_2 ∧ a₂ = x_1 then K x b₁ x_2 else 0) * (starRingEnd ℂ) (K x b₂ x_1) = (K x b₁ a₁) * (starRingEnd ℂ) (K x b₂ a₂) := by
      simp [ Finset.sum_ite, Finset.filter_eq, Finset.filter_and ];
      intro x; rw [ Finset.sum_eq_single a₂ ] <;> aesop;
    exact Finset.sum_congr rfl fun _ _ => h_inner _

def congruence (M : Matrix B A ℂ) : MatrixMap A B ℂ where
  toFun X := M * X * M.conjTranspose
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' r X := by simp [Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq A] in
theorem congruence_isPositive (M : Matrix B A ℂ) : (congruence M).IsPositive := by
  exact fun X hX => hX.mul_mul_conjTranspose_same M

omit [DecidableEq A] in
theorem IsPositive_sum {ι : Type*} [Fintype ι] (f : ι → MatrixMap A B ℂ) (h : ∀ i, (f i).IsPositive) :
    (∑ i, f i).IsPositive := by
  intro X hX;
  replace hX : ∀ i, ((f i) X).PosSemidef := fun i => h i hX;
  simp [Matrix.PosSemidef, Matrix.IsHermitian] at hX ⊢
  simp [Matrix.conjTranspose_sum, Matrix.mulVec, dotProduct] at hX ⊢
  simp [Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul] at hX ⊢
  constructor
  · simp [hX]
  field_simp
  simp_rw [mul_assoc, mul_comm ((f _) X _ _), ← mul_assoc]
  intro x
  rw [Finset.sum_comm_cycle]
  exact Finset.sum_nonneg fun i _ => by simpa [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] using hX i |>.2 x;

omit [DecidableEq A] in
theorem of_kraus_isPositive {κ : Type*} [Fintype κ] (K : κ → Matrix B A ℂ) :
  (MatrixMap.of_kraus K K).IsPositive := by
  rw [MatrixMap.of_kraus]
  apply IsPositive_sum
  intro k
  exact congruence_isPositive (K k)

theorem congruence_kron {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (M : Matrix B A ℂ) (N : Matrix D C ℂ) :
  congruence M ⊗ₖₘ congruence N = congruence (M ⊗ₖ N) := by
    apply LinearMap.ext;
    intro x
    have h_eq : ∀ (X : Matrix A A ℂ) (Y : Matrix C C ℂ), (congruence M ⊗ₖₘ congruence N) (X ⊗ₖ Y) = (congruence (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) M N)) (X ⊗ₖ Y) := by
      intro X Y;
      convert MatrixMap.kron_map_of_kron_state _ _ X Y using 1;
      ext ⟨ b₁, d₁ ⟩ ⟨ b₂, d₂ ⟩
      simp only [Matrix.kroneckerMap]
      ring_nf
      simp [congruence, Matrix.mul_apply]
      simp only [mul_left_comm, mul_comm, Finset.mul_sum _ _ _, mul_assoc, Finset.sum_mul];
      simp only [← Finset.univ_product_univ, ← Finset.sum_product'];
      refine' Finset.sum_bij (fun x _ => ( x.1.2, x.2.2, x.1.1, x.2.1 )) _ _ _ _ <;> simp;
    -- By linearity, it suffices to show that the maps agree on a basis.
    have h_basis : ∀ (x : Matrix (A × C) (A × C) ℂ), x ∈ Submodule.span ℂ (Set.range (fun (p : Matrix A A ℂ × Matrix C C ℂ) => p.1 ⊗ₖ p.2)) → (congruence M ⊗ₖₘ congruence N) x = (congruence (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) M N)) x := by
      intro x hx;
      induction hx using Submodule.span_induction;
      · rename_i h
        simp only [Set.mem_range, Prod.exists] at h
        obtain ⟨w, ⟨w', rfl⟩⟩ := h
        apply h_eq
      · simp [congruence];
      · simp_all
      · simp_all
    convert h_basis x _;
    -- By definition of matrix multiplication and the properties of the Kronecker product, we can express any matrix as a sum of Kronecker products of basis matrices.
    have h_decomp : ∀ (x : Matrix (A × C) (A × C) ℂ), ∃ (coeffs : A → C → A → C → ℂ), x = ∑ a₁, ∑ c₁, ∑ a₂, ∑ c₂, coeffs a₁ c₁ a₂ c₂ • Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (Matrix.single a₁ a₂ 1) (Matrix.single c₁ c₂ 1) := by
      intro x
      use fun a₁ c₁ a₂ c₂ => x (a₁, c₁) (a₂, c₂);
      ext ⟨ a₁, c₁ ⟩ ⟨ a₂, c₂ ⟩
      simp only [Matrix.single]
      simp only [Matrix.sum_apply, Matrix.kroneckerMap]
      rw [ Finset.sum_eq_single a₁ ] <;> simp [Finset.sum_ite]
      · rw [ Finset.sum_eq_single c₁ ] <;> simp +contextual
        rw [ Finset.sum_eq_single c₂ ] <;> simp +contextual;
      · simp +contextual [Finset.filter_eq', Finset.filter_and ];
    obtain ⟨ coeffs, rfl ⟩ := h_decomp x;
    exact Submodule.sum_mem _ fun a₁ _ => Submodule.sum_mem _ fun c₁ _ => Submodule.sum_mem _ fun a₂ _ => Submodule.sum_mem _ fun c₂ _ => Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ ( Matrix.single a₁ a₂ 1, Matrix.single c₁ c₂ 1 ), rfl ⟩ )

theorem congruence_one_eq_id : congruence (1 : Matrix A A ℂ) = MatrixMap.id A ℂ := by
  ext x
  simp [congruence]

theorem congruence_CP {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (M : Matrix B A ℂ) : (congruence M).IsCompletelyPositive := by
  intro n;
  -- The tensor product of congruence maps is a congruence map.
  have h_tensor_congruence : congruence M ⊗ₖₘ LinearMap.id = congruence (M ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    convert congruence_kron M ( 1 : Matrix ( Fin n ) ( Fin n ) ℂ );
    -- The identity map is equal to the congruence map with the identity matrix because multiplying by the identity matrix doesn't change the matrix.
    ext M
    simp [congruence]
  convert congruence_isPositive ( M ⊗ₖ ( 1 : Matrix ( Fin n ) ( Fin n ) ℂ ) ) using 1

theorem IsCompletelyPositive_sum {ι : Type*} [Fintype ι] (f : ι → MatrixMap A B ℂ) (h : ∀ i, (f i).IsCompletelyPositive) :
    (∑ i, f i).IsCompletelyPositive := by
      convert IsCompletelyPositive.finset_sum h using 1

omit [Fintype B] [DecidableEq A] in
theorem of_kraus_eq_sum_congruence {κ : Type*} [Fintype κ] (K : κ → Matrix B A ℂ) :
  MatrixMap.of_kraus K K = ∑ k, congruence (K k) := by
  ext
  simp [MatrixMap.of_kraus, congruence]

theorem of_kraus_CP {κ : Type*} [Fintype κ] (K : κ → Matrix B A ℂ) :
  (MatrixMap.of_kraus K K).IsCompletelyPositive := by
    -- By definition of `MatrixMap.of_kraus`, we know that it is a sum of congruence maps.
    have h_sum_congruence : MatrixMap.of_kraus K K = ∑ k, congruence (K k) := by
      -- By definition of `MatrixMap.of_kraus`, we know that it is equal to the sum of the congruence maps of each Kraus operator.
      apply MatrixMap.IsCompletelyPositive.of_kraus_eq_sum_congruence;
    have h_congruence_CP : ∀ k, (congruence (K k)).IsCompletelyPositive := by
      intro k; exact (by
      convert congruence_CP ( K k ) using 1;
      -- Since B is a finite type, we can use the fact that finite types have decidable equality.
      apply Classical.decEq);
    exact h_sum_congruence.symm ▸ IsCompletelyPositive_sum _ h_congruence_CP

theorem exists_kraus_of_choi_PSD {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (C : Matrix (B × A) (B × A) ℂ) (hC : C.PosSemidef) :
    ∃ (κ : Type) (_ : Fintype κ) (K : κ → Matrix B A ℂ), C = (MatrixMap.of_kraus K K).choi_matrix := by
  -- Since $C$ is positive semidefinite, it has a spectral decomposition $C = \sum_i \lambda_i u_i u_i^\dagger$ where $\lambda_i \ge 0$. Let $v_i = \sqrt{\lambda_i} u_i$. Then $C = \sum_i v_i v_i^\dagger$.
  obtain ⟨κ, fκ, ⟨v, hv⟩⟩ : ∃ (κ : Type) (_f : Fintype κ), ∃ (v : κ → Matrix (B × A) Unit ℂ), C = ∑ k, Matrix.vecMulVec (fun (x : B × A) => v k x ()) (fun (x : B × A) => star (v k x ())) := by
    have h_eigen : ∀ (n : ℕ), ∀ (M : Matrix (Fin n) (Fin n) ℂ), M.PosSemidef → ∃ (κ : Type) (_f : Fintype κ), ∃ (v : κ → Matrix (Fin n) Unit ℂ), M = ∑ k, Matrix.vecMulVec (fun (x : Fin n) => v k x ()) (fun (x : Fin n) => star (v k x ())) := by
      intro n M hM
      use Fin n, inferInstance
      have := hM.1;
      have := Matrix.IsHermitian.spectral_theorem this;
      use fun k i _ => ( hM.1.eigenvectorUnitary : Matrix ( Fin n ) ( Fin n ) ℂ ) i k * ( hM.1.eigenvalues k |> RCLike.ofReal |> Real.sqrt )
      convert this using 1;
      ext i j; simp [ Matrix.mul_apply, Matrix.vecMulVec ]
      ring_nf
      simp [ Matrix.sum_apply, Matrix.diagonal ];
      exact Finset.sum_congr rfl fun _ _ => by rw [ ← Complex.ofReal_pow, Real.sq_sqrt ( hM.eigenvalues_nonneg _ ) ] ;
    -- Since $B \times A$ is a finite type, we can use the fact that it is equivalent to $\text{Fin}(\text{card}(B \times A))$.
    obtain ⟨n, hn⟩ : ∃ n : ℕ, Nonempty (B × A ≃ Fin n) := by
      exact ⟨ Fintype.card ( B × A ), ⟨ Fintype.equivFin _ ⟩ ⟩;
    obtain ⟨ e ⟩ := hn;
    obtain ⟨ κ, fκ, v, hv ⟩ := by
      apply h_eigen n ( Matrix.reindex e e C )
      simp_all [ Matrix.PosSemidef ];
      intro x;
      convert hC.2 ( fun i => x ( e i ) ) using 1;
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm ]
      rw [ ← Equiv.sum_comp e.symm ];
      apply Finset.sum_congr rfl fun i _ ↦ ?_
      rw [ ← Equiv.sum_comp e ]
      simp [ mul_assoc, mul_comm, mul_left_comm ]
    refine' ⟨ κ, fκ, fun k => Matrix.reindex e.symm ( Equiv.refl Unit ) ( v k ), _ ⟩;
    convert congr_arg ( Matrix.reindex e.symm e.symm ) hv using 1;
    · ext i j; simp [ Matrix.reindex_apply ] ;
    · ext i j
      simp [ Matrix.vecMulVec, Matrix.reindex_apply ] ;
      simp  [ Matrix.sum_apply, Matrix.of_apply ];
  -- Let $K_k(b, a) = v_k(b, a)$.
  set K : κ → Matrix B A ℂ := fun k => fun b a => v k (b, a) ();
  refine' ⟨ κ, fκ, K, hv.trans _ ⟩;
  convert choi_of_kraus K |> Eq.symm

end AristotleLemmas

/-- Choi's theorem on completely positive maps: A map `IsCompletelyPositive` iff its Choi Matrix is PSD. -/
theorem _root_.MatrixMap.choi_PSD_iff_CP_map (M : MatrixMap A B ℂ) :
    M.IsCompletelyPositive ↔ M.choi_matrix.PosSemidef := by
  by_cases hA : Nonempty A
  · constructor
    · intro hcp
      rw [choi_matrix_state_rep]
      apply Matrix.PosSemidef.smul _ (ha := by positivity)
      exact of_Fintype hcp A (MState.pure (Ket.MES A)).pos
    · by_contra h_not_CP
      obtain ⟨κ, fκ, K, hK⟩ : ∃ (κ : Type) (fκ : Fintype κ) (K : κ → Matrix B A ℂ), M.choi_matrix = (MatrixMap.of_kraus K K).choi_matrix := by
        convert exists_kraus_of_choi_PSD M.choi_matrix _;
        · exact Classical.decEq B;
        · grind;
      -- Since `MatrixMap.choi_matrix` is injective (`MatrixMap.choi_matrix_inj`), conclude `M = MatrixMap.of_kraus K K`.
      have hM_eq : M = MatrixMap.of_kraus K K := by
        exact MatrixMap.choi_matrix_inj hK;
      exact h_not_CP fun _ => hM_eq ▸ MatrixMap.IsCompletelyPositive.of_kraus_CP K
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

noncomputable section AristotleLemmas

/-
The Choi matrix of a map in symmetric Kraus form is a sum of rank-1 projectors.
-/
theorem MatrixMap.choi_of_kraus_R {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq A] [RCLike R]
    {κ : Type*} [Fintype κ] (K : κ → Matrix B A R) :
    (MatrixMap.of_kraus K K).choi_matrix = ∑ k, Matrix.vecMulVec (fun (x : B × A) => K k x.1 x.2) (fun (x : B × A) => star (K k x.1 x.2)) := by
  unfold MatrixMap.of_kraus MatrixMap.choi_matrix
  ext i j : 2
  simp [ Matrix.sum_apply, Matrix.mul_apply, Matrix.vecMulVec ]
  simp [ Matrix.single]
  simp +contextual [ Finset.sum_ite, Finset.filter_and ];
  congr! with k
  simp_all [Finset.filter_eq]
  rw [ Finset.sum_eq_single j.2 ]
  · simp
  · aesop
  · simp

/-
A positive semidefinite matrix can be written as a sum of rank-1 matrices $v v^*$.
-/
theorem Matrix.PosSemidef.eq_sum_vecMulVec {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    ∃ (r : ℕ) (v : Fin r → n → 𝕜), A = ∑ i, Matrix.vecMulVec (v i) (star (v i)) := by
      have := Matrix.IsHermitian.spectral_theorem hA.1;
      -- Since the eigenvalues are non-negative, we can write the diagonal matrix as a sum of rank-1 projectors.
      obtain ⟨r, v, hv⟩ : ∃ (r : ℕ) (v : Fin r → n → 𝕜), (Matrix.diagonal (RCLike.ofReal ∘ hA.1.eigenvalues)) = ∑ i, Matrix.vecMulVec (v i) (Star.star (v i)) := by
        -- Since the eigenvalues are non-negative, we can write the diagonal matrix as a sum of rank-1 projectors by taking the square root of each eigenvalue.
        have h_sqrt : ∃ (v : n → n → 𝕜), Matrix.diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) = ∑ i, Matrix.vecMulVec (fun j => v j i) (Star.star (fun j => v j i)) := by
          use fun j i => if j = i then RCLike.ofReal ( Real.sqrt ( hA.1.eigenvalues i ) ) else 0;
          ext i j; by_cases hij : i = j <;> simp [ hij, Matrix.vecMulVec ] ;
          · simp [ Matrix.sum_apply, Matrix.of_apply ];
            norm_cast ; rw [ Real.mul_self_sqrt ( hA.eigenvalues_nonneg _ ) ];
          · rw [ Finset.sum_apply, Finset.sum_apply ]
            simp
            exact Or.inr fun h => False.elim ( hij ( h.symm ) );
        obtain ⟨ v, hv ⟩ := h_sqrt
        use Fintype.card n, fun i => fun j => v j (Fintype.equivFin n |>.symm i);
        convert hv using 1
        generalize_proofs at *;
        exact Fintype.sum_equiv (Fintype.equivFin n).symm _ _ (congrFun rfl);
      use r
      use fun i => ( hA.1.eigenvectorUnitary : Matrix n n 𝕜 ) |> Matrix.mulVec <| v i
      convert congr_arg ( fun m => ( hA.1.eigenvectorUnitary : Matrix n n 𝕜 ) * m * Star.star ( hA.1.eigenvectorUnitary : Matrix n n 𝕜 ) ) hv using 1;
      simp [ Matrix.mul_sum, Matrix.sum_mul, Matrix.vecMulVec ];
      ext i j
      simp [Matrix.mulVec, dotProduct]
      simp [Matrix.mul_apply, Matrix.sum_apply, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm ];
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )

/-
The Choi matrix of M is the result of applying M \otimes I to the unnormalized maximally entangled state (Choi matrix of identity).
-/
variable {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq A] [RCLike R]

theorem choi_eq_kron_id_apply_choi_id (M : MatrixMap A B R) :
    M.choi_matrix = (M ⊗ₖₘ MatrixMap.id A R) ((MatrixMap.id A R).choi_matrix) := by
  ext ⟨j₁, a₁⟩ ⟨j₂, a₂⟩ : 2
  rw [ MatrixMap.kron_def ]
  simp [ MatrixMap.choi_matrix, Matrix.single ]
  simp [ ← Finset.sum_filter, Finset.filter_eq', Finset.filter_and]
  rw [ Finset.sum_eq_single a₁ ]
  · simp +contextual
    rw [ Finset.sum_eq_single a₂ ]
    · rw [ Finset.sum_eq_single a₁ ] <;> aesop
    · simp
      intro b hb
      rw [ Finset.sum_eq_zero ]
      aesop
    · simp
  · simp +contextual only
    rename_i x x_1
    intro b a
    split_ifs with h <;> simp [h]
  · simp +contextual

/-
The Choi matrix of the identity map is positive semidefinite.
-/
theorem choi_id_is_PSD {A R : Type*} [Fintype A] [DecidableEq A] [RCLike R] :
    (MatrixMap.id A R).choi_matrix.PosSemidef := by
  -- Let $v$ be the vector with $v_{(a,b)} = \delta_{ab}$.
  set v : A × A → R := fun p => if p.1 = p.2 then 1 else 0;
  -- By definition of $C$, we know that $C = v v^*$.
  have hC : (MatrixMap.id A R).choi_matrix = Matrix.of (fun (i j : A × A) => v i * star (v j)) := by
    ext ⟨ i, j ⟩ ⟨ k, l ⟩ ; simp [ MatrixMap.choi_matrix, Matrix.single ] ; aesop;
  refine' ⟨ _, fun x => _ ⟩;
  · ext i j; aesop;
  · -- By definition of $v$, we know that $star x ⬝ᵥ v v^* x = |star x ⬝ᵥ v|^2$.
    have h_inner : star x ⬝ᵥ (MatrixMap.id A R).choi_matrix.mulVec x = star (star x ⬝ᵥ v) * (star x ⬝ᵥ v) := by
      simp [ hC, Matrix.mulVec, dotProduct ];
      simp [ Finset.mul_sum, mul_comm, v]
      exact Finset.sum_congr rfl fun i hi => by split_ifs <;> simp [ * ] ;
    rw [ h_inner, mul_comm ];
    exact mul_star_self_nonneg (star x ⬝ᵥ v)

/-
If a map is completely positive, its Choi matrix is positive semidefinite.
-/
theorem is_CP_implies_choi_PSD {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [RCLike R] (M : MatrixMap A B R) (hCP : M.IsCompletelyPositive) :
    M.choi_matrix.PosSemidef := by
  rw [choi_eq_kron_id_apply_choi_id]
  exact MatrixMap.IsCompletelyPositive.of_Fintype hCP A choi_id_is_PSD

end AristotleLemmas

theorem exists_kraus (Φ : MatrixMap A B R) (hCP : Φ.IsCompletelyPositive) :
    ∃ r : ℕ, ∃ (M : Fin r → Matrix B A R), Φ = of_kraus M M := by
  -- By `Matrix.PosSemidef.eq_sum_vecMulVec`, there exist vectors `v : Fin r → B × A → R` such that `Φ.choi_matrix = ∑ i, vecMulVec (v i) (star (v i))`.
    obtain ⟨r, v, hv⟩ : ∃ (r : ℕ) (v : Fin r → B × A → R), Φ.choi_matrix = ∑ i, Matrix.vecMulVec (v i) (star (v i)) := by
      convert Matrix.PosSemidef.eq_sum_vecMulVec _;
      classical exacts [ inferInstance, inferInstance, is_CP_implies_choi_PSD Φ hCP ];
    refine' ⟨ r, fun i => Matrix.of ( fun b a => v i ( b, a ) ), _ ⟩;
    have h_choi_eq : Φ.choi_matrix = (MatrixMap.of_kraus (fun i => Matrix.of (fun b a => v i (b, a))) (fun i => Matrix.of (fun b a => v i (b, a)))).choi_matrix := by
      rw [ hv, MatrixMap.choi_of_kraus_R ];
      rfl;
    exact MatrixMap.choi_matrix_inj h_choi_eq

noncomputable section AristotleLemmas

/--
The Kronecker product of two Kraus maps is the Kraus map of the Kronecker products of the operators.
-/
theorem kron_of_kraus {A B C D R : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq C] [CommSemiring R] [StarRing R] [SMulCommClass R R R]
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (M : κ → Matrix B A R) (N : ι → Matrix D C R) :
    of_kraus M M ⊗ₖₘ of_kraus N N =
    of_kraus (fun (k : κ × ι) => M k.1 ⊗ₖ N k.2) (fun k => M k.1 ⊗ₖ N k.2) := by
  open Classical
  in convert MatrixMap.choi_map_inv _ using 1;
  rotate_left
  · infer_instance
  · infer_instance
  rw [choi_map_inv]
  apply MatrixMap.choi_matrix_inj
  ext ⟨ b, a ⟩ ⟨ d, c ⟩
  simp only [of_kraus] ;
  simp only [choi_matrix, LinearMap.coeFn_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]
  rw [ MatrixMap.kron_def ]
  simp only [LinearMap.coeFn_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    star_mul'] ;
  simp only [Matrix.single, Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite, not_and,
    Finset.sum_const_zero, add_zero, ne_eq];
  simp only [Finset.sum_sigma', Finset.univ_sigma_univ];
  simp only [mul_comm, Finset.mul_sum, Finset.sum_sigma', mul_left_comm, mul_assoc];
  refine Finset.sum_bij ( fun x _ => ⟨ ⟨ ⟨ x.snd.snd.fst.fst, x.snd.fst.fst.fst ⟩, x.snd.snd.fst.snd, x.snd.fst.fst.snd ⟩, x.snd.snd.snd, x.snd.fst.snd ⟩ ) ?_ ?_ ?_ ?_
  · simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, and_imp]
    grind
  · simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, Sigma.mk.injEq,
      Prod.mk.injEq, heq_eq_eq, and_imp]
    grind
  · simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, exists_prop,
      Sigma.exists, existsAndEq, and_true, exists_and_left, and_imp]
    grind
  · simp

end AristotleLemmas

/-- The Kronecker product of IsCompletelyPositive maps is also completely positive. -/
theorem kron [DecidableEq C] [Fintype D] {M₁ : MatrixMap A B R} {M₂ : MatrixMap C D R}
    (h₁ : M₁.IsCompletelyPositive) (h₂ : M₂.IsCompletelyPositive) : IsCompletelyPositive (M₁ ⊗ₖₘ M₂) := by
  obtain ⟨r₁, K₁, rfl⟩ := exists_kraus M₁ h₁
  obtain ⟨r₂, K₂, rfl⟩ := exists_kraus M₂ h₂
  rw [kron_of_kraus K₁ K₂]
  apply of_kraus_isCompletelyPositive

end IsCompletelyPositive

end MatrixMap
