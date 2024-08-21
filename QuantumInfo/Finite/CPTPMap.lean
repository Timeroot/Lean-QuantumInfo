import QuantumInfo.Finite.MState
import QuantumInfo.Finite.Unitary
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.Data.Set.Card

/-- A `MatrixMap` is a linear map between squares matrices of size A to size B, over R. -/
abbrev MatrixMap (A B R : Type*) [Semiring R] := Matrix A A R →ₗ[R] Matrix B B R

namespace MatrixMap

section matrix
variable {A B C D E F R : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F] [Semiring R]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Choi matrix of a given linear matrix map. Note that this is defined even for things that
  aren't CPTP, it's just rarely talked about in those contexts. -/
def choi_matrix (M : MatrixMap A B R) : Matrix (A × B) (A × B) R :=
  fun (i₁,j₁) (i₂,j₂) ↦ M (Matrix.stdBasisMatrix i₁ i₂ 1) j₁ j₂

def of_choi_matrix (M : Matrix (A × B) (A × B) R) : MatrixMap A B R :=
  sorry
  -- fun (j₁,j₂) (i₁,i₂) ↦ M (i₁,j₁) (i₂,j₂)

@[simp]
theorem map_choi_inv (M : Matrix (A × B) (A × B) R) : choi_matrix (of_choi_matrix M) = M :=
  sorry--rfl

@[simp]
theorem choi_map_inv (M : MatrixMap A B R) : of_choi_matrix (choi_matrix M) = M :=
  sorry

  -- suffices asMatrixMap (matrixMap_kron M 1) x' = Matrix.submatrix (asMatrixMap M x) eqB eqB by
  --   rw [← Matrix.posSemidef_submatrix_equiv eqB, ← this]
  --   exact hM 1 (hx.PosSemidef_kronecker Matrix.PosSemidef.one)
  -- unfold_let eqB x'
  -- ext ⟨a1,aU⟩ ⟨b1,bU⟩
  -- simp [submatrix, Fin.fin_one_eq_zero, Matrix.mulVec, Matrix.dotProduct, asMatrixMap, matrixMap_kron]

-- theorem asMatrixMap_mul (M₁ : Matrix (C × D) (A × B) R) (M₂ : Matrix (E × F) (C × D) R) :
--     (M₂ * M₁).asMatrixMap = M₂.asMatrixMap ∘ M₁.asMatrixMap := by
--   ext x i j
--   simp only [asMatrixMap, mulVec, dotProduct, Fintype.sum_prod_type, of_apply, mul_assoc,
--     Function.comp_apply, Prod.mk.eta, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
--   rw [Finset.sum_comm_3]
--   congr 1
--   ext c
--   rw [Finset.sum_comm_3]

variable {R : Type*} [CommSemiring R]

/-- Linear equivalence between MatrixMap's and matrices on a larger space. -/
noncomputable def toMatrix : MatrixMap A B R ≃ₗ[R] Matrix (B × B) (A × A) R :=
  LinearMap.toMatrix (Matrix.stdBasis R A A) (Matrix.stdBasis R B B)

theorem toMatrix_comp (M₁ : MatrixMap A B R) (M₂ : MatrixMap B C R) : toMatrix (M₂ ∘ₗ M₁) = (toMatrix M₂) * (toMatrix M₁) :=
  LinearMap.toMatrix_comp _ _ _ M₂ M₁

-- /-- The canonical tensor product on linear maps between matrices, where a map from
--   M[A,B] to M[C,D] is given by M[A×C,B×D]. This tensor product acts independently on
--   Kronecker products and gives Kronecker products as outputs. -/
-- def matrixMap_kron (M₁ : Matrix (A₁ × B₁) (C₁ × D₁) R) (M₂ : Matrix (A₂ × B₂) (C₂ × D₂) R) : Matrix ((A₁ × A₂) × (B₁ × B₂)) ((C₁ × C₂) × (D₁ × D₂)) R :=
--   Matrix.of fun ((a₁, a₂), (b₁, b₂)) ((c₁, c₂), (d₁, d₂)) ↦
--     (M₁ (a₁, b₁) (c₁, d₁)) * (M₂ (a₂, b₂) (c₂, d₂))

theorem choi_matrix_inj : Function.Injective (@choi_matrix A B R _ _) := by
  intro x y h
  simpa only [choi_map_inv] using congrArg of_choi_matrix h

end matrix

section prod

variable {A B C D R : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable [CommSemiring R] [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

noncomputable def MatrixMap_Prod (M₁ : MatrixMap A B R) (M₂ : MatrixMap C D R) : MatrixMap (A × C) (B × D) R :=
  let h₁ := (LinearMap.toMatrix (Basis.tensorProduct (Matrix.stdBasis R A A) (Matrix.stdBasis R C C))
      (Basis.tensorProduct (Matrix.stdBasis R B B) (Matrix.stdBasis R D D)))
    (TensorProduct.map M₁ M₂);
  let r₁ := Equiv.prodProdProdComm B B D D;
  let r₂ := Equiv.prodProdProdComm A A C C;
  let h₂ := Matrix.reindex r₁ r₂ h₁;
  Matrix.toLin (Matrix.stdBasis R (A × C) (A × C)) (Matrix.stdBasis R (B × D) (B × D)) h₂

open BigOperators
theorem MatrixMap_Prod_def (M₁ : MatrixMap A B R) (M₂ : MatrixMap C D R) (M : Matrix (A × C) (A × C) R) : MatrixMap_Prod M₁ M₂ M (b₁, d₁) (b₂, d₂) =
  ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂, (M₁ (Matrix.stdBasisMatrix a₁ a₂ 1) b₁ b₂) * (M₂ (Matrix.stdBasisMatrix c₁ c₂ 1) d₁ d₂) * (M (a₁, c₁) (a₂, c₂)) := by
  -- dsimp [MatrixMap_Prod]
  -- rw [Matrix.toLin]
  -- dsimp [LinearMap.toMatrix, MatrixMap, Matrix.stdBasis, Matrix.reindex]
  -- simp [Matrix.submatrix, Pi.basis, Matrix.mulVec]
  -- simp_rw [Matrix.dotProduct]
  -- simp
  sorry

open Kronecker
theorem MatrixMap_Prod_kron (M₁ : MatrixMap A B R) (M₂ : MatrixMap C D R) (MA : Matrix A A R) (MC : Matrix C C R) : MatrixMap_Prod M₁ M₂ (MA ⊗ₖ MC) = (M₁ MA) ⊗ₖ (M₂ MC) := by
  ext bd₁ bd₂
  let (b₁, d₁) := bd₁
  let (b₂, d₂) := bd₂
  rw [MatrixMap_Prod_def]
  simp only [Matrix.kroneckerMap_apply]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp_rw [mul_comm (M₂ _ _ _), mul_assoc, ← Finset.mul_sum, ← mul_assoc]
  simp_rw [← Finset.sum_mul]
  congr
  -- simp_rw [← Matrix.stdBasis_eq_stdBasisMatrix ]
  -- unfold Matrix.stdBasisMatrix
  -- simp_rw [← LinearMap.sum_apply]
  -- simp
  sorry
  sorry

end prod

variable {A B C D E F R : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq F]

open Kronecker
open TensorProduct

/-- A linear matrix map is *trace preserving* if trace of the output equals trace of the input. -/
def IsTracePreserving [Semiring R] (M : MatrixMap A B R) : Prop :=
  ∀ (x : Matrix A A R), (M x).trace = x.trace

/-- The trace of a Choi matrix of a TP map is the cardinality of the input space. -/
theorem trace_choi_iff_TP_map [Semiring R] (M : MatrixMap A B R) : M.IsTracePreserving
    ↔ M.choi_matrix.trace = (Finset.univ (α := A)).card :=
  sorry

open ComplexOrder
variable [RCLike R]

/-- A linear matrix map is *Hermitian preserving* if it maps `IsHermitian` matrices to `IsHermitian`.-/
def IsHermitianPreserving (M : MatrixMap A B R) : Prop :=
  ∀{x}, x.IsHermitian → (M x).IsHermitian

/-- A linear matrix map is *positive* if it maps `PosSemidef` matrices to `PosSemidef`.-/
def IsPositive (M : MatrixMap A B R) : Prop :=
  ∀{x}, x.PosSemidef → (M x).PosSemidef

/-- A linear matrix map is *completely positive* if, for any integer n, the tensor product
with `I(n)` is positive. -/
def IsCompletelyPositive (M : MatrixMap A B R) : Prop :=
  ∀ (n : ℕ), (MatrixMap_Prod M (LinearMap.id : MatrixMap (Fin n) (Fin n) R)).IsPositive

namespace IsTracePreserving

theorem comp [CommSemiring R] {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R} (h₁ : M₁.IsTracePreserving) (h₂ : M₂.IsTracePreserving) :
    IsTracePreserving (M₂ ∘ₗ M₁) := by
  sorry

end IsTracePreserving

namespace IsCompletelyPositive

/-- A completely positive map, but with `Fintype F` instead of Fin. -/
theorem IsCompletelyPositive_Fintype {M : MatrixMap A B R} (h : IsCompletelyPositive M)
    (T : Type*) [Fintype T] [DecidableEq T ] :
    (MatrixMap_Prod M (LinearMap.id : MatrixMap T T R)).IsPositive := by
  sorry

end IsCompletelyPositive

/-- Choi's theorem on completely positive maps: Complete Positivity iff Choi Matrix is PSD. -/
theorem choi_PSD_iff_CP_map (M : MatrixMap A B ℂ) : M.IsCompletelyPositive
    ↔ M.choi_matrix.PosSemidef :=
  sorry

--TODO: Positive maps are all Hermitian preserving, because positive matrices generate the full
--set of Hermitian matrices (generate as a vector space). Concretely, every pair of elements
-- (i,j) and (j,i) must be conjugate because we can look at the PSD matrices with 1's on (i,i),
-- on (j,j), and on all 4 elements (i or j, i or j).
theorem IsPositive.IsHermitianPreserving (M : MatrixMap A B R)
    (hM : IsPositive M) : IsHermitianPreserving M := by
  sorry

theorem IsCompletelyPositive.IsPositiveMap (M : MatrixMap A B R)
    (hM : IsCompletelyPositive M) : IsPositive M := by
  intro x hx
  let x' : Matrix (A × Fin 1) (A × Fin 1) R := x ⊗ₖ 1
  let eqB : (B × Fin 1) ≃ B :=
    (Equiv.prodCongrRight (fun _ ↦ finOneEquiv)).trans (Equiv.prodPUnit B)
  sorry

end MatrixMap

variable (dIn dOut dOut₂ : Type*) [Fintype dIn] [Fintype dOut] [Fintype dOut₂] [DecidableEq dIn]

/-- Positive trace-preserving linear maps. These includes all channels, but aren't
  necessarily *completely* positive, see `CPTPMap`. -/
structure PTPMap where
  map : MatrixMap dIn dOut ℂ
  pos : map.IsPositive
  trace_preserving : map.IsTracePreserving

/-- Quantum channels, aka CPTP maps: completely positive trace preserving linear maps. -/
structure CPTPMap extends PTPMap dIn dOut where
  mk' ::
    completely_pos : map.IsCompletelyPositive

variable {dIn dOut dOut₂}

namespace PTPMap
noncomputable section
open ComplexOrder

@[ext]
theorem ext {Λ₁ Λ₂ : PTPMap dIn dOut} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ :=
  PTPMap.mk.injEq Λ₁.map _ _ _ _ _ ▸ h

theorem apply_PosSemidef (Λ : PTPMap dIn dOut) (hρ : ρ.PosSemidef) : (Λ.map ρ).PosSemidef :=
  Λ.pos hρ

theorem apply_trace (Λ : PTPMap dIn dOut) (ρ : Matrix dIn dIn ℂ) : (Λ.map ρ).trace = ρ.trace :=
  Λ.trace_preserving ρ

instance instFunLike : FunLike (PTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe Λ := fun ρ ↦ MState.mk (Λ.map ρ.m) (Λ.apply_PosSemidef ρ.pos) (ρ.tr ▸ Λ.apply_trace ρ.m)
  coe_injective' _ _ h := sorry

--If we have a PTPMap, the input and output dimensions are always both nonempty (otherwise
--we can't preserve trace) - or they're both empty. So `[Nonempty dIn]` will always suffice.
-- This would be nice as an `instance` but that would leave `dIn` as a metavariable.
theorem nonemptyOut (Λ : PTPMap dIn dOut) [hIn : Nonempty dIn] : Nonempty dOut := by
  by_contra h
  simp only [not_nonempty_iff] at h
  let M := (1 : Matrix dIn dIn ℂ)
  have := calc (Finset.univ.card (α := dIn) : ℂ)
    _ = M.trace := by simp [Matrix.trace, M]
    _ = (Λ.map M).trace := (Λ.trace_preserving M).symm
    _ = 0 := by simp only [Matrix.trace_eq_zero_of_isEmpty]
  norm_num [Finset.univ_eq_empty_iff] at this

end
end PTPMap

namespace CPTPMap
noncomputable section
open scoped Matrix ComplexOrder

def mk (map : MatrixMap dIn dOut ℂ) (h₁ : map.IsTracePreserving) (h₂ : map.IsCompletelyPositive) : CPTPMap dIn dOut :=
  ⟨⟨map, h₂.IsPositiveMap, h₁⟩, h₂⟩

@[simp]
theorem map_mk (map : MatrixMap dIn dOut ℂ) (h₁) (h₂) : (CPTPMap.mk map h₁ h₂).map = map :=
  rfl

variable {dM : Type*} [Fintype dM] [DecidableEq dM]
variable {dM₂ : Type*} [Fintype dM₂] [DecidableEq dM₂]

def choi (Λ : CPTPMap dIn dOut) := Λ.map.choi_matrix

theorem map_ext {Λ₁ Λ₂ : CPTPMap dIn dOut} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ :=
  CPTPMap.mk'.injEq Λ₁.toPTPMap _ _ _ ▸ (PTPMap.ext h)

theorem choi_ext {Λ₁ Λ₂ : CPTPMap dIn dOut} (h : Λ₁.choi = Λ₂.choi) : Λ₁ = Λ₂ :=
  CPTPMap.mk'.injEq Λ₁.toPTPMap _ _ _ ▸ (PTPMap.ext (MatrixMap.choi_matrix_inj h))

-- theorem ext_iff {Λ₁ Λ₂ : CPTPMap dIn dOut} : Λ₁.map_mat = Λ₂.map_mat ↔ Λ₁ = Λ₂ :=
--   CPTPMap.mk.injEq Λ₁.toPTPMap _ _ _ ▸ (PTPMap.ext h)

/-- The Choi matrix of a channel is PSD. -/
theorem choi_PSD_of_CPTP (Λ : CPTPMap dIn dOut) : Λ.map.choi_matrix.PosSemidef :=
  Λ.map.choi_PSD_iff_CP_map.1 Λ.completely_pos

/-- The trace of a Choi matrix of a CPTP map is the cardinality of the input space. -/
@[simp]
theorem Tr_of_choi_of_CPTP (Λ : CPTPMap dIn dOut) : Λ.choi.trace =
    (Finset.univ (α := dIn)).card :=
  (Λ.map.trace_choi_iff_TP_map).1 Λ.trace_preserving

/-- Build a CPTP map from a PSD Choi matrix with correct trace. -/
def CPTP_of_choi_PSD_Tr {M : Matrix (dIn × dOut) (dIn × dOut) ℂ} (h₁ : M.PosSemidef)
    (h₂ : M.trace = (Finset.univ (α := dIn)).card) : CPTPMap dIn dOut := CPTPMap.mk
  (map := MatrixMap.of_choi_matrix M)
  (h₁ := (MatrixMap.trace_choi_iff_TP_map _).2 (MatrixMap.map_choi_inv M ▸ h₂))
  (h₂ := (MatrixMap.choi_PSD_iff_CP_map _).2 ((MatrixMap.map_choi_inv M).symm ▸ h₁))

@[simp]
theorem choi_of_CPTP_of_choi (M : Matrix (dIn × dOut) (dIn × dOut) ℂ) {h₁} {h₂} :
    (CPTP_of_choi_PSD_Tr (M := M) h₁ h₂).choi = M := by
  sorry--rfl

instance instFunLike : FunLike (CPTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe Λ := fun ρ ↦ MState.mk (Λ.map ρ.m) (Λ.apply_PosSemidef ρ.pos) (ρ.tr ▸ Λ.apply_trace ρ.m)
  coe_injective' _ _ h := by sorry

theorem mat_coe_eq_apply_mat (Λ : CPTPMap dIn dOut) (ρ : MState dIn) : (Λ ρ).m = Λ.map ρ.m :=
  rfl

@[ext]
theorem ext {Λ₁ Λ₂ : CPTPMap dIn dOut} (h : ∀ ρ, Λ₁ ρ = Λ₂ ρ) : Λ₁ = Λ₂ := by
  apply DFunLike.coe_injective'
  funext
  exact (h _)

theorem ext_iff {Λ₁ Λ₂ : CPTPMap dIn dOut} : (∀ ρ, Λ₁ ρ = Λ₂ ρ) ↔ Λ₁ = Λ₂ :=
  ⟨ext, fun h _ ↦ h ▸rfl⟩

def compose (Λ₂ : CPTPMap dM dOut) (Λ₁ : CPTPMap dIn dM) : CPTPMap dIn dOut :=
  CPTPMap.mk (Λ₂.map ∘ₗ Λ₁.map)
  (Λ₁.trace_preserving.comp Λ₂.trace_preserving)
  (by sorry)

@[simp]
theorem compose_eq {Λ₁ : CPTPMap dIn dM} {Λ₂ : CPTPMap dM dOut} : ∀ρ, (Λ₂.compose Λ₁) ρ = Λ₂ (Λ₁ ρ) :=
  fun _ ↦ rfl

theorem compose_assoc  (Λ₃ : CPTPMap dM₂ dOut) (Λ₂ : CPTPMap dM dM₂) (Λ₁ : CPTPMap dIn dM) :
    (Λ₃.compose Λ₂).compose Λ₁ = Λ₃.compose (Λ₂.compose Λ₁) := by
  ext1 ρ
  simp

/-- The identity channel, which leaves the input unchanged. -/
def id : CPTPMap dIn dIn :=
  CPTPMap.mk LinearMap.id
  (by simp [MatrixMap.IsTracePreserving])
  (by sorry)

/-- The map `CPTPMap.id` leaves any matrix unchanged. -/
@[simp]
theorem id_fun_id (M : Matrix dIn dIn ℂ) : CPTPMap.id.map M = M := by
  ext
  simp [id]

/-- The map `CPTPMap.id` leaves the input state unchanged. -/
@[simp]
theorem id_MState (ρ : MState dIn) : CPTPMap.id ρ = ρ := by
  ext1
  rw [mat_coe_eq_apply_mat]
  exact id_fun_id ρ.m

/-- The map `CPTPMap.id` composed with any map is the same map. -/
@[simp]
theorem id_compose [DecidableEq dOut] (Λ : CPTPMap dIn dOut) : CPTPMap.id.compose Λ = Λ := by
  simp only [← ext_iff, compose_eq, id_MState, implies_true]

/-- Any map composed with `CPTPMap.id` is the same map. -/
@[simp]
theorem compose_id [DecidableEq dOut] (Λ : CPTPMap dIn dOut) : Λ.compose CPTPMap.id = Λ := by
  simp only [← ext_iff, compose_eq, id_MState, implies_true]

/-- There is a CPTP map that takes a system of any dimension and outputs the trivial Hilbert
space, 1-dimensional, indexed by `Unit`. -/
def destroy [Nonempty dIn] [Unique dOut] : CPTPMap dIn dOut :=
  CPTP_of_choi_PSD_Tr
    (M := (1 / Finset.univ.card (α := dIn) : ℂ) • 1)
    (by sorry)
    (by sorry)

/-- Two CPTP maps into the same one-dimensional output space must be equal -/
theorem eq_if_output_unique [Unique dOut] (Λ₁ Λ₂ : CPTPMap dIn dOut) : Λ₁ = Λ₂ :=
  ext fun _ ↦ (Unique.eq_default _).trans (Unique.eq_default _).symm

instance instUnique [Nonempty dIn] [Unique dOut] : Unique (CPTPMap dIn dOut) where
  default := destroy
  uniq := fun _ ↦ eq_if_output_unique _ _

--could go before destroy (in which case destroy is a special case), or after (building as a
-- composition with destroy and of_state)
-- /--The replacement channel that maps all inputs to a given state. -/
-- def replacement [Nonempty dIn] (ρ : MState dOut) : CPTPMap dIn dOut :=
--   CPTPMap.mk ...

/-- A state can be viewed as a CPTP map from the trivial Hilbert space (indexed by `Unit`)
 that outputs exactly that state. -/
def of_state (ρ : MState dOut) : CPTPMap Unit dOut :=
  sorry --need the canonical isomorphism from (Unit × d) ≃ d.
  -- CPTP_of_choi_PSD_Tr (M := ρ.m) (ρ.pos) (ρ.tr)

section prod
open Kronecker

variable {dI₁ dI₂ dO₁ dO₂ : Type*} [Fintype dI₁] [Fintype dI₂] [Fintype dO₁] [Fintype dO₂]
variable [DecidableEq dI₁] [DecidableEq dI₂] [DecidableEq dO₁] [DecidableEq dO₂]

/-- The tensor product of two CPTPMaps. -/
def prod (Λ₁ : CPTPMap dI₁ dO₁) (Λ₂ : CPTPMap dI₂ dO₂) : CPTPMap (dI₁ × dI₂) (dO₁ × dO₂) :=
  CPTPMap.mk
    (MatrixMap.MatrixMap_Prod Λ₁.map Λ₂.map)
    (by sorry)
    (by
      intro n M hM
      have M' : Matrix (dI₁ × (dI₂ × Fin n)) (dI₁ × (dI₂ × Fin n)) ℂ := sorry --reorder indices of M
      have hM' : M'.PosSemidef := sorry --PSD preserved under reordering
      let Λ₁M := ((Λ₁.map.MatrixMap_Prod LinearMap.id) M')
      have hΛ₁M : Λ₁M.PosSemidef := Λ₁.completely_pos.IsCompletelyPositive_Fintype (dI₂ × Fin n) hM'
      have Λ₁M' : Matrix (dI₂ × (dO₁ × Fin n)) (dI₂ × (dO₁ × Fin n)) ℂ := sorry --reorder Λ₁M
      have hΛ₁M' : Λ₁M'.PosSemidef := sorry --PSD preserved under reordering
      let Λ₂Λ₁M := (Λ₂.map.MatrixMap_Prod LinearMap.id) Λ₁M'
      have hΛ₂Λ₁M : Λ₂Λ₁M.PosSemidef := Λ₂.completely_pos.IsCompletelyPositive_Fintype (dO₁ × Fin n) hΛ₁M'
      --PSD preserved under reordering to get (((Λ₁.map.MatrixMap_Prod Λ₂.map).MatrixMap_Prod LinearMap.id) M)
      sorry
    )

notation ρL "⊗" ρR => prod ρL ρR

end prod

section finprod
section

variable {k : ℕ}
variable {dI : Fin k → Type v} [∀(i : Fin k), Fintype (dI i)] [∀(i : Fin k), DecidableEq (dI i)]
variable {dO : Fin k → Type w} [∀(i : Fin k), Fintype (dO i)] [∀(i : Fin k), DecidableEq (dO i)]

/-- Finitely-indexed tensor products of CPTPMaps, when the indices are Fin n.  -/
def fin_n_prod (Λi : (i : Fin k) → CPTPMap (dI i) (dO i)) : CPTPMap ((i:Fin k) → (dI i)) ((i:Fin k) → (dO i)) :=
  sorry

theorem fin_n_prod_1 {dI : Fin 1 → Type v} [Fintype (dI 0)] [DecidableEq (dI 0)] {dO : Fin 1 → Type w} [Fintype (dO 0)] [DecidableEq (dO 0)] (Λi : (i : Fin 1) → CPTPMap (dI 0) (dO 0)) :
    fin_n_prod Λi = CPTPMap.compose sorry ((Λi 1).compose sorry) :=
  sorry --TODO: permutations

end
section

variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable {dI : ι → Type v} [∀(i :ι), Fintype (dI i)] [∀(i :ι), DecidableEq (dI i)]
variable {dO : ι → Type w} [∀(i :ι), Fintype (dO i)] [∀(i :ι), DecidableEq (dO i)]

/-- Finitely-indexed tensor products of CPTPMaps.  -/
def fintype_prod (Λi : ι → CPTPMap (dI i) (dO i)) : CPTPMap ((i:ι) → dI i) ((i:ι) → dO i) :=
  sorry

end
end finprod

section trace
variable {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]

/-- Partial tracing out the left, as a CPTP map. -/
def trace_left : CPTPMap (d₁ × d₂) d₂ :=
  sorry

/-- Partial tracing out the right, as a CPTP map. -/
def trace_right : CPTPMap (d₁ × d₂) d₁ :=
  sorry

theorem trace_left_eq_MState_trace_left (ρ : MState (d₁ × d₂)) : trace_left ρ = ρ.trace_left :=
  sorry

theorem trace_right_eq_MState_trace_right (ρ : MState (d₁ × d₂)) : trace_right ρ = ρ.trace_right :=
  sorry

end trace

section equiv
variable [DecidableEq dOut]

/-- Given a equivalence (a bijection) between the types d₁ and d₂, that is, if they're
 the same dimension, then there's a CPTP channel for this. This is what we need for
 defining e.g. the SWAP channel, which is 'unitary' but takes heterogeneous input
 and outputs types (d₁ × d₂) and (d₂ × d₁). -/
def of_equiv (σ : dIn ≃ dOut) : CPTPMap dIn dOut :=
  sorry

theorem equiv_inverse (σ : dIn ≃ dOut)  : (of_equiv σ) ∘ (of_equiv σ.symm) = id :=
  sorry

variable {d₁ d₂ d₃ : Type*} [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]

--TODO: of_equiv (id) = id
--(of_equiv σ).compose (of_equiv τ) = of_equiv (σ ∘ τ)

/-- The SWAP operation, as a channel. -/
def SWAP : CPTPMap (d₁ × d₂) (d₂ × d₁) :=
  of_equiv (Equiv.prodComm d₁ d₂)

/-- The associator, as a channel. -/
def assoc : CPTPMap ((d₁ × d₂) × d₃) (d₁ × d₂ × d₃) :=
  of_equiv (Equiv.prodAssoc d₁ d₂ d₃)

/-- The inverse associator, as a channel. -/
def assoc' : CPTPMap (d₁ × d₂ × d₃) ((d₁ × d₂) × d₃) :=
  of_equiv (Equiv.prodAssoc d₁ d₂ d₃).symm

theorem assoc_assoc' : (assoc (d₁ := d₁) (d₂ := d₂) (d₃ := d₃)).compose assoc' = id :=
  sorry

end equiv

section unitary

/-- Conjugating density matrices by a unitary as a channel, standard unitary evolution. -/
def of_unitary (U : 𝐔[dIn]) : CPTPMap dIn dIn :=
  CPTP_of_choi_PSD_Tr (M := sorry) --v v†
    (sorry)
    (sorry)

/-- The unitary channel U conjugated by U. -/
theorem of_unitary_eq_conj (U : 𝐔[dIn]) (ρ : MState dIn) :
    (of_unitary U) ρ = ρ.U_conj U :=
  sorry

/-- A channel is unitary iff it is `of_unitary U`. -/
def IsUnitary (Λ : CPTPMap dIn dIn) : Prop :=
  ∃ U, Λ = of_unitary U

/-- A channel is unitary iff it can be written as conjugation by a unitary. -/
theorem IsUnitary_iff_U_conj (Λ : CPTPMap dIn dIn) : IsUnitary Λ ↔ ∃ U, ∀ ρ, Λ ρ = ρ.U_conj U := by
  simp_rw [IsUnitary, ← of_unitary_eq_conj, CPTPMap.ext_iff]

theorem IsUnitary_equiv (σ : dIn ≃ dIn) : IsUnitary (of_equiv σ) :=
  sorry

end unitary

/-- A channel is *entanglement breaking* iff its product with the identity channel
  only outputs separable states. -/
def EntanglementBreaking (Λ : CPTPMap dIn dOut) : Prop :=
  ∀ (dR : Type u_1) [Fintype dR] [DecidableEq dR], ∀ (ρ : MState (dR × dIn)),
    ((id ⊗ Λ) ρ).IsSeparable

--TODO:
--Theorem: entanglement breaking iff it holds for all channels, not just id.
--Theorem: entanglement break iff it breaks a Bell pair (Wilde Exercise 4.6.2)
--Theorem: entanglement break if c-q or q-c, e.g. measurements
--Theorem: eb iff Kraus operators can be written as all unit rank (Wilde Theorem 4.6.1)

section purify
variable [DecidableEq dOut] [Inhabited dOut]

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
  sorry

--TODO: Constructing this will probably need Kraus operators first.

theorem purify_IsUnitary (Λ : CPTPMap dIn dOut) : Λ.purify.IsUnitary :=
  sorry

/-- With a channel Λ : A → B, a valid purification (A×B×B)→(A×B×B) is such that:
 * Preparing the default ∣0⟩ state on two copies of B
 * Appending these to the input
 * Applying the purified unitary channel
 * Tracing out the two left parts of the output
is equivalent to the original channel. -/
theorem purify_trace (Λ : CPTPMap dIn dOut) : Λ = (
  let zero_prep : CPTPMap Unit (dOut × dOut) := CPTPMap.of_state (MState.pure (Ket.basis default))
  let prep := (id ⊗ zero_prep)
  let append : CPTPMap dIn (dIn × Unit) := CPTPMap.of_equiv (Equiv.prodPUnit dIn).symm
  CPTPMap.trace_left.compose $ CPTPMap.trace_left.compose $ Λ.purify.compose $ prep.compose append
  ) :=
  sorry

--TODO Theorem: `purify` is unique up to unitary equivalence.

--TODO: Best to rewrite the "zero_prep / prep / append" as one CPTPMap.append channel when we
-- define that.

/-- The complementary channel comes from tracing out the other half of the purified channel. -/
def complementary (Λ : CPTPMap dIn dOut) : CPTPMap dIn (dIn × dOut) :=
  let zero_prep : CPTPMap Unit (dOut × dOut) := CPTPMap.of_state (MState.pure (Ket.basis default))
  let prep := (id ⊗ zero_prep)
  let append : CPTPMap dIn (dIn × Unit) := CPTPMap.of_equiv (Equiv.prodPUnit dIn).symm
  CPTPMap.trace_right.compose $ CPTPMap.assoc'.compose $ Λ.purify.compose $ prep.compose append

end purify

section degradable
variable [DecidableEq dOut] [Inhabited dOut] [DecidableEq dOut₂] [Inhabited dOut₂]

/-- A channel is *degradable to* another, if the other can be written as a composition of
  a _degrading_ channel D with the original channel. -/
def IsDegradableTo (Λ : CPTPMap dIn dOut) (Λ₂ : CPTPMap dIn dOut₂) : Prop :=
  ∃ (D : CPTPMap dOut (dOut₂)), D.compose Λ = Λ₂

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

end
end CPTPMap
