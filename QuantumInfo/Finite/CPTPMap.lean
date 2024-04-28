import QuantumInfo.Finite.MState


--TODO: Give an actual definition of a channel. These lets are just so that it
--      binds the surrounding necessary variables and has the right type signature.

namespace Matrix

variable {A B C D E F R : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F] [DecidableEq A]
  [NonUnitalNonAssocSemiring R]
open Kronecker

/-- Given a `Matrix (C × D) (A × B) R`, this can also be viewed as a (linear) map from
  `Matrix A B R` → `Matrix C D R`.-/
def asMatrixMap (M : Matrix (C × D) (A × B) R) : Matrix A B R → Matrix C D R :=
    fun arg ↦
    let arg_vec : (A × B) → R := (fun ((i, j) : Prod A B) ↦ arg i j)
    Matrix.of (fun i j ↦ (M *ᵥ arg_vec) (i, j))

variable {R : Type*} [NonUnitalSemiring R]

theorem asMatrixMap_mul (M₁ : Matrix (C × D) (A × B) R) (M₂ : Matrix (E × F) (C × D) R) :
    (M₂ * M₁).asMatrixMap = M₂.asMatrixMap ∘ M₁.asMatrixMap := by
  ext x i j
  simp only [asMatrixMap, mulVec, dotProduct, Fintype.sum_prod_type, of_apply, mul_assoc,
    Function.comp_apply, Prod.mk.eta, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm_3]
  congr 1
  ext c
  rw [Finset.sum_comm_3]

/-- A matrix map is *trace preserving* if trace of the output equals trace of the input. -/
def _root_.IsTracePreserving (M : Matrix A A R → Matrix B B R) : Prop :=
  ∀ (x : Matrix A A R), (M x).trace = x.trace

/-- A linear matrix map is *trace preserving* if trace of the output equals trace of the input. -/
@[reducible]
def IsTracePreserving (M : Matrix (B × B) (A × A) R) : Prop :=
  _root_.IsTracePreserving M.asMatrixMap

open ComplexOrder
variable {R : Type*} [RCLike R]

/-- A matrix map is *positive* if it maps `PosSemidef` matrices to `PosSemidef`.-/
def _root_.IsPositiveMatrixMap (M : Matrix A A R → Matrix B B R) : Prop :=
  ∀{x}, x.PosSemidef → (M x).PosSemidef

/-- A linear matrix map is *positive* if it maps `PosSemidef` matrices to `PosSemidef`.-/
@[reducible]
def IsPositiveMap (M : Matrix (B × B) (A × A) R) : Prop :=
  _root_.IsPositiveMatrixMap M.asMatrixMap

variable (M₁ : Matrix (A₁ × B₁) (C₁ × D₁) R)
variable (M₂ : Matrix (A₂ × B₂) (C₂ × D₂) R)

/-- The canonical tensor product on linear maps between matrices, where a map from
  M[A,B] to M[C,D] is given by M[A×C,B×D]. This tensor product acts independently on
  Kronecker products and gives Kronecker products as outputs. -/
def matrixMap_kron : Matrix ((A₁ × A₂) × (B₁ × B₂)) ((C₁ × C₂) × (D₁ × D₂)) R :=
  Matrix.of fun ((a₁, a₂), (b₁, b₂)) ((c₁, c₂), (d₁, d₂)) ↦
    (M₁ (a₁, b₁) (c₁, d₁)) * (M₂ (a₂, b₂) (c₂, d₂))

/-- A linear matrix map is *completely positive* if, for any integer n, the tensor product
with `I(n)` is positive. -/
def IsCompletelyPositive (M : Matrix (B × B) (A × A) R) : Prop :=
  ∀ (n : ℕ), IsPositiveMap (matrixMap_kron M (1 : Matrix (Fin n × _) (Fin n × _) _))

theorem IsCompletelyPositive.IsPositiveMap {M : Matrix (B × B) (A × A) R}
    (hM : M.IsCompletelyPositive) : M.IsPositiveMap := by
  intro x hx
  let x' : Matrix (A × Fin 1) (A × Fin 1) R := x ⊗ₖ 1
  let eqB : (B × Fin 1) ≃ B :=
    (Equiv.prodCongrRight (fun _ ↦ finOneEquiv)).trans (Equiv.prodPUnit B)
  suffices asMatrixMap (matrixMap_kron M 1) x' = Matrix.submatrix (asMatrixMap M x) eqB eqB by
    rw [← Matrix.posSemidef_submatrix_equiv eqB, ← this]
    exact hM 1 (hx.PosSemidef_kronecker Matrix.PosSemidef.one)
  unfold_let eqB x'
  ext ⟨a1,aU⟩ ⟨b1,bU⟩
  simp [submatrix, Fin.fin_one_eq_zero, Matrix.mulVec, Matrix.dotProduct, asMatrixMap, matrixMap_kron]

end Matrix

variable (dIn dOut : Type*) [Fintype dIn] [Fintype dOut] [DecidableEq dIn]

/-- Positive trace-preserving linear maps. These includes all channels, but aren't
  necessarily *completely* positive, see `CPTPMap`. -/
structure PTPMap where
  map_mat : Matrix (dOut × dOut) (dIn × dIn) ℂ
  pos : map_mat.IsPositiveMap
  trace_preserving : map_mat.IsTracePreserving

/-- Quantum channels, aka CPTP maps: completely positive trace preserving linear maps. -/
structure CPTPMap extends PTPMap dIn dOut where
  completely_pos : map_mat.IsCompletelyPositive
  pos := completely_pos.IsPositiveMap

namespace PTPMap
noncomputable section
open ComplexOrder

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn]

@[ext]
theorem ext {Λ₁ Λ₂ : PTPMap dIn dOut} (h : Λ₁.map_mat = Λ₂.map_mat) : Λ₁ = Λ₂ :=
  PTPMap.mk.injEq Λ₁.map_mat _ _ _ _ _ ▸ h

def apply (Λ : PTPMap dIn dOut) := Λ.map_mat.asMatrixMap

theorem apply_PosSemidef (Λ : PTPMap dIn dOut) (hρ : ρ.PosSemidef) : (Λ.apply ρ).PosSemidef :=
  Λ.pos hρ

theorem apply_trace (Λ : PTPMap dIn dOut) (ρ : Matrix dIn dIn ℂ) : (Λ.apply ρ).trace = ρ.trace :=
  Λ.trace_preserving ρ

instance instFunLike : FunLike (PTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe Λ := fun ρ ↦ MState.mk (Λ.apply ρ.m) (Λ.apply_PosSemidef ρ.pos) (ρ.tr ▸ Λ.apply_trace ρ.m)
  coe_injective' _ _ h := sorry

/-- Choi matrix of a given matrix mapping. Note that this is defined even for things that
  aren't PTPMaps. It's just that no one ever cares about the Choi matrix otherwise, so it
  goes in this namespace. -/
def choi_matrix (M : Matrix (dOut × dOut) (dIn × dIn) R) : Matrix (dIn × dOut) (dIn × dOut) R :=
  fun (i₁,j₁) (i₂,j₂) ↦ M (j₁,j₂) (i₁,i₂)

def map_of_choi_matrix (M : Matrix (dIn × dOut) (dIn × dOut) R) :  Matrix (dOut × dOut) (dIn × dIn) R :=
  fun (j₁,j₂) (i₁,i₂) ↦ M (i₁,j₁) (i₂,j₂)

@[simp]
theorem map_choi_inv (M : Matrix (dIn × dOut) (dIn × dOut) R) : choi_matrix (map_of_choi_matrix M) = M :=
  rfl

@[simp]
theorem choi_map_inv (M : Matrix (dIn × dIn) (dOut × dOut) R) : map_of_choi_matrix (choi_matrix M) = M :=
  rfl

end
end PTPMap

namespace CPTPMap
noncomputable section
open scoped Matrix ComplexOrder
variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn]

def choi (Λ : CPTPMap dIn dOut) := PTPMap.choi_matrix Λ.map_mat

@[ext]
theorem ext {Λ₁ Λ₂ : CPTPMap dIn dOut} (h : Λ₁.map_mat = Λ₂.map_mat) : Λ₁ = Λ₂ :=
  CPTPMap.mk.injEq Λ₁.toPTPMap _ _ _ ▸ (PTPMap.ext h)

/-- Choi's theorem on completely positive maps: Complete Positivity iff Choi Matrix is PSD. -/
theorem choi_PSD_of_CP_map (M : Matrix (dOut × dOut) (dIn × dIn) ℂ) : M.IsCompletelyPositive
    ↔ (PTPMap.choi_matrix M).PosSemidef :=
  sorry

/-- The trace of a Choi matrix of a TP map is the cardinality of the input space. -/
theorem trace_choi_of_TP_map (M : Matrix (dOut × dOut) (dIn × dIn) ℂ) : M.IsTracePreserving
    ↔ (PTPMap.choi_matrix M).trace = (Finset.univ (α := dIn)).card :=
  sorry

/-- The Choi matrix of a channel is PSD. -/
theorem choi_PSD_of_CPTP (Λ : CPTPMap dIn dOut) : (PTPMap.choi_matrix Λ.map_mat).PosSemidef :=
  (choi_PSD_of_CP_map Λ.map_mat).1 Λ.completely_pos

/-- The trace of a Choi matrix of a CPTP map is the cardinality of the input space. -/
theorem Tr_of_choi_of_CPTP (Λ : CPTPMap dIn dOut) : (PTPMap.choi_matrix Λ.map_mat).trace =
    (Finset.univ (α := dIn)).card :=
  (trace_choi_of_TP_map Λ.map_mat).1 Λ.trace_preserving

/-- Build a CPTP map from a PSD Choi matrix with correct trace. -/
def CPTP_of_choi_PSD_Tr {M : Matrix (dIn × dOut) (dIn × dOut) ℂ} (h₁ : M.PosSemidef)
    (h₂ : M.trace = (Finset.univ (α := dIn)).card) : CPTPMap dIn dOut where
  map_mat := PTPMap.map_of_choi_matrix M
  trace_preserving := sorry
  completely_pos := sorry

/--  Choi's theorem on CPTP maps, stated as a state-channel correspondence between CPTP maps
 and Choi matrices given as a mixed state. -/
def choi_MState_iff_CPTP (M : Matrix (dIn × dOut) (dIn × dOut) ℂ) :
    CPTPMap dIn dOut ≃ MState (dIn × dOut) := by
  sorry

@[simp]
theorem apply_of_choi (M : Matrix (dIn × dOut) (dIn × dOut) ℂ) {h₁} {h₂} :
    (CPTP_of_choi_PSD_Tr (M := M) h₁ h₂).apply x = (PTPMap.map_of_choi_matrix M).asMatrixMap x :=
  rfl

@[simp]
theorem choi_of_CPTP_of_choi (M : Matrix (dIn × dOut) (dIn × dOut) ℂ) {h₁} {h₂} :
    (CPTP_of_choi_PSD_Tr (M := M) h₁ h₂).choi = M :=
  rfl

instance instFunLike : FunLike (CPTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe Λ := fun ρ ↦ MState.mk (Λ.apply ρ.m) (Λ.apply_PosSemidef ρ.pos) (ρ.tr ▸ Λ.apply_trace ρ.m)
  coe_injective' _ _ h := sorry

/-- The identity channel, which leaves the input unchanged. -/
def id : CPTPMap dIn dIn :=
  CPTP_of_choi_PSD_Tr (M := PTPMap.choi_matrix 1) (by
    constructor
    · ext
      simp [PTPMap.choi_matrix, Matrix.conjTranspose, Matrix.one_apply, and_comm]
    · intro x
      simp only [Matrix.dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec,
        PTPMap.choi_matrix, Matrix.one_apply, Prod.mk.injEq, ite_mul, one_mul, zero_mul,
        Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero, ite_and, Finset.sum_ite_irrel,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← map_sum, Complex.conj_mul']
      positivity
  ) (by
    simp [PTPMap.choi_matrix, Matrix.trace, Matrix.one_apply]
    rw [Finset.card_filter, Finset.sum_finset_product (s := Finset.univ) (t := fun _ ↦ Finset.univ) (h := by simp)]
    simp
  )

/-- The map `id_mat` leaves the input unchanged. -/
@[simp]
theorem CPTPMap_id_fun_id (M : Matrix dIn dIn ℂ) : CPTPMap.id.apply M = M := by
  ext
  simp [id, Matrix.asMatrixMap]

section prod
open Kronecker

variable {dI₁ dI₂ dO₁ dO₂ : Type*} [Fintype dI₁] [Fintype dI₂] [Fintype dO₁] [Fintype dO₂]
variable [DecidableEq dI₁] [DecidableEq dI₂]

def prod (Λ₁ : CPTPMap dI₁ dO₁) (Λ₂ : CPTPMap dI₂ dO₂) : CPTPMap (dI₁ × dI₂) (dO₁ × dO₂) :=
  CPTP_of_choi_PSD_Tr (M := sorry)--Λ₁.choi ⊗ₖ Λ₂.choi)
    (sorry)
    (sorry)

end prod

end
end CPTPMap
