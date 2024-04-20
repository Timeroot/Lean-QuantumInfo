import QuantumInfo.Finite.QState


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
structure QChannel extends PTPMap dIn dOut where
  completely_pos : map_mat.IsCompletelyPositive
  pos := completely_pos.IsPositiveMap

namespace PTPMap
noncomputable section
open ComplexOrder

def apply (Λ : PTPMap dIn dOut) := Λ.map_mat.asMatrixMap

theorem apply_PosSemidef (Λ : PTPMap dIn dOut) (hρ : ρ.PosSemidef) : (Λ.apply ρ).PosSemidef :=
  Λ.pos hρ

theorem apply_trace (Λ : PTPMap dIn dOut) (ρ : Matrix dIn dIn ℂ) : (Λ.apply ρ).trace = ρ.trace :=
  Λ.trace_preserving ρ

instance instFunLike : FunLike (PTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe Λ := fun ρ ↦ MState.mk (Λ.apply ρ.m) (Λ.apply_PosSemidef ρ.pos) (ρ.tr ▸ Λ.apply_trace ρ.m)
  coe_injective' _ _ h := sorry

end
end PTPMap

namespace QChannel
noncomputable section

instance instFunLike : FunLike (QChannel dIn dOut) (MState dIn) (MState dOut) where
  coe Λ := fun ρ ↦ MState.mk (Λ.apply ρ.m) (Λ.apply_PosSemidef ρ.pos) (ρ.tr ▸ Λ.apply_trace ρ.m)
  coe_injective' _ _ h := sorry

-- TODO: @[ext]

/-- The matrix corresponding to the identity map. -/
def id_mat : Matrix (dIn × dIn) (dIn × dIn) ℂ :=
  fun (i₁,j₁) (i₂,j₂) ↦ if i₁ = i₂ then if j₁ = j₂ then 1 else 0 else 0

/-- The map `id_mat` leaves the input unchanged. -/
theorem id_mat_is_id (M : Matrix dIn dIn ℂ) : (id_mat dIn).asMatrixMap M = M := by
  ext
  simp [Matrix.asMatrixMap, QChannel.id_mat, Matrix.mulVec, Matrix.dotProduct]

theorem id_mat_IsCompletelyPositive : (id_mat dIn).IsCompletelyPositive := by
  intro n x hx
  sorry
  --want to use Matrix.PosSemidef.PosSemidef_kronecker, but matrixMap_kron isn't actually
  -- a Kronecker multiplication. Choi's theorem -> Kronecker map would work.

theorem id_mat_IsTracePreserving : (id_mat dIn).IsTracePreserving :=
  fun x ↦ congrArg Matrix.trace <| id_mat_is_id dIn x

#print id_mat_IsTracePreserving

/-- The identity channel leaves the input unchanged. -/
def id : QChannel dIn dIn where
  map_mat := id_mat dIn
  completely_pos := id_mat_IsCompletelyPositive dIn
  trace_preserving := id_mat_IsTracePreserving dIn

section prod

variable {dI₁ dI₂ dO₁ dO₂ : Type*} [Fintype dI₁] [Fintype dI₂] [Fintype dO₁] [Fintype dO₂]
variable [DecidableEq dI₁] [DecidableEq dI₂]

def prod (Λ₁ : QChannel dI₁ dO₁) (Λ₂ : QChannel dI₂ dO₂) : QChannel (dI₁ × dI₂) (dO₁ × dO₂) where
  map_mat := Matrix.matrixMap_kron Λ₁.map_mat Λ₂.map_mat
  trace_preserving := sorry
  completely_pos := sorry

end prod

end
end QChannel
