import QuantumInfo.Finite.MState
import QuantumInfo.Finite.Unitary

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

variable {dIn dOut}

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

theorem choi_matrix_inj : Function.Injective (choi_matrix (dIn := dIn) (dOut := dOut) (R := R)) := by
  intro x y h
  simpa only [choi_map_inv] using congrArg map_of_choi_matrix h

--If we have a PTPMap, the input and output dimensions are always both nonempty (otherwise
--we can't preserve trace) - or they're both empty. So `[Nonempty dIn]` will always suffice.
-- This would be nice as an `instance` but that would leave `dIn` as a metavariable.
theorem nonemptyOut (Λ : PTPMap dIn dOut) [hIn : Nonempty dIn] : Nonempty dOut := by
  by_contra h
  simp only [not_nonempty_iff] at h
  let M := (1 : Matrix dIn dIn ℂ)
  have := calc (Finset.univ.card (α := dIn) : ℂ)
    _ = M.trace := by simp [Matrix.trace, M]
    _ = (Λ.apply M).trace := (Λ.trace_preserving M).symm
    _ = 0 := by simp only [Matrix.trace_eq_zero_of_isEmpty]
  norm_num [Finset.univ_eq_empty_iff] at this

end
end PTPMap

namespace CPTPMap
noncomputable section
open scoped Matrix ComplexOrder

variable {dIn dOut}
variable {dM : Type*} [Fintype dM] [DecidableEq dM]

def choi (Λ : CPTPMap dIn dOut) := PTPMap.choi_matrix Λ.map_mat

theorem map_ext {Λ₁ Λ₂ : CPTPMap dIn dOut} (h : Λ₁.map_mat = Λ₂.map_mat) : Λ₁ = Λ₂ :=
  CPTPMap.mk.injEq Λ₁.toPTPMap _ _ _ ▸ (PTPMap.ext h)

theorem choi_ext {Λ₁ Λ₂ : CPTPMap dIn dOut} (h : Λ₁.choi = Λ₂.choi) : Λ₁ = Λ₂ :=
  CPTPMap.mk.injEq Λ₁.toPTPMap _ _ _ ▸ (PTPMap.ext (PTPMap.choi_matrix_inj h))

-- theorem ext_iff {Λ₁ Λ₂ : CPTPMap dIn dOut} : Λ₁.map_mat = Λ₂.map_mat ↔ Λ₁ = Λ₂ :=
--   CPTPMap.mk.injEq Λ₁.toPTPMap _ _ _ ▸ (PTPMap.ext h)

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
@[simp]
theorem Tr_of_choi_of_CPTP (Λ : CPTPMap dIn dOut) : Λ.choi.trace =
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
  constructor
  case toFun =>
    intro Λ
    use (1 / (Finset.univ (α := dIn)).card : ℝ) • Λ.choi
    sorry
    simp
    sorry
  case invFun =>
    intro ρ
    apply CPTP_of_choi_PSD_Tr (M := (Finset.univ (α := dIn)).card • ρ.m)
    sorry
    sorry
  sorry
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

theorem mat_coe_eq_apply_mat (Λ : CPTPMap dIn dOut) (ρ : MState dIn) : (Λ ρ).m = Λ.apply ρ.m :=
  rfl

@[ext]
theorem ext {Λ₁ Λ₂ : CPTPMap dIn dOut} (h : ∀ ρ, Λ₁ ρ = Λ₂ ρ) : Λ₁ = Λ₂ := by
  apply DFunLike.coe_injective'
  funext
  exact (h _)

theorem ext_iff {Λ₁ Λ₂ : CPTPMap dIn dOut} : (∀ ρ, Λ₁ ρ = Λ₂ ρ) ↔ Λ₁ = Λ₂ :=
  ⟨ext, fun h _ ↦ h ▸rfl⟩

def compose (Λ₂ : CPTPMap dM dOut) (Λ₁ : CPTPMap dIn dM) : CPTPMap dIn dOut :=
  sorry

theorem compose_eq {Λ₁ : CPTPMap dIn dM} {Λ₂ : CPTPMap dM dOut} : ∀ρ, Λ₂ (Λ₁ ρ) =
    (Λ₂.compose Λ₁) ρ :=
  sorry

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

/-- The map `id_mat` leaves the input unchanged. -/
@[simp]
theorem CPTPMap_id_MState (ρ : MState dIn) : CPTPMap.id ρ = ρ := by
  ext1
  rw [mat_coe_eq_apply_mat]
  exact CPTPMap_id_fun_id ρ.m

/-- There is a CPTP map that takes a system of any dimension and outputs the trivial Hilbert
space, 1-dimensional, indexed by `Unit`. -/
def destroy [Nonempty dIn] : CPTPMap dIn Unit :=
  CPTP_of_choi_PSD_Tr (M := (1 / Finset.univ.card (α := dIn)) • 1) (sorry) (sorry)

/-- A state can be viewed as a CPTP map from the trivial Hilbert space (indexed by `Unit`)
 that outputs exactly that state. -/
def of_state (ρ : MState dOut) : CPTPMap Unit dOut :=
  sorry --need the canonical isomorphism from (Unit × d) ≃ d.
  -- CPTP_of_choi_PSD_Tr (M := ρ.m) (ρ.pos) (ρ.tr)

section prod
open Kronecker

variable {dI₁ dI₂ dO₁ dO₂ : Type*} [Fintype dI₁] [Fintype dI₂] [Fintype dO₁] [Fintype dO₂]
variable [DecidableEq dI₁] [DecidableEq dI₂]

def prod (Λ₁ : CPTPMap dI₁ dO₁) (Λ₂ : CPTPMap dI₂ dO₂) : CPTPMap (dI₁ × dI₂) (dO₁ × dO₂) :=
  CPTP_of_choi_PSD_Tr (M := sorry)--Λ₁.choi ⊗ₖ Λ₂.choi)
    (sorry)
    (sorry)

notation ρL "⊗" ρR => prod ρL ρR

end prod

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
variable [DecidableEq dOut] [Inhabited dOut]

/-- A channel is *degradable* if its complementary channel can be written as a composition of
  a _degrading_ channel D with the original channel. -/
def IsDegradable (Λ : CPTPMap dIn dOut) : Prop :=
  ∃ (D : CPTPMap dOut (dIn × dOut)), D.compose Λ = Λ.complementary

/-- A channel is *antidegradable* if it can be written as a composition of
  a _degrading_ channel D with its complementary channel. -/
def IsAntidegradable (Λ : CPTPMap dIn dOut) : Prop :=
  ∃ (D : CPTPMap (dIn × dOut) dOut), D.compose Λ.complementary = Λ

--Theorem (Wilde Exercise 13.5.7): Entanglement breaking channels are antidegradable.
end degradable

end
end CPTPMap
