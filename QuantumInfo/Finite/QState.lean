import Mathlib
import QuantumInfo.Finite.Helper
import QuantumInfo.Finite.Entropy

/-
Finite dimensional quantum states.

These could be done with a Hilbert space of Fintype, which would look like
(H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
or by choosing a particular `Basis` and asserting it is `Fintype`. But frankly it seems easier to
mostly focus on the basis-dependent notion of `Matrix`, which has the added benefit of an obvious
"classical" interpretation (as the basis elements, or diagonal elements of a mixed state). In that
sense, this quantum theory comes with the a particular classical theory always preferred.
-/

noncomputable section

open Classical
open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

section
variable (d : Type*) [Fintype d]

/-- A ket as a vector of unit norm. We follow the convention in `Matrix` of vectors as simple functions
 from a Fintype. -/
structure Ket :=
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖^2 = 1

/-- A bra is definitionally identical to a ket, but are separate for type reasons. They can be interconverted
  with the adjoint. -/
structure Bra :=
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖^2 =1

/-- A mixed state as a PSD matrix with trace 1.-/
structure MState :=
  m : Matrix d d ℂ
  pos : m.PosSemidef
  tr : m.trace = 1

end section

namespace Braket

scoped notation:max "〈" ψ:90 "∣" => (ψ : Bra _)

scoped notation:max "∣" ψ:90 "〉" => (ψ : Ket _)

variable {d : Type*} [Fintype d]

instance instFunLikeKet : FunLike (Ket d) d ℂ where
  coe ψ := ψ.vec
  coe_injective' _ _ h := by rwa [Ket.mk.injEq]

instance instFunLikeBra : FunLike (Bra d) d ℂ where
  coe ψ := ψ.vec
  coe_injective' _ _ h := by rwa [Bra.mk.injEq]

theorem ket_apply (ψ : Ket d) (i : d) : ψ i = ψ.vec i :=
  rfl

theorem bra_apply (ψ : Bra d) (i : d) : ψ i = ψ.vec i :=
  rfl

@[ext]
theorem _root_.Ket.ext {ξ ψ : Ket d} (h : ∀ x, ξ x = ψ x) : ξ = ψ :=
  DFunLike.ext ξ ψ h

@[ext]
theorem _root_.Bra.ext {ξ ψ : Bra d} (h : ∀ x, ξ x = ψ x) : ξ = ψ :=
  DFunLike.ext ξ ψ h

theorem _root_.Ket.normalized (ψ : Ket d) : ∑ x, Complex.normSq (ψ x) = 1 := by
  convert ψ.normalized'
  rw [Complex.norm_eq_abs, Complex.sq_abs]
  rfl

theorem _root_.Bra.normalized (ψ : Bra d) : ∑ x, Complex.normSq (ψ x) = 1 := by
  convert ψ.normalized'
  rw [Complex.norm_eq_abs, Complex.sq_abs]
  rfl

/-- Any Bra can be turned into a Ket by conjugating the elements. -/
@[coe]
def bra_of_ket (ψ : Ket d) : Bra d :=
  ⟨conj ψ, by simpa using ψ.2⟩

/-- Any Ket can be turned into a Bra by conjugating the elements. -/
@[coe]
def ket_of_bra (ψ : Bra d) : Ket d :=
  ⟨conj ψ, by simpa using ψ.2⟩

instance instBraOfKet : Coe (Ket d) (Bra d) := ⟨bra_of_ket⟩

instance instKetOfBra : Coe (Bra d) (Ket d) := ⟨ket_of_bra⟩

@[simp]
theorem bra_eq_conj (ψ : Ket d) (x : d) :〈ψ∣ x = conj (∣ψ〉 x) :=
  rfl

def dot (ξ : Bra d) (ψ : Ket d) : ℂ := ∑ x, (ξ x) * (ψ x)

local notation "〈" ξ:90 "∣" ψ:90 "〉" => dot (ξ : Bra _) (ψ : Ket _)

/-- Construct the Ket corresponding to a basis vector, with a +1 phase. -/
def basisKet (i : d) : Ket d :=
  ⟨fun j ↦ if i = j then 1 else 0, by simp [apply_ite]⟩

/-- Construct the Bra corresponding to a basis vector, with a +1 phase. -/
def basisBra (i : d) : Bra d :=
  ⟨fun j ↦ if i = j then 1 else 0, by simp [apply_ite]⟩

/-- A Bra can be viewed as a function from Ket's to ℂ. -/
instance instFunLikeBraket : FunLike (Bra d) (Ket d) ℂ where
  coe ξ := dot ξ
  coe_injective' x y h := by
    ext i
    simpa [basisKet, dot, ket_apply] using congrFun h (basisKet i)

/-- The inner product of any state with itself is 1. -/
theorem dot_self_eq_one (ψ : Ket d) :〈ψ∣ψ〉= 1 := by
  have h₁ : ∀x, conj (ψ x) * ψ x = Complex.normSq (ψ x) := fun x ↦ by
    rw [Complex.normSq_eq_conj_mul_self]
  simp only [dot, bra_eq_conj, h₁]
  have h₂ := congrArg Complex.ofReal ψ.normalized
  simpa using h₂

end Braket

namespace MState

variable {d : Type*} [Fintype d]
variable {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂]

/-- Every mixed state is Hermitian. -/
theorem Hermitian (ρ : MState d) : ρ.m.IsHermitian :=
  ρ.pos.left

theorem PosSemidef_outer_conj_self (v : d → ℂ) : Matrix.PosSemidef (Matrix.vecMulVec (conj v) v) := by
  constructor
  · ext
    simp [Matrix.vecMulVec_apply, mul_comm]
  · intro x
    simp_rw [Matrix.dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec, Matrix.dotProduct,
      Matrix.vecMulVec_apply, mul_assoc, ← Finset.mul_sum, ← mul_assoc, ← Finset.sum_mul]
    change
      0 ≤ (∑ i : d, (starRingEnd ℂ) (x i) * (starRingEnd ℂ) (v i)) * ∑ i : d, v i * x i
    simp_rw [← map_mul]
    have : (∑ x_1 : d, (starRingEnd ℂ) (x x_1 * v x_1)) =
        (∑ x_1 : d, (starRingEnd ℂ) (v x_1 * x x_1)) := by simp_rw [mul_comm]
    rw [this, ← map_sum, ← Complex.normSq_eq_conj_mul_self, Complex.zero_le_real, ← Complex.sq_abs]
    exact sq_nonneg _

/-- A mixed state as a pure state arising from a ket. -/
def pure (ψ : Ket d) : MState d where
  m := Matrix.vecMulVec (ψ : Bra d) ψ
  pos := PosSemidef_outer_conj_self ψ
  tr := Braket.dot_self_eq_one ψ

section prod

#check TensorProduct.toMatrix_map

def prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : MState (d₁ × d₂) where
  m := ρ₁.m ⊗ₖ ρ₂.m
  pos := ρ₁.pos.PosSemidef_kronecker ρ₂.pos
  tr := by simpa [ρ₁.tr, ρ₂.tr] using Matrix.trace_kronecker ρ₁.m ρ₂.m

notation ρL "⊗" ρR => prod ρL ρR

-- TODO: Product of pure states is a pure state (specifically of the product ket.)

end prod

section ptrace

-- TODO:
-- * Define partial trace
-- * Partial trace of direct product is the original state

/-- Partial tracing out the left half of a system. -/
def trace_left (ρ : MState (d₁ × d₂)) : MState d₂ :=
  sorry

/-- Partial tracing out the right half of a system. -/
def trace_right (ρ : MState (d₁ × d₂)) : MState d₁ :=
  sorry

/-- Taking the direct product on the left and tracing it back out gives the same state. -/
theorem trace_left_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : trace_left (ρ₁ ⊗ ρ₂) = ρ₂ :=
  sorry

/-- Taking the direct product on the right and tracing it back out gives the same state. -/
theorem trace_right_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : trace_right (ρ₁ ⊗ ρ₂) = ρ₁ :=
  sorry

end ptrace

-- TODO: direct sum (by zero-padding), Ket → MState
-- Mixing (convexity)

/-- The eigenvalue spectrum of a mixed quantum state, as a `Distribution`. -/
def spectrum (ρ : MState d) : Distribution d :=
  ⟨fun i ↦ ⟨ρ.Hermitian.eigenvalues i, --The values are the eigenvalues
    ρ.pos.eigenvalues_nonneg i⟩, --The values are all nonnegative
  by --The values sum to 1
    rw [← NNReal.eq_iff]
    push_cast
    have h := congrArg Complex.re (ρ.Hermitian.sum_eigenvalues_eq_trace)
    simp only [ρ.tr, RCLike.ofReal_sum, Complex.re_sum, Complex.one_re] at h
    rw [← h]
    rfl⟩

--TODO: Spectrum of ket is 1
--Spectrum of direct product / direct sum. Spectrum of partial trace?

/-- A mixed state is separable iff it can be written as a convex combination of product mixed states. -/
def IsSeparable (ρ : MState (d₁ × d₂)) : Prop :=
  ∃ ρLRs : Finset (MState d₁ × MState d₂), --Finite set of (ρL, ρR) pairs
    ∃ ps : Distribution ρLRs, --Distribution over those pairs, an ensemble
      ρ.m = ∑ ρLR : ρLRs, (ps ρLR) • (Prod.fst ρLR.val).m ⊗ₖ (Prod.snd ρLR.val).m

/-- A product state is separable -/
theorem IsSeparable_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : IsSeparable (ρ₁ ⊗ ρ₂) := by
  let only := (ρ₁, ρ₂)
  use { only }
  use Distribution.indicator ⟨only, Finset.mem_singleton_self only⟩
  simp only [Finset.univ_unique, Distribution.indicator_eq, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_singleton]
  simp only [Unique.eq_default, ite_true, prod]

--TODO: Separable states are convex

section purification

/-- The purification of a mixed state. Always uses the full dimension of the Hilbert space (d) to
 purify, so e.g. an existing pure state with d=4 still becomes d=16 in the purification. -/
def purify (ρ : MState d) : { ψ : Ket (d × d) // (pure ψ).trace_right = ρ } :=
  sorry

end purification

end MState

variable (dIn dOut : Type*) [Fintype dIn] [Fintype dOut]

--TODO: Give an actual definition of a channel. These lets are just so that it
--      binds the surrounding necessary variables and has the right type signature.
def QChannel : Type :=
  let a : Fintype dIn := inferInstance
  let b : Fintype dOut := inferInstance
  sorry

namespace QChannel

instance instFunLikeQChannel : FunLike (QChannel dIn dOut) (MState dIn) (MState dOut) where
  coe ψ := sorry
  coe_injective' _ _ h := sorry

/-- The identity channel leaves the input unchanged. -/
def id : QChannel dIn dIn :=
  sorry

section prod

variable {dI₁ dI₂ dO₁ dO₂ : Type*} [Fintype dI₁] [Fintype dI₂] [Fintype dO₁] [Fintype dO₂]

def prod (Λ₁ : QChannel dI₁ dO₁) (Λ₂ : QChannel dI₂ dO₂) : QChannel (dI₁ × dI₂) (dO₁ × dI₂) :=
  sorry

end prod

end QChannel
