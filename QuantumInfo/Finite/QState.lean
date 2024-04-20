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

theorem bra_apply' (ψ : Ket d) (i : d) : 〈ψ∣ i = conj (ψ.vec i) :=
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


section prod

variable {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂]

/-- The outer product of two kets, creating an unentangled state. -/
def prod (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : Ket (d₁ × d₂) where
  vec := fun (i,j) ↦ ψ₁ i * ψ₂ j
  normalized' := by
    simp only [Fintype.sum_prod_type, norm_mul, Complex.norm_eq_abs, mul_pow, ← Finset.mul_sum,
      Complex.sq_abs, ψ₂.normalized, mul_one, ψ₁.normalized]

notation ψ₁ "⊗" ψ₂ => prod ψ₁ ψ₂

end prod

end Braket

namespace MState

variable {d : Type*} [Fintype d]
variable {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂]

/-- Every mixed state is Hermitian. -/
theorem Hermitian (ρ : MState d) : ρ.m.IsHermitian :=
  ρ.pos.left

@[ext]
theorem ext {ρ₁ ρ₂ : MState d} (h : ρ₁.m = ρ₂.m) : ρ₁ = ρ₂ := by
  rwa [MState.mk.injEq]

theorem PosSemidef_outer_self_conj (v : d → ℂ) : Matrix.PosSemidef (Matrix.vecMulVec v (conj v)) := by
  constructor
  · ext
    simp [Matrix.vecMulVec_apply, mul_comm]
  · intro x
    simp_rw [Matrix.dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec, Matrix.dotProduct,
      Matrix.vecMulVec_apply, mul_assoc, ← Finset.mul_sum, ← mul_assoc, ← Finset.sum_mul]
    change
      0 ≤ (∑ i : d, (starRingEnd ℂ) (x i) * v i) * ∑ i : d, (starRingEnd ℂ) (v i) * x i
    have : (∑ i : d, (starRingEnd ℂ) (x i) * v i) =
        (∑ i : d, (starRingEnd ℂ) ((starRingEnd ℂ) (v i) * x i)) := by
          simp only [mul_comm ((starRingEnd ℂ) (x _)) (v _), map_mul,
          RingHomCompTriple.comp_apply, RingHom.id_apply]
    rw [this, ← map_sum, ← Complex.normSq_eq_conj_mul_self, Complex.zero_le_real, ← Complex.sq_abs]
    exact sq_nonneg _

/-- A mixed state as a pure state arising from a ket. -/
def pure (ψ : Ket d) : MState d where
  m := Matrix.vecMulVec ψ (ψ : Bra d)
  pos := PosSemidef_outer_self_conj ψ
  tr := by
    have h₁ : ∀x, ψ x * conj (ψ x) = Complex.normSq (ψ x) := fun x ↦ by
      rw [mul_comm, Complex.normSq_eq_conj_mul_self]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply, Braket.bra_eq_conj, h₁]
    have h₂ := congrArg Complex.ofReal ψ.normalized
    simpa using h₂

section prod

def prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : MState (d₁ × d₂) where
  m := ρ₁.m ⊗ₖ ρ₂.m
  pos := ρ₁.pos.PosSemidef_kronecker ρ₂.pos
  tr := by simpa [ρ₁.tr, ρ₂.tr] using Matrix.trace_kronecker ρ₁.m ρ₂.m

notation ρL "⊗" ρR => prod ρL ρR

/-- The product of pure states is a pure state (specifically of the product ket.) -/
theorem pure_prod_pure (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : pure (ψ₁ ⊗ ψ₂) = ((pure ψ₁) ⊗ (pure ψ₂) : MState _) := by
  dsimp [pure, prod, Braket.prod]
  ext
  simp [Matrix.vecMulVec_apply, Braket.ket_apply]
  ring

end prod

section ptrace

section mat_trace

variable [AddCommMonoid R]

def _root_.Matrix.trace_left (m : Matrix (d × d₁) (d × d₂) R) : Matrix d₁ d₂ R :=
  Matrix.of fun i₁ j₁ ↦ ∑ i₂, m (i₂, i₁) (i₂, j₁)

def _root_.Matrix.trace_right (m : Matrix (d₁ × d) (d₂ × d) R) : Matrix d₁ d₂ R :=
  Matrix.of fun i₂ j₂ ↦ ∑ i₁, m (i₂, i₁) (j₂, i₁)

@[simp]
theorem _root_.Matrix.trace_of_trace_left (A : Matrix (d₁ × d₂) (d₁ × d₂) R) : A.trace_left.trace = A.trace := by
  convert Fintype.sum_prod_type_right.symm
  rfl

@[simp]
theorem _root_.Matrix.trace_of_trace_right (A : Matrix (d₁ × d₂) (d₁ × d₂) R) : A.trace_right.trace = A.trace := by
  convert Fintype.sum_prod_type.symm
  rfl

variable [RCLike R] {A : Matrix (d₁ × d₂) (d₁ × d₂) R}

theorem _root_.Matrix.PosSemidef.trace_left  (hA : A.PosSemidef) : A.trace_left.PosSemidef :=
  sorry

theorem _root_.Matrix.PosSemidef.trace_right  (hA : A.PosSemidef) : A.trace_right.PosSemidef :=
  sorry

end mat_trace

-- TODO:
-- * Partial trace of direct product is the original state

/-- Partial tracing out the left half of a system. -/
def trace_left (ρ : MState (d₁ × d₂)) : MState d₂ where
  m := ρ.m.trace_left
  pos := ρ.pos.trace_left
  tr := ρ.tr ▸ ρ.m.trace_of_trace_left

/-- Partial tracing out the right half of a system. -/
def trace_right (ρ : MState (d₁ × d₂)) : MState d₁ where
  m := ρ.m.trace_right
  pos := ρ.pos.trace_right
  tr := ρ.tr ▸ ρ.m.trace_of_trace_right

/-- Taking the direct product on the left and tracing it back out gives the same state. -/
theorem trace_left_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : trace_left (ρ₁ ⊗ ρ₂) = ρ₂ := by
  ext
  rw [trace_left]
  dsimp
  rw [Matrix.trace_left, prod]
  dsimp
  have h : (∑ i : d₁, ρ₁.m i i) = 1 := ρ₁.tr
  rw [← Finset.sum_mul, h, one_mul]

/-- Taking the direct product on the right and tracing it back out gives the same state. -/
theorem trace_right_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : trace_right (ρ₁ ⊗ ρ₂) = ρ₁ :=
  sorry

end ptrace

-- TODO: direct sum (by zero-padding)
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

/-- The specturm of a pure state is (1,0,0,...), i.e. a constant distribution. -/
theorem spectrum_pure_eq_constant (ψ : Ket d) :
    ∃ i, (pure ψ).spectrum = Distribution.constant i := by
  let ρ := pure ψ
  let ρ_linMap := Matrix.toEuclideanLin ρ.m
  -- have ρ_linMap_evals := Matrix.isHermitian_iff_isSymmetric.1 ρ.Hermitian
  --Prove that "1" is in the spectrum by exhibiting an eigenvector with value 1.
  have hasLinMapEigen1 : Module.End.HasEigenvalue ρ_linMap 1 := by
    --The eigenvector 1 witness, which is ψ.
    let x1 : EuclideanSpace ℂ d := ψ.vec
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := x1)
    constructor --to show it's an eigenvector, show that it's scaled and nonzero.
    · rw [Module.End.mem_eigenspace_iff, one_smul]
      change (pure ψ).m *ᵥ ψ.vec = ψ.vec
      ext
      simp_rw [pure, Matrix.mulVec, Matrix.vecMulVec_apply, Matrix.dotProduct, Braket.bra_apply',
        Braket.ket_apply, mul_assoc, ← Finset.mul_sum, ← Complex.normSq_eq_conj_mul_self,
        ← Complex.ofReal_sum, ← Braket.ket_apply, ψ.normalized, Complex.ofReal_one, mul_one]
    · have : ‖x1‖ = 1 := by
        rw [PiLp.norm_eq_of_L2, ψ.normalized']
        exact Real.sqrt_one
      by_contra hz
      simp only [hz, norm_zero, zero_ne_one] at this
  --If 1 is in the spectrum of ρ_linMap, it's in the spectrum of pure ψ.
  have : ∃i, (pure ψ).spectrum i = 1 := by
    sorry
  --If 1 is in a distribution, the distribution is a constant.
  sorry

/-- Spectrum of direct product. There is a permutation σ so that the spectrum of the direct product of
  ρ₁ and ρ₂, as permuted under σ, is the pairwise products of the spectra of ρ₁ and ρ₂. -/
theorem spectrum_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : ∃(σ : d₁ × d₂ ≃ d₁ × d₂),
    ∀i, ∀j, MState.spectrum (ρ₁ ⊗ ρ₂) (σ (i, j)) = (ρ₁.spectrum i) * (ρ₂.spectrum j) := by
  sorry

--TODO: Spectrum of direct sum. Spectrum of partial trace?

/-- A mixed state is separable iff it can be written as a convex combination of product mixed states. -/
def IsSeparable (ρ : MState (d₁ × d₂)) : Prop :=
  ∃ ρLRs : Finset (MState d₁ × MState d₂), --Finite set of (ρL, ρR) pairs
    ∃ ps : Distribution ρLRs, --Distribution over those pairs, an ensemble
      ρ.m = ∑ ρLR : ρLRs, (ps ρLR) • (Prod.fst ρLR.val).m ⊗ₖ (Prod.snd ρLR.val).m

/-- A product state is separable -/
theorem IsSeparable_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : IsSeparable (ρ₁ ⊗ ρ₂) := by
  let only := (ρ₁, ρ₂)
  use { only }
  use Distribution.constant ⟨only, Finset.mem_singleton_self only⟩
  simp only [Finset.univ_unique, Distribution.constant_eq, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_singleton]
  simp only [Unique.eq_default, ite_true, prod]

--TODO: Separable states are convex

section purification

/-- The purification of a mixed state. Always uses the full dimension of the Hilbert space (d) to
 purify, so e.g. an existing pure state with d=4 still becomes d=16 in the purification. The defining
 property is `MState.trace_right_of_purify`; see also `MState.purify'` for the bundled version. -/
def purify (ρ : MState d) : Ket (d × d) where
  vec := fun (i,j) ↦
    let ρ2 := ρ.Hermitian.eigenvectorMatrix i j
    (ρ.Hermitian.eigenvalues j).sqrt
  normalized' := sorry

/-- The defining property of purification, that tracing out the purifying system gives the
 original mixed state. -/
theorem trace_right_of_purify (ρ : MState d) : (pure ρ.purify).trace_right = ρ :=
  sorry

/-- `MState.purify` bundled with its defining property `MState.trace_right_of_purify`. -/
def purify' (ρ : MState d) : { ψ : Ket (d × d) // (pure ψ).trace_right = ρ } :=
  ⟨ρ.purify, ρ.trace_right_of_purify⟩

end purification

end MState
