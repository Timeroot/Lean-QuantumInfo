import QuantumInfo.Mathlib.All
import ClassicalInfo.Distribution
import QuantumInfo.Finite.Braket

/-
Finite dimensional quantum mixed states, ρ.

The same comments apply as in `Braket`:

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

/-- A mixed state as a PSD matrix with trace 1.-/
structure MState (d : Type*) [Fintype d] :=
  m : Matrix d d ℂ
  pos : m.PosSemidef
  tr : m.trace = 1

namespace MState

variable {d d₁ d₂ d₃ : Type*} [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]

/-- Every mixed state is Hermitian. -/
theorem Hermitian (ρ : MState d) : ρ.m.IsHermitian :=
  ρ.pos.left

@[ext]
theorem ext {ρ₁ ρ₂ : MState d} (h : ρ₁.m = ρ₂.m) : ρ₁ = ρ₂ := by
  rwa [MState.mk.injEq]

instance instMixable : Mixable (Matrix d d ℂ) (MState d) where
  to_U := MState.m
  to_U_inj := ext
  mkT := fun h ↦ ⟨⟨_,
    Exists.casesOn h fun t ht => ht ▸ t.pos,
    Exists.casesOn h fun t ht => ht ▸ t.tr⟩, rfl⟩
  convex := by
    simp only [Convex, Set.mem_range, StarConvex,
      forall_exists_index, forall_apply_eq_imp_iff]
    intro x y a b ha hb hab
    replace ha : 0 ≤ (a : ℂ) := by norm_cast
    replace hb : 0 ≤ (b : ℂ) := by norm_cast
    replace hab : a + b = (1 : ℂ) := by norm_cast
    exact ⟨⟨_, x.pos.convex_cone y.pos ha hb, by simpa [x.tr, y.tr] using hab⟩, rfl⟩

--An MState is a witness that d is nonempty.
instance nonempty (ρ : MState d) : Nonempty d := by
  by_contra h
  simpa [not_nonempty_iff.mp h] using ρ.tr

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

section pure

/-- A mixed state can be constructed as a pure state arising from a ket. -/
def pure (ψ : Ket d) : MState d where
  m := Matrix.vecMulVec ψ (ψ : Bra d)
  pos := PosSemidef_outer_self_conj ψ
  tr := by
    have h₁ : ∀x, ψ x * conj (ψ x) = Complex.normSq (ψ x) := fun x ↦ by
      rw [mul_comm, Complex.normSq_eq_conj_mul_self]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply, Bra.eq_conj, h₁]
    have h₂ := congrArg Complex.ofReal ψ.normalized
    simpa using h₂

@[simp]
theorem pure_of (ψ : Ket d) : (pure ψ).m i j = (ψ i) * conj (ψ j) := by
  rfl

/-- The purity of a state is Tr[ρ^2]. This is a `Prob`, because it is always between zero and one. -/
def purity (ρ : MState d) : Prob :=
  ⟨RCLike.re (ρ.m * ρ.m).trace, ⟨by
    suffices 0 ≤ Matrix.trace (ρ.m * ρ.m) by
      exact (RCLike.nonneg_iff.mp this).1
    nth_rewrite 1 [← ρ.pos.1]
    exact ρ.m.posSemidef_conjTranspose_mul_self.trace_nonneg,
      by
    nth_rewrite 1 [← ρ.pos.1]
    convert ρ.pos.inner_le_mul_trace ρ.pos
    simp [ρ.tr]
    ⟩⟩

/-- The eigenvalue spectrum of a mixed quantum state, as a `Distribution`. -/
def spectrum (ρ : MState d) : Distribution d :=
  Distribution.mk'
    (fun i ↦ ρ.Hermitian.eigenvalues i) --The values are the eigenvalues
    (fun i ↦ ρ.pos.eigenvalues_nonneg i) --The values are all nonnegative
    (by --The values sum to 1
      have h := congrArg Complex.re (ρ.Hermitian.sum_eigenvalues_eq_trace)
      simp only [ρ.tr, RCLike.ofReal_sum, Complex.re_sum, Complex.one_re] at h
      rw [← h]
      rfl)

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
      simp_rw [pure, Matrix.mulVec, Matrix.vecMulVec_apply, Matrix.dotProduct, Bra.apply',
        Ket.apply, mul_assoc, ← Finset.mul_sum, ← Complex.normSq_eq_conj_mul_self,
        ← Complex.ofReal_sum, ← Ket.apply, ψ.normalized, Complex.ofReal_one, mul_one]
    · have : ‖x1‖ = 1 := by
        rw [PiLp.norm_eq_of_L2, ψ.normalized']
        exact Real.sqrt_one
      by_contra hz
      simp only [hz, norm_zero, zero_ne_one] at this
  --If 1 is in the spectrum of ρ_linMap, it's in the spectrum of pure ψ.
  have : ∃i, (pure ψ).spectrum i = 1 := by
    sorry
  --If 1 is in a distribution, the distribution is a constant.
  obtain ⟨i, hi⟩ := this
  use i
  exact Distribution.constant_of_exists_one hi

/-- If the specturm of a mixed state is (1,0,0...) i.e. a constant distribution, it is
 a pure state. -/
theorem pure_of_constant_spectrum (ρ : MState d) (h : ∃ i, ρ.spectrum = Distribution.constant i) :
    ∃ ψ, ρ = pure ψ :=
  sorry

theorem pure_iff_purity_one (ρ : MState d) : (∃ ψ, ρ = pure ψ) ↔ ρ.purity = 1 := by
  --purity = exp(-Collision entropy)
  --purity eq 1 iff collision entropy is zero
  --entropy is zero iff distribution is constant
  --disttibution is constant iff pure
  sorry

end pure

section prod

def prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : MState (d₁ × d₂) where
  m := ρ₁.m ⊗ₖ ρ₂.m
  pos := ρ₁.pos.PosSemidef_kronecker ρ₂.pos
  tr := by simpa [ρ₁.tr, ρ₂.tr] using Matrix.trace_kronecker ρ₁.m ρ₂.m

notation ρL "⊗" ρR => prod ρL ρR

/-- The product of pure states is a pure state (specifically of the product ket.) -/
theorem pure_prod_pure (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : pure (ψ₁ ⊗ ψ₂) = (pure ψ₁) ⊗ (pure ψ₂) := by
  ext
  simp only [pure, Ket.prod, Ket.apply, Matrix.vecMulVec_apply, Bra.eq_conj, map_mul, prod,
    Matrix.kroneckerMap_apply]
  ring

end prod

/-- A representation of a classical distribution as a quantum state, diagonal in the given basis. -/
def ofClassical (dist : Distribution d) : MState d where
  m := Matrix.diagonal (fun x ↦ dist x)
  pos := by simp [Matrix.posSemidef_diagonal_iff]
  tr := by
    simp [Matrix.trace_diagonal]
    have h₃ := dist.2
    norm_cast

/-- The maximally mixed state. -/
def uniform [Nonempty d] : MState d := ofClassical Distribution.uniform

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
@[simp]
theorem trace_left_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : trace_left (ρ₁ ⊗ ρ₂) = ρ₂ := by
  ext
  simp_rw [trace_left, Matrix.trace_left, prod]
  dsimp
  have h : (∑ i : d₁, ρ₁.m i i) = 1 := ρ₁.tr
  rw [← Finset.sum_mul, h, one_mul]

/-- Taking the direct product on the right and tracing it back out gives the same state. -/
@[simp]
theorem trace_right_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : trace_right (ρ₁ ⊗ ρ₂) = ρ₁ := by
  ext
  simp_rw [trace_right, Matrix.trace_right, prod]
  dsimp
  have h : (∑ i : d₂, ρ₂.m i i) = 1 := ρ₂.tr
  rw [← Finset.mul_sum, h, mul_one]

end ptrace

-- TODO: direct sum (by zero-padding)

--TODO: Spectra of left- and right- partial traces of a pure state are equal.

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
      ρ.m = ∑ ρLR : ρLRs, (ps ρLR : ℝ) • (Prod.fst ρLR.val).m ⊗ₖ (Prod.snd ρLR.val).m

/-- A product state is separable -/
theorem IsSeparable_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : IsSeparable (ρ₁ ⊗ ρ₂) := by
  let only := (ρ₁, ρ₂)
  use { only }, Distribution.constant ⟨only, Finset.mem_singleton_self only⟩
  simp only [prod, Finset.univ_unique, Unique.eq_default, Distribution.constant_eq, ite_true,
    Prob.toReal_one, Finset.default_singleton, one_smul, Finset.sum_const, Finset.card_singleton]

--TODO: Separable states are convex

section purification

/-- The purification of a mixed state. Always uses the full dimension of the Hilbert space (d) to
 purify, so e.g. an existing pure state with d=4 still becomes d=16 in the purification. The defining
 property is `MState.trace_right_of_purify`; see also `MState.purify'` for the bundled version. -/
def purify (ρ : MState d) : Ket (d × d) where
  vec := fun (i,j) ↦
    let ρ2 := ρ.Hermitian.eigenvectorMatrix i j
    ρ2 * (ρ.Hermitian.eigenvalues j).sqrt
  normalized' := by
    have h₁ := fun i ↦ ρ.pos.eigenvalues_nonneg i
    simp [mul_pow, Real.sq_sqrt, h₁]
    simp_rw [Matrix.IsHermitian.eigenvectorMatrix_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have : ∀x, ∑ i : d, Complex.abs ((Matrix.IsHermitian.eigenvectorBasis ρ.Hermitian) x i) ^ 2 = 1 :=
      sorry
    -- rw [this]
    sorry

/-- The defining property of purification, that tracing out the purifying system gives the
 original mixed state. -/
@[simp]
theorem trace_right_of_purify (ρ : MState d) : (pure ρ.purify).trace_right = ρ := by
  ext i j
  simp_rw [purify, trace_right, Matrix.trace_right]
  simp only [pure_of, Matrix.of_apply, Ket.apply]
  simp only [map_mul]
  simp_rw [mul_assoc, mul_comm, ← mul_assoc (Complex.ofReal' _), Complex.mul_conj]
  sorry

/-- `MState.purify` bundled with its defining property `MState.trace_right_of_purify`. -/
def purify' (ρ : MState d) : { ψ : Ket (d × d) // (pure ψ).trace_right = ρ } :=
  ⟨ρ.purify, ρ.trace_right_of_purify⟩

end purification

--TODO: Swap and assoc for kets.
--TODO: Connect these to unitaries (when they can be)

/-- The heterogeneous SWAP gate that exchanges the left and right halves of a quantum system.
  This can apply even when the two "halves" are of different types, as opposed to (say) the SWAP
  gate on quantum circuits that leaves the qubit dimensions unchanged. Notably, it is not unitary. -/
def SWAP (ρ : MState (d₁ × d₂)) : MState (d₂ × d₁) where
  m := Matrix.of fun (i₁,j₁) (i₂,j₂) ↦ ρ.m (j₁,i₁) (j₂,i₂)
  pos := sorry
  tr := by convert ρ.tr; simp [Matrix.trace]; rw [Finset.sum_comm]

-- @[simp] --This theorem statement doesn't typecheck because spectrum reuses indices.
-- theorem spectrum_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.spectrum = ρ.spectrum :=
--   sorry

@[simp]
theorem SWAP_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.SWAP = ρ :=
  sorry

@[simp]
theorem trace_left_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.trace_left = ρ.trace_right :=
  sorry

@[simp]
theorem trace_right_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.trace_right = ρ.trace_left :=
  sorry

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc (ρ : MState ((d₁ × d₂) × d₃)) : MState (d₁ × d₂ × d₃) where
  m := Matrix.of fun (i₁,(j₁,k₁)) (i₂,(j₂,k₂)) ↦ ρ.m ((i₁,j₁),k₁) ((i₂,j₂),k₂)
  pos := sorry
  tr := by convert ρ.tr; simp [Matrix.trace]

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc' (ρ : MState (d₁ × d₂ × d₃)) : MState ((d₁ × d₂) × d₃) :=
  ρ.SWAP.assoc.SWAP.assoc.SWAP

@[simp]
theorem assoc_assoc' (ρ : MState (d₁ × d₂ × d₃)) : ρ.assoc'.assoc = ρ := by
  ext
  simp [assoc', assoc, SWAP]

@[simp]
theorem assoc'_assoc (ρ : MState ((d₁ × d₂) × d₃)) : ρ.assoc.assoc' = ρ := by
  have := ρ.SWAP.assoc_assoc'
  unfold assoc' at this
  rw [assoc', ← ρ.SWAP_SWAP, this]

@[simp]
theorem trace_left_right_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.trace_left.trace_right = ρ.trace_right.trace_left := by
  ext
  simp [assoc, Matrix.trace_left, trace_left, Matrix.trace_right, trace_right]
  rw [Finset.sum_comm]

@[simp]
theorem trace_right_left_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.trace_right.trace_left = ρ.trace_left.trace_right := by
  rw [← ρ.assoc'.trace_left_right_assoc, assoc_assoc']

@[simp]
theorem trace_right_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.trace_right = ρ.trace_right.trace_right := by
  ext
  simp [assoc, Matrix.trace_right, trace_right]

@[simp]
theorem trace_left_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.trace_left = ρ.trace_left.trace_left := by
  convert ρ.SWAP.assoc.SWAP.trace_right_assoc
  simp

@[simp]
theorem trace_left_left_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.trace_left.trace_left = ρ.trace_left := by
  ext
  simp only [assoc, trace_left, Matrix.trace_left, Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

@[simp]
theorem trace_right_right_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.trace_right.trace_right = ρ.trace_right := by
  simp [assoc']


theorem traceNorm_eq_1 (ρ : MState d) : ρ.m.traceNorm = 1 :=
  have := calc (ρ.m.traceNorm : ℂ)
    _ = ρ.m.trace := ρ.pos.traceNorm_PSD_eq_trace
    _ = 1 := ρ.tr
  Complex.ofReal_eq_one.mp this

end MState
