import QuantumInfo.ForMathlib
import ClassicalInfo.Distribution
import QuantumInfo.Finite.Braket

import Mathlib.Logic.Equiv.Basic

/-!
Finite dimensional quantum mixed states, ρ.

The same comments apply as in `Braket`:

These could be done with a Hilbert space of Fintype, which would look like
```lean4
(H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
```
or by choosing a particular `Basis` and asserting it is `Fintype`. But frankly it seems easier to
mostly focus on the basis-dependent notion of `Matrix`, which has the added benefit of an obvious
"classical" interpretation (as the basis elements, or diagonal elements of a mixed state). In that
sense, this quantum theory comes with the a particular classical theory always preferred.

Important definitions:
 * `instMixable`: the `Mixable` instance allowing convex combinations of `MState`s
 * `ofClassical`: Mixed states representing classical distributions
 * `purity`: The purity `Tr[ρ^2]` of a state
 * `spectrum`: The spectrum of the matrix
 * `uniform`: The maximally mixed state
 * `MEnsemble` and `PEnsemble`: Ensemble of mixed and pure states, respectively
 * `mix`: The total state corresponding to an ensemble
 * `average`: Averages a function over an ensemble, with appropriate weights
-/

noncomputable section

open Classical
open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

/-- A mixed state as a PSD matrix with trace 1.-/
structure MState (d : Type*) [Fintype d] extends HermitianMat d ℂ where
  zero_le : 0 ≤ toSubtype
  tr : val.trace = 1

namespace MState

variable {d d₁ d₂ d₃ : Type*} [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]

/-- The underlying `Matrix` in an MState-/
def m (ρ : MState d) : Matrix d d ℂ := ρ.val

/-- The underlying `HermitianMat` in an MState-/
@[reducible, coe]
def M (ρ : MState d) : HermitianMat d ℂ := ρ.toSubtype

instance instCoe : Coe (MState d) (HermitianMat d ℂ) := ⟨MState.M⟩

@[simp]
theorem tr' (ρ : MState d) : ρ.M.trace = 1 := by
  simp [HermitianMat.trace_eq_re_trace, ρ.tr]

@[simp]
theorem toSubtype_eq_coe (ρ : MState d) : ρ.toSubtype = ρ.M :=
  rfl


@[ext]
theorem ext {ρ₁ ρ₂ : MState d} (h : ρ₁.M = ρ₂.M) : ρ₁ = ρ₂ := by
  rw [MState.mk.injEq]
  exact h

--XXX These are methods that directly reference the matrix, "m" or ".val".
-- We'd like to remove these (where possible) so that mostly go through HermitianMat
-- where possible.
theorem pos (ρ : MState d) : ρ.val.PosSemidef :=
  HermitianMat.zero_le_iff.mp ρ.zero_le

/-- Every mixed state is Hermitian. -/
theorem Hermitian (ρ : MState d) : ρ.m.IsHermitian :=
  ρ.pos.left

@[simp]
theorem rtr (ρ : MState d) : ρ.Hermitian.rtrace = 1 := by
  simp only [Matrix.IsHermitian.rtrace, m, toSubtype_eq_coe, HermitianMat.val_eq_coe, ρ.tr,
    RCLike.one_re]

theorem ext_m {ρ₁ ρ₂ : MState d} (h : ρ₁.m = ρ₂.m) : ρ₁ = ρ₂ := by
  rw [MState.mk.injEq]
  ext1
  exact h
--XXX

/-- The map from mixed states to their matrices is injective -/
theorem toMat_inj : (MState.m (d := d)).Injective :=
  fun _ _ h ↦ by ext1; ext1; exact h

variable (d) in
/-- The matrices corresponding to MStates are `Convex ℝ` -/
theorem convex : Convex ℝ (Set.range (MState.m (d := d))) := by
  simp only [Convex, Set.mem_range, StarConvex,
    forall_exists_index, forall_apply_eq_imp_iff]
  intro x y a b ha hb hab
  replace hab : a + b = (1 : ℂ) := by norm_cast
  have := HermitianMat.convex_cone x.zero_le y.zero_le ha hb
  exact ⟨⟨_, this, by simp [x.tr, y.tr, hab]⟩, rfl⟩

instance instMixable : Mixable (Matrix d d ℂ) (MState d) where
  to_U := MState.m
  to_U_inj := ext_m
  mkT {u} := fun h ↦
    ⟨⟨⟨u, Exists.casesOn h fun t ht => ht ▸ t.pos.left⟩,
      Exists.casesOn h fun t ht => ht ▸ t.zero_le,
      Exists.casesOn h fun t ht => ht ▸ t.tr⟩, rfl⟩
  convex := convex d

--An MState is a witness that d is nonempty.
instance nonempty (ρ : MState d) : Nonempty d := by
  by_contra h
  simpa [not_nonempty_iff.mp h] using ρ.tr

theorem PosSemidef_outer_self_conj (v : d → ℂ) : Matrix.PosSemidef (Matrix.vecMulVec v (conj v)) := by
  constructor
  · ext
    simp [Matrix.vecMulVec_apply, mul_comm]
  · intro x
    simp_rw [dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec, dotProduct,
      Matrix.vecMulVec_apply, mul_assoc, ← Finset.mul_sum, ← mul_assoc, ← Finset.sum_mul]
    change
      0 ≤ (∑ i : d, (starRingEnd ℂ) (x i) * v i) * ∑ i : d, (starRingEnd ℂ) (v i) * x i
    have : (∑ i : d, (starRingEnd ℂ) (x i) * v i) =
        (∑ i : d, (starRingEnd ℂ) ((starRingEnd ℂ) (v i) * x i)) := by
          simp only [mul_comm ((starRingEnd ℂ) (x _)) (v _), map_mul,
          RingHomCompTriple.comp_apply, RingHom.id_apply]
    rw [this, ← map_sum, ← Complex.normSq_eq_conj_mul_self, Complex.zero_le_real, ← Complex.sq_norm]
    exact sq_nonneg _

-- Could have used properties of ρ.spectrum
theorem eigenvalue_nonneg (ρ : MState d) : ∀ i, 0 ≤ ρ.Hermitian.eigenvalues i := by
  apply (Matrix.PosSemidef.nonneg_iff_eigenvalue_nonneg ρ.Hermitian).mp
  exact ρ.zero_le

-- Could have used properties of  ρ.spectrum
theorem eigenvalue_le_one (ρ : MState d) : ∀ i, ρ.Hermitian.eigenvalues i ≤ 1 := by
  intro i
  have hsum : ρ.Hermitian.eigenvalues i ≤ ∑ x, ρ.Hermitian.eigenvalues x := by
    have hnonneg : ∀ y ∈ Finset.univ, 0 ≤ ρ.Hermitian.eigenvalues y := fun y _ ↦ Matrix.PosSemidef.eigenvalues_nonneg ρ.pos y
    have hi : i ∈ Finset.univ := Finset.mem_univ i
    exact Finset.single_le_sum hnonneg hi
  rw [Matrix.IsHermitian.sum_eigenvalues_eq_rtrace ρ.Hermitian, ρ.rtr] at hsum
  exact hsum

theorem le_one (ρ : MState d) : ρ.M ≤ 1 := by
  rw [Subtype.mk_le_mk]
  simp only [toSubtype_eq_coe, HermitianMat.val_eq_coe, selfAdjoint.val_one]
  suffices h : (↑ρ.toSubtype : Matrix d d ℂ) ≤ (1 : ℝ) • 1 by simp_all only [toSubtype_eq_coe, one_smul]
  apply (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff ρ.pos 1).mp
  exact eigenvalue_le_one ρ

/-- The inner product of two MState's, as a real number between 0 and 1. -/
def inner (ρ : MState d) (σ : MState d) : Prob :=
  ⟨ρ.M.inner σ.M, ρ.M.inner_ge_zero ρ.zero_le σ.zero_le,
    (ρ.M.inner_le_mul_trace ρ.zero_le σ.zero_le).trans (by simp)⟩

section exp_val

def exp_val_ℂ (T : Matrix d d ℂ) (ρ : MState d) : ℂ :=
  (T * ρ.m).trace

def exp_val (T : HermitianMat d ℂ) (ρ : MState d) : ℝ :=
  ρ.M.inner T

theorem exp_val_nonneg {T : HermitianMat d ℂ} (h : 0 ≤ T) (ρ : MState d) : 0 ≤ ρ.exp_val T :=
  HermitianMat.inner_ge_zero ρ.zero_le h

variable [DecidableEq d]

theorem exp_val_le_one {T : HermitianMat d ℂ} (h : T ≤ 1) (ρ : MState d) : ρ.exp_val T ≤ 1 := by
  have hmono := HermitianMat.inner_mono ρ.zero_le T 1 h
  rwa [HermitianMat.inner_one ρ.M, ρ.tr'] at hmono

theorem exp_val_prob {T : HermitianMat d ℂ} (h : 0 ≤ T ∧ T ≤ 1) (ρ : MState d) :
    0 ≤ ρ.exp_val T ∧ ρ.exp_val T ≤ 1 :=
  ⟨ρ.exp_val_nonneg h.1, ρ.exp_val_le_one h.2⟩

end exp_val

section pure

/-- A mixed state can be constructed as a pure state arising from a ket. -/
def pure (ψ : Ket d) : MState d where
  val := Matrix.vecMulVec ψ (ψ : Bra d)
  property := (PosSemidef_outer_self_conj ψ).1
  zero_le := HermitianMat.zero_le_iff.mpr (PosSemidef_outer_self_conj ψ)
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
  ⟨ρ.M.inner ρ.M, ⟨HermitianMat.inner_ge_zero ρ.zero_le ρ.zero_le,
    by simpa [ρ.tr'] using  HermitianMat.inner_le_mul_trace ρ.zero_le ρ.zero_le⟩⟩

/-- The eigenvalue spectrum of a mixed quantum state, as a `Distribution`. -/
def spectrum (ρ : MState d) : Distribution d :=
  Distribution.mk'
    (ρ.M.H.eigenvalues ·)
    (ρ.pos.eigenvalues_nonneg ·)
    (by simpa [ρ.tr] using congrArg Complex.re (ρ.M.H.sum_eigenvalues_eq_trace))

/-- The specturm of a pure state is (1,0,0,...), i.e. a constant distribution. -/
theorem spectrum_pure_eq_constant (ψ : Ket d) :
    ∃ i, (pure ψ).spectrum = Distribution.constant i := by
  let ρ := pure ψ
  let ρ_linMap := Matrix.toEuclideanLin ρ.m
  -- Prove 1 is in the spectrum of pure ψ by exhibiting an eigenvector with value 1.
  have : ∃i, (pure ψ).spectrum i = 1 := by
    simp [spectrum, Distribution.mk']
    have hEig : ∃i, (pure ψ).M.H.eigenvalues i = 1 := by
      -- Prove ψ is an eigenvector of ρ = pure ψ
      have hv : ρ.M *ᵥ ψ = ψ := by
        ext
        simp_rw [ρ, pure, Matrix.mulVec, MState.M, HermitianMat.toMat, Matrix.vecMulVec_apply, dotProduct,
        Bra.apply', Ket.apply, mul_assoc, ← Finset.mul_sum, ← Complex.normSq_eq_conj_mul_self,
        ← Complex.ofReal_sum, ← Ket.apply, ψ.normalized, Complex.ofReal_one, mul_one]
      let U : Matrix.unitaryGroup d ℂ := star ρ.M.H.eigenvectorUnitary -- Diagonalizing unitary of ρ
      let w : d → ℂ := U *ᵥ ψ
      -- Prove w = U ψ is an eigenvector of the diagonalized matrix of ρ = pure ψ
      have hDiag : Matrix.diagonal (RCLike.ofReal ∘ ρ.M.H.eigenvalues) *ᵥ w = w := by
        simp_rw [←Matrix.IsHermitian.star_mul_self_mul_eq_diagonal, eq_comm,
        ←Matrix.mulVec_mulVec, w, U, Matrix.mulVec_mulVec] -- Uses spectral theorem
        simp_all
        rw [←Matrix.mulVec_mulVec, hv]
      -- Prove w = U ψ is nonzero by contradiction
      have hwNonZero : ∃j, w j ≠ 0 := by
        by_contra hwZero
        simp at hwZero
        rw [←funext_iff] at hwZero
        -- If w is zero, then ψ is zero, since U is invertible
        have hψZero : ∀x, ψ x = 0 := by
          apply congr_fun
          -- Prove U is invertible
          have hUdetNonZero : (U : Matrix d d ℂ).det ≠ 0 := by
            by_contra hDetZero
            obtain ⟨u, huUni⟩ := U
            have h0uni: 0 ∈ unitary ℂ := by
              rw [←hDetZero]
              simp
              exact Matrix.det_of_mem_unitary huUni
            rw [unitary.mem_iff] at h0uni
            simp_all
          exact Matrix.eq_zero_of_mulVec_eq_zero hUdetNonZero hwZero
        -- Reach an contradiction that ψ has norm 0
        have hψn := Ket.normalized ψ
        have hnormZero : ∀ x : d, Complex.normSq (ψ x) = 0 := fun x => by
          rw [hψZero x, Complex.normSq_zero]
        have hsumZero : ∑ x : d, Complex.normSq (ψ x) = 0 := by
          apply Finset.sum_eq_zero
          intros x _
          exact hnormZero x
        simp_all
      obtain ⟨j, hwNonZero'⟩ := hwNonZero
      have hDiagj := congr_fun hDiag j
      rw [Matrix.mulVec_diagonal, mul_eq_right₀ hwNonZero'] at hDiagj
      use j
      simp_all
    obtain ⟨i, hEig'⟩ := hEig
    use i
    ext
    exact hEig'
  --If 1 is in a distribution, the distribution is a constant.
  obtain ⟨i, hi⟩ := this
  use i
  exact Distribution.constant_of_exists_one hi

/-- If the specturm of a mixed state is (1,0,0...) i.e. a constant distribution, it is
 a pure state. -/
theorem pure_of_constant_spectrum (ρ : MState d) (h : ∃ i, ρ.spectrum = Distribution.constant i) :
    ∃ ψ, ρ = pure ψ := by
  obtain ⟨i, h'⟩ := h
  -- Translate assumption to eigenvalues being (1,0,0,...)
  have hEig : ρ.M.H.eigenvalues = fun x => if x = i then 1 else 0 := by
    ext x
    simp [spectrum, Distribution.constant, Distribution.mk'] at h'
    rw [Subtype.mk.injEq] at h'
    have h'x := congr_fun h' x
    rw [if_congr (Eq.comm) (Eq.refl 1) (Eq.refl 0)]
    rw [Prob.eq_iff] at h'x
    dsimp at h'x
    rw [h'x]
    split_ifs
    case pos => rfl
    case neg => rfl
  -- Choose the eigenvector v of ρ with eigenvalue 1 to make ψ
  let ⟨u, huUni⟩ := ρ.M.H.eigenvectorUnitary -- Diagonalizing unitary of ρ
  let D : Matrix d d ℂ := Matrix.diagonal (RCLike.ofReal ∘ ρ.M.H.eigenvalues) -- Diagonal matrix of ρ
  let v : EuclideanSpace ℂ d := ρ.M.H.eigenvectorBasis i
  -- Prove v is normalized
  have hUvNorm : ∑ x, ‖v x‖^2 = 1 := by
    have hinnerv : Inner.inner ℂ v v = 1 := by
      have := OrthonormalBasis.orthonormal ρ.M.H.eigenvectorBasis
      rw [orthonormal_iff_ite] at this
      simpa using this i i
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.mul_conj'] at hinnerv
    rw [← Fintype.sum_equiv (Equiv.refl d) _ (fun x => (Complex.ofReal ‖v x‖) ^ 2) (fun x => Complex.ofReal_pow ‖v x‖ 2)] at hinnerv
    rw [← Complex.ofReal_sum Finset.univ (fun x => ‖v x‖ ^ 2), Complex.ofReal_eq_one] at hinnerv
    exact hinnerv
  let ψ : Ket d := ⟨v, hUvNorm⟩ -- Construct ψ
  use ψ
  ext j k
  simp
  -- Use spectral theorem to prove that ρ = pure ψ
  rw [Matrix.IsHermitian.spectral_theorem ρ.M.H, Matrix.mul_apply]
  simp [ψ, Ket.apply, v, hEig]
  have hsum : ∀ x ∈ Finset.univ, x ∉ ({i} : Finset d) → (ρ.M.H.eigenvectorBasis x j) * (↑(if x = i then 1 else 0) : ℝ) * (starRingEnd ℂ) (ρ.Hermitian.eigenvectorBasis x k) = 0 := by
    intros x hx hxnoti
    rw [Finset.mem_singleton] at hxnoti
    rw [eq_false hxnoti, if_false, Complex.ofReal_zero]
    ring
  simp_rw [←Finset.sum_subset (Finset.subset_univ {i}) hsum, Finset.sum_singleton, reduceIte, Complex.ofReal_one, mul_one]
  rfl

/-- A state ρ is pure iff its spectrum is (1,0,0,...) i.e. a constant distribution. -/
theorem pure_iff_constant_spectrum (ρ : MState d) : (∃ ψ, ρ = pure ψ) ↔
    ∃ i, ρ.spectrum = Distribution.constant i :=
  ⟨fun h ↦ h.rec fun ψ h₂ ↦ h₂ ▸ spectrum_pure_eq_constant ψ,
  pure_of_constant_spectrum ρ⟩

theorem pure_iff_purity_one (ρ : MState d) : (∃ ψ, ρ = pure ψ) ↔ ρ.purity = 1 := by
  --purity = exp(-Collision entropy)
  --purity eq 1 iff collision entropy is zero
  --entropy is zero iff distribution is constant
  --distribution is constant iff pure
  sorry

end pure

section prod

def prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : MState (d₁ × d₂) where
  val := ρ₁.m ⊗ₖ ρ₂.m
  property := (ρ₁.pos.PosSemidef_kronecker ρ₂.pos).1
  zero_le := HermitianMat.zero_le_iff.mpr (ρ₁.pos.PosSemidef_kronecker ρ₂.pos)
  tr := by simpa [MState.m, MState.tr] using ρ₁.m.trace_kronecker ρ₂.m

notation ρL "⊗" ρR => prod ρL ρR

/-- The product of pure states is a pure product state , `Ket.prod`. -/
theorem pure_prod_pure (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : pure (ψ₁ ⊗ ψ₂) = (pure ψ₁) ⊗ (pure ψ₂) := by
  ext
  simp only [pure, Ket.prod, Ket.apply, Matrix.vecMulVec_apply, Bra.eq_conj, map_mul, prod,
    Matrix.kroneckerMap_apply, MState.m]
  ring

end prod

/-- A representation of a classical distribution as a quantum state, diagonal in the given basis. -/
def ofClassical (dist : Distribution d) : MState d where
  val := Matrix.diagonal (fun x ↦ dist x)
  property : Matrix.IsHermitian _ := by simp [Matrix.isHermitian_diagonal_iff, IsSelfAdjoint]
  zero_le := HermitianMat.zero_le_iff.mpr (by simp [Matrix.posSemidef_diagonal_iff])
  tr := by
    simp [Matrix.trace_diagonal]
    have h₃ := dist.2
    norm_cast

/-- The maximally mixed state. -/
def uniform [Nonempty d] : MState d := ofClassical Distribution.uniform

/-- There is exactly one state on a dimension-1 system. -/
instance instUnique [Unique d] : Unique (MState d) where
  default := @uniform _ _ instNonemptyOfInhabited
  uniq := by
    intro ρ
    ext
    have h₁ := ρ.tr
    have h₂ := (@uniform _ _ instNonemptyOfInhabited : MState d).tr
    simp [Matrix.trace, Unique.eq_default] at h₁ h₂ ⊢
    exact h₁.trans h₂.symm

/-- There exists a mixed state for every nonempty `d`.
Here, the maximally mixed one is chosen. -/
instance instInhabited [Nonempty d] : Inhabited (MState d) where
  default := uniform

section ptrace

-- TODO:
-- * Partial trace of direct product is the original state

/-- Partial tracing out the left half of a system. -/
def traceLeft (ρ : MState (d₁ × d₂)) : MState d₂ where
  toSubtype := ⟨ρ.m.traceLeft, ρ.M.H.traceLeft⟩
  zero_le :=  HermitianMat.zero_le_iff.mpr (ρ.pos.traceLeft)
  tr := ρ.tr ▸ ρ.m.traceLeft_trace

/-- Partial tracing out the right half of a system. -/
def traceRight (ρ : MState (d₁ × d₂)) : MState d₁ where
  toSubtype := ⟨ρ.m.traceRight, ρ.M.H.traceRight⟩
  zero_le := HermitianMat.zero_le_iff.mpr (ρ.pos.traceRight)
  tr := ρ.tr ▸ ρ.m.traceRight_trace

/-- Taking the direct product on the left and tracing it back out gives the same state. -/
@[simp]
theorem traceLeft_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : traceLeft (ρ₁ ⊗ ρ₂) = ρ₂ := by
  ext
  simp_rw [traceLeft, Matrix.traceLeft, prod]
  dsimp
  have h : (∑ i : d₁, ρ₁.M.toMat i i) = 1 := ρ₁.tr
  simp [MState.m, ← Finset.sum_mul, h]

/-- Taking the direct product on the right and tracing it back out gives the same state. -/
@[simp]
theorem traceRight_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : traceRight (ρ₁ ⊗ ρ₂) = ρ₁ := by
  ext
  simp_rw [traceRight, Matrix.traceRight, prod]
  dsimp
  have h : (∑ i : d₂, ρ₂.M.toMat i i) = 1 := ρ₂.tr
  simp [MState.m, ← Finset.mul_sum, h]

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

/-- A product state `MState.prod` is separable. -/
theorem IsSeparable_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : IsSeparable (ρ₁ ⊗ ρ₂) := by
  let only := (ρ₁, ρ₂)
  use { only }, Distribution.constant ⟨only, Finset.mem_singleton_self only⟩
  simp only [prod, Finset.univ_unique, Unique.eq_default, Distribution.constant_eq, ite_true,
    Prob.coe_one, Finset.default_singleton, one_smul, Finset.sum_const, Finset.card_singleton,
    only, MState.m]

/-- A pure state is separable iff the ket is a product state. -/
theorem pure_separable_iff_IsProd (ψ : Ket (d₁ × d₂)) :
    IsSeparable (pure ψ) ↔ ψ.IsProd := by
  sorry

/-- A pure state is separable iff the partial trace on the left is pure. -/
theorem pure_separable_iff_traceLeft_pure (ψ : Ket (d₁ × d₂)) : IsSeparable (pure ψ) ↔
    ∃ ψ₁, pure ψ₁ = (pure ψ).traceLeft := by
  sorry

--TODO: Separable states are convex

section purification

/-- The purification of a mixed state. Always uses the full dimension of the Hilbert space (d) to
 purify, so e.g. an existing pure state with d=4 still becomes d=16 in the purification. The defining
 property is `MState.traceRight_of_purify`; see also `MState.purify'` for the bundled version. -/
def purify (ρ : MState d) : Ket (d × d) where
  vec := fun (i,j) ↦
    let ρ2 := ρ.Hermitian.eigenvectorUnitary i j
    ρ2 * (ρ.Hermitian.eigenvalues j).sqrt
  normalized' := by
    have h₁ := fun i ↦ ρ.pos.eigenvalues_nonneg i
    simp [mul_pow, Real.sq_sqrt, h₁, Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_mul]
    have : ∀x, ∑ i : d, ‖ρ.Hermitian.eigenvectorBasis x i‖ ^ 2 = 1 :=
      sorry
    apply @RCLike.ofReal_injective ℂ
    simp_rw [this, one_mul, Matrix.IsHermitian.sum_eigenvalues_eq_trace]
    exact ρ.tr

/-- The defining property of purification, that tracing out the purifying system gives the
 original mixed state. -/
@[simp]
theorem purify_spec (ρ : MState d) : (pure ρ.purify).traceRight = ρ := by
  ext i j
  simp_rw [purify, traceRight, Matrix.traceRight]
  simp only [pure_of, Matrix.of_apply, Ket.apply]
  simp only [map_mul]
  simp_rw [mul_assoc, mul_comm, ← mul_assoc (Complex.ofReal _), Complex.mul_conj]
  sorry

/-- `MState.purify` bundled with its defining property `MState.traceRight_of_purify`. -/
def purifyX (ρ : MState d) : { ψ : Ket (d × d) // (pure ψ).traceRight = ρ } :=
  ⟨ρ.purify, ρ.purify_spec⟩

end purification

def relabel (ρ : MState d₁) (e : d₂ ≃ d₁) : MState d₂ where
  val := ρ.m.reindex e.symm e.symm
  property := ((Matrix.posSemidef_submatrix_equiv e).mpr ρ.pos).1
  zero_le := (HermitianMat.zero_le_iff.trans (Matrix.posSemidef_submatrix_equiv e)).mpr <| ρ.pos
  tr := ρ.tr ▸ Fintype.sum_equiv _ _ _ (congrFun rfl)

@[simp]
theorem relabel_m (ρ : MState d₁) (e : d₂ ≃ d₁) :
    (ρ.relabel e).m = ρ.m.submatrix e e := by
  rfl

--TODO: Swap and assoc for kets.
--TODO: Connect these to unitaries (when they can be)

/-- The heterogeneous SWAP gate that exchanges the left and right halves of a quantum system.
  This can apply even when the two "halves" are of different types, as opposed to (say) the SWAP
  gate on quantum circuits that leaves the qubit dimensions unchanged. Notably, it is not unitary. -/
def SWAP (ρ : MState (d₁ × d₂)) : MState (d₂ × d₁) :=
  ρ.relabel (Equiv.prodComm d₁ d₂).symm

def spectrum_SWAP (ρ : MState (d₁ × d₂)) : ∃ e, ρ.SWAP.spectrum.relabel e = ρ.spectrum := by
  sorry

@[simp]
theorem SWAP_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.SWAP = ρ :=
  rfl

@[simp]
theorem traceLeft_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.traceLeft = ρ.traceRight :=
  rfl

@[simp]
theorem traceRight_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.traceRight = ρ.traceLeft :=
  rfl

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc (ρ : MState ((d₁ × d₂) × d₃)) : MState (d₁ × d₂ × d₃) :=
  ρ.relabel (Equiv.prodAssoc d₁ d₂ d₃).symm

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc' (ρ : MState (d₁ × d₂ × d₃)) : MState ((d₁ × d₂) × d₃) :=
  ρ.SWAP.assoc.SWAP.assoc.SWAP

@[simp]
theorem assoc_assoc' (ρ : MState (d₁ × d₂ × d₃)) : ρ.assoc'.assoc = ρ := by
  rfl

@[simp]
theorem assoc'_assoc (ρ : MState ((d₁ × d₂) × d₃)) : ρ.assoc.assoc' = ρ := by
  rfl

@[simp]
theorem traceLeft_right_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceLeft.traceRight = ρ.traceRight.traceLeft := by
  ext
  simpa [assoc, relabel, Matrix.traceLeft, traceLeft, Matrix.traceRight, traceRight]
    using Finset.sum_comm

@[simp]
theorem traceRight_left_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceRight.traceLeft = ρ.traceLeft.traceRight := by
  rw [← ρ.assoc'.traceLeft_right_assoc, assoc_assoc']

@[simp]
theorem traceRight_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceRight = ρ.traceRight.traceRight := by
  simp [Matrix.traceRight, traceRight, Fintype.sum_prod_type]
  rfl

@[simp]
theorem traceLeft_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceLeft = ρ.traceLeft.traceLeft := by
  convert ρ.SWAP.assoc.SWAP.traceRight_assoc
  simp

@[simp]
theorem traceLeft_left_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceLeft.traceLeft = ρ.traceLeft := by
  ext
  simpa [assoc, relabel, traceLeft, Matrix.traceLeft, Matrix.of_apply, Fintype.sum_prod_type]
    using Finset.sum_comm

@[simp]
theorem traceRight_right_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceRight.traceRight = ρ.traceRight := by
  simp [assoc']

@[simp]
theorem traceNorm_eq_1 (ρ : MState d) : ρ.m.traceNorm = 1 :=
  have := calc (ρ.m.traceNorm : ℂ)
    _ = ρ.m.trace := ρ.pos.traceNorm_PSD_eq_trace
    _ = 1 := ρ.tr
  Complex.ofReal_eq_one.mp this

section topology

/-- Mixed states inherit the subspace topology from matrices -/
instance instTopoMState : TopologicalSpace (MState d) :=
  TopologicalSpace.induced (MState.m) instTopologicalSpaceMatrix

/-- The projection from mixed states to their matrices is an embedding -/
theorem toMat_IsEmbedding : Topology.IsEmbedding (MState.m (d := d)) where
  eq_induced := rfl
  injective := toMat_inj

instance instT5MState : T3Space (MState d) :=
  Topology.IsEmbedding.t3Space toMat_IsEmbedding

instance instCompactSpace : CompactSpace (MState d) :=
  sorry

theorem Continuous_Matrix : Continuous (MState.M (d := d)) :=
  sorry

end topology

section finprod

variable {ι : Type u} [DecidableEq ι] [fι : Fintype ι]
variable {dI : ι → Type v} [∀(i :ι), Fintype (dI i)] [∀(i :ι), DecidableEq (dI i)]

def piProd (ρi : (i:ι) → MState (dI i)) : MState ((i:ι) → dI i) where
  val j k := ∏ (i : ι), (ρi i).m (j i) (k i)
  property := sorry
  zero_le := by
    rw [HermitianMat.zero_le_iff]
    --Should be in Mathlib
    constructor
    · ext j k
      dsimp
      rw [map_prod]
      congr! with i
      exact Matrix.ext_iff.mpr ((ρi i).pos.isHermitian) (j i) (k i)
    · intro v
      sorry
  tr := by
    dsimp [Matrix.trace]
    convert (Finset.prod_univ_sum (κ := dI) (fun _ ↦ Finset.univ) (fun i_1 x ↦ (ρi i_1).m x x)).symm
    symm
    apply Finset.prod_eq_one
    intro x hx
    exact (ρi x).tr

def npow (ρ : MState d) (n : ℕ) : MState (Fin n → d) :=
  piProd (fun _ ↦ ρ)

notation ρ "⊗^" n => MState.npow ρ n

end finprod

end MState
