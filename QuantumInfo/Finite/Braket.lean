import QuantumInfo.ForMathlib
import ClassicalInfo.Distribution

/-!
Finite dimensional quantum pure states, bra and kets. Mixed states are `MState` in that file.

These could be done with a Hilbert space of Fintype, which would look like
```lean4
(H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
```
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
 from a Fintype. Kets are distinctly not a vector space in our notion, as they represent only normalized
 states and so cannot (in general) be added or scaled. -/
structure Ket where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖^2 = 1

/-- A bra is definitionally identical to a `Ket`, but are separate to avoid complex conjugation confusion.
 They can be interconverted with the adjoint: `Ket.to_bra` and `Bra.to_ket` -/
structure Bra where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖^2 =1

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

def dot (ξ : Bra d) (ψ : Ket d) : ℂ := ∑ x, (ξ x) * (ψ x)

scoped notation "〈" ξ:90 "‖" ψ:90 "〉" => dot (ξ : Bra _) (ψ : Ket _)

end Braket

section braket
open Braket

variable {d : Type*} [Fintype d]

theorem Ket.apply (ψ : Ket d) (i : d) : ψ i = ψ.vec i :=
  rfl

theorem Bra.apply (ψ : Bra d) (i : d) : ψ i = ψ.vec i :=
  rfl

@[ext]
theorem Ket.ext {ξ ψ : Ket d} (h : ∀ x, ξ x = ψ x) : ξ = ψ :=
  DFunLike.ext ξ ψ h

@[ext]
theorem Bra.ext {ξ ψ : Bra d} (h : ∀ x, ξ x = ψ x) : ξ = ψ :=
  DFunLike.ext ξ ψ h

theorem Ket.normalized (ψ : Ket d) : ∑ x, Complex.normSq (ψ x) = 1 := by
  convert ψ.normalized'
  rw [Complex.norm_eq_abs, Complex.sq_abs]
  rfl

theorem Bra.normalized (ψ : Bra d) : ∑ x, Complex.normSq (ψ x) = 1 := by
  convert ψ.normalized'
  rw [Complex.norm_eq_abs, Complex.sq_abs]
  rfl

/-- Any Bra can be turned into a Ket by conjugating the elements. -/
@[coe]
def Ket.to_bra (ψ : Ket d) : Bra d :=
  ⟨conj ψ, by simpa using ψ.2⟩

/-- Any Ket can be turned into a Bra by conjugating the elements. -/
@[coe]
def Bra.to_ket (ψ : Bra d) : Ket d :=
  ⟨conj ψ, by simpa using ψ.2⟩

instance instBraOfKet : Coe (Ket d) (Bra d) := ⟨Ket.to_bra⟩

instance instKetOfBra : Coe (Bra d) (Ket d) := ⟨Bra.to_ket⟩

@[simp]
theorem Bra.eq_conj (ψ : Ket d) (x : d) :〈ψ∣ x = conj (∣ψ〉 x) :=
  rfl

theorem Bra.apply' (ψ : Ket d) (i : d) : 〈ψ∣ i = conj (ψ.vec i) :=
  rfl

/-- Construct the Ket corresponding to a basis vector, with a +1 phase. -/
def Ket.basis (i : d) : Ket d :=
  ⟨fun j ↦ if i = j then 1 else 0, by simp [apply_ite]⟩

/-- Construct the Bra corresponding to a basis vector, with a +1 phase. -/
def Bra.basis (i : d) : Bra d :=
  ⟨fun j ↦ if i = j then 1 else 0, by simp [apply_ite]⟩

/-- A Bra can be viewed as a function from Ket's to ℂ. -/
instance instFunLikeBraket : FunLike (Bra d) (Ket d) ℂ where
  coe ξ := dot ξ
  coe_injective' x y h := by
    ext i
    simpa [Ket.basis, dot, Ket.apply] using congrFun h (Ket.basis i)

/-- The inner product of any state with itself is 1. -/
theorem Braket.dot_self_eq_one (ψ : Ket d) :〈ψ‖ψ〉= 1 := by
  have h₁ : ∀x, conj (ψ x) * ψ x = Complex.normSq (ψ x) := fun x ↦ by
    rw [Complex.normSq_eq_conj_mul_self]
  simp only [dot, Bra.eq_conj, h₁]
  have h₂ := congrArg Complex.ofReal ψ.normalized
  simpa using h₂

section prod
variable {d d₁ d₂ : Type*} [Fintype d] [Fintype d₁] [Fintype d₂]

/-- The outer product of two kets, creating an unentangled state. -/
def Ket.prod (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : Ket (d₁ × d₂) where
  vec := fun (i,j) ↦ ψ₁ i * ψ₂ j
  normalized' := by
    simp only [Fintype.sum_prod_type, norm_mul, Complex.norm_eq_abs, mul_pow, ← Finset.mul_sum,
      Complex.sq_abs, ψ₂.normalized, mul_one, ψ₁.normalized]

notation ψ₁ "⊗" ψ₂ => Ket.prod ψ₁ ψ₂

/-- A Ket is a product if it's `Ket.prod` of two kets. -/
def Ket.IsProd (ψ : Ket (d₁ × d₂)) : Prop := ∃ ξ φ, ψ = ξ ⊗ φ

/-- A Ket is entangled if it's not `Ket.prod` of two kets. -/
def Ket.IsEntangled (ψ : Ket (d₁ × d₂)) : Prop := ¬ψ.IsProd

/-- `Ket.prod` states are product states. -/
@[simp]
theorem Ket.IsProd_prod (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : (ψ₁.prod ψ₂).IsProd :=
  ⟨ψ₁, ψ₂, rfl⟩

/-- `Ket.prod` states are not entangled states. -/
@[simp]
theorem Ket.not_IsEntangled_prod (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : ¬(ψ₁.prod ψ₂).IsEntangled :=
  (· (ψ₁.IsProd_prod ψ₂))

/-- A ket is a product state iff its components are cross-multiplicative. -/
theorem Ket.IsProd_iff_mul_eq_mul (ψ : Ket (d₁ × d₂)) : ψ.IsProd ↔
    ∀ i₁ i₂ j₁ j₂, ψ (i₁,j₁)  * ψ (i₂,j₂) = ψ (i₁,j₂) * ψ (i₂,j₁) := by
  constructor
  · rintro ⟨ξ,φ,rfl⟩ i₁ i₂ j₁ j₂
    simp only [prod, apply]
    ring_nf
  · sorry

end prod

section mes
/-- The Maximally Entangled State, or MES, on a d×d system. In principle there are many, this
is specifically the MES with an all-positive phase. For instance on `d := Fin 2`, this is the
Bell state -/
def Ket.MES (d) [Fintype d] [Nonempty d] : Ket (d × d) where
  vec := fun (i,j) ↦ if i = j then 1 / Real.sqrt (Fintype.card (α := d)) else 0
  normalized' := by
    simp [apply_ite, Fintype.sum_prod_type]

/-- On any space of dimension at least two, the maximally entangled state `MES` is entangled. -/
theorem Ket.MES_IsEntangled [Nontrivial d] : (Ket.MES d).IsEntangled := by
  obtain ⟨x, y, h⟩ := @Nontrivial.exists_pair_ne d _
  rw [IsEntangled, MES, IsProd_iff_mul_eq_mul]
  push_neg
  use x, y, x, y
  simp [apply, h]

end mes

section equiv

/-- The equivalence relation on `Ket` where two kets equivalent if they are equal up to a global phase, i.e. `∃ z, ‖z‖ = 1 ∧ a.vec = z • b.vec -/
def Ket.PhaseEquiv : Setoid (Ket d) where
  r a b := ∃ z : ℂ, ‖z‖ = 1 ∧ a.vec = z • b.vec
  iseqv := {
    refl := fun x ↦ ⟨1, by simp⟩,
    symm := fun ⟨z,h₁,h₂⟩ ↦ ⟨conj z,
      by simp [h₁],
      by simp [h₂, smul_smul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, h₁]⟩,
    trans := fun ⟨z₁,h₁₁,h₁₂⟩ ⟨z₂,h₂₁,h₂₂⟩ ↦ ⟨z₁ * z₂,
      by simp [h₁₁, h₂₁],
      by simpa [h₁₂, h₂₂] using smul_smul _ _ _⟩
  }

variable (d) in
/-- The type of `Ket`s up to a global phase equivalence, as given by `Ket.PhaseEquiv`. In particular, `MState`s really only care about a KetUpToPhase, and not Kets themselves. -/
def KetUpToPhase :=
  @Quotient (Ket d) Ket.PhaseEquiv

end equiv
end braket
