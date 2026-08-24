/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.PiKron
import QuantumLib.QECC.UnitaryBasis
import QuantumLib.QECC.KnillLaflamme

/-!
# Correcting `d` errors implies correcting the erasure of `2d` qudits

A code that corrects arbitrary unitary errors on any `d` of its qudits survives the *erasure* of
any `2d` of them, and hence obeys the quantum Singleton bound in the form
`|d1| · |d2| ^ (2d) ≤ |d2| ^ n`.

The bridge between the two error models is the Knill–Laflamme condition. The Kraus operators of the
erasure channel multiply to operators supported on the erased set (`piKron A` with `A q = 1` off the
set), so the erasure is correctable as soon as every such operator compresses to a scalar on the
code space. Splitting the erased set into two halves of at most `d` qudits, each factor is a linear
combination of unitary errors of weight at most `d` — the *discretisation of errors*,
`errMat_mem_of_unitary_mem`, which comes from the spanning family `unitaryBasis` — and the
compression of a product of two unitary errors is a scalar because a single decoder corrects both,
`exists_scalar_of_recovery_two_unitaries`.

## Main results

* `QECC.errMat_mem_of_unitary_mem` — discretisation: a linear condition holding for all unitary
  errors on a set holds for all errors on that set;
* `QECC.exists_scalar_piKron_of_correctsErrors` — every operator supported on `2d` qudits
  compresses to a scalar on the code space;
* `QECC.correctsErasure_of_correctsErrors` — correcting `d` errors implies correcting the erasure
  of any `2d` qudits;
* `QECC.singleton_bound_of_correctsErrors` — the quantum Singleton bound for a code correcting `d`
  errors;
* `QECC.two_mul_lt_card_of_correctsErrors` — the no-cloning bound `2d < n`.
-/

open scoped Matrix

namespace QuantumLib

/-! ### Operators sandwiched to a scalar -/

variable {m n p : Type*} [Fintype m] [Fintype n] [DecidableEq p]

/-- The operators `Z` with `L * Z * R` a scalar matrix. Being a submodule is what upgrades a
statement about unitary errors to a statement about arbitrary errors. -/
def scalarSandwich (L : Matrix p m ℂ) (R : Matrix n p ℂ) : Submodule ℂ (Matrix m n ℂ) where
  carrier := {Z | ∃ z : ℂ, L * Z * R = z • 1}
  add_mem' := by
    rintro Z Z' ⟨z, hz⟩ ⟨z', hz'⟩
    exact ⟨z + z', by rw [Matrix.mul_add, Matrix.add_mul, hz, hz', add_smul]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c Z ⟨z, hz⟩
    exact ⟨c * z, by rw [Matrix.mul_smul, Matrix.smul_mul, hz, smul_smul]⟩

theorem mem_scalarSandwich {L : Matrix p m ℂ} {R : Matrix n p ℂ} {Z : Matrix m n ℂ} :
    Z ∈ scalarSandwich L R ↔ ∃ z : ℂ, L * Z * R = z • 1 := Iff.rfl

namespace QECC

variable {d1 i d2 : Type*} [Fintype i] [DecidableEq i] [Fintype d1] [DecidableEq d1]
  [Fintype d2] [DecidableEq d2]

/-! ### Discretisation of errors -/

/-- **Discretisation of errors.** A linear condition satisfied by every *unitary* error supported on
`T` is satisfied by every error supported on `T`: each site is expanded in the spanning family of
unitaries `unitaryBasis`. -/
theorem errMat_mem_of_unitary_mem (T : Finset i) {M : Submodule ℂ (Matrix (i → d2) (i → d2) ℂ)}
    (hM : ∀ U : i → 𝐔[d2], errMat T (fun q => (U q : Matrix d2 d2 ℂ)) ∈ M)
    (A : i → Matrix d2 d2 ℂ) : errMat T A ∈ M :=
  errMat_mem_of_mem (fun k => ((unitaryBasis k : 𝐔[d2]) : Matrix d2 d2 ℂ)) (Sum.inl ())
    exists_unitaryBasis_expansion T (fun f => hM fun q => unitaryBasis (f q)) A

/-! ### Compressions to the code space -/

/-- The compression of a product of two unitary errors, each of weight at most `k`, is a scalar on
the code space of a code correcting `k` errors. -/
theorem exists_scalar_errMat_mul_errMat [Nonempty d1] {C : QECC d1 i d2} {k : ℕ}
    {W : Matrix (i → d2) d1 ℂ} (hW : Wᴴ * W = 1) (hC : C.encoder = CPTPOp.ofIsometry W hW)
    (hcorr : C.CorrectsErrors k) {S₁ S₂ : Finset i} (h₁ : S₁.card ≤ k) (h₂ : S₂.card ≤ k)
    (U V : i → 𝐔[d2]) :
    ∃ z : ℂ, Wᴴ * (errMat S₁ fun q => (U q : Matrix d2 d2 ℂ)) *
      ((errMat S₂ fun q => (V q : Matrix d2 d2 ℂ)) * W) = z • 1 := by
  have hstar : (errMat S₁ fun q => ((star (U q) : 𝐔[d2]) : Matrix d2 d2 ℂ))ᴴ
      = errMat S₁ fun q => (U q : Matrix d2 d2 ℂ) := by
    rw [errMat_conjTranspose]
    refine congrArg (errMat S₁) (funext fun q => ?_)
    rw [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  obtain ⟨z, hz⟩ := exists_scalar_of_recovery_two_unitaries hW
    (errMat_conjTranspose_mul_self S₁ fun q => star (U q))
    (errMat_conjTranspose_mul_self S₂ V)
    (unitaryError_map S₁ fun q => star (U q)) (unitaryError_map S₂ V)
    (hC ▸ hcorr S₁ h₁ fun q => star (U q)) (hC ▸ hcorr S₂ h₂ V)
  rw [hstar] at hz
  exact ⟨z, by rw [← Matrix.mul_assoc]; exact hz⟩

/-- **Every operator supported on `2k` qudits compresses to a scalar** on the code space of a code
correcting `k` errors. The support is split into two halves of at most `k` qudits, and each half is
discretised into unitary errors. -/
theorem exists_scalar_piKron_of_correctsErrors [Nonempty d1] {C : QECC d1 i d2} {k : ℕ}
    {W : Matrix (i → d2) d1 ℂ} (hW : Wᴴ * W = 1) (hC : C.encoder = CPTPOp.ofIsometry W hW)
    (hcorr : C.CorrectsErrors k) {S : Finset i} (hS : S.card ≤ 2 * k)
    {A : i → Matrix d2 d2 ℂ} (hA : ∀ q ∉ S, A q = 1) :
    ∃ z : ℂ, Wᴴ * piKron A * W = z • 1 := by
  obtain ⟨S₁, hS₁sub, hS₁card⟩ :=
    Finset.exists_subset_card_eq (s := S) (n := min k S.card) (min_le_right _ _)
  have hcard₁ : S₁.card ≤ k := by rw [hS₁card]; exact min_le_left _ _
  have hcard₂ : (S \ S₁).card ≤ k := by
    rw [Finset.card_sdiff_of_subset hS₁sub, hS₁card]
    omega
  have hsplit : piKron A = errMat S₁ A * errMat (S \ S₁) A := by
    rw [errMat_mul_errMat Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hS₁sub, errMat]
    refine congrArg piKron (funext fun q => ?_)
    by_cases hq : q ∈ S
    · simp [hq]
    · simp [hq, hA q hq]
  have step₁ : ∀ V : i → 𝐔[d2], ∃ z : ℂ,
      Wᴴ * errMat S₁ A * ((errMat (S \ S₁) fun q => (V q : Matrix d2 d2 ℂ)) * W) = z • 1 := by
    intro V
    refine mem_scalarSandwich.mp (errMat_mem_of_unitary_mem S₁ (fun U => ?_) A)
    exact mem_scalarSandwich.mpr (exists_scalar_errMat_mul_errMat hW hC hcorr hcard₁ hcard₂ U V)
  have step₂ : ∃ z : ℂ, Wᴴ * errMat S₁ A * errMat (S \ S₁) A * W = z • 1 := by
    refine mem_scalarSandwich.mp (errMat_mem_of_unitary_mem (S \ S₁)
      (M := scalarSandwich (Wᴴ * errMat S₁ A) W) (fun V => ?_) A)
    obtain ⟨z, hz⟩ := step₁ V
    exact mem_scalarSandwich.mpr ⟨z, by rw [Matrix.mul_assoc]; exact hz⟩
  obtain ⟨z, hz⟩ := step₂
  exact ⟨z, by rw [hsplit, ← Matrix.mul_assoc]; exact hz⟩

/-! ### Erasure and the Singleton bound -/

/-- **Correcting `k` errors implies correcting the erasure of `2k` qudits.** The products of the
Kraus operators of the erasure channel are supported on the erased set, hence compress to scalars on
the code space; the Knill–Laflamme theorem then produces a recovery channel acting on the surviving
qudits alone. -/
theorem correctsErasure_of_correctsErrors [Nonempty d1] {C : QECC d1 i d2} {k : ℕ}
    {W : Matrix (i → d2) d1 ℂ} (hW : Wᴴ * W = 1) (hC : C.encoder = CPTPOp.ofIsometry W hW)
    (hcorr : C.CorrectsErrors k) {S : Finset i} (hS : S.card ≤ 2 * k) :
    C.CorrectsErasure S := by
  have hKL : IsKnillLaflamme W (discardKraus S) := by
    have key : ∀ s s' : {q : i // q ∈ S} → d2, ∃ z : ℂ,
        Wᴴ * (discardKraus S s)ᴴ * discardKraus S s' * W = z • 1 := by
      intro s s'
      obtain ⟨A, hA, hAeq⟩ := exists_piKron_discardKraus_conjTranspose_mul S s s'
      obtain ⟨z, hz⟩ := exists_scalar_piKron_of_correctsErrors hW hC hcorr hS hA
      exact ⟨z, by rw [Matrix.mul_assoc Wᴴ, hAeq]; exact hz⟩
    choose z hz using key
    exact ⟨z, hz⟩
  obtain ⟨R, hR⟩ := exists_recovery_of_isKnillLaflamme hW (discard_map S) hKL
  exact ⟨R, by rw [hC]; exact hR⟩

/-- **The quantum Singleton bound.** A code with an isometric encoder that corrects `k` errors
satisfies `|d1| · |d2| ^ (2k) ≤ |d2| ^ n`; in the qubit case `|d1| = 2 ^ K` and `|d2| = 2`, this is
`K + 2k ≤ n`. -/
theorem singleton_bound_of_correctsErrors {C : QECC d1 i d2} {k : ℕ}
    {W : Matrix (i → d2) d1 ℂ} (hW : Wᴴ * W = 1) (hC : C.encoder = CPTPOp.ofIsometry W hW)
    (hcorr : C.CorrectsErrors k) (hk : 2 * k ≤ Fintype.card i) :
    Fintype.card d1 * Fintype.card d2 ^ (2 * k) ≤ Fintype.card d2 ^ Fintype.card i := by
  rcases isEmpty_or_nonempty d1 with _ | _
  · simp
  · obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset i))
      (n := 2 * k) (by simpa using hk)
    have h := singleton_bound_of_erasure
      (correctsErasure_of_correctsErrors hW hC hcorr (S := S) hScard.le)
    rwa [hScard] at h

/-- **No-cloning bound.** A code with at least two logical states cannot correct errors on half of
its qudits: correcting `k` errors makes the erasure of any `2k` qudits recoverable, and if `2k`
reached `n` the recovery would reconstruct the logical state from the empty set of qudits. -/
theorem two_mul_lt_card_of_correctsErrors [Nonempty d2] {C : QECC d1 i d2} {k : ℕ}
    {W : Matrix (i → d2) d1 ℂ} (hW : Wᴴ * W = 1) (hC : C.encoder = CPTPOp.ofIsometry W hW)
    (hcorr : C.CorrectsErrors k) (hd1 : 2 ≤ Fintype.card d1) : 2 * k < Fintype.card i := by
  by_contra hc
  push Not at hc
  have : Nonempty d1 := Fintype.card_pos_iff.mp (by omega)
  have hS : (Finset.univ : Finset i).card ≤ 2 * k := by rwa [Finset.card_univ]
  have h := singleton_bound_of_erasure (correctsErasure_of_correctsErrors hW hC hcorr hS)
  rw [Finset.card_univ] at h
  have hpos : 0 < Fintype.card d2 ^ Fintype.card i := Nat.pow_pos Fintype.card_pos
  have h2 : 2 * Fintype.card d2 ^ Fintype.card i
      ≤ Fintype.card d1 * Fintype.card d2 ^ Fintype.card i := Nat.mul_le_mul_right _ hd1
  exact absurd (h2.trans h) (by omega)

end QECC

end QuantumLib
