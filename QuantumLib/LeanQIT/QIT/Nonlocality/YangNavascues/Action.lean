/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Nonlocality.YangNavascues.Coherence

/-!
# Branch-sum action lemmas for the CGS Yang-Navascues local isometry

This module exposes the finite branch-sum expansion layer needed before the
final CGS density calculation.  It does not identify the sum with the residual
garbage tensor target; that calculation remains a downstream theorem.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

namespace QIT
namespace YangNavascues

universe u v w

noncomputable section

/-- Applying the ancilla Fourier is the finite Fourier sum on the ancilla register. -/
theorem ancillaFourierMatrix_mulVec_apply {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (φ : H × Fin d → ℂ) (h : H) (k : Fin d) :
    ((ancillaFourierMatrix (H := H) d).mulVec φ) (h, k) =
      ∑ l : Fin d, fourierMatrix d k l * φ (h, l) := by
  rw [Matrix.mulVec, dotProduct, ← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_eq_single h]
  · simp [ancillaFourierMatrix]
  · intro h' _ hh'
    simp [ancillaFourierMatrix, Ne.symm hh']
  · intro hh
    exact (hh (Finset.mem_univ h)).elim

/-- Applying the inverse ancilla Fourier is the inverse Fourier sum on the ancilla register. -/
theorem ancillaInverseFourierMatrix_mulVec_apply
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (φ : H × Fin d → ℂ) (h : H) (k : Fin d) :
    ((ancillaInverseFourierMatrix (H := H) d).mulVec φ) (h, k) =
      ∑ l : Fin d, inverseFourierMatrix d k l * φ (h, l) := by
  rw [Matrix.mulVec, dotProduct, ← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_eq_single h]
  · simp [ancillaInverseFourierMatrix]
  · intro h' _ hh'
    simp [ancillaInverseFourierMatrix, Ne.symm hh']
  · intro hh
    exact (hh (Finset.mem_univ h)).elim

/-- Applying the zero-ancilla embedding places the input vector in the zero block. -/
theorem ancillaZeroMatrix_mulVec_apply
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (zero : Fin d) (φ : H → ℂ) (h : H) (k : Fin d) :
    ((ancillaZeroMatrix (H := H) zero).mulVec φ) (h, k) =
      if k = zero then φ h else 0 := by
  by_cases hk : k = zero
  · subst k
    simp [ancillaZeroMatrix, Matrix.mulVec, dotProduct]
  · simp [ancillaZeroMatrix, Matrix.mulVec, dotProduct, hk]

/-- Applying Fourier after the zero-ancilla embedding gives the zero column of `F`. -/
theorem ancillaFourierMatrix_ancillaZeroMatrix_mulVec_apply
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (zero : Fin d) (φ : H → ℂ) (h : H) (k : Fin d) :
    ((ancillaFourierMatrix (H := H) d *
      ancillaZeroMatrix (H := H) zero).mulVec φ) (h, k) =
      fourierMatrix d k zero * φ h := by
  rw [← Matrix.mulVec_mulVec]
  rw [ancillaFourierMatrix_mulVec_apply]
  rw [Finset.sum_eq_single zero]
  · simp [ancillaZeroMatrix_mulVec_apply]
  · intro y _ hy
    simp [ancillaZeroMatrix_mulVec_apply, hy]
  · intro hz
    exact (hz (Finset.mem_univ zero)).elim

/-- Applying a block-controlled operator only uses the block matching the ancilla value. -/
theorem controlledOperator_mulVec_apply
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (U : Fin d → CMatrix H)
    (φ : H × Fin d → ℂ) (h : H) (k : Fin d) :
    (controlledOperator U).mulVec φ (h, k) =
      (U k).mulVec (fun h' => φ (h', k)) h := by
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [controlledOperator]

/-- Applying a controlled unitary specializes the generic controlled-operator action. -/
theorem controlledUnitary_mulVec_apply
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (U : Fin d → Matrix.unitaryGroup H ℂ)
    (φ : H × Fin d → ℂ) (h : H) (k : Fin d) :
    (controlledUnitary U).mulVec φ (h, k) =
      (U k : CMatrix H).mulVec (fun h' => φ (h', k)) h := by
  simp [controlledUnitary, controlledOperator_mulVec_apply]

/-- Applying a controlled phase uses the phase-operator power selected by the ancilla. -/
theorem controlledPhase_mulVec_apply
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (φ : H × Fin d → ℂ) (h : H) (k : Fin d) :
    (controlledPhase P).mulVec φ (h, k) =
      ((phaseOperator P) ^ (k : ℕ)).mulVec (fun h' => φ (h', k)) h := by
  simp [controlledPhase, controlledOperator_mulVec_apply]

/--
The explicit projection branch selected by the finite Fourier gadget.

For incomplete projection families, the complement contributes only to the
distinguished zero Fourier branch.
-/
def fourierProjectionBranch {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H) (k : Fin d) : CMatrix H :=
  P k + if k = ⟨0, NeZero.pos d⟩ then (1 - ∑ l : Fin d, P l) else 0

private theorem finEquiv_eq_natCast (d : ℕ) [NeZero d] (i : Fin d) :
    ZMod.finEquiv d i = (i : ℕ) := by
  apply ZMod.val_injective d
  cases d with
  | zero => exact Fin.elim0 i
  | succ n =>
      change (i : ℕ) = ((i : ℕ) : ZMod (n + 1)).val
      rw [ZMod.val_natCast_of_lt i.isLt]

private theorem weightedProjection_mul {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H) (c e : Fin d → ℂ)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    (∑ i : Fin d, c i • P i) * (∑ j : Fin d, e j • P j) =
      ∑ i : Fin d, (c i * e i) • P i := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Matrix.mul_sum]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hIdem]
  · intro j _ hji
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hOrth i j (fun h => hji h.symm)]
    simp
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem weightedProjection_left_complement {H : Type u}
    [Fintype H] [DecidableEq H] {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (c : Fin d → ℂ)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    (∑ k : Fin d, c k • P k) * (1 - ∑ k : Fin d, P k) = 0 := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  calc
    (c i • P i) * (1 - ∑ k : Fin d, P k)
        = c i • (P i * (1 - ∑ k : Fin d, P k)) := by rw [Matrix.smul_mul]
    _ = 0 := by
      rw [Matrix.mul_sub]
      have hsum : P i * (∑ k : Fin d, P k) = P i := by
        rw [Matrix.mul_sum]
        rw [Finset.sum_eq_single i]
        · exact hIdem i
        · intro j _ hji
          exact hOrth i j (fun h => hji h.symm)
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
      rw [hsum]
      simp

private theorem weightedProjection_right_complement {H : Type u}
    [Fintype H] [DecidableEq H] {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (c : Fin d → ℂ)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    (1 - ∑ k : Fin d, P k) * (∑ k : Fin d, c k • P k) = 0 := by
  classical
  rw [Matrix.mul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  calc
    (1 - ∑ k : Fin d, P k) * (c i • P i)
        = c i • ((1 - ∑ k : Fin d, P k) * P i) := by rw [Matrix.mul_smul]
    _ = 0 := by
      rw [Matrix.sub_mul]
      have hsum : (∑ k : Fin d, P k) * P i = P i := by
        rw [Finset.sum_mul]
        rw [Finset.sum_eq_single i]
        · exact hIdem i
        · intro j _ hji
          exact hOrth j i hji
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
      rw [hsum]
      simp

private theorem projection_complement_idempotent {H : Type u}
    [Fintype H] [DecidableEq H] {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) :
    (1 - ∑ k : Fin d, P k) * (1 - ∑ k : Fin d, P k) =
      1 - ∑ k : Fin d, P k := by
  have hsum : (∑ k : Fin d, P k) * (∑ k : Fin d, P k) = ∑ k : Fin d, P k := by
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_mul]
    rw [Finset.sum_eq_single i]
    · exact hIdem i
    · intro j _ hji
      exact hOrth j i hji
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  calc
    (1 - ∑ k : Fin d, P k) * (1 - ∑ k : Fin d, P k)
        = 1 - ∑ k : Fin d, P k - ∑ k : Fin d, P k +
            (∑ k : Fin d, P k) * (∑ k : Fin d, P k) := by noncomm_ring
    _ = 1 - ∑ k : Fin d, P k := by rw [hsum]; noncomm_ring

/-- Expansion of a CGS phase operator power on an orthogonal projection family. -/
theorem phaseOperator_pow_eq
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) (n : ℕ) :
    phaseOperator P ^ n =
      (∑ m : Fin d, (fourierRoot d) ^ ((m : ℕ) * n) • P m) +
        (1 - ∑ m : Fin d, P m) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih]
      unfold phaseOperator
      have hmul := weightedProjection_mul P
        (fun m : Fin d => (fourierRoot d) ^ ((m : ℕ) * n))
        (fun m : Fin d => (fourierRoot d) ^ (m : ℕ)) hIdem hOrth
      have hlc := weightedProjection_left_complement P
        (fun m : Fin d => (fourierRoot d) ^ ((m : ℕ) * n)) hIdem hOrth
      have hrc := weightedProjection_right_complement P
        (fun m : Fin d => (fourierRoot d) ^ (m : ℕ)) hIdem hOrth
      have hc := projection_complement_idempotent P hIdem hOrth
      calc
        ((∑ m : Fin d, fourierRoot d ^ (↑m * n) • P m) + (1 - ∑ m : Fin d, P m)) *
            ((∑ k : Fin d, fourierRoot d ^ ↑k • P k) + (1 - ∑ k : Fin d, P k))
            = (∑ m : Fin d, fourierRoot d ^ (↑m * n) • P m) *
                (∑ k : Fin d, fourierRoot d ^ ↑k • P k) +
              (∑ m : Fin d, fourierRoot d ^ (↑m * n) • P m) * (1 - ∑ k : Fin d, P k) +
              ((1 - ∑ m : Fin d, P m) * (∑ k : Fin d, fourierRoot d ^ ↑k • P k) +
                (1 - ∑ m : Fin d, P m) * (1 - ∑ k : Fin d, P k)) := by
                noncomm_ring
        _ = ∑ m : Fin d, fourierRoot d ^ (↑m * (n + 1)) • P m +
              (1 - ∑ m : Fin d, P m) := by
          rw [hmul, hlc, hrc, hc]
          simp only [add_zero, zero_add]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro m _
          congr 1
          rw [Nat.mul_succ, pow_add]

theorem fourierMatrix_zero_mul_root_pow
    {d : ℕ} [NeZero d] (l m : Fin d) :
    fourierMatrix d l ⟨0, NeZero.pos d⟩ * (fourierRoot d) ^ ((m : ℕ) * (l : ℕ)) =
      fourierMatrix d l m := by
  simp [fourierMatrix, fourierRoot, ← AddChar.map_nsmul_eq_pow]
  left
  congr 1
  rw [finEquiv_eq_natCast d l, finEquiv_eq_natCast d m]
  ring

theorem inverseFourier_coeff_projection
    {d : ℕ} [NeZero d] (k m : Fin d) :
    (∑ x : Fin d,
      inverseFourierMatrix d k x *
        ((fourierRoot d) ^ ((m : ℕ) * (x : ℕ)) *
          fourierMatrix d x ⟨0, NeZero.pos d⟩)) =
      (1 : CMatrix (Fin d)) k m := by
  calc
    (∑ x : Fin d,
      inverseFourierMatrix d k x *
        ((fourierRoot d) ^ ((m : ℕ) * (x : ℕ)) *
          fourierMatrix d x ⟨0, NeZero.pos d⟩)) =
      ∑ x : Fin d, inverseFourierMatrix d k x * fourierMatrix d x m := by
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [mul_comm ((fourierRoot d) ^ ((m : ℕ) * (x : ℕ)))
          (fourierMatrix d x ⟨0, NeZero.pos d⟩)]
        rw [fourierMatrix_zero_mul_root_pow]
    _ = (inverseFourierMatrix d * fourierMatrix d) k m := by
        simp [Matrix.mul_apply]
    _ = (1 : CMatrix (Fin d)) k m := by
        rw [inverseFourierMatrix_mul_fourierMatrix]

theorem inverseFourier_coeff_base
    {d : ℕ} [NeZero d] (k : Fin d) :
    (∑ x : Fin d, inverseFourierMatrix d k x * fourierMatrix d x ⟨0, NeZero.pos d⟩) =
      (1 : CMatrix (Fin d)) k ⟨0, NeZero.pos d⟩ := by
  calc
    (∑ x : Fin d, inverseFourierMatrix d k x * fourierMatrix d x ⟨0, NeZero.pos d⟩) =
      (inverseFourierMatrix d * fourierMatrix d) k ⟨0, NeZero.pos d⟩ := by
        simp [Matrix.mul_apply]
    _ = (1 : CMatrix (Fin d)) k ⟨0, NeZero.pos d⟩ := by
        rw [inverseFourierMatrix_mul_fourierMatrix]

/-- Applying the controlled phase to the Fourier zero-column vector, coordinatewise. -/
theorem controlledPhase_fourierZero_mulVec_apply
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0)
    (φ : H → ℂ) (h : H) (x : Fin d) :
    ((controlledPhase P *
      (ancillaFourierMatrix (H := H) d *
        ancillaZeroMatrix (H := H) (⟨0, NeZero.pos d⟩ : Fin d))).mulVec φ) (h, x) =
      (∑ m : Fin d,
          (fourierRoot d ^ ((m : ℕ) * (x : ℕ)) *
            fourierMatrix d x (⟨0, NeZero.pos d⟩ : Fin d)) *
            (P m).mulVec φ h) +
        fourierMatrix d x (⟨0, NeZero.pos d⟩ : Fin d) *
          ((1 - ∑ m : Fin d, P m).mulVec φ h) := by
  rw [← Matrix.mulVec_mulVec]
  rw [controlledPhase_mulVec_apply]
  rw [phaseOperator_pow_eq P hIdem hOrth]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec,
    Matrix.smul_mulVec, Pi.add_apply, Pi.sub_apply]
  simp_rw [ancillaFourierMatrix_ancillaZeroMatrix_mulVec_apply]
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, sub_eq_add_neg,
    add_assoc, add_comm]
  rw [mul_add, mul_neg, Finset.mul_sum]
  rw [show
      (∑ x_1 : Fin d, fourierMatrix d x 0 * ∑ y : H, P x_1 h y * φ y) =
        ∑ x_1 : Fin d, ∑ y : H, fourierMatrix d x 0 * P x_1 h y * φ y by
    refine Finset.sum_congr rfl ?_
    intro x_1 _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro y _
    ring]
  simp [mul_left_comm, mul_comm]
  abel

/-- The CGS Fourier gadget selects the explicit projection branch. -/
theorem fourierGadgetBranch_mulVec_apply
    {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H)
    (hIdem : ∀ k, P k * P k = P k)
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0)
    (φ : H → ℂ) (h : H) (k : Fin d) :
    ((ancillaInverseFourierMatrix (H := H) d *
      (controlledPhase P *
        (ancillaFourierMatrix (H := H) d *
          ancillaZeroMatrix (H := H) (⟨0, NeZero.pos d⟩ : Fin d)))).mulVec φ) (h, k)
      =
    (fourierProjectionBranch P k).mulVec φ h := by
  rw [← Matrix.mulVec_mulVec]
  rw [ancillaInverseFourierMatrix_mulVec_apply]
  simp_rw [controlledPhase_fourierZero_mulVec_apply P hIdem hOrth φ]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [show
      (∑ y : Fin d, ∑ x : Fin d,
          inverseFourierMatrix d k x *
            (fourierRoot d ^ (↑y * ↑x) *
              fourierMatrix d x (⟨0, NeZero.pos d⟩ : Fin d) * (P y *ᵥ φ) h)) =
        ∑ y : Fin d,
          (∑ x : Fin d,
            inverseFourierMatrix d k x *
              (fourierRoot d ^ (↑y * ↑x) *
                fourierMatrix d x (⟨0, NeZero.pos d⟩ : Fin d))) *
            (P y *ᵥ φ) h by
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro x _
    ring]
  rw [show
      (∑ x : Fin d,
          inverseFourierMatrix d k x *
            (fourierMatrix d x (⟨0, NeZero.pos d⟩ : Fin d) *
              ((1 - ∑ m : Fin d, P m) *ᵥ φ) h)) =
        (∑ x : Fin d,
          inverseFourierMatrix d k x *
            fourierMatrix d x (⟨0, NeZero.pos d⟩ : Fin d)) *
          ((1 - ∑ m : Fin d, P m) *ᵥ φ) h by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro x _
    ring]
  simp_rw [inverseFourier_coeff_projection (d := d)]
  rw [inverseFourier_coeff_base]
  by_cases hk : k = (0 : Fin d)
  · simp [fourierProjectionBranch, hk, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.sum_mulVec, Matrix.one_apply]
  · simp [fourierProjectionBranch, hk, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.sum_mulVec, Matrix.one_apply]

private theorem kronecker_mulVec_apply
    {a : Type u} {a' : Type v} {b : Type w} {b' : Type*}
    [Fintype a] [DecidableEq a] [Fintype a'] [DecidableEq a']
    [Fintype b] [DecidableEq b] [Fintype b'] [DecidableEq b']
    (A : Matrix a' a ℂ) (B : Matrix b' b ℂ)
    (φ : a × b → ℂ) (a0 : a') (b0 : b') :
    ((A ⊗ₖ B).mulVec φ) (a0, b0) =
      A.mulVec (fun a => B.mulVec (fun b => φ (a, b)) b0) a0 := by
  simp [Matrix.mulVec, dotProduct]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Finset.mul_sum, mul_assoc]

namespace YNData

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

variable (data : YNData ι HA HB)

/-- Alice's explicit side-branch operator after the CGS Fourier gadget collapses. -/
def aliceBranchOperator (B : SchmidtTarget.BaseReindexToFin data.target)
    (k : Fin (Fintype.card ι)) : CMatrix HA :=
  (data.aliceUnitary (B.toEquiv.symm k) : CMatrix HA) *
    data.aliceProjection.effects (B.toEquiv.symm k)

/-- Alice's assembled side matrix acts as the explicit branch operator. -/
theorem aliceSideMatrix_mulVec_apply
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (φ : HA → ℂ) (ha : HA) (k : Fin (Fintype.card ι)) :
    (data.aliceSideMatrix B).mulVec φ (ha, k) =
      (data.aliceBranchOperator B k).mulVec φ ha := by
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  have hzero :
      data.target.baseIndex =
        (⟨0, NeZero.pos (Fintype.card ι)⟩ : Fin (Fintype.card ι)) := by
    ext
    simp [SchmidtTarget.baseIndex]
  unfold aliceSideMatrix aliceBranchOperator aliceControlledUnitary aliceControlledPhase
  rw [hzero]
  rw [← Matrix.mulVec_mulVec]
  rw [controlledUnitary_mulVec_apply]
  have hbranch :
      fourierProjectionBranch
        (fun l : Fin (Fintype.card ι) => data.aliceProjection.effects (B.toEquiv.symm l)) k =
        data.aliceProjection.effects (B.toEquiv.symm k) := by
    have hsum :
        (∑ l : Fin (Fintype.card ι), data.aliceProjection.effects (B.toEquiv.symm l)) =
          (1 : CMatrix HA) := by
      rw [← data.aliceProjection.sum_effects]
      exact (Fintype.sum_equiv B.toEquiv
        (fun i : ι => data.aliceProjection.effects i)
        (fun l : Fin (Fintype.card ι) => data.aliceProjection.effects (B.toEquiv.symm l))
        (by intro i; simp)).symm
    by_cases hk : k = (0 : Fin (Fintype.card ι))
    · simp [fourierProjectionBranch, hk, hsum]
    · simp [fourierProjectionBranch, hk]
  have hIdem :
      ∀ l : Fin (Fintype.card ι),
        data.aliceProjection.effects (B.toEquiv.symm l) *
            data.aliceProjection.effects (B.toEquiv.symm l) =
          data.aliceProjection.effects (B.toEquiv.symm l) := by
    intro l
    exact data.aliceProjection.idempotent (B.toEquiv.symm l)
  have hOrth :
      ∀ i j : Fin (Fintype.card ι), i ≠ j →
        data.aliceProjection.effects (B.toEquiv.symm i) *
            data.aliceProjection.effects (B.toEquiv.symm j) =
          0 := by
    intro i j hij
    apply data.aliceProjection.orthogonal
    intro h
    apply hij
    exact B.toEquiv.symm.injective h
  simp_rw [fourierGadgetBranch_mulVec_apply
    (fun l : Fin (Fintype.card ι) => data.aliceProjection.effects (B.toEquiv.symm l))
    hIdem hOrth φ]
  rw [hbranch]
  rw [Matrix.mulVec_mulVec]

/-- The output basis type of the assembled CGS local isometry. -/
abbrev CGSOutput (ι : Type u) (HA : Type v) (HB : Type w) [Fintype ι] :=
  (HA × Fin (Fintype.card ι)) × (HB × Fin (Fintype.card ι))

/-- The full output vector after applying the assembled CGS local isometry. -/
def cgsActionVector {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB)) :
    CGSOutput ι HA HB → ℂ :=
  (data.cgsLocalIsometry B W).matrix.mulVec ψ.amp

/--
The `k`th explicit branch of the CGS output vector, selected by the Alice
ancilla register after the assembled local isometry.
-/
def cgsActionBranchVector {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB))
    (k : Fin (Fintype.card ι)) : CGSOutput ι HA HB → ℂ :=
  fun x => if x.1.2 = k then data.cgsActionVector B W ψ x else 0

/-- The rank-one/cross block between two explicit CGS branches. -/
def cgsActionBranchBlock {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB))
    (i j : Fin (Fintype.card ι)) : CMatrix (CGSOutput ι HA HB) :=
  YNData.rankOneCoherence
    (data.cgsActionBranchVector B W ψ i)
    (data.cgsActionBranchVector B W ψ j)

/-- The explicit finite double-sum branch expansion of the CGS output density. -/
def cgsActionBranchSumMatrix {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB)) :
    CMatrix (CGSOutput ι HA HB) :=
  ∑ i : Fin (Fintype.card ι),
    ∑ j : Fin (Fintype.card ι), data.cgsActionBranchBlock B W ψ i j

private theorem cgsActionVector_eq_sum_branches {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB)) :
    data.cgsActionVector B W ψ =
      ∑ k : Fin (Fintype.card ι), data.cgsActionBranchVector B W ψ k := by
  classical
  ext x
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single x.1.2]
  · simp [cgsActionBranchVector]
  · intro k _ hk
    simp [cgsActionBranchVector, hk.symm]
  · intro hx
    exact (hx (Finset.mem_univ x.1.2)).elim

private theorem rankOneCoherence_sum_sum {α : Type*} {β : Type*} {γ : Type*}
    [Fintype β] [Fintype γ]
    (f : β → α → ℂ) (g : γ → α → ℂ) :
    YNData.rankOneCoherence (∑ i, f i) (∑ j, g j) =
      ∑ i, ∑ j, YNData.rankOneCoherence (f i) (g j) := by
  classical
  ext x y
  calc
    YNData.rankOneCoherence (∑ i, f i) (∑ j, g j) x y
        = ∑ j, ∑ i, f i x * star (g j y) := by
            simp [YNData.rankOneCoherence_apply, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ i, ∑ j, f i x * star (g j y) := by
            rw [Finset.sum_comm]
    _ = (∑ i, ∑ j, YNData.rankOneCoherence (f i) (g j)) x y := by
            simp [Matrix.sum_apply, YNData.rankOneCoherence_apply]

private theorem localIsometry_applyMatrix_rankOne
    {a : Type u} {a' : Type v} {b : Type w} {b' : Type*}
    [Fintype a] [DecidableEq a] [Fintype a'] [DecidableEq a']
    [Fintype b] [DecidableEq b] [Fintype b'] [DecidableEq b']
    (V : TwoQubit.LocalIsometry a a' b b') (ψ : a × b → ℂ) :
    V.applyMatrix (rankOneMatrix ψ) = rankOneMatrix (V.matrix.mulVec ψ) := by
  ext x y
  simp [TwoQubit.LocalIsometry.applyMatrix, rankOneMatrix, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.conjTranspose, Matrix.vecMulVec_apply,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/--
The assembled CGS local isometry sends a pure input density to the explicit
finite double-sum over its branch blocks.
-/
theorem cgsLocalIsometry_applyMatrix_eq_actionBranchSum {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB)) :
    (data.cgsLocalIsometry B W).applyMatrix ψ.state.matrix =
      data.cgsActionBranchSumMatrix B W ψ := by
  classical
  rw [PureVector.state_matrix]
  rw [localIsometry_applyMatrix_rankOne]
  unfold cgsActionBranchSumMatrix cgsActionBranchBlock
  rw [← rankOneCoherence_sum_sum
    (fun k : Fin (Fintype.card ι) => data.cgsActionBranchVector B W ψ k)
    (fun k : Fin (Fintype.card ι) => data.cgsActionBranchVector B W ψ k)]
  rw [← data.cgsActionVector_eq_sum_branches B W ψ]
  rfl

/-- The explicit branch-sum density is the rank-one density of the CGS output vector. -/
theorem cgsActionBranchSumMatrix_eq_rankOneActionVector {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB)) :
    data.cgsActionBranchSumMatrix B W ψ =
      rankOneMatrix (data.cgsActionVector B W ψ) := by
  rw [← data.cgsLocalIsometry_applyMatrix_eq_actionBranchSum B W ψ]
  rw [PureVector.state_matrix]
  rw [localIsometry_applyMatrix_rankOne]
  rfl

end YNData

namespace BobLocalOrthogonalization

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
variable {data : YNData ι HA HB} {rho : State (HA × HB)}

variable (W : BobLocalOrthogonalization data rho)

/--
Bob's explicit side-branch operator after the CGS Fourier gadget collapses.

The complement term is present only on the target base branch, because Bob's
source-side projection family is not assumed to be complete.
-/
def bobBranchOperator (B : SchmidtTarget.BaseReindexToFin data.target)
    (k : Fin (Fintype.card ι)) : CMatrix HB :=
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  (data.bobUnitary (B.toEquiv.symm k) : CMatrix HB) *
    fourierProjectionBranch
      (fun l : Fin (Fintype.card ι) => (W.bobLocal (B.toEquiv.symm l)).matrix) k

/-- Bob's assembled side matrix acts as the explicit branch operator. -/
theorem bobSideMatrix_mulVec_apply
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (φ : HB → ℂ) (hb : HB) (k : Fin (Fintype.card ι)) :
    (W.bobSideMatrix B).mulVec φ (hb, k) =
      (W.bobBranchOperator B k).mulVec φ hb := by
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  have hzero :
      data.target.baseIndex =
        (⟨0, NeZero.pos (Fintype.card ι)⟩ : Fin (Fintype.card ι)) := by
    ext
    simp [SchmidtTarget.baseIndex]
  unfold bobSideMatrix bobBranchOperator YNData.bobControlledUnitary bobControlledPhase
  rw [hzero]
  rw [← Matrix.mulVec_mulVec]
  rw [controlledUnitary_mulVec_apply]
  have hIdem :
      ∀ l : Fin (Fintype.card ι),
        (W.bobLocal (B.toEquiv.symm l)).matrix *
            (W.bobLocal (B.toEquiv.symm l)).matrix =
          (W.bobLocal (B.toEquiv.symm l)).matrix := by
    intro l
    exact (W.bobLocal (B.toEquiv.symm l)).idempotent
  have hOrth :
      ∀ i j : Fin (Fintype.card ι), i ≠ j →
        (W.bobLocal (B.toEquiv.symm i)).matrix *
            (W.bobLocal (B.toEquiv.symm j)).matrix =
          0 := by
    intro i j hij
    apply W.orthogonal
    intro h
    apply hij
    exact B.toEquiv.symm.injective h
  simp_rw [fourierGadgetBranch_mulVec_apply
    (fun l : Fin (Fintype.card ι) => (W.bobLocal (B.toEquiv.symm l)).matrix)
    hIdem hOrth φ]
  rw [Matrix.mulVec_mulVec]

@[simp]
theorem bobBranchOperator_base
    (B : SchmidtTarget.BaseReindexToFin data.target) :
    W.bobBranchOperator B data.target.baseIndex =
      (data.bobUnitary data.target.base : CMatrix HB) *
        ((W.bobLocal data.target.base).matrix +
          (1 - ∑ l : Fin (Fintype.card ι), (W.bobLocal (B.toEquiv.symm l)).matrix)) := by
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  have hbase_symm : B.toEquiv.symm data.target.baseIndex = data.target.base := by
    apply B.toEquiv.injective
    simp [B.toEquiv_base]
  have hzero :
      data.target.baseIndex =
        (⟨0, NeZero.pos (Fintype.card ι)⟩ : Fin (Fintype.card ι)) := by
    ext
    simp [SchmidtTarget.baseIndex]
  rw [bobBranchOperator, fourierProjectionBranch]
  rw [hbase_symm]
  rw [if_pos hzero]

@[simp]
theorem bobBranchOperator_ne_base
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (k : Fin (Fintype.card ι)) (hk : k ≠ data.target.baseIndex) :
    W.bobBranchOperator B k =
      (data.bobUnitary (B.toEquiv.symm k) : CMatrix HB) *
        (W.bobLocal (B.toEquiv.symm k)).matrix := by
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  have hzero :
      (⟨0, NeZero.pos (Fintype.card ι)⟩ : Fin (Fintype.card ι)) =
        data.target.baseIndex := by
    ext
    simp [SchmidtTarget.baseIndex]
  have hkzero :
      k ≠ (⟨0, NeZero.pos (Fintype.card ι)⟩ : Fin (Fintype.card ι)) := by
    intro h
    exact hk (h.trans hzero)
  have hkzero' : k ≠ (0 : Fin (Fintype.card ι)) := by
    simpa using hkzero
  simp [bobBranchOperator, fourierProjectionBranch, hkzero']

end BobLocalOrthogonalization

namespace YNData

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

variable (data : YNData ι HA HB)

/-- Coordinate form of the assembled CGS action through the collapsed branch operators. -/
theorem cgsActionVector_apply_branchOperators {rho : State (HA × HB)}
    (B : SchmidtTarget.BaseReindexToFin data.target)
    (W : BobLocalOrthogonalization data rho) (ψ : PureVector (HA × HB))
    (ha : HA) (hb : HB) (ka kb : Fin (Fintype.card ι)) :
    data.cgsActionVector B W ψ ((ha, ka), (hb, kb)) =
      ((data.aliceBranchOperator B ka ⊗ₖ W.bobBranchOperator B kb).mulVec ψ.amp) (ha, hb) := by
  unfold cgsActionVector
  change (((data.aliceSideMatrix B) ⊗ₖ (W.bobSideMatrix B)).mulVec ψ.amp) ((ha, ka), (hb, kb)) =
    ((data.aliceBranchOperator B ka ⊗ₖ W.bobBranchOperator B kb).mulVec ψ.amp) (ha, hb)
  rw [kronecker_mulVec_apply
    (A := data.aliceSideMatrix B) (B := W.bobSideMatrix B)]
  simp_rw [W.bobSideMatrix_mulVec_apply B]
  rw [data.aliceSideMatrix_mulVec_apply B]
  rw [kronecker_mulVec_apply
    (A := data.aliceBranchOperator B ka) (B := W.bobBranchOperator B kb)]

end YNData

namespace YNPhaseAlignedConditions

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
variable {data : YNData ι HA HB} {ψ : PureVector (HA × HB)}

/--
The phase-aligned YN witness consumes the same branch-sum expansion through its
Bob-local orthogonalization witness.
-/
theorem cgsLocalIsometry_applyMatrix_eq_actionBranchSum
    (h : YNPhaseAlignedConditions data ψ)
    (B : SchmidtTarget.BaseReindexToFin data.target) :
    (data.cgsLocalIsometry B h.toBobLocalOrthogonalization).applyMatrix ψ.state.matrix =
      data.cgsActionBranchSumMatrix B h.toBobLocalOrthogonalization ψ :=
  data.cgsLocalIsometry_applyMatrix_eq_actionBranchSum B h.toBobLocalOrthogonalization ψ

end YNPhaseAlignedConditions

end

end YangNavascues
end QIT
