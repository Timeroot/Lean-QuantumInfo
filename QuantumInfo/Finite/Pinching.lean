/-
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Leonardo A Lessa, Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap
import QuantumInfo.Finite.MState
import QuantumInfo.Finite.Entropy
import QuantumInfo.ForMathlib.HermitianMat.CFC

/-! # Pinching channels
A pinching channel decoheres in the eigenspaces of a given state.
More precisely, given a state ρ, the pinching channel with respect to ρ is defined as
  E(σ) = ∑ Pᵢ σ Pᵢ
where the P_i are the projectors onto the i-th eigenspaces of ρ = ∑ᵢ pᵢ Pᵢ, with i ≠ j → pᵢ ≠ pⱼ.

TODO: Generalize to pinching with respect to arbitrary P(O)VM.
-/

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

def pinching_kraus (ρ : MState d) : spectrum ℝ ρ.m → HermitianMat d ℂ :=
  fun x ↦ ρ.M.cfc (fun y ↦ if y = x then 1 else 0)

theorem pinching_kraus_commutes (ρ : MState d) (i : spectrum ℝ ρ.m) :
    Commute (pinching_kraus ρ i).toMat ρ.m := by
  rw [MState.m, ← ρ.M.cfc_id, commute_iff_eq, pinching_kraus]
  rw [← ρ.M.coe_cfc_mul, ← ρ.M.coe_cfc_mul]
  congr 2; ext; simp

theorem pinching_kraus_mul_self (ρ : MState d) (i : spectrum ℝ ρ.m) :
    (pinching_kraus ρ i).toMat * ρ.m = i.val • pinching_kraus ρ i := by
  dsimp [MState.m]
  nth_rw 1 [← ρ.M.cfc_id]
  rw [pinching_kraus]
  rw [← ρ.M.coe_cfc_mul]
  conv_rhs => change HermitianMat.toMat (i.val • _)
  rw [← ρ.M.cfc_const_mul]
  congr! 3
  simp +contextual

instance finite_spectrum_inst (ρ : MState d) : Fintype (spectrum ℝ ρ.m) :=
  Fintype.ofFinite (spectrum ℝ ρ.m)

theorem pinching_sq_eq_self (ρ : MState d) : ∀ k, (pinching_kraus ρ k)^2 = (pinching_kraus ρ k) := fun k => by
  ext1
  push_cast
  rw [pow_two, pinching_kraus, HermitianMat.cfc, ←cfc_mul
  (hf := by simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology])
  (hg := by simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology])]
  simp only [← pow_two, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow]

theorem pinching_sum (ρ : MState d) : ∑ k, pinching_kraus ρ k = 1 := by
  ext i j
  simp only [pinching_kraus, HermitianMat.cfc, HermitianMat.val_eq_coe, MState.toMat_M, AddSubgroup.val_finset_sum,
    selfAdjoint.val_one]
  have heq : Set.EqOn (fun x => ∑ i : spectrum ℝ ρ.m, if x = ↑i then (1 : ℝ) else 0) 1 (spectrum ℝ ρ.m) := by
    unfold Set.EqOn; intro x hx
    dsimp
    rw [Finset.sum_set_coe (f := fun i => if x = i then 1 else 0) (s := spectrum ℝ ρ.m), Finset.sum_ite_eq_of_mem]
    rw [Set.mem_toFinset]
    exact hx
  rw [←cfc_sum (hf := by simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology, implies_true]),
  Finset.sum_fn, cfc_congr heq, cfc_one (R := ℝ) (ha := _)]
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, ρ.Hermitian]

def pinching_map (ρ : MState d) : CPTPMap d d ℂ :=
  CPTPMap.of_kraus_CPTPMap (HermitianMat.toMat ∘ pinching_kraus ρ) (by
  conv =>
    enter [1, 2, k]
    rw [Function.comp_apply, (pinching_kraus ρ k).H, ←pow_two]
    norm_cast
    rw [pinching_sq_eq_self ρ k]
  norm_cast
  rw [pinching_sum]
  rfl
  )

theorem pinchingMap_apply_M (σ ρ : MState d) : (pinching_map σ ρ).M =
  ⟨_, (MatrixMap.IsCompletelyPositive.of_kraus_isCompletelyPositive
    (HermitianMat.toMat ∘ pinching_kraus σ)).IsPositive.IsHermitianPreserving ρ.M.H⟩ := by
  rfl

theorem pinching_commutes (ρ σ : MState d) :
    Commute (pinching_map σ ρ).m σ.m := by
  dsimp [MState.m, Commute, SemiconjBy]
  rw [pinchingMap_apply_M]
  simp only [MatrixMap.of_kraus, Function.comp_apply]
  simp only [HermitianMat.conjTranspose_toMat, MState.toMat_M, LinearMap.coeFn_sum,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, HermitianMat.mk_toMat]
  simp only [Finset.sum_mul, Finset.mul_sum]
  congr! 1 with i
  have hl : (pinching_kraus σ i) * σ.m = i.val • (pinching_kraus σ i) :=
    pinching_kraus_mul_self σ i
  have hr : σ.m * (pinching_kraus σ i) = i.val • (pinching_kraus σ i) := by
    rwa [pinching_kraus_commutes] at hl
  simp only [mul_assoc, hl]
  simp only [← mul_assoc, hr]
  simp

@[simp]
theorem pinching_self (ρ : MState d) : pinching_map ρ ρ = ρ := by
  ext1
  rw [pinchingMap_apply_M]
  simp only [MatrixMap.of_kraus, Function.comp_apply]
  simp only [HermitianMat.conjTranspose_toMat, MState.toMat_M, LinearMap.coeFn_sum,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]
  simp_rw [(pinching_kraus_commutes ρ _).eq, mul_assoc, ← sq]
  conv_lhs =>
    enter [1, 2, x, 2]
    change (pinching_kraus ρ x ^ 2).toMat
    rw [pinching_sq_eq_self]
  simp_rw [← Finset.mul_sum, ← AddSubgroup.val_finset_sum]
  simp only [pinching_sum, selfAdjoint.val_one, mul_one]
  rfl

/-- Exercise 2.8 of Hayashi's book "A group theoretic approach to Quantum Information".
-- Used in (S59) -/
theorem pinching_pythagoras (ρ σ : MState d) :  𝐃(ρ‖σ) = 𝐃(ρ‖pinching_map σ ρ) + 𝐃(pinching_map σ ρ‖σ) :=
  sorry

omit [DecidableEq d] in
open ComplexOrder in
theorem HermitianMat.le_iff_mulVec_le_mulVec {𝕜 : Type*} [RCLike 𝕜] (A B : HermitianMat d 𝕜) :
    A ≤ B ↔ ∀ v : d → 𝕜, star v ⬝ᵥ A.toMat.mulVec v ≤ star v ⬝ᵥ B.toMat.mulVec v := by
  rw [← sub_nonneg, HermitianMat.zero_le_iff]
  conv_rhs => enter [v]; rw [← sub_nonneg]
  have h := (B - A).H
  simp only [AddSubgroupClass.coe_sub] at h
  simp [Matrix.PosSemidef, Matrix.sub_mulVec, h]

/-- Lemma 3.10 of Hayashi's book "Quantum Information Theory - Mathematical Foundations".
Also, Lemma 5 in https://arxiv.org/pdf/quant-ph/0107004.
-- Used in (S60) -/
theorem pinching_bound (ρ σ : MState d) : ρ.M ≤ (↑(Fintype.card (spectrum ℝ σ.m)) : ℝ) • (pinching_map σ ρ).M := by
  rw [pinchingMap_apply_M]
  suffices ρ.M ≤ (Fintype.card (spectrum ℝ σ.m) : ℝ) • ∑ c, ρ.M.conj (pinching_kraus σ c) by
    convert this
    simp [MatrixMap.of_kraus, HermitianMat.conj]
  --Rewrite ρ as its spectral decomposition
  obtain ⟨ψs, hρm⟩ := ρ.spectralDecomposition
  simp only [hρm, map_sum, Finset.smul_sum]
  rw [Finset.sum_comm (α := d)]
  gcongr with i _
  --
  open ComplexOrder in
  rw [HermitianMat.le_iff_mulVec_le_mulVec]
  intro v
  simp [← Finset.smul_sum, smul_comm _ (ρ.spectrum i : ℝ), Matrix.smul_mulVec, dotProduct_smul]
  gcongr
  · --The spectrum of a MState is always positive.
    --Should be a helper lemma, it's only like two lines though.
    --*Could* be a positivity extension.
    dsimp [MState.spectrum, Distribution.mk']
    rw [Complex.zero_le_real]
    exact (HermitianMat.zero_le_iff.mp ρ.zero_le).eigenvalues_nonneg _
  have h1 : (1 : Matrix d d ℂ) = (1 : HermitianMat d ℂ) := by exact selfAdjoint.val_one
  conv_lhs =>
    enter [2, 1]
    rw [← one_mul (MState.m _), h1, ← congr(HermitianMat.toMat $(pinching_sum σ))]
    enter [2]
    rw [← mul_one (MState.m _), h1, ← congr(HermitianMat.toMat $(pinching_sum σ))]
  simp only [AddSubgroup.val_finset_sum, HermitianMat.val_eq_coe]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_mulVec, dotProduct_sum]
  simp only [MState.pure]
  dsimp [MState.m]
  --This out to be Cauchy-Schwarz.
  have hschwarz := inner_mul_inner_self_le (𝕜 := ℂ) (E := EuclideanSpace ℂ (↑(spectrum ℝ σ.m)))
    (x := fun i ↦ 1) (y := fun k ↦ (
      star v ⬝ᵥ ((pinching_kraus σ k).toMat.mulVec (ψs i))
    ))
  rw [← Complex.real_le_real] at hschwarz
  simp only [PiLp.inner_apply] at hschwarz
  simp only [RCLike.inner_apply, map_one, mul_one, one_mul, Complex.ofReal_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, RCLike.natCast_re, map_sum, RCLike.re_to_complex,
    Complex.ofReal_natCast, Complex.ofReal_sum] at hschwarz
  simp only [HermitianMat.mk_toMat] at ⊢
  have h_mul (x y : spectrum ℝ σ.m) :
      star v ⬝ᵥ ((pinching_kraus σ y).toMat *
        (Matrix.vecMulVec ⇑(ψs i) ((ψs i).to_bra) : Matrix d d ℂ)
        * (pinching_kraus σ x).toMat).mulVec v =
      star v ⬝ᵥ (pinching_kraus σ y).toMat.mulVec (ψs i)
        * (starRingEnd ℂ) (star v ⬝ᵥ (pinching_kraus σ x).toMat.mulVec (ψs i)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_comm]
    congr
    rw [starRingEnd_apply, ← Matrix.star_dotProduct, Matrix.star_mulVec]
    rw [← Matrix.dotProduct_mulVec, HermitianMat.conjTranspose_toMat]
    --Uses the defeq of `star (_ : Bra)` and `(_ : Ket)`. Would be good to have a lemma
    -- so that we don't 'abuse' this defeq, TODO. (Maybe even make the coercions between
    -- kets and bras irreducible?)
    rfl
  convert hschwarz with x <;> clear hschwarz
  · rw [← map_sum, ← Complex.ofReal_mul, ← norm_mul]
    rw [Complex.mul_conj, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _)]
    simp_rw [← Complex.mul_conj, map_sum, Finset.mul_sum, Finset.sum_mul]
    congr! with x _ y _
    rw [← Matrix.mul_assoc]
    exact h_mul x y
  · have hc (c d : ℂ) : d = starRingEnd ℂ d  → c = d → c = d.re := by
      rintro h rfl; simp [Complex.ext_iff] at h ⊢; linarith
    apply hc <;> clear hc
    · simpa using mul_comm _ _
    · exact h_mul x x

open ComplexOrder in
theorem ker_le_ker_pinching_of_PosDef (ρ σ : MState d) (hpos : σ.m.PosDef) : σ.M.ker ≤ (pinching_map σ ρ).M.ker := by
  sorry
