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

theorem pinching_kraus_orthogonal (ρ : MState d) {i j : spectrum ℝ ρ.m} (h : i ≠ j) :
    (pinching_kraus ρ i).toMat * (pinching_kraus ρ j).toMat = 0 := by
  convert (HermitianMat.coe_cfc_mul ρ.M _ _).symm
  convert congr($((HermitianMat.cfc_const ρ.M 0).symm).toMat)
  · simp
  · grind [Pi.mul_apply]

/-- The Kraus operators of the pinching channelare projectors: they square to themselves. -/
theorem pinching_sq_eq_self (ρ : MState d) : ∀ k, (pinching_kraus ρ k)^2 = (pinching_kraus ρ k) := fun k => by
  ext1
  push_cast
  rw [pow_two, pinching_kraus,  ← ρ.M.coe_cfc_mul]
  congr! 3
  simp

/-- The Kraus operators of the pinching channel are orthogonal projectors. -/
theorem pinching_kraus_ortho (ρ : MState d) (i j : spectrum ℝ ρ.m) :
    (pinching_kraus ρ i).toMat * (pinching_kraus ρ j).toMat = if i = j then (pinching_kraus ρ i).toMat else 0 := by
  split_ifs with hij
  · grind [selfAdjoint.val_pow, sq, pinching_sq_eq_self]
  · exact pinching_kraus_orthogonal ρ hij

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
  ⟨_, (MatrixMap.of_kraus_isCompletelyPositive
    (HermitianMat.toMat ∘ pinching_kraus σ)).IsPositive.IsHermitianPreserving ρ.M.H⟩ := by
  rfl

theorem pinching_eq_sum_conj (σ ρ : MState d) : (pinching_map σ ρ).M =
    ∑ k, (pinching_kraus σ k).toMat * ρ.M * (pinching_kraus σ k).toMat := by
  rw [pinchingMap_apply_M]
  simp [MatrixMap.of_kraus, Matrix.mul_assoc]

theorem pinching_commutes_kraus (σ ρ : MState d) (i : spectrum ℝ σ.m) :
    Commute (pinching_map σ ρ).m (pinching_kraus σ i).toMat := by
  have h_expand := pinching_eq_sum_conj σ ρ
  simp only [MState.toMat_M] at h_expand
  simp only [Commute, h_expand];
  simp only [SemiconjBy, Finset.sum_mul]
  simp only [mul_assoc, Finset.mul_sum]
  congr! 1 with x
  by_cases h : x = i <;> simp [ h, ← mul_assoc, pinching_kraus_ortho ];
  grind

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
  have h_ker : σ.M.ker = ⊥ :=
    hpos.toLin_ker_eq_bot
  rw [h_ker]
  exact bot_le

theorem pinching_idempotent (ρ σ : MState d) :
    (pinching_map σ) (pinching_map σ ρ) = (pinching_map σ ρ) := by
  rw [MState.ext_iff]
  have h_idempotent : ∀ (ρ : MState d), (∑ k, (pinching_kraus σ k).toMat * (∑ l, (pinching_kraus σ l).toMat * ρ.M * (pinching_kraus σ l).toMat) * (pinching_kraus σ k).toMat) = (∑ k, (pinching_kraus σ k).toMat * ρ.M * (pinching_kraus σ k).toMat) := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, ← mul_assoc, pinching_kraus_ortho]
    simp [mul_assoc, pinching_kraus_ortho]
  convert h_idempotent ρ using 1
  grind [pinching_eq_sum_conj]

theorem Commute.cfc_left_commute {d : Type*} [Fintype d] [DecidableEq d]
  {A B : HermitianMat d ℂ} (f : ℝ → ℝ) (hAB : Commute A.toMat B.toMat) :
    Commute (A.cfc f).toMat B.toMat := by
  grind [HermitianMat.cfc]

theorem Commute.cfc_right_commute {d : Type*} [Fintype d] [DecidableEq d]
  {A B : HermitianMat d ℂ} (f : ℝ → ℝ) (hAB : Commute A.toMat B.toMat) :
    Commute A.toMat (B.cfc f).toMat :=
  (hAB.symm.cfc_left_commute f).symm

theorem inner_cfc_pinching (ρ σ : MState d) (f : ℝ → ℝ) :
    ρ.M.inner ((pinching_map σ ρ).M.cfc f) = (pinching_map σ ρ).M.inner ((pinching_map σ ρ).M.cfc f) := by
  nth_rw 2 [pinchingMap_apply_M]
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace]
  congr 1
  simp only [HermitianMat.val_eq_coe, MState.toMat_M, HermitianMat.mk_toMat]
  conv_rhs =>
    rw [MatrixMap.of_kraus, LinearMap.sum_apply, Finset.sum_mul]
    rw [Matrix.trace_sum]
    simp only [Function.comp_apply, HermitianMat.conjTranspose_toMat, LinearMap.coe_mk,
      AddHom.coe_mk]
    enter [2, x]
    rw [mul_assoc, ← Matrix.trace_mul_cycle, mul_assoc]
  conv_rhs =>
    rw [← Matrix.trace_sum, ← Finset.mul_sum]
    enter [1, 2, 2, x]
    rw [(pinching_commutes_kraus σ ρ x).symm.cfc_right_commute]
    rw [mul_assoc, ← sq]
    change _ * (pinching_kraus σ x ^ 2).toMat
    rw [pinching_sq_eq_self σ x]
  congr 2
  rw [← Finset.mul_sum]
  convert (mul_one _).symm
  convert congr($(pinching_sum σ).toMat)
  simp

theorem inner_cfc_pinching_right (ρ σ : MState d) (f : ℝ → ℝ) :
    (pinching_map σ ρ).M.inner (σ.M.cfc f) = ρ.M.inner (σ.M.cfc f) := by
  -- By definition of pinching_map, we have pinching_map σ ρ = ∑ k, (pinching_kraus σ k).toMat * ρ.toMat * (pinching_kraus σ k).toMat.
  have h_pinching_def : (pinching_map σ ρ).M = ∑ k, (pinching_kraus σ k).toMat * ρ.M.toMat * (pinching_kraus σ k).toMat := by
    exact pinching_eq_sum_conj σ ρ
  -- By definition of pinching_map, we know that (pinching_kraus σ k).toMat * (σ.M.cfc f).toMat = (σ.M.cfc f).toMat * (pinching_kraus σ k).toMat.
  have h_comm_cfc : ∀ k, (pinching_kraus σ k).toMat * (σ.M.cfc f).toMat = (σ.M.cfc f).toMat * (pinching_kraus σ k).toMat := by
    intro k
    apply Commute.cfc_left_commute;
    exact Commute.cfc_right_commute f rfl;
  simp_all [ HermitianMat.inner, Matrix.mul_assoc ];
  simp [Finset.sum_mul, Matrix.mul_assoc]
  simp only [h_comm_cfc, ← Matrix.mul_assoc];
  -- By definition of pinching_map, we know that ∑ k, (pinching_kraus σ k).toMat * (pinching_kraus σ k).toMat = 1.
  have h_sum_kraus : ∑ k : spectrum ℝ σ.m, (pinching_kraus σ k).toMat * (pinching_kraus σ k).toMat = 1 := by
    convert pinching_sum σ using 1;
    simp [HermitianMat.ext_iff ];
    -- Since each pinching_kraus is a projection, multiplying it by itself gives the same projection. Therefore, the sum of the squares is the same as the sum of the pinching_kraus themselves.
    have h_proj : ∀ k : spectrum ℝ σ.m, (pinching_kraus σ k).toMat * (pinching_kraus σ k).toMat = (pinching_kraus σ k).toMat := by
      exact fun k => by simpa [ sq ] using congr_arg ( fun x : HermitianMat d ℂ => x.toMat ) ( pinching_sq_eq_self σ k ) ;
    rw [ Finset.sum_congr rfl fun _ _ => h_proj _ ];
  convert congr_arg ( fun x : Matrix d d ℂ => x.trace.re ) ( congr_arg ( fun x : Matrix d d ℂ => x * ( ρ.m * cfc f σ.m ) ) h_sum_kraus ) using 1;
  · simp [Matrix.sum_mul]
    refine' Finset.sum_congr rfl fun x _ => _;
    rw [ ← Matrix.trace_mul_comm ] ; simp [ Matrix.mul_assoc ] ;
  · simp [ Matrix.trace ]

noncomputable section AristotleLemmas

open ComplexOrder
open scoped Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem HermitianMat.inner_mulVec_nonneg {A : HermitianMat d ℂ} (hA : 0 ≤ A) (v : d → ℂ) :
    0 ≤ star v ⬝ᵥ A.toMat.mulVec v := by
      convert hA using 1;
      constructor <;> intro h <;> rw [HermitianMat.le_iff_mulVec_le_mulVec] at * <;> aesop

open ComplexOrder
open scoped Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem HermitianMat.mem_ker_of_inner_mulVec_zero {A : HermitianMat d ℂ} (hA : 0 ≤ A) (v : d → ℂ)
    (h : star v ⬝ᵥ A.toMat.mulVec v = 0) : v ∈ A.ker := by
      -- Since $A$ is positive semidefinite, there exists a matrix $B$ such that $A = B^* B$.
      obtain ⟨B, hB⟩ : ∃ B : Matrix d d ℂ, A.toMat = B.conjTranspose * B := by
        have h_pos_semidef : Matrix.IsHermitian A.toMat ∧ ∀ v : d → ℂ, 0 ≤ star v ⬝ᵥ A.toMat.mulVec v := by
          exact ⟨ A.H, fun v => by simpa [ Matrix.mulVec, dotProduct ] using hA.2 v ⟩;
        exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp h_pos_semidef;
      -- Since $v^* A v = 0$, we have $v^* B^* B v = 0$, which implies $B v = 0$.
      have hBv : B.mulVec v = 0 := by
        have hBv : star (B.mulVec v) ⬝ᵥ (B.mulVec v) = 0 := by
          simp_all [ ← Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec ];
          simp_all [ Matrix.vecMul, dotProduct, mul_assoc, mul_comm, mul_left_comm ];
          simp_all [ Matrix.mul_apply, Matrix.mulVec, dotProduct ];
          convert h using 3 ; simp [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
          exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
        simp_all [ dotProduct, Complex.ext_iff ];
        exact funext fun x => by norm_num [ Complex.ext_iff ] ; constructor <;> nlinarith only [ hBv.1 ▸ Finset.single_le_sum ( fun x _ => add_nonneg ( mul_self_nonneg ( ( B *ᵥ v ) x |> Complex.re ) ) ( mul_self_nonneg ( ( B *ᵥ v ) x |> Complex.im ) ) ) ( Finset.mem_univ x ) ] ;
      simp_all [ ← Matrix.mulVec_mulVec, Submodule.mem_bot ];
      replace hB := congr_arg ( fun m => m.mulVec v ) hB; simp_all [ ← Matrix.mulVec_mulVec ] ;
      exact hB

open ComplexOrder
open scoped Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem HermitianMat.ker_add {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A + B).ker = A.ker ⊓ B.ker := by
  -- If $(A + B)v = 0$, then $Av + Bv = 0$. Since $A$ and $B$ are positive semidefinite, this implies $Av = 0$ and $Bv = 0$.
  have h_subset : ∀ v : d → ℂ, (A + B).toMat.mulVec v = 0 → A.toMat.mulVec v = 0 ∧ B.toMat.mulVec v = 0 := by
    intro v hv
    have h_pos : 0 ≤ star v ⬝ᵥ A.toMat.mulVec v ∧ 0 ≤ star v ⬝ᵥ B.toMat.mulVec v := by
      exact ⟨ HermitianMat.inner_mulVec_nonneg hA v, HermitianMat.inner_mulVec_nonneg hB v ⟩
    have h_eq_zero : star v ⬝ᵥ A.toMat.mulVec v + star v ⬝ᵥ B.toMat.mulVec v = 0 := by
      convert congr_arg ( fun w => star v ⬝ᵥ w ) hv using 1 ;
      simp [ Matrix.add_mulVec ] ; ring_nf!;
      aesop;
    have h_eq_zero : star v ⬝ᵥ A.toMat.mulVec v = 0 ∧ star v ⬝ᵥ B.toMat.mulVec v = 0 := by
      exact ⟨ by simpa using le_antisymm ( le_trans ( le_add_of_nonneg_right h_pos.2 ) h_eq_zero.le ) h_pos.1, by simpa using le_antisymm ( le_trans ( le_add_of_nonneg_left h_pos.1 ) h_eq_zero.le ) h_pos.2 ⟩
    exact ⟨ HermitianMat.mem_ker_of_inner_mulVec_zero hA v h_eq_zero.1, HermitianMat.mem_ker_of_inner_mulVec_zero hB v h_eq_zero.2 ⟩
  generalize_proofs at *;
  refine' le_antisymm _ _;
  · exact fun v hv => ⟨ h_subset v hv |>.1, h_subset v hv |>.2 ⟩;
  · intro v hv
    obtain ⟨hvA, hvB⟩ := hv
    have hv_sum : (A + B).toMat.mulVec v = 0 := by
      convert congr_arg₂ ( · + · ) hvA hvB using 1 ; ext ; simp [ Matrix.add_mulVec ] ; ring!;
      norm_num +zetaDelta at *
    exact hv_sum

open ComplexOrder
open scoped Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem HermitianMat.ker_sum {ι : Type*} [Fintype ι] (f : ι → HermitianMat d ℂ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, f i).ker = ⨅ i, (f i).ker := by
  -- By definition of sum, we know that if $v \in \ker(\sum_{i \in s} f_i)$, then $\sum_{i \in s} (f_i v, v) = 0$.
  have h_sum_zero : ∀ v : d → ℂ, (∑ i, f i).toMat.mulVec v = 0 ↔ ∀ i, (f i).toMat.mulVec v = 0 := by
    intro v
    constructor
    intro hv_zero
    have h_inner_zero : ∑ i, star v ⬝ᵥ (f i).toMat.mulVec v = 0 := by
      have h_inner_zero : star v ⬝ᵥ (∑ i, (f i).toMat).mulVec v = 0 := by
        aesop
      convert h_inner_zero using 1
      simp [Matrix.mulVec, dotProduct];
      simp only [Finset.mul_sum _ _ _, Matrix.sum_apply, Finset.sum_mul];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm )
    have h_inner_zero_i : ∀ i, star v ⬝ᵥ (f i).toMat.mulVec v = 0 := by
      have h_inner_zero_i : ∀ i, 0 ≤ star v ⬝ᵥ (f i).toMat.mulVec v := by
        exact fun i => inner_mulVec_nonneg (hf i) v;
      exact fun i => le_antisymm ( le_trans ( Finset.single_le_sum ( fun i _ => h_inner_zero_i i ) ( Finset.mem_univ i ) ) h_inner_zero.le ) ( h_inner_zero_i i )
    have h_zero_i : ∀ i, (f i).toMat.mulVec v = 0 := by
      intro i
      have h_inner_zero_i : star v ⬝ᵥ (f i).toMat.mulVec v = 0 := h_inner_zero_i i
      have h_zero_i : (f i).toMat.mulVec v = 0 := by
        apply HermitianMat.mem_ker_of_inner_mulVec_zero (hf i) v h_inner_zero_i
      exact h_zero_i
    exact h_zero_i
    intro hv_zero_i
    have h_sum_zero : ∑ i, (f i).toMat.mulVec v = 0 := by
      aesop
    convert h_sum_zero using 1
    simp
    apply Matrix.sum_mulVec
  ext v
  simp
  convert h_sum_zero v using 1

open ComplexOrder
open scoped Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem HermitianMat.ker_conj {A : HermitianMat d ℂ} (hA : 0 ≤ A) (B : Matrix d d ℂ) :
    (A.conj B).ker = Submodule.comap (Matrix.toEuclideanLin B.conjTranspose) A.ker := by
  ext v; simp [HermitianMat.conj];
  constructor <;> intro h;
  · -- By definition of $A$, we know that $⟨w, A w⟩ = 0$ implies $w \in \ker A$.
    have h_inner_zero : ∀ w : EuclideanSpace ℂ d, 0 ≤ A → (star w ⬝ᵥ A.toMat.mulVec w) = 0 → w ∈ A.ker := by
      intro w hw h_zero
      apply HermitianMat.mem_ker_of_inner_mulVec_zero hw w h_zero;
    convert h_inner_zero ( Bᴴ.mulVec v ) hA _;
    convert congr_arg ( fun w => star v ⬝ᵥ w ) h using 1;
    · simp [ Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, dotProduct_comm ];
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, HermitianMat.lin ];
      simp [ Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Matrix.mul_apply ];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
    · simp [ dotProduct ];
  · simp_all [ HermitianMat.ker, Matrix.mul_assoc ];
    convert congr_arg ( Matrix.toEuclideanLin B ) h using 1;
    · simp [ HermitianMat.lin, Matrix.mulVec ];
      simp [ Matrix.toEuclideanLin, Matrix.mulVec ];
    · exact Eq.symm (LinearMap.map_zero (Matrix.toEuclideanLin B))

open ComplexOrder
open scoped Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem pinching_map_eq_sum_conj_hermitian (σ ρ : MState d) :
    (pinching_map σ ρ).M = ∑ k, ρ.M.conj (pinching_kraus σ k).toMat := by
      convert pinching_eq_sum_conj σ ρ using 1;
      simp [ HermitianMat.ext_iff ]

open ComplexOrder
open scoped Matrix

variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]

theorem HermitianMat.conj_nonneg {A : HermitianMat d ℂ} (hA : 0 ≤ A) (B : Matrix d₂ d ℂ) :
    0 ≤ A.conj B := by
  convert Matrix.PosSemidef.mul_mul_conjTranspose_same ( show Matrix.PosSemidef A.toMat from ?_ ) using 1;
  convert iff_of_true ?_ ?_;
  all_goals try assumption;
  · exact conj_le hA B;
  · convert Matrix.PosSemidef.mul_mul_conjTranspose_same ( show Matrix.PosSemidef A.toMat from ?_ ) using 1;
    convert hA using 1;
    exact Iff.symm zero_le_iff;
  · exact zero_le_iff.mp hA

end AristotleLemmas

theorem pinching_map_ker_le (ρ σ : MState d) : (pinching_map σ ρ).M.ker ≤ ρ.M.ker := by
  -- By definition of pinching map, we can write it as a sum of terms ρ.M.conj (pinching_kraus σ k).toMat.
  have h_sum : (pinching_map σ ρ).M = ∑ k, ρ.M.conj (pinching_kraus σ k).toMat := by
    exact pinching_map_eq_sum_conj_hermitian σ ρ
  -- By `HermitianMat.ker_sum`, the kernel of the sum is the intersection of the kernels of the terms.
  have h_ker_sum : (∑ k, ρ.M.conj (pinching_kraus σ k).toMat).ker = ⨅ k, (ρ.M.conj (pinching_kraus σ k).toMat).ker := by
    convert HermitianMat.ker_sum _ _;
    have h_conj_nonneg : 0 ≤ ρ.M := by
      exact ρ.zero_le
    exact fun i ↦ HermitianMat.conj_nonneg h_conj_nonneg (pinching_kraus σ i).toMat;
  -- By `HermitianMat.ker_conj`, the kernel of `ρ.M.conj P_k` (where $P_k$ is the Kraus operator) is `Submodule.comap P_k.conjTranspose ρ.M.ker`.
  have h_ker_conj : ∀ k, (ρ.M.conj (pinching_kraus σ k).toMat).ker = Submodule.comap (Matrix.toEuclideanLin (pinching_kraus σ k).toMat.conjTranspose) ρ.M.ker := by
    intro k;
    apply HermitianMat.ker_conj;
    exact ρ.zero_le
  -- Since $\sum_k P_k = 1$ (by `pinching_sum`), we have $v = \sum_k P_k v$.
  have h_sum_eq_one : ∑ k : (spectrum ℝ σ.m), (pinching_kraus σ k).toMat = 1 := by
    convert pinching_sum σ using 1;
    simp [ ← Matrix.ext_iff, HermitianMat.ext_iff ];
  intro v hv
  have hv_sum : v = ∑ k : (spectrum ℝ σ.m), (pinching_kraus σ k).toMat.mulVec v := by
    convert congr_arg ( fun m => m.mulVec v ) h_sum_eq_one.symm using 1 ;
    simp
    simp [ Matrix.sum_mulVec ];
  rw [h_sum] at hv;
  rw [h_ker_sum] at hv;
  simp at h_ker_conj hv ⊢
  rw [ hv_sum ];
  exact Submodule.sum_mem _ fun k _ => by simpa [ h_ker_conj _ k.2 ] using hv _ k.2;

noncomputable section AristotleLemmas

/-
If v is in the kernel of σ, then for any non-zero eigenvalue k, the projection of v onto the k-eigenspace is 0.
-/
theorem pinching_kraus_ker_of_ne_zero {d : Type*} [Fintype d] [DecidableEq d]
    (σ : MState d) (v : d → ℂ) (hv : σ.m.mulVec v = 0)
    (k : spectrum ℝ σ.m) (hk : k.val ≠ 0) :
    (pinching_kraus σ k).toMat.mulVec v = 0 := by
  -- Applying the equation $(pinching_kraus \sigma k).toMat * \sigma.m = k.val \bullet (pinching_kraus \sigma k).toMat$ to $v$, we get $(pinching_kraus \sigma k).toMat (\sigma.m v) = k.val (pinching_kraus \sigma k).toMat v$.
  have h_eq_zero : ((pinching_kraus σ k).toMat * σ.m |>.mulVec v) = k.val • ((pinching_kraus σ k).toMat.mulVec v) := by
    have h_eq_zero : ((pinching_kraus σ k).toMat * σ.m) = k.val • (pinching_kraus σ k).toMat := by
      convert pinching_kraus_mul_self σ k using 1;
    simp [ h_eq_zero];
    ext i
    simp [ Matrix.mulVec, dotProduct ] ;
    simp only [mul_assoc, Finset.mul_sum _ _ _];
  simp_all [ ← Matrix.mulVec_mulVec ];
  rw [ eq_comm ] at h_eq_zero ; aesop

end AristotleLemmas

set_option maxHeartbeats 2000000 in
theorem ker_le_ker_pinching_map_ker (ρ σ : MState d) (h : σ.M.ker ≤ ρ.M.ker) :
    σ.M.ker ≤ (pinching_map σ ρ).M.ker := by
  intro v hv;
  -- Since $v \in \ker \sigma$, we have $P_k v = 0$ for all $k$ where the eigenvalue of $k$ is non-zero.
  have h_proj_zero : ∀ k : spectrum ℝ σ.m, k.val ≠ 0 → (pinching_kraus σ k).toMat.mulVec v = 0 := by
    exact fun k hk ↦ pinching_kraus_ker_of_ne_zero σ v ( by simpa [ Matrix.mulVec ] using hv ) k hk;
  -- Since $v \in \ker \sigma$, we have $P_k v = v$ for all $k$ where the eigenvalue of $k$ is zero.
  have h_proj_one : ∀ k : spectrum ℝ σ.m, k.val = 0 → (pinching_kraus σ k).toMat.mulVec v = v := by
    intro k hk
    have := pinching_kraus_mul_self σ k
    simp_all only [ne_eq, Subtype.forall, zero_smul]
    -- Since $v$ is in the kernel of $\sigma$, we have $\sum_{i} P_i v = v$ where $P_i$ are the projectors onto the eigenspaces of $\sigma$.
    have h_sum_proj : ∑ i : spectrum ℝ σ.m, (pinching_kraus σ i).toMat.mulVec v = v := by
      have h_sum_proj : ∑ i : spectrum ℝ σ.m, (pinching_kraus σ i).toMat = 1 := by
        convert pinching_sum σ;
        simp [ ← Matrix.ext_iff, HermitianMat.ext_iff ];
      convert congr_arg ( fun m => m.mulVec v ) h_sum_proj using 1;
      · induction' ( Finset.univ : Finset ( spectrum ℝ σ.m ) ) using Finset.induction
        · simp_all only [Finset.sum_empty, Matrix.zero_mulVec];
        · simp_all only [not_false_eq_true, Finset.sum_insert];
          simp [ Matrix.add_mulVec ];
      · norm_num;
    rw [ Finset.sum_eq_single k ] at h_sum_proj <;> aesop;
  -- Since $v \in \ker \sigma$, we have $\mathcal{E}_\sigma(\rho) v = \sum_k P_k \rho P_k v$.
  have h_sum : (pinching_map σ ρ).M.toMat.mulVec v = ∑ k : spectrum ℝ σ.m, (pinching_kraus σ k).toMat.mulVec (ρ.M.toMat.mulVec ((pinching_kraus σ k).toMat.mulVec v)) := by
    convert congr_arg ( fun x : Matrix d d ℂ => x.mulVec v ) ( pinching_eq_sum_conj σ ρ ) using 1;
    simp [ Matrix.mul_assoc, Matrix.sum_mulVec ];
  refine' h_sum.trans _;
  refine' Finset.sum_eq_zero fun k hk => _;
  by_cases hk_zero : k.val = 0
  · simp_all only [ne_eq, Subtype.forall, MState.toMat_M, Matrix.mulVec_mulVec, Finset.mem_univ]
    convert congr_arg ( fun x => ( pinching_kraus σ k |> HermitianMat.toMat |> Matrix.mulVec ) x ) (h hv) using 1;
    · simp [ ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
      congr! 2;
      convert h_proj_one k.val k.2 hk_zero using 1;
      congr! 2;
      exact congr_arg _ ( Subtype.ext hk_zero );
    · simp
  · simp_all

/-- Exercise 2.8 of Hayashi's book "A group theoretic approach to Quantum Information". -/
theorem pinching_pythagoras (ρ σ : MState d) :
    𝐃(ρ‖σ) = 𝐃(ρ‖pinching_map σ ρ) + 𝐃(pinching_map σ ρ‖σ) := by
  by_cases h_ker : σ.M.ker ≤ ρ.M.ker
  · have h_ker₁ : (pinching_map σ ρ).M.ker ≤ ρ.M.ker := pinching_map_ker_le ρ σ
    have h_ker₂ : σ.M.ker ≤ (pinching_map σ ρ).M.ker := ker_le_ker_pinching_map_ker ρ σ h_ker
    rw [← EReal.coe_ennreal_eq_coe_ennreal_iff, EReal.coe_ennreal_add]
    rw [qRelativeEnt_ker h_ker, qRelativeEnt_ker h_ker₁, qRelativeEnt_ker h_ker₂]
    have h_eq₁ := inner_cfc_pinching_right ρ σ Real.log
    have h_eq₂ := inner_cfc_pinching ρ σ Real.log
    rw [← HermitianMat.log] at h_eq₁ h_eq₂
    simp only [HermitianMat.inner_left_sub]
    rw [h_eq₂, h_eq₁]
    simp only [EReal.coe_sub]
    rw [← add_sub_assoc, EReal.sub_add_cancel]
  · trans ⊤
    · exact dif_neg h_ker
    · convert (add_top _).symm
      apply dif_neg ?_
      contrapose! h_ker
      exact h_ker.trans (pinching_map_ker_le ρ σ)
