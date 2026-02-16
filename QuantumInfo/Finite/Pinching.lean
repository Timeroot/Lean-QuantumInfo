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
open scoped Matrix RealInnerProductSpace

variable {d : Type*} [Fintype d] [DecidableEq d]

def pinching_kraus (ρ : MState d) : spectrum ℝ ρ.m → HermitianMat d ℂ :=
  fun x ↦ ρ.M.cfc (fun y ↦ if y = x then 1 else 0)

theorem pinching_kraus_commutes (ρ : MState d) (i : spectrum ℝ ρ.m) :
    Commute (pinching_kraus ρ i).mat ρ.m := by
  rw [MState.m, ← ρ.M.cfc_id, commute_iff_eq, pinching_kraus]
  rw [← ρ.M.mat_cfc_mul, ← ρ.M.mat_cfc_mul]
  congr 2; ext; simp

theorem pinching_kraus_mul_self (ρ : MState d) (i : spectrum ℝ ρ.m) :
    (pinching_kraus ρ i).mat * ρ.m = i.val • pinching_kraus ρ i := by
  dsimp [MState.m]
  nth_rw 1 [← ρ.M.cfc_id]
  rw [pinching_kraus]
  rw [← ρ.M.mat_cfc_mul, ← HermitianMat.mat_smul]
  rw [← ρ.M.cfc_const_mul]
  congr! 3
  simp +contextual

instance finite_spectrum_inst (ρ : MState d) : Fintype (spectrum ℝ ρ.m) :=
  Fintype.ofFinite (spectrum ℝ ρ.m)

theorem pinching_kraus_orthogonal (ρ : MState d) {i j : spectrum ℝ ρ.m} (h : i ≠ j) :
    (pinching_kraus ρ i).mat * (pinching_kraus ρ j).mat = 0 := by
  convert (HermitianMat.mat_cfc_mul ρ.M _ _).symm
  convert congr($((ρ.M.cfc_const 0).symm).mat)
  · simp
  · grind [Pi.mul_apply]

/-- The Kraus operators of the pinching channelare projectors: they square to themselves. -/
@[simp]
theorem pinching_sq_eq_self (ρ : MState d) (k) : (pinching_kraus ρ k) ^ 2  = pinching_kraus ρ k := by
  ext1
  push_cast
  rw [pow_two, pinching_kraus, ← ρ.M.mat_cfc_mul]
  congr! 3
  simp

/-- The Kraus operators of the pinching channel are orthogonal projectors. -/
theorem pinching_kraus_ortho (ρ : MState d) (i j : spectrum ℝ ρ.m) :
    (pinching_kraus ρ i).mat * (pinching_kraus ρ j).mat = if i = j then (pinching_kraus ρ i).mat else 0 := by
  split_ifs with hij
  · grind [sq, HermitianMat.mat_pow, pinching_sq_eq_self]
  · exact pinching_kraus_orthogonal ρ hij

theorem pinching_sum (ρ : MState d) : ∑ k, pinching_kraus ρ k = 1 := by
  ext i j
  simp only [pinching_kraus, HermitianMat.cfc]
  have heq : Set.EqOn (fun x => ∑ i : spectrum ℝ ρ.m, if x = ↑i then (1 : ℝ) else 0) 1 (spectrum ℝ ρ.m) := by
    intro x hx
    dsimp
    rw [Finset.sum_set_coe (f := fun i => if x = i then 1 else 0), Finset.sum_ite_eq_of_mem]
    rwa [Set.mem_toFinset]
  simp [-HermitianMat.mat_apply]
  rw [← cfc_sum, Finset.sum_fn, cfc_congr heq, cfc_one (R := ℝ) (ha := _)]
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, ρ.Hermitian]

def pinching_map (ρ : MState d) : CPTPMap d d ℂ :=
  CPTPMap.of_kraus_CPTPMap (HermitianMat.mat ∘ pinching_kraus ρ) (by
  conv =>
    enter [1, 2, k]
    rw [Function.comp_apply, (pinching_kraus ρ k).H, ←pow_two]
    norm_cast
    rw [pinching_sq_eq_self ρ k]
  norm_cast
  simp [pinching_sum]
  )

theorem pinchingMap_apply_M (σ ρ : MState d) : (pinching_map σ ρ).M =
  ⟨_, (MatrixMap.of_kraus_isCompletelyPositive
    (HermitianMat.mat ∘ pinching_kraus σ)).IsPositive.IsHermitianPreserving ρ.M.H⟩ := by
  rfl

theorem pinching_eq_sum_conj (σ ρ : MState d) : (pinching_map σ ρ).M =
    ∑ k, (pinching_kraus σ k).mat * ρ.M * (pinching_kraus σ k).mat := by
  rw [pinchingMap_apply_M]
  simp [MatrixMap.of_kraus, Matrix.mul_assoc]

theorem pinching_commutes_kraus (σ ρ : MState d) (i : spectrum ℝ σ.m) :
    Commute (pinching_map σ ρ).m (pinching_kraus σ i).mat := by
  have h_expand := pinching_eq_sum_conj σ ρ
  simp only [MState.mat_M] at h_expand
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
  simp only [HermitianMat.conjTranspose_mat, MState.mat_M, LinearMap.coeFn_sum,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]
  simp only [HermitianMat.mat_mk, Finset.sum_mul, Finset.mul_sum]
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
  simp only [HermitianMat.conjTranspose_mat, MState.mat_M, LinearMap.coeFn_sum,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]
  simp_rw [(pinching_kraus_commutes ρ _).eq, mul_assoc, ← sq]
  conv_lhs =>
    enter [1, 2, x, 2]
    change (pinching_kraus ρ x ^ 2).mat
    rw [pinching_sq_eq_self]
  simp_rw [← Finset.mul_sum, ← HermitianMat.mat_finset_sum]
  simp only [pinching_sum, HermitianMat.mat_one, mul_one]
  rfl

/-- Lemma 3.10 of Hayashi's book "Quantum Information Theory - Mathematical Foundations".
Also, Lemma 5 in https://arxiv.org/pdf/quant-ph/0107004.
-- Used in (S60) -/
theorem pinching_bound (ρ σ : MState d) : ρ.M ≤ (↑(Fintype.card (spectrum ℝ σ.m)) : ℝ) • (pinching_map σ ρ).M := by
  rw [pinchingMap_apply_M]
  suffices ρ.M ≤ (Fintype.card (spectrum ℝ σ.m) : ℝ) • ∑ c, ρ.M.conj (pinching_kraus σ c) by
    convert this
    ext1
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
    rw [← one_mul (MState.m _), h1, ← congr(HermitianMat.mat $(pinching_sum σ))]
    enter [2]
    rw [← mul_one (MState.m _), h1, ← congr(HermitianMat.mat $(pinching_sum σ))]
  simp only [HermitianMat.mat_finset_sum]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_mulVec, dotProduct_sum]
  simp only [MState.pure]
  dsimp [MState.m]
  --This out to be Cauchy-Schwarz.
  have hschwarz := inner_mul_inner_self_le (𝕜 := ℂ) (E := EuclideanSpace ℂ (↑(spectrum ℝ σ.m)))
    (x := fun i ↦ 1) (y := fun k ↦ (
      star v ⬝ᵥ ((pinching_kraus σ k).mat *ᵥ (ψs i))
    ))
  rw [← Complex.real_le_real] at hschwarz
  simp only [PiLp.inner_apply] at hschwarz
  simp only [RCLike.inner_apply, map_one, mul_one, one_mul, Complex.ofReal_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, RCLike.natCast_re, map_sum, RCLike.re_to_complex,
    Complex.ofReal_natCast, Complex.ofReal_sum] at hschwarz
  simp only [HermitianMat.mat_mk] at ⊢
  have h_mul (x y : spectrum ℝ σ.m) :
      star v ⬝ᵥ ((pinching_kraus σ y).mat *
        (Matrix.vecMulVec ⇑(ψs i) ((ψs i).to_bra) : Matrix d d ℂ)
        * (pinching_kraus σ x).mat) *ᵥ v =
      star v ⬝ᵥ (pinching_kraus σ y).mat *ᵥ (ψs i)
        * (starRingEnd ℂ) (star v ⬝ᵥ (pinching_kraus σ x).mat *ᵥ (ψs i)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_comm]
    congr
    rw [starRingEnd_apply, ← Matrix.star_dotProduct, Matrix.star_mulVec]
    rw [← Matrix.dotProduct_mulVec, HermitianMat.conjTranspose_mat]
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
  have h_idempotent : (∑ k, (pinching_kraus σ k).mat * (∑ l, (pinching_kraus σ l).mat * ρ.M * (pinching_kraus σ l).mat) * (pinching_kraus σ k).mat) = (∑ k, (pinching_kraus σ k).mat * ρ.M * (pinching_kraus σ k).mat) := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, ← mul_assoc, pinching_kraus_ortho]
    simp [mul_assoc, pinching_kraus_ortho]
  ext1
  grind [pinching_eq_sum_conj]

theorem inner_cfc_pinching (ρ σ : MState d) (f : ℝ → ℝ) :
    ⟪ρ.M, (pinching_map σ ρ).M.cfc f⟫ = ⟪(pinching_map σ ρ).M, (pinching_map σ ρ).M.cfc f⟫ := by
  nth_rw 2 [pinchingMap_apply_M]
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace]
  congr 1
  simp only [MState.mat_M, HermitianMat.mat_mk]
  conv_rhs =>
    rw [MatrixMap.of_kraus, LinearMap.sum_apply, Finset.sum_mul]
    rw [Matrix.trace_sum]
    simp only [Function.comp_apply, HermitianMat.conjTranspose_mat, LinearMap.coe_mk,
      AddHom.coe_mk]
    enter [2, x]
    rw [mul_assoc, ← Matrix.trace_mul_cycle, mul_assoc]
  conv_rhs =>
    rw [← Matrix.trace_sum, ← Finset.mul_sum]
    enter [1, 2, 2, x]
    rw [(pinching_commutes_kraus σ ρ x).symm.cfc_right]
    rw [mul_assoc, ← sq]
    change _ * (pinching_kraus σ x ^ 2).mat
    rw [pinching_sq_eq_self σ x]
  congr 2
  rw [← Finset.mul_sum]
  convert (mul_one _).symm
  convert congr($(pinching_sum σ).mat)
  simp

theorem inner_cfc_pinching_right (ρ σ : MState d) (f : ℝ → ℝ) :
    ⟪(pinching_map σ ρ).M, σ.M.cfc f⟫ = ⟪ρ.M, σ.M.cfc f⟫ := by
  --TODO Cleanup
  -- By definition of pinching_map, we have pinching_map σ ρ = ∑ k, (pinching_kraus σ k).toMat * ρ.toMat * (pinching_kraus σ k).toMat.
  have h_pinching_def : (pinching_map σ ρ).M = ∑ k, (pinching_kraus σ k).mat * ρ.M.mat * (pinching_kraus σ k).mat := by
    exact pinching_eq_sum_conj σ ρ
  -- By definition of pinching_map, we know that (pinching_kraus σ k).toMat * (σ.M.cfc f).toMat = (σ.M.cfc f).toMat * (pinching_kraus σ k).toMat.
  have h_comm_cfc : ∀ k, (pinching_kraus σ k).mat * (σ.M.cfc f).mat = (σ.M.cfc f).mat * (pinching_kraus σ k).mat := by
    intro k
    apply Commute.cfc_left
    exact Commute.cfc_right f rfl
  simp_all [ HermitianMat.inner_def, Matrix.mul_assoc ];
  simp [Finset.sum_mul, Matrix.mul_assoc]
  simp only [h_comm_cfc, ← Matrix.mul_assoc];
  -- By definition of pinching_map, we know that ∑ k, (pinching_kraus σ k).toMat * (pinching_kraus σ k).toMat = 1.
  have h_sum_kraus : ∑ k : spectrum ℝ σ.m, (pinching_kraus σ k).mat * (pinching_kraus σ k).mat = 1 := by
    convert pinching_sum σ using 1;
    simp [HermitianMat.ext_iff ];
    -- Since each pinching_kraus is a projection, multiplying it by itself gives the same projection. Therefore, the sum of the squares is the same as the sum of the pinching_kraus themselves.
    have h_proj : ∀ k : spectrum ℝ σ.m, (pinching_kraus σ k).mat * (pinching_kraus σ k).mat = (pinching_kraus σ k).mat := by
      exact fun k => by simpa [ sq, -pinching_sq_eq_self ] using congr_arg ( fun x : HermitianMat d ℂ => x.mat ) ( pinching_sq_eq_self σ k ) ;
    rw [ Finset.sum_congr rfl fun _ _ => h_proj _ ];
  convert congr_arg ( fun x : Matrix d d ℂ => x.trace.re ) ( congr_arg ( fun x : Matrix d d ℂ => x * ( ρ.m * cfc f σ.m ) ) h_sum_kraus ) using 1;
  · simp [Matrix.sum_mul]
    refine' Finset.sum_congr rfl fun x _ => _;
    rw [ ← Matrix.trace_mul_comm ] ; simp [ Matrix.mul_assoc ] ;
  · simp [ Matrix.trace ]

open ComplexOrder in
theorem pinching_map_eq_sum_conj_hermitian (σ ρ : MState d) :
    (pinching_map σ ρ).M = ∑ k, ρ.M.conj (pinching_kraus σ k).mat := by
  ext1
  simp [pinching_eq_sum_conj σ ρ]

theorem pinching_map_ker_le (ρ σ : MState d) : (pinching_map σ ρ).M.ker ≤ ρ.M.ker := by
  --TODO Cleanup
  -- By `HermitianMat.ker_sum`, the kernel of the sum is the intersection of the kernels of the terms.
  have h_ker_sum : (∑ k, ρ.M.conj (pinching_kraus σ k).mat).ker = ⨅ k, (ρ.M.conj (pinching_kraus σ k).mat).ker := by
    apply HermitianMat.ker_sum
    exact fun i ↦ HermitianMat.conj_nonneg (pinching_kraus σ i).mat ρ.zero_le
  -- By `HermitianMat.ker_conj`, the kernel of `ρ.M.conj P_k` (where $P_k$ is the Kraus operator) is `Submodule.comap P_k.conjTranspose ρ.M.ker`.
  have h_ker_conj : ∀ k, (ρ.M.conj (pinching_kraus σ k).mat).ker = Submodule.comap (Matrix.toEuclideanLin (pinching_kraus σ k).mat.conjTranspose) ρ.M.ker := by
    intro k;
    apply HermitianMat.ker_conj;
    exact ρ.zero_le
  -- Since $\sum_k P_k = 1$ (by `pinching_sum`), we have $v = \sum_k P_k v$.
  have h_sum_eq_one : ∑ k : (spectrum ℝ σ.m), (pinching_kraus σ k).mat = 1 := by
    convert pinching_sum σ using 1;
    simp [ ← Matrix.ext_iff, HermitianMat.ext_iff ];
  intro v hv
  have hv_sum : v = ∑ k : (spectrum ℝ σ.m), (pinching_kraus σ k).mat *ᵥ v := by
    convert congr_arg ( fun m => m *ᵥ v ) h_sum_eq_one.symm using 1 ;
    · simp
    · rw [Matrix.sum_mulVec]
  rw [pinching_map_eq_sum_conj_hermitian σ ρ, h_ker_sum] at hv
  simp at h_ker_conj hv ⊢
  rw [hv_sum]
  exact Submodule.sum_mem _ fun k _ => by simpa [h_ker_conj _ k.2] using hv _ k.2

noncomputable section AristotleLemmas

/-
If v is in the kernel of σ, then for any non-zero eigenvalue k, the projection of v onto the k-eigenspace is 0.
-/
theorem pinching_kraus_ker_of_ne_zero {d : Type*} [Fintype d] [DecidableEq d]
    (σ : MState d) (v : d → ℂ) (hv : σ.m.mulVec v = 0)
    (k : spectrum ℝ σ.m) (hk : k.val ≠ 0) :
    (pinching_kraus σ k).mat *ᵥ v = 0 := by
  -- Applying the equation $(pinching_kraus \sigma k).toMat * \sigma.m = k.val \bullet (pinching_kraus \sigma k).toMat$ to $v$, we get $(pinching_kraus \sigma k).toMat (\sigma.m v) = k.val (pinching_kraus \sigma k).toMat v$.
  have h_eq_zero : ((pinching_kraus σ k).mat * σ.m) *ᵥ v = k.val • ((pinching_kraus σ k).mat *ᵥ v) := by
    have h_eq_zero : ((pinching_kraus σ k).mat * σ.m) = k.val • (pinching_kraus σ k).mat := by
      convert pinching_kraus_mul_self σ k using 1;
    simp [ h_eq_zero];
    ext i
    simp [ Matrix.mulVec, dotProduct ] ;
    simp only [mul_assoc, Finset.mul_sum];
  simp_all [ ← Matrix.mulVec_mulVec ];
  rw [eq_comm] at h_eq_zero
  aesop

end AristotleLemmas

set_option maxHeartbeats 2000000 in
theorem ker_le_ker_pinching_map_ker (ρ σ : MState d) (h : σ.M.ker ≤ ρ.M.ker) :
    σ.M.ker ≤ (pinching_map σ ρ).M.ker := by
  --TODO Cleanup
  intro v hv;
  -- Since $v \in \ker \sigma$, we have $P_k v = 0$ for all $k$ where the eigenvalue of $k$ is non-zero.
  have h_proj_zero : ∀ k : spectrum ℝ σ.m, k.val ≠ 0 → (pinching_kraus σ k).mat *ᵥ v = 0 := by
    exact fun k hk ↦ pinching_kraus_ker_of_ne_zero σ v ( by simpa [ Matrix.mulVec ] using hv ) k hk;
  -- Since $v \in \ker \sigma$, we have $P_k v = v$ for all $k$ where the eigenvalue of $k$ is zero.
  have h_proj_one : ∀ k : spectrum ℝ σ.m, k.val = 0 → (pinching_kraus σ k).mat *ᵥ v = v := by
    intro k hk
    have := pinching_kraus_mul_self σ k
    simp_all only [ne_eq, Subtype.forall, zero_smul]
    -- Since $v$ is in the kernel of $\sigma$, we have $\sum_{i} P_i v = v$ where $P_i$ are the projectors onto the eigenspaces of $\sigma$.
    have h_sum_proj : ∑ i : spectrum ℝ σ.m, (pinching_kraus σ i).mat *ᵥ v = v := by
      have h_sum_proj : ∑ i : spectrum ℝ σ.m, (pinching_kraus σ i).mat = 1 := by
        convert pinching_sum σ;
        simp [ ← Matrix.ext_iff, HermitianMat.ext_iff ];
      convert congr_arg ( fun m => m *ᵥ v ) h_sum_proj using 1;
      · induction' ( Finset.univ : Finset ( spectrum ℝ σ.m ) ) using Finset.induction
        · simp_all only [Finset.sum_empty, Matrix.zero_mulVec];
        · simp_all only [not_false_eq_true, Finset.sum_insert];
          simp [ Matrix.add_mulVec ];
      · norm_num;
    rw [ Finset.sum_eq_single k ] at h_sum_proj <;> aesop;
  -- Since $v \in \ker \sigma$, we have $\mathcal{E}_\sigma(\rho) v = \sum_k P_k \rho P_k v$.
  have h_sum : (pinching_map σ ρ).M.mat *ᵥ v = ∑ k : spectrum ℝ σ.m, (pinching_kraus σ k).mat *ᵥ (ρ.M.mat *ᵥ ((pinching_kraus σ k).mat *ᵥ v)) := by
    convert congr_arg ( fun x : Matrix d d ℂ => x.mulVec v ) ( pinching_eq_sum_conj σ ρ ) using 1;
    simp [ Matrix.mul_assoc, Matrix.sum_mulVec ];
  refine' h_sum.trans _;
  refine' Finset.sum_eq_zero fun k hk => _;
  by_cases hk_zero : k.val = 0
  · simp_all only [ne_eq, Subtype.forall, Matrix.mulVec_mulVec, Finset.mem_univ]
    convert congr_arg ( fun x => (pinching_kraus σ k).mat *ᵥ x ) (h hv) using 1;
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
    simp only [inner_sub_right]
    rw [h_eq₂, h_eq₁]
    simp only [EReal.coe_sub]
    rw [← add_sub_assoc, EReal.sub_add_cancel]
  · trans ⊤
    · exact dif_neg h_ker
    · convert (add_top _).symm
      apply dif_neg ?_
      contrapose! h_ker
      exact h_ker.trans (pinching_map_ker_le ρ σ)
