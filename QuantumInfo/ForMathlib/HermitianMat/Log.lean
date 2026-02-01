/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.CfcOrder
import Batteries.Tactic.ShowUnused

/-! # Properties of the matrix logarithm

In particular, operator monotonicity and concavity of the matrix logarithm.
These are proved using `inv_antitone`, so, first showing that the matrix inverse
is operator antitone for positive definite matrices.
-/

namespace HermitianMat

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

@[simp]
theorem log_zero : (0 : HermitianMat n 𝕜).log = 0 := by
  simp [log, cfc]

@[simp]
theorem log_one : (1 : HermitianMat n 𝕜).log = 0 := by
  simp [log, cfc]

open ComplexOrder in
theorem log_smul {A : HermitianMat n 𝕜} {x : ℝ} (hx : 0 < x) (hA : A.toMat.PosDef) :
    (x • A).log = Real.log x • 1 + A.log := by
  have h_cfc_log : (x • A).log = cfc A (fun t => Real.log (x * t)) := by
    have h_cfc_log : (x • A).log = cfc (x • A) Real.log := by
      rfl;
    convert h_cfc_log using 1;
    have h_cfc_log : (x • A).toMat = cfc A (fun t => x * t) := by
      convert cfc_const_mul_id A x using 1 ;
      grind;
    have h_cfc_log : cfc (x • A) Real.log = cfc (cfc A (fun t => x * t)) Real.log := by
      grind;
    rw [ h_cfc_log, ← cfc_comp ];
    rfl;
  have h_log_mul : ∀ t > 0, Real.log (x * t) = Real.log x + Real.log t := by
    exact fun t ht => Real.log_mul hx.ne' ht.ne';
  have h_cfc_log_mul : cfc A (fun t => Real.log (x * t)) = cfc A (fun t => Real.log x + Real.log t) := by
    apply_rules [ cfc_congr_of_posDef ];
  have h_cfc_add : cfc A (fun t => Real.log x + Real.log t) = cfc A (fun t => Real.log x) + cfc A (fun t => Real.log t) := by
    convert cfc_add A ( fun t => Real.log x ) ( fun t => Real.log t ) using 1;
  aesop

/-
The inverse function is operator antitone for positive definite matrices.
-/
open ComplexOrder in
theorem inv_antitone {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A B : HermitianMat n 𝕜} (hA : A.toMat.PosDef)
    (h : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  -- Since $B - A$ is positive semidefinite, we can write it as $C^*C$ for some matrix $C$.
  obtain ⟨C, hC⟩ : ∃ C : Matrix n n 𝕜, B.toMat - A.toMat = C.conjTranspose * C :=
    Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp h
  -- Using the fact that $B = A + C^*C$, we can write $B^{-1}$ as $(A + C^*C)^{-1}$.
  have h_inv_posDef : (1 + C * A.toMat⁻¹ * C.conjTranspose).PosDef := by
    exact Matrix.PosDef.one.add_posSemidef (hA.inv.posSemidef.mul_mul_conjTranspose_same C)
  have hB_inv : B.toMat⁻¹ = A.toMat⁻¹ - A.toMat⁻¹ * C.conjTranspose * (1 + C * A.toMat⁻¹ * C.conjTranspose)⁻¹ * C * A.toMat⁻¹ := by
    have hB_inv : (A.toMat + C.conjTranspose * C)⁻¹ = A.toMat⁻¹ - A.toMat⁻¹ * C.conjTranspose * (1 + C * A.toMat⁻¹ * C.conjTranspose)⁻¹ * C * A.toMat⁻¹ := by
      have hB_inv : (A.toMat + C.conjTranspose * C) * (A.toMat⁻¹ - A.toMat⁻¹ * C.conjTranspose * (1 + C * A.toMat⁻¹ * C.conjTranspose)⁻¹ * C * A.toMat⁻¹) = 1 := by
        have h_inv : (1 + C * A.toMat⁻¹ * C.conjTranspose) * (1 + C * A.toMat⁻¹ * C.conjTranspose)⁻¹ = 1 := by
          exact Matrix.mul_nonsing_inv _ ( show IsUnit _ from by simpa [ Matrix.isUnit_iff_isUnit_det ] using h_inv_posDef.det_pos.ne' );
        simp only [mul_assoc, Matrix.mul_sub] at *
        simp only [← Matrix.mul_assoc, add_mul, one_mul] at *
        simp only [isUnit_iff_ne_zero, ne_eq, hA.det_pos.ne', not_false_eq_true,
          Matrix.mul_nonsing_inv, one_mul, ← add_mul] at *
        simp only [mul_assoc, add_mul] at *
        simp_all only [← Matrix.mul_assoc, ← eq_sub_iff_add_eq']
        grind only [cases eager Subtype]
      rw [ Matrix.inv_eq_right_inv hB_inv ];
    rw [ ← hB_inv, ← hC, add_sub_cancel ];
  -- Since $(1 + C * A⁻¹ * C.conjTranspose)$ is positive definite, its inverse is also positive definite.
  have h_inv_pos : (A.toMat⁻¹ * C.conjTranspose * (1 + C * A.toMat⁻¹ * C.conjTranspose)⁻¹ * C * A.toMat⁻¹).PosSemidef := by
    have h_inv_pos : (C * A.toMat⁻¹).conjTranspose * (1 + C * A.toMat⁻¹ * C.conjTranspose)⁻¹ * (C * A.toMat⁻¹) = A.toMat⁻¹ * C.conjTranspose * (1 + C * A.toMat⁻¹ * C.conjTranspose)⁻¹ * C * A.toMat⁻¹ := by
      simp [ Matrix.mul_assoc, Matrix.conjTranspose_mul ];
      rw [ Matrix.conjTranspose_nonsing_inv, A.H ];
    rw [ ← h_inv_pos ];
    exact Matrix.PosSemidef.conjTranspose_mul_mul_same h_inv_posDef.inv.posSemidef _
  have h_inv_pos : (A.toMat⁻¹ - B.toMat⁻¹).PosSemidef := by
    simp_all [ Matrix.PosSemidef ];
  exact h_inv_pos

/-
The integral of $1/(1+t) - 1/(x+t)$ from 0 to T is $\log x + \log((1+T)/(x+T))$.
-/
lemma Real.integral_inv_sub_inv_finite (x T : ℝ) (hx : 0 < x) (hT : 0 < T) :
    ∫ t in (0)..T, (1 / (1 + t) - 1 / (x + t)) = Real.log x + Real.log ((1 + T) / (x + T)) := by
  rw [ intervalIntegral.integral_sub, intervalIntegral.integral_comp_add_left, intervalIntegral.integral_comp_add_left ];
  · rw [ ← Real.log_mul, intervalIntegral.integral_deriv_eq_sub' ];
    field_simp;
    rw [ intervalIntegral.integral_deriv_eq_sub' ];
    any_goals intro t ht; exact Real.differentiableAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith );
    any_goals positivity;
    · rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ) ] ; norm_num;
      ring;
    · exact funext fun x => by simp [ div_eq_inv_mul ] ;
    · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const continuousAt_id ( by cases Set.mem_uIcc.mp ht <;> linarith );
    · exact funext fun x => by simp [ div_eq_inv_mul ] ;
    · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const continuousAt_id <| by cases Set.mem_uIcc.mp ht <;> linarith;
  · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const ( continuousAt_const.add continuousAt_id ) ( by linarith [ Set.mem_Icc.mp ( by simpa [ hT.le ] using ht ) ] ) );
  · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const ( continuousAt_const.add continuousAt_id ) ( by linarith [ Set.mem_Icc.mp ( by simpa [ hT.le ] using ht ) ] ) )

/--
The limit of $\log((1+T)/(x+T))$ as $T \to \infty$ is 0, for $x > 0$.
-/
lemma Real.tendsto_log_div_add_atTop (x : ℝ) :
    Filter.Tendsto (fun T => Real.log ((1 + T) / (x + T))) .atTop (nhds 0) := by
  -- We can divide the numerator and the denominator by $b$ and then take the limit as $b$ approaches infinity.
  suffices h_div : Filter.Tendsto (fun b => Real.log ((1 / b + 1) / (x / b + 1))) Filter.atTop (nhds 0) by
    refine h_div.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with b hb using by rw [ show ( 1 + b ) / ( x + b ) = ( 1 / b + 1 ) / ( x / b + 1 ) by rw [ div_add_one, div_add_one, div_div_div_cancel_right₀ ] <;> positivity ] );
  exact le_trans ( Filter.Tendsto.log ( Filter.Tendsto.div ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) tendsto_const_nhds ) ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) tendsto_const_nhds ) ( by positivity ) ) ( by positivity ) ) ( by norm_num )

open ComplexOrder

set_option maxHeartbeats 1000000 in
open ComplexOrder MeasureTheory intervalIntegral in
/--
Monotonicity of the finite integral approximation of the logarithm.
-/
theorem logApprox_mono {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {x y : HermitianMat n 𝕜} (hx : x.toMat.PosDef) (hy : y.toMat.PosDef)
    (hxy : x ≤ y) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0)..T, ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (x + t • 1)⁻¹) ≤
    ∫ t in (0)..T, ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (y + t • 1)⁻¹) := by
  have h_integral_limit : ∀ t ∈ Set.Icc (0 : ℝ) T, (y + t • 1)⁻¹ ≤ (x + t • 1)⁻¹ := by
    intro t ht;
    apply inv_antitone;
    · constructor;
      · simp [ Matrix.IsHermitian];
      · intro v hv_ne_zero
        have h_pos : 0 < star v ⬝ᵥ x.toMat.mulVec v + t * star v ⬝ᵥ v := by
          have := hx.2 v hv_ne_zero;
          exact add_pos_of_pos_of_nonneg this ( mul_nonneg ( mod_cast ht.1 ) ( dotProduct_star_self_nonneg v ) );
        simp_all [ Matrix.add_mulVec ];
        convert h_pos using 2 ; simp [ Matrix.mulVec, dotProduct ];
        simp [ Matrix.one_apply, Finset.mul_sum, mul_left_comm ];
        simp [ mul_left_comm, Algebra.smul_def ];
    · exact add_le_add_right hxy _;
  -- By the properties of the integral, we can bring the limit inside, so we have:
  have h_integral_limit : ∫ t in (0)..T, (1 + t)⁻¹ • 1 - (x + t • 1)⁻¹ ≤ ∫ t in (0)..T, (1 + t)⁻¹ • 1 - (y + t • 1)⁻¹ := by
    have h_integrable : ContinuousOn (fun t : ℝ => (1 + t)⁻¹ • (1 : HermitianMat n 𝕜)) (Set.Icc 0 T) ∧ ContinuousOn (fun t : ℝ => (x + t • 1)⁻¹) (Set.Icc 0 T) ∧ ContinuousOn (fun t : ℝ => (y + t • 1)⁻¹) (Set.Icc 0 T) := by
      refine' ⟨ ContinuousOn.smul ( ContinuousOn.inv₀ ( continuousOn_const.add continuousOn_id ) fun t ht => by linarith [ ht.1 ] ) continuousOn_const, _, _ ⟩;
      · refine' ContinuousOn.comp ( show ContinuousOn ( fun m : HermitianMat n 𝕜 => m⁻¹ ) ( { m : HermitianMat n 𝕜 | m.toMat.PosDef } ) from _ ) _ _;
        · intro m hm;
          refine' ContinuousAt.continuousWithinAt _;
          have h_inv_cont : ContinuousAt (fun m : Matrix n n 𝕜 => m⁻¹) m.toMat := by
            have h_inv_cont : ContinuousAt (fun m : Matrix n n 𝕜 => m⁻¹) m.toMat := by
              have h_det_cont : ContinuousAt (fun m : Matrix n n 𝕜 => m.det) m.toMat := by
                exact Continuous.continuousAt ( continuous_id.matrix_det )
              have h_adj_cont : ContinuousAt (fun m : Matrix n n 𝕜 => m.adjugate) m.toMat := by
                exact Continuous.continuousAt ( continuous_id.matrix_adjugate )
              simp_all [ Matrix.inv_def ];
              exact ContinuousAt.smul ( h_det_cont.inv₀ ( by simpa using hm.det_pos.ne' ) ) h_adj_cont;
            exact h_inv_cont;
          rw [ ContinuousAt ] at *;
          rw [ tendsto_subtype_rng ] at *;
          exact h_inv_cont.comp ( continuous_subtype_val.tendsto _ );
        · fun_prop;
        · intro t ht;
          refine' ⟨ _, _ ⟩;
          · exact H ((fun t => x + t • 1) t);
          · intro v hv_ne_zero
            have h_pos : 0 < star v ⬝ᵥ x.toMat.mulVec v + t * star v ⬝ᵥ (1 : Matrix n n 𝕜).mulVec v := by
              have := hx.2 v hv_ne_zero;
              refine' add_pos_of_pos_of_nonneg this _;
              exact mul_nonneg ( mod_cast ht.1 ) ( Finset.sum_nonneg fun i _ => by simp [ mul_comm, RCLike.mul_conj ] );
            simp_all [ Matrix.add_mulVec ];
            simp_all [ Matrix.mulVec, dotProduct ];
            simp_all [ Matrix.one_apply, Finset.mul_sum, mul_left_comm,];
            convert h_pos using 3 ; simp [ mul_left_comm, Algebra.smul_def ];
      · have h_cont : ContinuousOn (fun t : ℝ => (y + t • 1 : Matrix n n 𝕜)⁻¹) (Set.Icc 0 T) := by
          have h_inv : ∀ t ∈ Set.Icc 0 T, (y + t • 1 : Matrix n n 𝕜).det ≠ 0 := by
            intro t ht;
            have h_det_pos : ∀ t ∈ Set.Icc (0 : ℝ) T, Matrix.PosDef (y.toMat + t • 1) := by
              intro t ht;
              refine' ⟨ _, _ ⟩;
              · simp [ Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul ];
              · intro x hx_ne_zero
                have h_pos : 0 < star x ⬝ᵥ y.toMat.mulVec x + t * star x ⬝ᵥ x := by
                  have := hy.2 x hx_ne_zero;
                  exact add_pos_of_pos_of_nonneg this ( mul_nonneg ( mod_cast ht.1 ) ( by simp [ dotProduct_comm ] ) );
                simp_all [ Matrix.add_mulVec ]
                simp_all [ Matrix.mulVec, dotProduct ]
                simp_all [ Matrix.one_apply, Finset.mul_sum, mul_left_comm ]
                convert h_pos using 1;
                simp [ mul_assoc, mul_comm, mul_left_comm, Algebra.smul_def ];
            exact ne_of_gt ( h_det_pos t ht |> fun h => h.det_pos )
          have h_cont_inv : ContinuousOn (fun t : ℝ => (y + t • 1 : Matrix n n 𝕜)⁻¹) (Set.Icc 0 T) := by
            have h_cont_det : ContinuousOn (fun t : ℝ => (y + t • 1 : Matrix n n 𝕜).det) (Set.Icc 0 T) := by
              fun_prop
            have h_cont_adj : ContinuousOn (fun t : ℝ => (y + t • 1 : Matrix n n 𝕜).adjugate) (Set.Icc 0 T) := by
              fun_prop;
            simp_all [ Matrix.inv_def ];
            exact ContinuousOn.smul ( h_cont_det.inv₀ fun t ht => h_inv t ht.1 ht.2 ) h_cont_adj;
          convert h_cont_inv using 1;
        rw [ continuousOn_iff_continuous_restrict ] at *;
        exact continuous_induced_rng.mpr h_cont
    rw [ intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le ];
    have h_integral_limit : ∀ t ∈ Set.Ioc 0 T, (1 + t)⁻¹ • 1 - (x + t • 1)⁻¹ ≤ (1 + t)⁻¹ • 1 - (y + t • 1)⁻¹ := by
      exact fun t ht => sub_le_sub_left ( h_integral_limit t <| Set.Ioc_subset_Icc_self ht ) _;
    apply_rules [ MeasureTheory.integral_mono_ae ];
    · exact ContinuousOn.integrableOn_Icc (ContinuousOn.sub h_integrable.1 h_integrable.2.1) |> fun h => h.mono_set (Set.Ioc_subset_Icc_self);
    · exact ContinuousOn.integrableOn_Icc (ContinuousOn.sub h_integrable.1 h_integrable.2.2) |> fun h => h.mono_set (Set.Ioc_subset_Icc_self);
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using h_integral_limit t ht;
  exact h_integral_limit

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
variable (A : Matrix n n 𝕜) (hA : A.IsHermitian)

open ComplexOrder MeasureTheory intervalIntegral Matrix in
/--
Spectral decomposition of `cfc A f` as a sum of scaled projections (matrix version).
-/
theorem cfc_toMat_eq_sum_smul_proj {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (A : HermitianMat n 𝕜) (f : ℝ → ℝ) :
    (cfc A f).toMat = ∑ i, f (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
  convert A.cfc_toMat using 1;
  constructor;
  · aesop;
  · intro hf;
    rw [ hf ];
    rw [ A.H.cfc_eq ];
    rw [ Matrix.IsHermitian.cfc ];
    rw [ show ( Matrix.diagonal ( RCLike.ofReal ∘ f ∘ Matrix.IsHermitian.eigenvalues A.H ) : Matrix n n 𝕜 ) = ∑ i, f ( A.H.eigenvalues i ) • Matrix.single i i 1 from ?_ ];
    · simp [ Matrix.mul_sum, Matrix.sum_mul ];
      simp [ Matrix.single, Matrix.mul_assoc ];
      refine' Finset.sum_congr rfl fun i _ => _;
      ext j k ; simp [ Matrix.mul_apply ];
      simp [ Finset.mul_sum _ _ _ ];
      simp only [Finset.smul_sum, smul_ite, smul_zero];
    · ext i j ; by_cases hij : i = j <;> simp [ hij ];
      · simp [ Matrix.sum_apply, Matrix.single ];
        simp [ Algebra.smul_def ];
      · rw [ Finset.sum_apply, Finset.sum_apply ] ; aesop

/-
Definition of the finite integral approximation of the logarithm.
-/
noncomputable def logApprox {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (x : HermitianMat n 𝕜) (T : ℝ) : HermitianMat n 𝕜 :=
  ∫ t in (0)..T, ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (x + t • 1)⁻¹)

/-
Definition of the scalar log approximation and its value.
-/
noncomputable def scalarLogApprox (T : ℝ) (u : ℝ) : ℝ :=
  ∫ t in (0)..T, ((1 + t)⁻¹ - (u + t)⁻¹)

theorem scalarLogApprox_eq (x T : ℝ) (hx : 0 < x) (hT : 0 < T) :
    scalarLogApprox T x = Real.log x + Real.log ((1 + T) / (x + T)) := by
  convert Real.integral_inv_sub_inv_finite x T hx hT using 1;
  unfold scalarLogApprox; norm_num

/-
The inverse of the CFC is the CFC of the inverse function.
-/
lemma cfc_inv {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (x : HermitianMat n 𝕜) (f : ℝ → ℝ) (hf : ∀ i, f (x.H.eigenvalues i) ≠ 0) :
    (cfc x f)⁻¹ = cfc x (fun u => (f u)⁻¹) := by
  -- By definition of $cfc$, we can write
  have h_def : (x.cfc f).toMat = ∑ i, f (x.H.eigenvalues i) • (x.H.eigenvectorUnitary.val * (Matrix.single i i 1) * x.H.eigenvectorUnitary.val.conjTranspose) := by
    exact cfc_toMat_eq_sum_smul_proj x f;
  -- Substitute the definition of $cfc$ into the goal.
  have h_subst : (x.cfc f).toMat⁻¹ = (x.cfc (fun u => 1 / f u)).toMat := by
    have h_subst : (x.cfc (fun u => 1 / f u)).toMat = ∑ i, (1 / f (x.H.eigenvalues i)) • (x.H.eigenvectorUnitary.val * (Matrix.single i i 1) * x.H.eigenvectorUnitary.val.conjTranspose) := by
      exact cfc_toMat_eq_sum_smul_proj x fun u => 1 / f u;
    have h_inv : (x.cfc f).toMat * (x.cfc (fun u => 1 / f u)).toMat = 1 := by
      -- Since the eigenvectorUnitary is unitary, we have that the product of the projections is the identity matrix.
      have h_unitary : x.H.eigenvectorUnitary.val * x.H.eigenvectorUnitary.val.conjTranspose = 1 := by
        simp [ Matrix.IsHermitian.eigenvectorUnitary ];
      have h_inv : ∀ i j, (x.H.eigenvectorUnitary.val * (Matrix.single i i 1) * x.H.eigenvectorUnitary.val.conjTranspose) * (x.H.eigenvectorUnitary.val * (Matrix.single j j 1) * x.H.eigenvectorUnitary.val.conjTranspose) = if i = j then x.H.eigenvectorUnitary.val * (Matrix.single i i 1) * x.H.eigenvectorUnitary.val.conjTranspose else 0 := by
        simp [ ← Matrix.mul_assoc ];
        intro i j; split_ifs <;> simp_all [ Matrix.mul_assoc, Matrix.mul_eq_one_comm.mp h_unitary ] ;
      simp_all [ Finset.sum_mul _ _ _, Finset.mul_sum ];
      have h_sum : ∑ i, (x.H.eigenvectorUnitary.val * (Matrix.single i i 1) * x.H.eigenvectorUnitary.val.conjTranspose) = x.H.eigenvectorUnitary.val * (∑ i, Matrix.single i i 1) * x.H.eigenvectorUnitary.val.conjTranspose := by
        simp [ Finset.mul_sum _ _ _, Finset.sum_mul, Matrix.mul_assoc ];
      simp_all [ Matrix.single ];
      convert h_unitary using 2;
      ext i j; simp [ Matrix.mul_apply]
      simp [ Matrix.sum_apply, Finset.filter_eq', Finset.filter_and ];
      rw [ Finset.sum_eq_single j ] <;> aesop;
    rw [ Matrix.inv_eq_right_inv h_inv ];
  ext i j; simpa using congr_fun ( congr_fun h_subst i ) j;

open ComplexOrder in
/-
The integrand in the log approximation is the CFC of the scalar integrand.
-/
lemma integrand_eq {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (x : HermitianMat n 𝕜) (hx : x.toMat.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (x + t • 1)⁻¹) = cfc x (fun u => (1 + t)⁻¹ - (u + t)⁻¹) := by
  have h_cfc_sub : (1 + t)⁻¹ • 1 = cfc x (fun u => (1 + t)⁻¹) ∧ x + t • 1 = cfc x (fun u => u + t) ∧ (x + t • 1)⁻¹ = cfc x (fun u => (u + t)⁻¹) := by
    refine' ⟨ _, _, _ ⟩;
    · exact Eq.symm (cfc_const x (1 + t)⁻¹);
    · -- By definition of CFC, we know that applying the function to the matrix gives the same result as applying the function to each eigenvalue.
      have h_cfc_add : cfc x (fun u => u + t) = cfc x (fun u => u) + cfc x (fun u => t) := by
        convert cfc_add x ( fun u => u ) ( fun u => t ) using 1;
      aesop;
    · -- Apply the fact that the inverse of the CFC is the CFC of the inverse function.
      have h_inv_cfc : ∀ (f : ℝ → ℝ), (∀ i, f (x.H.eigenvalues i) ≠ 0) → (cfc x f)⁻¹ = cfc x (fun u => (f u)⁻¹) := by
        exact fun f a => cfc_inv x f a;
      convert h_inv_cfc ( fun u => u + t ) _ using 1;
      · rw [ show x.cfc ( fun u => u + t ) = x + t • 1 from ?_ ];
        convert cfc_add x ( fun u => u ) ( fun u => t ) using 1;
        aesop;
      · have := hx.eigenvalues_pos;
        exact fun i => ne_of_gt ( add_pos_of_pos_of_nonneg ( this i ) ht );
  rw [ h_cfc_sub.1, h_cfc_sub.2.2, ← cfc_sub ];
  rfl

open MeasureTheory intervalIntegral in
open scoped Matrix.Norms.Frobenius in
/--
The integral of a Hermitian matrix function commutes with `toMat`.
-/
lemma integral_toMat {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (A : ℝ → HermitianMat n 𝕜) (T : ℝ)
    (hA : IntervalIntegrable A volume 0 T) :
    (∫ t in (0)..T, A t).toMat = ∫ t in (0)..T, (A t).toMat := by
  -- Since `toMat` is a continuous linear map, we can apply the linearity of the integral.
  have h_integral_linear : ∫ a in (0)..T, toMat (A a) = toMat (∫ t in (0)..T, A t) := by
    have h_cont : Continuous (fun x : HermitianMat n 𝕜 => x.toMat) := by
      exact continuous_subtype_val
    have h_integral_linear : ∀ (f : HermitianMat n 𝕜 →L[ℝ] Matrix n n 𝕜), ∫ a in (0)..T, f (A a) = f (∫ t in (0)..T, A t) := by
      exact fun f => ContinuousLinearMap.intervalIntegral_comp_comm f hA;
    convert h_integral_linear ( ContinuousLinearMap.mk ( show HermitianMat n 𝕜 →ₗ[ℝ] Matrix n n 𝕜 from { toFun := fun x => x.toMat, map_add' := fun x y => by aesop, map_smul' := fun c x => by aesop } ) h_cont ) using 1;
  exact h_integral_linear.symm

open MeasureTheory intervalIntegral in
open scoped Matrix.Norms.Frobenius in
/--
A sum of scaled constant matrices is integrable if the scalar functions are integrable.
-/
lemma integrable_sum_smul_const {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (T : ℝ) (g : ℝ → n → ℝ) (P : n → Matrix n n 𝕜)
    (hg : ∀ i, IntervalIntegrable (fun t => g t i) volume 0 T) :
    IntervalIntegrable (fun t => ∑ i, g t i • P i) volume 0 T := by
  simp_all [ intervalIntegrable_iff ];
  exact MeasureTheory.integrable_finset_sum _ fun i _ => MeasureTheory.Integrable.smul_const ( hg i ) _

open MeasureTheory intervalIntegral in
open scoped Matrix.Norms.Frobenius in
/--
A function to Hermitian matrices is integrable iff its matrix values are integrable.
-/
lemma intervalIntegrable_toMat_iff {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (A : ℝ → HermitianMat n 𝕜) (T : ℝ) :
    IntervalIntegrable (fun t => (A t).toMat) volume 0 T ↔ IntervalIntegrable A volume 0 T := by
  simp [ intervalIntegrable_iff ];
  constructor <;> intro h;
  · -- Since `toMat` is a linear isometry, the integrability of `A.toMat` implies the integrability of `A`.
    have h_toMat_integrable : IntegrableOn (fun t => (A t).toMat) (Set.uIoc 0 T) volume → IntegrableOn A (Set.uIoc 0 T) volume := by
      intro h_toMat_integrable
      have h_toMat_linear : ∃ (L : HermitianMat n 𝕜 →ₗ[ℝ] Matrix n n 𝕜), ∀ x, L x = x.toMat := by
        refine' ⟨ _, _ ⟩;
        refine' { .. };
        exacts [ fun x => x.toMat, fun x y => rfl, fun m x => rfl, fun x => rfl ];
      obtain ⟨L, hL⟩ := h_toMat_linear;
      have h_toMat_linear : IntegrableOn (fun t => L (A t)) (Set.uIoc 0 T) volume → IntegrableOn A (Set.uIoc 0 T) volume := by
        intro h_toMat_integrable
        have h_toMat_linear : ∃ (L_inv : Matrix n n 𝕜 →ₗ[ℝ] HermitianMat n 𝕜), ∀ x, L_inv (L x) = x := by
          have h_toMat_linear : Function.Injective L := by
            intro x y hxy; aesop;
          have h_toMat_linear : ∃ (L_inv : Matrix n n 𝕜 →ₗ[ℝ] HermitianMat n 𝕜), L_inv.comp L = LinearMap.id := by
            exact IsSemisimpleModule.extension_property L h_toMat_linear LinearMap.id;
          exact ⟨ h_toMat_linear.choose, fun x => by simpa using LinearMap.congr_fun h_toMat_linear.choose_spec x ⟩;
        obtain ⟨ L_inv, hL_inv ⟩ := h_toMat_linear;
        have h_toMat_linear : IntegrableOn (fun t => L_inv (L (A t))) (Set.uIoc 0 T) volume := by
          exact ContinuousLinearMap.integrable_comp ( L_inv.toContinuousLinearMap ) h_toMat_integrable;
        aesop;
      aesop;
    exact h_toMat_integrable h;
  · refine' h.norm.mono' _ _;
    · have := h.aestronglyMeasurable;
      -- Since the identity function is continuous, and A is AE-strongly measurable, the composition A.toMat is AE-strongly measurable.
      have h_cont : Continuous (fun x : HermitianMat n 𝕜 => x.toMat) := by
        fun_prop
      exact h_cont.comp_aestronglyMeasurable this;
    · filter_upwards with t using le_rfl

open MeasureTheory intervalIntegral in
open scoped Matrix.Norms.Frobenius in
/--
The CFC of an integrable function family is integrable.
-/
lemma integrable_cfc {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (x : HermitianMat n 𝕜) (T : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : ∀ i, IntervalIntegrable (fun t => f t (x.H.eigenvalues i)) volume 0 T) :
    IntervalIntegrable (fun t => cfc x (f t)) volume 0 T := by
      -- Use `cfc_toMat_eq_sum_smul_proj` to expand `(cfc x (f t)).toMat` as `∑ i, f t (λ_i) • P_i`.
      have h_expand : ∀ t, (cfc x (f t)).toMat = ∑ i, f t (x.H.eigenvalues i) • (x.H.eigenvectorUnitary.val * (Matrix.single i i 1) * x.H.eigenvectorUnitary.val.conjTranspose) := by
        exact fun t => cfc_toMat_eq_sum_smul_proj x (f t);
      rw [ ← intervalIntegrable_toMat_iff ];
      rw [ funext h_expand ];
      -- Apply the lemma `integrable_sum_smul_const` to conclude the proof.
      apply integrable_sum_smul_const; intro i; exact hf i

open MeasureTheory intervalIntegral in
open scoped Matrix.Norms.Frobenius in
/--
The integral of the CFC is the CFC of the integral.
-/
lemma integral_cfc_eq_cfc_integral {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (x : HermitianMat n 𝕜) (T : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : ∀ i, IntervalIntegrable (fun t => f t (x.H.eigenvalues i)) volume 0 T) :
    ∫ t in (0)..T, cfc x (f t) = cfc x (fun u => ∫ t in (0)..T, f t u) := by
  -- Apply `HermitianMat.ext` to check equality of matrices.
  apply HermitianMat.ext;
  rw [ integral_toMat ];
  · rw [ intervalIntegral.integral_congr fun t ht => HermitianMat.cfc_toMat_eq_sum_smul_proj x ( f t ), intervalIntegral.integral_finset_sum ];
    · rw [ Finset.sum_congr rfl fun i _ => intervalIntegral.integral_smul_const _ _ ];
      exact Eq.symm (cfc_toMat_eq_sum_smul_proj x fun u => ∫ (t : ℝ) in 0..T, f t u);
    · simp_all [ intervalIntegrable_iff ];
      exact fun i => ( hf i ).smul_const _;
  · exact integrable_cfc x T f hf

open ComplexOrder MeasureTheory intervalIntegral in
/--
The matrix log approximation is the CFC of the scalar log approximation.
-/
theorem logApprox_eq_cfc_scalar {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (x : HermitianMat n 𝕜) (hx : x.toMat.PosDef) (T : ℝ) (hT : 0 < T) :
    logApprox x T = cfc x (scalarLogApprox T) := by
  unfold scalarLogApprox logApprox;
  rw [ intervalIntegral.integral_congr fun t ht => ?_ ];
  convert integral_cfc_eq_cfc_integral x T ( fun t u => ( 1 + t ) ⁻¹ - ( u + t ) ⁻¹ ) ?_ using 1;
  · intro i;
    apply_rules [ ContinuousOn.intervalIntegrable ];
    field_simp;
    apply_rules [ ContinuousOn.sub, ContinuousOn.div, continuousOn_const, continuousOn_id ];
    · fun_prop;
    · exact fun x hx => by cases Set.mem_uIcc.mp hx <;> linarith;
    · fun_prop;
    · have := hx.eigenvalues_pos i;
      exact fun t ht => ne_of_gt ( add_pos_of_pos_of_nonneg this ( by cases Set.mem_uIcc.mp ht <;> linarith ) );
  · convert integrand_eq x hx t ( by cases Set.mem_uIcc.mp ht <;> linarith )

open ComplexOrder in
/--
The log approximation is the log plus an error term.
-/
theorem logApprox_eq_log_add_error {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (x : HermitianMat n 𝕜) (hx : x.toMat.PosDef) (T : ℝ) (hT : 0 < T) :
    logApprox x T = x.log + cfc x (fun u => Real.log ((1 + T) / (u + T))) := by
  have h_logApprox : ∫ t in (0)..T, ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (x + t • 1)⁻¹) = cfc x (fun u => Real.log u + Real.log ((1 + T) / (u + T))) := by
    convert logApprox_eq_cfc_scalar x hx T hT using 1;
    apply cfc_congr_of_posDef hx;
    exact fun u hu => Eq.symm ( scalarLogApprox_eq u T hu.out hT );
  have h_cfc_add : cfc x (fun u => Real.log u + Real.log ((1 + T) / (u + T))) = cfc x Real.log + cfc x (fun u => Real.log ((1 + T) / (u + T))) := by
    apply cfc_add;
  exact h_logApprox.trans h_cfc_add

open ComplexOrder Filter Topology in
open scoped Matrix.Norms.Frobenius in
/--
The error term in the log approximation tends to 0 as T goes to infinity.
-/
lemma tendsto_cfc_log_div_add_atTop {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (x : HermitianMat n 𝕜) :
    Tendsto (fun T => cfc x (fun u => Real.log ((1 + T) / (u + T)))) atTop (nhds 0) := by
  -- Expand `(cfc x ...).toMat` using `cfc_toMat_eq_sum_smul_proj`.
  have h_expand : ∀ T : ℝ, ((cfc x (fun u => Real.log ((1 + T) / (u + T)))).toMat) = ∑ i, Real.log ((1 + T) / (x.H.eigenvalues i + T)) • (x.H.eigenvectorUnitary.val * (Matrix.single i i 1) * x.H.eigenvectorUnitary.val.conjTranspose) := by
    exact fun T => cfc_toMat_eq_sum_smul_proj x fun u => Real.log ((1 + T) / (u + T));
  -- The limit of a sum is the sum of the limits.
  have h_sum : Filter.Tendsto (fun T : ℝ => ∑ i, Real.log ((1 + T) / (x.H.eigenvalues i + T)) • (x.H.eigenvectorUnitary.val * (Matrix.single i i 1) * x.H.eigenvectorUnitary.val.conjTranspose)) Filter.atTop (nhds (∑ i, 0 • (x.H.eigenvectorUnitary.val * (Matrix.single i i 1) * x.H.eigenvectorUnitary.val.conjTranspose))) := by
    refine' tendsto_finset_sum _ fun i _ => _;
    convert Filter.Tendsto.smul_const ( Real.tendsto_log_div_add_atTop ( x.H.eigenvalues i ) ) _ using 1;
    all_goals try infer_instance;
    norm_num +zetaDelta at *
  rw [ tendsto_iff_norm_sub_tendsto_zero ] at *;
  convert h_sum using 2 ; simp [ ← h_expand ]

open ComplexOrder Filter in
/--
The log approximation converges to the matrix logarithm.
-/
lemma tendsto_logApprox {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {x : HermitianMat n 𝕜} (hx : x.toMat.PosDef) :
  Tendsto (fun T => logApprox x T) atTop (nhds x.log) := by
    have h_log_approx_eq : ∀ᶠ T in Filter.atTop, x.logApprox T = x.log + cfc x (fun u => Real.log ((1 + T) / (u + T))) := by
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with T hT using logApprox_eq_log_add_error x hx T hT;
    rw [ Filter.tendsto_congr' h_log_approx_eq ];
    simpa using tendsto_const_nhds.add ( tendsto_cfc_log_div_add_atTop x )

open ComplexOrder HermitianMat in
/--
The matrix logarithm is operator monotone.
-/
theorem log_mono {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {x y : HermitianMat n 𝕜} (hx : x.toMat.PosDef) (hy : y.toMat.PosDef)
    (ha : x ≤ y) : x.log ≤ y.log := by
  apply le_of_tendsto_of_tendsto (tendsto_logApprox hx) (tendsto_logApprox hy)
  rw [Filter.EventuallyLE, Filter.eventually_atTop]
  exact ⟨1, fun T hT => by simpa using logApprox_mono hx hy ha T ( zero_lt_one.trans_le hT )⟩

set_option maxHeartbeats 10000000 in
open ComplexOrder Matrix in
/--
The inverse function is operator convex on positive definite matrices.
-/
lemma inv_convex {x y : HermitianMat n 𝕜} (hx : x.toMat.PosDef) (hy : y.toMat.PosDef)
    ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • x + b • y)⁻¹ ≤ a • x⁻¹ + b • y⁻¹ := by
  -- Using the fact that the set of positive semidefinite matrices is a convex cone, we can show that the matrix
  -- $\begin{pmatrix} a \bullet x + b \bullet y & I \\ I & a \bullet x^{-1} + b \bullet y^{-1} \end{pmatrix}$
  -- is positive semidefinite.
  have h_pos_semidef :
    (Matrix.fromBlocks (a • x.toMat + b • y.toMat) (1 : Matrix n n 𝕜) (1 : Matrix n n 𝕜) (a • (x.toMat)⁻¹ + b • (y.toMat)⁻¹)).PosSemidef := by
      -- Since $a + b = 1$, we can use the fact that the block matrix $\begin{pmatrix} A & I \\ I & A^{-1} \end{pmatrix}$ is positive semidefinite for any positive definite $A$.
      have h_block_pos : ∀ A : Matrix n n 𝕜, A.PosDef → (Matrix.fromBlocks A 1 1 A⁻¹).PosSemidef := by
        intro A hA
        have h_block_pos : (Matrix.fromBlocks A (1 : Matrix n n 𝕜) (1 : Matrix n n 𝕜) (A⁻¹)).PosSemidef := by
          have h_inv_pos : A⁻¹.PosSemidef := by
            exact hA.inv.posSemidef
          have h_block_pos : (Matrix.fromBlocks A (1 : Matrix n n 𝕜) (1 : Matrix n n 𝕜) (A⁻¹)) = (Matrix.fromBlocks 1 0 A⁻¹ 1) * (Matrix.fromBlocks A 0 0 (A⁻¹ - A⁻¹ * A * A⁻¹)) * (Matrix.fromBlocks 1 A⁻¹ 0 1) := by
            simp [ Matrix.fromBlocks_multiply ];
            have := hA.det_pos;
            exact ⟨ by rw [ Matrix.mul_nonsing_inv _ ( show IsUnit A.det from isUnit_iff_ne_zero.mpr this.ne' ) ], by rw [ Matrix.nonsing_inv_mul _ ( show IsUnit A.det from isUnit_iff_ne_zero.mpr this.ne' ) ] ⟩;
          have h_block_pos : (Matrix.fromBlocks A 0 0 (A⁻¹ - A⁻¹ * A * A⁻¹)).PosSemidef := by
            have h_block_pos : (Matrix.fromBlocks A 0 0 (A⁻¹ - A⁻¹ * A * A⁻¹)) = (Matrix.fromBlocks A 0 0 0) := by
              have h_inv : A⁻¹ * A = 1 := by
                rw [ Matrix.nonsing_inv_mul _ ];
                exact isUnit_iff_ne_zero.mpr hA.det_pos.ne';
              simp [ h_inv ];
            rw [h_block_pos];
            constructor;
            · ext i j ; simp [ Matrix.fromBlocks ];
              cases i <;> cases j <;> simp
              exact hA.1.apply _ _;
            · intro x
              simp [Matrix.mulVec, dotProduct];
              have := hA.2 ( fun i => x ( Sum.inl i ) );
              by_cases h : ( fun i => x ( Sum.inl i ) ) = 0 <;> simp_all [ dotProduct, Matrix.mulVec ];
              · simp_all [ funext_iff ];
              · exact le_of_lt this;
          rw [ Matrix.PosSemidef ] at *;
          simp_all [ Matrix.IsHermitian, Matrix.mul_assoc ];
          refine' ⟨ _, _ ⟩;
          · simp [Matrix.fromBlocks_conjTranspose, h_inv_pos.1 ];
          · intro x
            set y : n ⊕ n → 𝕜 := (Matrix.fromBlocks 1 A⁻¹ 0 1).mulVec x
            have h_y : star x ⬝ᵥ (Matrix.fromBlocks 1 0 A⁻¹ 1 * (Matrix.fromBlocks A 0 0 (A⁻¹ - A⁻¹ * (A * A⁻¹)) * Matrix.fromBlocks 1 A⁻¹ 0 1)).mulVec x = star y ⬝ᵥ (Matrix.fromBlocks A 0 0 (A⁻¹ - A⁻¹ * (A * A⁻¹))).mulVec y := by
              simp +zetaDelta at *;
              simp [Matrix.dotProduct_mulVec ];
              simp [ Matrix.star_mulVec ];
              congr! 2;
              ext i j ; simp [ Matrix.mul_apply, Matrix.fromBlocks ];
              cases i <;> cases j <;> simp [ Matrix.one_apply];
              · rw [ ← Matrix.ext_iff ] at * ; aesop;
              · rw [ ← Matrix.ext_iff ] at * ; aesop;
            exact h_y.symm ▸ h_block_pos.2 y;
        exact h_block_pos;
      -- Since $a + b = 1$, we can use the fact that the block matrix $\begin{pmatrix} a \bullet x + b \bullet y & I \\ I & a \bullet x^{-1} + b \bullet y^{-1} \end{pmatrix}$ is positive semidefinite.
      have h_convex : Matrix.PosSemidef ((a • Matrix.fromBlocks (x.toMat) (1 : Matrix n n 𝕜) (1 : Matrix n n 𝕜) (x.toMat)⁻¹) + (b • Matrix.fromBlocks (y.toMat) (1 : Matrix n n 𝕜) (1 : Matrix n n 𝕜) (y.toMat)⁻¹)) := by
        apply_rules [ Matrix.PosSemidef.add, Matrix.PosSemidef.smul ];
      convert h_convex using 1;
      ext i j ; simp [ Matrix.fromBlocks ];
      rcases i with ( i | i ) <;> rcases j with ( j | j ) <;> simp [ Matrix.one_apply ];
      · split_ifs <;> simp_all [ ← add_smul ];
      · split_ifs <;> simp_all [ ← add_smul ];
  have h_schur : (a • x.toMat + b • y.toMat).PosDef := by
    by_cases ha' : a = 0 <;> by_cases hb' : b = 0 <;> simp_all [ Matrix.PosSemidef ];
    constructor;
    · simp_all [ Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul ];
    · intro v hv_ne_zero
      have h_pos : 0 < a * (star v ⬝ᵥ x.toMat.mulVec v) + b * (star v ⬝ᵥ y.toMat.mulVec v) := by
        have := hx.2 v hv_ne_zero; have := hy.2 v hv_ne_zero; simp_all [ Matrix.mulVec, dotProduct ] ;
        exact add_pos_of_nonneg_of_pos ( mul_nonneg ( mod_cast ha ) ( le_of_lt ‹_› ) ) ( mul_pos ( mod_cast lt_of_le_of_ne hb ( Ne.symm hb' ) ) ( mod_cast this ) );
      convert h_pos using 1 ; simp [ Matrix.add_mulVec]
      ring_nf
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm];
      simp [mul_left_comm, Algebra.smul_def ];
  change (a • (x.toMat)⁻¹ + b • (y.toMat)⁻¹ - (a • x.toMat + b • y.toMat)⁻¹).PosSemidef
  refine' ⟨ _, fun v => _ ⟩;
  · simp_all [ Matrix.IsHermitian, Matrix.conjTranspose_nonsing_inv ];
  · have := h_pos_semidef.2;
    specialize this (Sum.elim (- (a • x.toMat + b • y.toMat)⁻¹.mulVec v) v);
    simp_all [ Matrix.fromBlocks_mulVec ];
    simp_all [ Matrix.mul_nonsing_inv _ ( show IsUnit ( Matrix.det ( a • ( x : Matrix n n 𝕜 ) + b • ( y : Matrix n n 𝕜 ) ) ) from isUnit_iff_ne_zero.mpr <| h_schur.det_pos.ne' ), Matrix.mulVec_neg];
    simp_all [ dotProduct, Matrix.sub_mulVec ];
    exact this.trans_eq ( Finset.sum_congr rfl fun _ _ => by ring );

/--
The shifted inverse function is operator convex.
-/
lemma inv_shift_convex {x y : HermitianMat n 𝕜} (hx : x.toMat.PosDef) (hy : y.toMat.PosDef)
    ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (t : ℝ) (ht : 0 ≤ t) :
    (a • x + b • y + t • 1)⁻¹ ≤ a • (x + t • 1)⁻¹ + b • (y + t • 1)⁻¹ := by
  have hx' : (x + t • 1).toMat.PosDef := hx.add_posSemidef (.smul .one ht)
  have hy' : (y + t • 1).toMat.PosDef := hy.add_posSemidef (.smul .one ht)
  convert inv_convex hx' hy' ha hb hab using 1
  ext
  simp [add_assoc, add_left_comm, hab, ← add_smul]

open MeasureTheory intervalIntegral ComplexOrder Matrix in
open scoped Matrix.Norms.Frobenius in
/--
Definition of the approximation of the matrix logarithm.
-/
lemma integrable_inv_shift {A : HermitianMat n 𝕜} (hA : A.toMat.PosDef) (b : ℝ) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t => (A + t • 1)⁻¹) volume 0 b := by
  -- The function $t \mapsto (A + tI)^{-1}$ is continuous on $[0, b]$ because $A + tI$ is invertible for all $t \geq 0$.
  have h_cont : ContinuousOn (fun t : ℝ => (A + t • 1 : HermitianMat n 𝕜)⁻¹) (Set.Icc 0 b) := by
    have h_cont : ContinuousOn (fun t : ℝ => (A + t • 1 : Matrix n n 𝕜)⁻¹) (Set.Icc 0 b) := by
      have h_inv : ∀ t ∈ Set.Icc 0 b, IsUnit (A + t • 1 : Matrix n n 𝕜) := by
        intro t ht
        have h_pos_def : Matrix.PosDef (A + t • 1 : Matrix n n 𝕜) := by
          simp_all [ Matrix.PosDef ];
          simp_all [ Matrix.IsHermitian, Matrix.add_mulVec ]
          intro x hx; specialize hA x hx; simp_all [ Matrix.mulVec, dotProduct ];
          simp_all [ Matrix.one_apply, Finset.mul_sum ];
          apply add_pos_of_pos_of_nonneg hA
          refine Finset.sum_nonneg fun i _ ↦ ?_
          simp [ Algebra.smul_def, mul_comm ];
          apply mul_nonneg (by simp [RCLike.mul_conj])
          simpa using ht.1
        exact h_pos_def.isUnit
      have h_cont_inv : ContinuousOn (fun t : ℝ => (A + t • 1 : Matrix n n 𝕜).det⁻¹) (Set.Icc 0 b) := by
        apply ContinuousOn.inv₀ (by fun_prop)
        exact (Matrix.det_ne_zero_of_left_inverse <| h_inv · · |>.unit.inv_mul)
      simp [Matrix.inv_def]
      fun_prop
    rw [continuousOn_iff_continuous_restrict] at *
    exact continuous_induced_rng.mpr h_cont
  exact h_cont.intervalIntegrable_of_Icc hb

open ComplexOrder MeasureTheory intervalIntegral in
/--
The finite integral approximation of the matrix logarithm is operator concave.
-/
theorem logApprox_concave {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {x y : HermitianMat n 𝕜} (hx : x.toMat.PosDef) (hy : y.toMat.PosDef)
    ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (T : ℝ) (hT : 0 ≤ T) :
    a • x.logApprox T + b • y.logApprox T ≤ (a • x + b • y).logApprox T := by
  have h_integrable {z : HermitianMat n 𝕜} : z.toMat.PosDef → IntervalIntegrable (fun t => (1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (z + t • 1)⁻¹) MeasureTheory.volume 0 T := by
    intro hz
    have h_integrable := integrable_inv_shift hz T hT
    rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le hT ] at *
    refine MeasureTheory.Integrable.sub ?_ h_integrable
    exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.smul ( ContinuousAt.inv₀ ( continuousAt_const.add continuousAt_id ) ( by linarith [ ht.1 ] ) ) continuousAt_const ) |> fun h => h.mono_set ( Set.Ioc_subset_Icc_self );
  have h_int2 : IntervalIntegrable (fun t => (1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - ((a • x + b • y) + t • 1)⁻¹) MeasureTheory.volume 0 T := by
    exact h_integrable (Matrix.PosDef.Convex hx hy ha hb hab)
  have h_integral_mono : ∫ t in (0)..T, a • ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (x + t • 1)⁻¹) + b • ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (y + t • 1)⁻¹) ≤ ∫ t in (0)..T, (1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - ((a • x + b • y) + t • 1)⁻¹ := by
    have h_integral_mono : ∀ t ∈ Set.Icc 0 T, a • ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (x + t • 1)⁻¹) + b • ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (y + t • 1)⁻¹) ≤ (1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - ((a • x + b • y) + t • 1)⁻¹ := by
      intros t ht
      have h_inv_shift_convex : ((a • x + b • y) + t • 1)⁻¹ ≤ a • (x + t • 1)⁻¹ + b • (y + t • 1)⁻¹ := by
        convert HermitianMat.inv_shift_convex hx hy ha hb hab t ht.1 using 1;
      simp_all [smul_sub, ← smul_assoc ];
      rw [ show ( 1 + t ) ⁻¹ • ( 1 : HermitianMat n 𝕜 ) = ( a * ( 1 + t ) ⁻¹ ) • ( 1 : HermitianMat n 𝕜 ) + ( b * ( 1 + t ) ⁻¹ ) • ( 1 : HermitianMat n 𝕜 ) by rw [ ← add_smul, ← add_mul, hab, one_mul ] ];
      convert sub_le_sub_left h_inv_shift_convex _ using 1 ; abel_nf;
    rw [ intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT ];
    apply MeasureTheory.integral_mono_ae
    · exact ( (h_integrable hx).1.smul a |> fun h => h.add ( (h_integrable hy).1.smul b ) ) |> fun h => h.mono_measure ( MeasureTheory.Measure.restrict_mono ( Set.Ioc_subset_Ioc le_rfl le_rfl ) le_rfl );
    · exact h_int2.1.mono_set (Set.Ioc_subset_Ioc le_rfl le_rfl)
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using h_integral_mono t <| Set.Ioc_subset_Icc_self ht;
  convert h_integral_mono using 1;
  rw [ intervalIntegral.integral_add ( by exact (h_integrable hx).smul a ) ( by exact (h_integrable hy).smul b ), intervalIntegral.integral_smul, intervalIntegral.integral_smul ]
  rw [logApprox, logApprox]

/--
The matrix logarithm is operator concave.
-/
theorem log_concave {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {x y : HermitianMat n 𝕜} (hx : x.toMat.PosDef) (hy : y.toMat.PosDef)
    ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x.log + b • y.log ≤ (a • x + b • y).log := by
  apply le_of_tendsto_of_tendsto (b := .atTop) (f := fun T => a • x.logApprox T + b • y.logApprox T) (g := (a • x + b • y).logApprox)
  · exact ((tendsto_const_nhds.smul (tendsto_logApprox hx)).add (tendsto_const_nhds.smul (y.tendsto_logApprox hy)))
  · apply tendsto_logApprox
    exact Matrix.PosDef.Convex hx hy ha hb hab
  · rw [Filter.EventuallyLE, Filter.eventually_atTop]
    exact ⟨0, logApprox_concave hx hy ha hb hab⟩
