/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Inner
import QuantumInfo.ForMathlib.Isometry

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

/-! Matrix operations on HermitianMats with the CFC -/

--PULLOUT
namespace Matrix

open ComplexOrder in
theorem IsHermitian.spectrum_subset_Ici_of_sub {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
  {A x: Matrix d d 𝕜} (hA : A.IsHermitian) (hl : (x - A).PosSemidef) :
    spectrum ℝ x ⊆ Set.Ici (⨅ i, hA.eigenvalues i) := by
  --Thanks Aristotle
  intro μ hμ
  obtain ⟨v, hv₁, hv₂⟩ : ∃ v : d → 𝕜, v ≠ 0 ∧ x.mulVec v = μ • v := by
    have h_singular : ∃ v : d → 𝕜, v ≠ 0 ∧ (μ • 1 - x).mulVec v = 0 := by
      simp only [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ne_eq, Decidable.not_not] at hμ
      convert Matrix.exists_mulVec_eq_zero_iff.mpr hμ;
      simp [Algebra.smul_def]
    refine h_singular.imp fun v h ↦ ⟨h.left, ?_⟩
    simp_all [Matrix.sub_mulVec, sub_eq_iff_eq_add, funext_iff, Matrix.mulVec, dotProduct, Matrix.one_apply]
  -- Since $x - A$ is positive semidefinite, for any eigenvalue $\lambda$ of $x$, we have $\lambda \geq \min(\text{eigenvalues of } A)$.
  have h_lower_bound : ∀ (v : d → 𝕜), v ≠ 0 → (star v ⬝ᵥ (x.mulVec v)) ≥ (⨅ i, (hA.eigenvalues i)) * (star v ⬝ᵥ v) := by
    intro v hv_nonzero
    have h_eigenvalue : (star v ⬝ᵥ (A.mulVec v)) ≥ (⨅ i, (hA.eigenvalues i)) * (star v ⬝ᵥ v) := by
      have h_expand : (star v ⬝ᵥ (A.mulVec v)) = ∑ i, (hA.eigenvalues i) * (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) := by
        change (star v ⬝ᵥ (A.mulVec v)) = ∑ i, (hA.eigenvalues i) * (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i))
        have h_decomp : A = ∑ i, (hA.eigenvalues i) • (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k)))) := by
          convert Matrix.IsHermitian.spectral_theorem hA using 1;
          ext i j
          simp only [RCLike.star_def, Matrix.smul_of, Matrix.sum_apply, Matrix.of_apply,
            Pi.smul_apply, Matrix.diagonal, Function.comp_apply, Matrix.mul_apply,
            Matrix.IsHermitian.eigenvectorUnitary_apply, PiLp.ofLp_apply, mul_ite, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Matrix.star_apply];
          simp [ mul_comm, mul_left_comm, Algebra.smul_def ]
        -- Substitute the decomposition of $A$ into the expression $(star v ⬝ᵥ (A.mulVec v))$.
        have h_subst : (star v ⬝ᵥ (A.mulVec v)) = ∑ i, (hA.eigenvalues i) * (star v ⬝ᵥ (Matrix.mulVec (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k)))) v)) := by
          -- Substitute the decomposition of $A$ into the expression $(star v ⬝ᵥ (A.mulVec v))$ and use the linearity of matrix multiplication.
          have h_subst : (star v ⬝ᵥ (A.mulVec v)) = (star v ⬝ᵥ ((∑ i, (hA.eigenvalues i) • (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k))))).mulVec v)) := by
            rw [ ← h_decomp ];
          -- By the linearity of matrix multiplication and the dot product, we can distribute the sum over the dot product.
          have h_distribute : (star v ⬝ᵥ (∑ i, (hA.eigenvalues i) • (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k))))).mulVec v) = ∑ i, (star v ⬝ᵥ ((hA.eigenvalues i) • (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k))))).mulVec v) := by
            -- By the linearity of matrix multiplication and the dot product, we can distribute the sum over the dot product. This follows from the fact that matrix multiplication is linear.
            have h_distribute : ∀ (M N : Matrix d d 𝕜) (v : d → 𝕜), Star.star v ⬝ᵥ (M + N).mulVec v = Star.star v ⬝ᵥ M.mulVec v + Star.star v ⬝ᵥ N.mulVec v := by
              simp [ Matrix.add_mulVec, dotProduct_add ];
            -- By induction on the number of terms in the sum, we can apply the distributive property repeatedly.
            have h_induction : ∀ (n : ℕ) (M : Fin n → Matrix d d 𝕜) (v : d → 𝕜), Star.star v ⬝ᵥ (∑ i, M i).mulVec v = ∑ i, Star.star v ⬝ᵥ (M i).mulVec v := by
              intro n M v
              induction n
              · simp [*]
              · simp [Fin.sum_univ_succ, *]
            convert h_induction ( Fintype.card d ) ( fun i => Matrix.of ( hA.eigenvalues ( Fintype.equivFin d |>.symm i ) • fun j k => hA.eigenvectorBasis ( Fintype.equivFin d |>.symm i ) j * starRingEnd 𝕜 ( hA.eigenvectorBasis ( Fintype.equivFin d |>.symm i ) k ) ) ) v using 1;
            · rw [ ← Equiv.sum_comp ( Fintype.equivFin d ) ];
              simp [ Fintype.equivFin ];
            · rw [ ← Equiv.sum_comp ( Fintype.equivFin d ) ];
              simp [ Fintype.equivFin ];
          convert h_distribute using 1;
          simp only [dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec, Matrix.of_apply,
            Finset.mul_sum _ _ _, Matrix.smul_apply, Algebra.smul_mul_assoc,
            Algebra.mul_smul_comm];
          simp [ Algebra.smul_def ];
        convert h_subst using 2;
        simp only [dotProduct, Pi.star_apply, RCLike.star_def, mul_comm, mul_assoc, Matrix.mulVec,
          Matrix.of_apply, mul_eq_mul_left_iff, map_eq_zero];
        simp [ mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      -- Since $\lambda_i \geq \inf(\text{eigenvalues of } A)$ for all $i$, we can bound each term in the sum.
      have h_bound : ∀ i, (hA.eigenvalues i) * (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) ≥ (⨅ i, (hA.eigenvalues i)) * (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) := by
        intro i
        have h_eigenvalue_bound : (hA.eigenvalues i) ≥ (⨅ i, (hA.eigenvalues i)) :=
          ciInf_le (Set.finite_range _).bddBelow _
        -- Since the product of the inner products is real and non-negative, multiplying both sides of the inequality by this product preserves the inequality.
        have h_nonneg : 0 ≤ (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) := by
          -- Since the inner product is conjugate symmetric, we have star v ⬝ᵥ (hA.eigenvectorBasis i) = conjugate(star (hA.eigenvectorBasis i) ⬝ᵥ v).
          have h_conj_symm : star v ⬝ᵥ (hA.eigenvectorBasis i) = star (star (hA.eigenvectorBasis i) ⬝ᵥ v) := by
            simp [ dotProduct, mul_comm];
          rw [ h_conj_symm ];
          exact mul_star_self_nonneg (star (hA.eigenvectorBasis i) ⬝ᵥ v);
        norm_num [ mul_assoc ];
        exact mul_le_mul_of_nonneg_right ( mod_cast h_eigenvalue_bound ) h_nonneg;
      -- Since $\sum_{i} (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) = star v ⬝ᵥ v$, we can factor out $(⨅ i, (hA.eigenvalues i))$ from the sum.
      have h_sum : ∑ i, (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) = star v ⬝ᵥ v := by
        have h_sum : ∑ i, (star (hA.eigenvectorBasis i) ⬝ᵥ v) • (hA.eigenvectorBasis i) = v := by
          have := hA.eigenvectorBasis.sum_repr v;
          convert this using 1;
          simp only [dotProduct, Pi.star_apply, RCLike.star_def, mul_comm,
            hA.eigenvectorBasis.repr_apply_apply, PiLp.inner_apply, RCLike.inner_apply];
        -- Taking the inner product of both sides of h_sum with star v, we get the desired equality.
        have h_inner : star v ⬝ᵥ (∑ i, (star (hA.eigenvectorBasis i) ⬝ᵥ v) • (hA.eigenvectorBasis i)) = star v ⬝ᵥ v := by
          rw [h_sum];
        convert h_inner using 1;
        simp [ dotProduct, Finset.mul_sum _ _ _ ];
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      rw [ h_expand ];
      refine' le_trans _ ( Finset.sum_le_sum fun i _ => h_bound i );
      simp only [ mul_assoc];
      rw [ ← Finset.mul_sum _ _ _, h_sum ];
    have := hl.2 v; simp_all [ Matrix.sub_mulVec ] ;
    exact le_trans h_eigenvalue this;
  change (⨅ i, hA.eigenvalues i) ≤ μ
  have := h_lower_bound v hv₁
  simp_all only [ne_eq, star, RCLike.star_def, Matrix.dotProduct_mulVec, ge_iff_le,
    dotProduct_smul];
  simp_all only [dotProduct, mul_comm, RCLike.mul_conj];
  rw [ Algebra.smul_def ] at this;
  -- Since the sum of the squares of the norms of v is positive, we can divide both sides of the inequality by it.
  have h_sum_pos : 0 < ∑ x : d, (‖v x‖ : ℝ) ^ 2 := by
    contrapose! hv₁;
    simp_all only [funext_iff, Pi.zero_apply, not_forall, forall_exists_index, Matrix.mulVec, Pi.smul_apply]
    intro i
    rw [← norm_eq_zero]
    simpa [ sq_nonneg ] using le_antisymm ( le_trans ( Finset.single_le_sum ( fun a _ => sq_nonneg ( ‖v a‖ ) ) ( Finset.mem_univ i ) ) hv₁ ) ( sq_nonneg ( ‖v i‖ ) )
  norm_cast at this;
  nlinarith

open ComplexOrder in
theorem IsHermitian.spectrum_subset_Iic_of_sub {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
  {A x : Matrix d d 𝕜} (hA : A.IsHermitian) (hl : (A - x).PosSemidef) :
    spectrum ℝ x ⊆ Set.Iic (⨆ i, hA.eigenvalues i) := by
  have h := spectrum_subset_Ici_of_sub hA.neg (x := -x) ?_
  · rcases isEmpty_or_nonempty d
    · simp
    rw [← spectrum.neg_eq] at h
    intro μ hμ
    specialize h (Set.neg_mem_neg.mpr hμ)
    rw [← Set.mem_neg, Set.neg_Ici] at h
    convert h
    rw [iInf, iSup, ← spectrum_real_eq_range_eigenvalues, ← spectrum_real_eq_range_eigenvalues]
    rw [← spectrum.neg_eq, csInf_neg ?_ (A.finite_real_spectrum.bddAbove), neg_neg]
    exact IsSelfAdjoint.spectrum_nonempty hA
  · convert hl using 1
    abel

open ComplexOrder in
theorem IsHermitian.spectrum_subset_of_mem_Icc {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
  {A B x : Matrix d d 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
  (hl : (x - A).PosSemidef) (hr : (B - x).PosSemidef) :
    spectrum ℝ x ⊆ Set.Icc (⨅ i, hA.eigenvalues i) (⨆ i, hB.eigenvalues i) := by
  rw [← Set.Ici_inter_Iic]
  exact Set.subset_inter (hA.spectrum_subset_Ici_of_sub hl) (hB.spectrum_subset_Iic_of_sub hr)

end Matrix

namespace HermitianMat

noncomputable section CFC

macro "herm_cont":term => `(term|
  by simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology])

variable {d d₂ 𝕜 : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [RCLike 𝕜]

@[simp]
theorem conjTranspose_cfc (A : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    (cfc f A.toMat).conjTranspose = cfc f A.toMat := by
  exact cfc_predicate f A.toMat

noncomputable nonrec def cfc (A : HermitianMat d 𝕜) (f : ℝ → ℝ) : HermitianMat d 𝕜 :=
  ⟨cfc f A.toMat, cfc_predicate _ _⟩

variable (A : HermitianMat d 𝕜) (f : ℝ → ℝ) (g : ℝ → ℝ) (r : ℝ)

@[simp]
theorem cfc_toMat : (cfc A f).toMat = _root_.cfc f A.toMat := by
  rfl

/-- Reindexing a matrix commutes with applying the CFC. -/
@[simp]
theorem cfc_reindex (e : d ≃ d₂) : cfc (A.reindex e) f = (cfc A f).reindex e := by
  rw [HermitianMat.ext_iff]
  simp only [cfc_toMat, reindex_coe]
  exact Matrix.cfc_reindex f e


/--
Spectral decomposition of `cfc A f` as a sum of scaled projections (matrix version).
-/
theorem cfc_toMat_eq_sum_smul_proj : (cfc A f).toMat =
    ∑ i, f (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
  rw [A.cfc_toMat]
  rw [ A.H.cfc_eq ];
  rw [ Matrix.IsHermitian.cfc ];
  have h : ( Matrix.diagonal ( RCLike.ofReal ∘ f ∘ Matrix.IsHermitian.eigenvalues A.H ) : Matrix d d 𝕜 ) = ∑ i, f ( A.H.eigenvalues i ) • Matrix.single i i 1 := by
    ext i j ; by_cases hij : i = j <;> simp [ hij ];
    · simp [ Matrix.sum_apply, Matrix.single ];
      simp [ Algebra.smul_def ];
    · rw [ Finset.sum_apply, Finset.sum_apply ] ; aesop
  rw [h]
  simp [ Matrix.mul_sum, Matrix.sum_mul ];
  simp [ Matrix.single, Matrix.mul_assoc ];
  congr! 1
  ext j k
  simp [Matrix.mul_apply,Finset.mul_sum, Finset.smul_sum, smul_ite, smul_zero]

--Ensure we get this instance:
/-- info: locallyCompact_of_proper -/
#guard_msgs in
#synth LocallyCompactSpace (HermitianMat d 𝕜)

--PULLOUT to Inner.lean
--Better name ...
open RealInnerProductSpace in
omit [DecidableEq d] in
theorem inner_eq_trace_mul' (A B : HermitianMat d 𝕜) :
    ⟪A, B⟫ = RCLike.re (Matrix.trace (A.toMat * B.toMat)) := by
  exact inner_eq_re_trace A B

--PULLOUT to Inner.lean
@[simp]
theorem norm_one : ‖(1 : HermitianMat d 𝕜)‖ = √(Fintype.card d : ℝ) := by
  simp [norm_eq_sqrt_real_inner, inner_eq_trace_mul']

theorem cfc_eigenvalues (A : HermitianMat d 𝕜) :
    ∃ (e : d ≃ d), (A.cfc f).H.eigenvalues = f ∘ A.H.eigenvalues ∘ e :=
  A.H.cfc_eigenvalues f

--PULLOUT to Inner.lean
theorem norm_eq_trace_sq (A : HermitianMat d 𝕜) :
    ‖A‖ ^ 2 = (A.toMat ^ 2).trace := by
  rw [norm_eq_frobenius, ← RCLike.ofReal_pow, ← Real.rpow_two, ← Real.rpow_mul (by positivity)]
  simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀, Real.rpow_one]
  simp only [sq A.toMat, map_sum, map_pow, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, toMat_apply]
  congr! with i _ j _
  --ew ew ew make this better
  rw [← star_star (A j i)]
  conv => enter [2, 2, 1]; exact (Matrix.conjTranspose_apply A.toMat j i).symm
  rw [A.H]
  symm
  exact RCLike.mul_conj (A.toMat i j)

/-! Here we give HermitianMat versions of many cfc theorems, like `cfc_id`, `cfc_sub`, `cfc_comp`,
etc. We need these because (as above) `HermitianMat.cfc` is different from `_root_.cfc`. -/

@[simp]
nonrec theorem cfc_id : cfc A id = A := by
  simp [HermitianMat.ext_iff, cfc_id]

@[simp]
nonrec theorem cfc_id' : cfc A (·) = A :=
  cfc_id A

nonrec theorem cfc_add : cfc A (f + g) = cfc A f + cfc A g := by
  rw [HermitianMat.ext_iff]
  exact cfc_add (hf := herm_cont) (hg := herm_cont)

nonrec theorem cfc_sub : cfc A (f - g) = cfc A f - cfc A g := by
  rw [HermitianMat.ext_iff]
  exact cfc_sub (hf := herm_cont) (hg := herm_cont)

nonrec theorem cfc_neg : cfc A (-f) = -cfc A f := by
  rw [HermitianMat.ext_iff]
  exact cfc_neg f A.toMat

/-- We don't have a direct analog of `cfc_mul`, since we can't generally multiply
to HermitianMat's to get another one, so the theorem statement wouldn't be well-typed.
But, we can say that the matrices are always equal. See `cfc_conj` for the coe-free
analog to multiplication. -/
theorem coe_cfc_mul : (cfc A (f * g)).toMat = cfc A f * cfc A g := by
  simp only [cfc_toMat]
  exact cfc_mul (hf := herm_cont) (hg := herm_cont)

nonrec theorem cfc_comp : cfc A (g ∘ f) = cfc (cfc A f) g := by
  rw [HermitianMat.ext_iff]
  exact cfc_comp (hf := herm_cont) (hg := herm_cont)

nonrec theorem cfc_conj : (cfc A f).conj (cfc A g) = cfc A (f * g^2) := by
  rw [HermitianMat.ext_iff, conj_apply]
  simp only [cfc_toMat, val_eq_coe, mk_toMat, conjTranspose_cfc]
  rw [← cfc_mul (hf := herm_cont) (hg := herm_cont)]
  rw [← cfc_mul (hf := herm_cont) (hg := herm_cont)]
  rw [Pi.mul_def, Pi.pow_def]
  congr! 2; ring

theorem cfc_sq : cfc A (· ^ 2) = A ^ 2 := by
  ext1
  simp_rw [selfAdjoint.val_pow, sq]
  conv_lhs => exact coe_cfc_mul A (f := id) (g := id)
  rw [cfc_id]

@[simp]
nonrec theorem cfc_const : (cfc A (fun _ ↦ r)) = r • 1 := by
  rw [HermitianMat.ext_iff]
  simp only [cfc_toMat, selfAdjoint.val_smul, val_eq_coe, selfAdjoint.val_one]
  rw [cfc_const r A.toMat]
  exact Algebra.algebraMap_eq_smul_one r

@[simp]
nonrec theorem cfc_const_mul_id : cfc A (fun x => r * x) = r • A := by
  rw [HermitianMat.ext_iff]
  simp only [cfc_toMat, selfAdjoint.val_smul, val_eq_coe]
  exact cfc_const_mul_id r A.toMat

@[simp]
nonrec theorem cfc_const_mul : cfc A (fun x => r * f x) = r • cfc A f := by
  rw [← cfc_const_mul_id, ← cfc_comp]
  rfl

@[simp]
nonrec theorem cfc_apply_zero : cfc (0 : HermitianMat d 𝕜) f = f 0 • 1 := by
  simp [HermitianMat.ext_iff, Algebra.algebraMap_eq_smul_one]

@[simp]
nonrec theorem cfc_apply_one : cfc (1 : HermitianMat d 𝕜) f = f 1 • 1 := by
  simp [HermitianMat.ext_iff, Algebra.algebraMap_eq_smul_one]

variable {f g} in
nonrec theorem cfc_congr (hfg : Set.EqOn f g (spectrum ℝ A.toMat)) :
    cfc A f = cfc A g := by
  rw [HermitianMat.ext_iff]
  exact cfc_congr hfg

variable {f g A} in
/-- Version of `cfc_congr` specialized to PSD matrices. -/
nonrec theorem cfc_congr_of_zero_le (hA : 0 ≤ A) (hfg : Set.EqOn f g (Set.Ici 0)) :
    cfc A f = cfc A g := by
  refine cfc_congr A (hfg.mono ?_)
  open MatrixOrder in
  exact fun i hi ↦ spectrum_nonneg_of_nonneg hA hi

open ComplexOrder

variable {f g A} in
/-- Version of `cfc_congr` specialized to positive definite matrices. -/
nonrec theorem cfc_congr_of_posDef (hA : A.toMat.PosDef) (hfg : Set.EqOn f g (Set.Ioi 0)) :
    cfc A f = cfc A g := by
  refine cfc_congr A (hfg.mono ?_)
  rw [A.H.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  exact hA.eigenvalues_pos i

@[simp]
theorem cfc_diagonal (g : d → ℝ) :
    cfc (HermitianMat.diagonal 𝕜 g) f = HermitianMat.diagonal 𝕜 (f ∘ g) := by
  ext1
  exact Matrix.cfc_diagonal g f

theorem cfc_conj_unitary (f : ℝ → ℝ) (U : Matrix.unitaryGroup d 𝕜) :
  cfc (A.conj U.val) f = (cfc A f).conj U := by
  ext1
  exact Matrix.cfc_conj_unitary f U

theorem zero_le_cfc : 0 ≤ A.cfc f ↔ ∀ i, 0 ≤ f (A.H.eigenvalues i) := by
  open MatrixOrder in
  rw [cfc, ← Subtype.coe_le_coe]
  dsimp
  rw [cfc_nonneg_iff (hf := herm_cont), A.H.spectrum_real_eq_range_eigenvalues]
  grind

variable {A f} in
theorem zero_le_cfc_of_zero_le (hA : 0 ≤ A) (hf : ∀ i ≥ 0, 0 ≤ f i) :
    0 ≤ A.cfc f := by
  rw [zero_le_cfc]
  intro i
  rw [zero_le_iff, A.H.posSemidef_iff_eigenvalues_nonneg] at hA
  exact hf _ (hA i)

theorem cfc_PosDef : (A.cfc f).toMat.PosDef ↔ ∀ i, 0 < f (A.H.eigenvalues i) := by
  rw [(A.cfc f).H.posDef_iff_eigenvalues_pos]
  obtain ⟨e, he⟩ := A.cfc_eigenvalues f
  rw [he]
  refine ⟨fun h i ↦ ?_, fun h i ↦ h (e i)⟩
  convert h (e.symm i)
  simp

theorem norm_eq_sum_eigenvalues_sq (A : HermitianMat d 𝕜) :
    ‖A‖ ^ 2 = ∑ i, (A.H.eigenvalues i)^2 := by
  rw [← RCLike.ofReal_inj (K := 𝕜), RCLike.ofReal_pow, norm_eq_trace_sq]
  conv_lhs => change (A ^ 2).toMat.trace; rw [(A ^ 2).H.trace_eq_sum_eigenvalues]
  simp only [map_sum, map_pow]
  rw [← cfc_sq]
  obtain ⟨e, he⟩ := cfc_eigenvalues (· ^ 2) A
  simp only [he, Function.comp_apply, map_pow]
  exact e.sum_comp (fun x ↦ (algebraMap ℝ 𝕜) (A.H.eigenvalues x) ^ 2)

variable {A} in
theorem lt_smul_of_norm_lt {r : ℝ} (h : ‖A‖ ≤ r) : A ≤ r • 1 := by
  rcases lt_or_ge r 0 with _ | hr
  · have := norm_nonneg A
    order
  rcases isEmpty_or_nonempty d
  · exact le_of_subsingleton
  have h' := (sq_le_sq₀ (by positivity) (by positivity)).mpr h
  rw [norm_eq_sum_eigenvalues_sq] at h'
  nth_rw 1 [← cfc_const A, ← cfc_id A]
  rw [le_iff, ← cfc_sub]
  rw [(HermitianMat.H _).posSemidef_iff_eigenvalues_nonneg]
  intro i; rw [Pi.zero_apply]
  obtain ⟨e, he⟩ := cfc_eigenvalues ((fun x ↦ r) - id) A
  rw [he]; clear he
  dsimp only [Function.comp_apply, Pi.sub_apply, id_eq]
  rw [sub_nonneg]
  apply le_of_sq_le_sq _ hr
  refine le_trans ?_ h'
  exact Finset.single_le_sum (f := fun x ↦ (A.H.eigenvalues x)^2) (by intros; positivity) (Finset.mem_univ _)

theorem ball_subset_Icc (r : ℝ) : Metric.ball A r ⊆ Set.Icc (A - r • 1) (A + r • 1) := by
  intro x
  simp only [Metric.mem_ball, dist_eq_norm, Set.mem_Icc, tsub_le_iff_right]
  intro h
  constructor
  · rw [← norm_neg] at h
    grw [← lt_smul_of_norm_lt h.le]
    simp
  · grw [← lt_smul_of_norm_lt h.le]
    simp

theorem spectrum_subset_of_mem_Icc (A B : HermitianMat d 𝕜) :
    ∃ a b, ∀ x, A ≤ x ∧ x ≤ B → spectrum ℝ x.toMat ⊆ Set.Icc a b := by
  use ⨅ i, A.H.eigenvalues i, ⨆ i, B.H.eigenvalues i
  rintro x ⟨hl, hr⟩
  exact A.H.spectrum_subset_of_mem_Icc B.H hl hr

@[fun_prop]
protected theorem cfc_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (cfc · f : HermitianMat d ℂ → HermitianMat d ℂ) := by
  unfold cfc
  suffices Continuous (fun A : HermitianMat d ℂ ↦ _root_.cfc f (toMat A)) by
    fun_prop
  have h_compact_cover := LocallyCompactSpace.local_compact_nhds (X := HermitianMat d ℂ)
  apply continuous_of_continuousOn_iUnion_of_isOpen (ι := HermitianMat d ℂ × {x : ℝ // 0 < x})
    (s := fun ab ↦ Metric.ball ab.1 ab.2)
  · rintro ⟨A, r, hr⟩
    apply ContinuousOn.mono ?_ (ball_subset_Icc A r)
    obtain ⟨a, b, hab⟩ := spectrum_subset_of_mem_Icc (A - r • 1) (A + r • 1)
    open ComplexOrder in
    have := ContinuousOn.cfc (A := CStarMatrix d d ℂ) isCompact_Icc f (by fun_prop) hab (fun x _ ↦ x.H)
    convert this
  · simp
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    use ⟨x, 1⟩
    simp

/--
The inverse of the CFC is the CFC of the inverse function.
-/
lemma inv_cfc_eq_cfc_inv (f : ℝ → ℝ) (hf : ∀ i, f (A.H.eigenvalues i) ≠ 0) :
    (cfc A f)⁻¹ = cfc A (fun u => (f u)⁻¹) := by
  -- By definition of $cfc$, we can write
  have h_def : (A.cfc f).toMat = ∑ i, f (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
    exact cfc_toMat_eq_sum_smul_proj A f;
  -- Substitute the definition of $cfc$ into the goal.
  have h_subst : (A.cfc f).toMat⁻¹ = (A.cfc (fun u => 1 / f u)).toMat := by
    have h_subst : (A.cfc (fun u => 1 / f u)).toMat = ∑ i, (1 / f (A.H.eigenvalues i)) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
      exact cfc_toMat_eq_sum_smul_proj A fun u => 1 / f u;
    have h_inv : (A.cfc f).toMat * (A.cfc (fun u => 1 / f u)).toMat = 1 := by
      -- Since the eigenvectorUnitary is unitary, we have that the product of the projections is the identity matrix.
      have h_unitary : A.H.eigenvectorUnitary.val * A.H.eigenvectorUnitary.val.conjTranspose = 1 := by
        simp [ Matrix.IsHermitian.eigenvectorUnitary ];
      have h_inv : ∀ i j, (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) * (A.H.eigenvectorUnitary.val * (Matrix.single j j 1) * A.H.eigenvectorUnitary.val.conjTranspose) = if i = j then A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose else 0 := by
        simp [ ← Matrix.mul_assoc ];
        intro i j; split_ifs <;> simp_all [ Matrix.mul_assoc, Matrix.mul_eq_one_comm.mp h_unitary ] ;
      simp_all [ Finset.sum_mul _ _ _, Finset.mul_sum ];
      have h_sum : ∑ i, (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) = A.H.eigenvectorUnitary.val * (∑ i, Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose := by
        simp [ Finset.mul_sum _ _ _, Finset.sum_mul, Matrix.mul_assoc ];
      simp_all [ Matrix.single ];
      convert h_unitary using 2;
      ext i j; simp [ Matrix.mul_apply]
      simp [ Matrix.sum_apply, Finset.filter_eq', Finset.filter_and ];
      rw [ Finset.sum_eq_single j ] <;> aesop;
    rw [ Matrix.inv_eq_right_inv h_inv ];
  ext i j; simpa using congr_fun ( congr_fun h_subst i ) j;

theorem cfc_inv (hf : ∀ i, A.H.eigenvalues i ≠ 0) :
    cfc A (fun u => u⁻¹) = A⁻¹ := by
  simpa using (inv_cfc_eq_cfc_inv A id hf).symm

/-- Matrix power of a positive semidefinite matrix, as given by the elementwise
  real power of the diagonal in a diagonalized form.

  Note that this has the usual `Real.rpow` caveats, such as 0 to the power -1 giving 0. -/
def rpow (p : ℝ) : HermitianMat d 𝕜 :=
  cfc A (Real.rpow · p)

instance instRPow : Pow (HermitianMat d 𝕜) ℝ :=
  ⟨rpow⟩

theorem pow_eq_rpow (p : ℝ) : A ^ p = A.rpow p :=
  rfl

theorem pow_eq_cfc (p : ℝ) : A ^ p = cfc A (· ^ p) :=
  rfl

theorem diagonal_pow (f : d → ℝ) (p : ℝ) :
    (diagonal 𝕜 f) ^ p = diagonal 𝕜 (fun i => (f i) ^ p) := by
  simp [pow_eq_cfc]
  rfl

@[simp]
theorem pow_one : A ^ (1 : ℝ) = A := by
  simp [pow_eq_cfc]

@[simp]
theorem reindex_pow (A : HermitianMat d ℂ) (e : d ≃ d₂) (p : ℝ) :
    A.reindex e ^ p = (A ^ p).reindex e := by
  apply A.cfc_reindex

variable {A} in
theorem coe_rpow_add (hA : 0 ≤ A) {p q : ℝ} (hpq : p + q ≠ 0) :
    (A ^ (p + q)).toMat = (A ^ p).toMat * (A ^ q).toMat := by
  simp only [pow_eq_cfc, ← coe_cfc_mul, ← HermitianMat.ext_iff]
  exact cfc_congr_of_zero_le hA (fun i hi ↦ Real.rpow_add' hi hpq)

variable {A} in
theorem rpow_mul (hA : 0 ≤ A) {p q : ℝ} :
    (A ^ (p * q)) = ((A ^ p) ^ q) := by
  simp only [pow_eq_cfc, ← cfc_comp]
  exact cfc_congr_of_zero_le hA (fun i hi ↦ Real.rpow_mul hi p q)

variable {A} in
theorem conj_rpow (hA : 0 ≤ A) {p q : ℝ}
  (hq : q ≠ 0) (hpq : p + 2 * q ≠ 0) :
    (A ^ p).conj (A ^ q) = A ^ (p + 2 * q) := by
  simp only [pow_eq_cfc, cfc_conj]
  refine cfc_congr_of_zero_le hA (fun i hi ↦ ?_)
  rw [pow_two, Real.rpow_add' hi hpq, two_mul, Real.rpow_add' hi (by simpa)]
  rfl

theorem pow_half_mul {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
  {A : HermitianMat d 𝕜} (hA : 0 ≤ A) :
    (A ^ (1/2 : ℝ)).toMat * (A ^ (1/2 : ℝ)).toMat = A := by
  rw [← coe_rpow_add hA]
  · norm_num
  · norm_num

/-- Matrix logarithm (base e) of a Hermitian matrix, as given by the elementwise
  real logarithm of the diagonal in a diagonalized form, using `Real.log`

  Note that this means that the nullspace of the image includes all of the nullspace of the
  original matrix. This contrasts to the standard definition, which is only defined for positive
  *definite* matrices, and the nullspace of the image is exactly the (λ=1)-eigenspace of the
  original matrix. It coincides with the standard definition if A is positive definite. -/
def log : HermitianMat d 𝕜 :=
  cfc A Real.log

@[simp]
theorem reindex_log (e : d ≃ d₂) : (A.reindex e).log = A.log.reindex e :=
  cfc_reindex A Real.log e

section integral

open MeasureTheory
open scoped Matrix.Norms.Frobenius

/--
The integral of a Hermitian matrix function commutes with `toMat`.
-/
lemma integral_toMat {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (A : ℝ → HermitianMat n 𝕜) (T : ℝ)
    (hA : IntervalIntegrable A volume 0 T) :
    (∫ t in (0)..T, A t).toMat = ∫ t in (0)..T, (A t).toMat := by
  have h_cont : Continuous (fun x : HermitianMat n 𝕜 => x.toMat) := by
      exact continuous_subtype_val
  have h_integral_linear : ∀ (f : HermitianMat n 𝕜 →L[ℝ] Matrix n n 𝕜), ∫ a in (0)..T, f (A a) = f (∫ t in (0)..T, A t) := by
    exact fun f => ContinuousLinearMap.intervalIntegral_comp_comm f hA
  symm
  exact h_integral_linear ( ContinuousLinearMap.mk ( show HermitianMat n 𝕜 →ₗ[ℝ] Matrix n n 𝕜 from { toFun := fun x => x.toMat, map_add' := fun x y => by aesop, map_smul' := fun c x => by aesop } ) h_cont )

/--
A sum of scaled constant matrices is integrable if the scalar functions are integrable.
-/
lemma intervalIntegrable_sum_smul_const {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (T : ℝ) (g : ℝ → n → ℝ) (P : n → Matrix n n 𝕜)
    (hg : ∀ i, IntervalIntegrable (fun t => g t i) volume 0 T) :
    IntervalIntegrable (fun t => ∑ i, g t i • P i) volume 0 T := by
  simp_all [ intervalIntegrable_iff ];
  exact MeasureTheory.integrable_finset_sum _ fun i _ => MeasureTheory.Integrable.smul_const ( hg i ) _

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
      apply intervalIntegrable_sum_smul_const
      exact hf

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

end integral
end CFC
