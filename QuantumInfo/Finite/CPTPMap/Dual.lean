/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap.Bundled
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! # Duals of matrix map

Definitions and theorems about the dual of a matrix map. -/

noncomputable section
open ComplexOrder

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
variable {R : Type*} [CommRing R]
variable {𝕜 : Type*} [RCLike 𝕜]

namespace MatrixMap

variable [DecidableEq dIn] [DecidableEq dOut] {M : MatrixMap dIn dOut 𝕜}

--This should be definable with LinearMap.adjoint, but that requires InnerProductSpace stuff
--that is currently causing issues and pains (tried `open scoped Frobenius`).

/-- The dual of a map between matrices, defined by `Tr[A M(B)] = Tr[(dual M)(A) B]`. Sometimes
 called the adjoint of the map instead. -/
@[irreducible]
def dual (M : MatrixMap dIn dOut R) : MatrixMap dOut dIn R :=
  let iso1 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dIn dIn).symm
  let iso2 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dOut dOut)
  iso1 ∘ₗ LinearMap.dualMap M ∘ₗ iso2

/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem Dual.trace_eq (M : MatrixMap dIn dOut R) (A : Matrix dIn dIn R) (B : Matrix dOut dOut R) :
    (M A * B).trace = (A * M.dual B).trace := by
  unfold dual
  dsimp [Matrix.trace]
  rw [LinearMap.dualMap_apply']
  simp_rw [Matrix.mul_apply]
  sorry

--all properties below should provable just from `inner_eq`, since the definition of `dual` itself
-- is pretty hair (and maybe could be improved...)

/-- The dual of a `IsHermitianPreserving` map also `IsHermitianPreserving`. -/
theorem IsHermitianPreserving.dual (h : M.IsHermitianPreserving) : M.dual.IsHermitianPreserving := by
  sorry

/-- The dual of a `IsPositive` map also `IsPositive`. -/
theorem IsPositive.dual (h : M.IsPositive) : M.dual.IsPositive := by
  intro x hx
  use IsHermitianPreserving.dual h.IsHermitianPreserving hx.1
  sorry

/-- The dual of TracePreserving map is *not* trace-preserving, it's *unital*, that is, M*(I) = I. -/
theorem dual_Unital (h : M.IsTracePreserving) : M.dual.Unital := by
  -- By definition of dual, we know that for any matrix A, Tr(M(A) * I) = Tr(A * M*(I)).
  have h_dual_trace : ∀ A : Matrix dIn dIn 𝕜, (M A * 1).trace = (A * M.dual 1).trace := by
    exact fun A => Dual.trace_eq M A 1;
  ext i j
  specialize h_dual_trace ( Matrix.of ( fun k l => if k = j then if l = i then 1 else 0 else 0 ) )
  simp_all [ Matrix.trace, Matrix.mul_apply ] ;
  specialize h ( Matrix.of ( fun k l => if k = j then if l = i then 1 else 0 else 0 ) )
  simp_all [ Matrix.trace ]
  simp [ Matrix.one_apply, eq_comm ]

alias IsTracePreserving.dual := dual_Unital

/--
If two matrix maps satisfy the trace duality property, they are equal.
-/
lemma dual_unique
    (M : MatrixMap dIn dOut 𝕜) (M' : MatrixMap dOut dIn 𝕜)
    (h : ∀ A B, (M A * B).trace = (A * M' B).trace) : M.dual = M' := by
  -- By definition of dual, we know that for any A and B, the trace of (M A) * B equals the trace of A * (M.dual B).
  have h_dual : ∀ A : Matrix dIn dIn 𝕜, ∀ B : Matrix dOut dOut 𝕜, (M A * B).trace = (A * M.dual B).trace := by
    exact fun A B => Dual.trace_eq M A B;
  -- Since these two linear maps agree on all bases, they must be equal.
  have h_eq : ∀ A : Matrix dIn dIn 𝕜, ∀ B : Matrix dOut dOut 𝕜, (A * M.dual B).trace = (A * M' B).trace := by
    exact fun A B => h_dual A B ▸ h A B;
  refine' LinearMap.ext fun B => _;
  exact Matrix.ext_iff_trace_mul_left.mpr fun x => h_eq x B

/--
The Choi matrix of the dual map is the transpose of the reindexed Choi matrix of the original map.
-/
lemma dual_choi_matrix (M : MatrixMap dIn dOut 𝕜) :
    M.dual.choi_matrix = (M.choi_matrix.transpose).reindex (Equiv.prodComm dOut dIn) (Equiv.prodComm dOut dIn) := by
  -- By definition of dual, we know that $(M.dual (single j₁ j₂ 1)) i₁ i₂ = (M (single i₂ i₁ 1)) j₂ j₁$.
  have h_dual_def : ∀ (i₁ : dIn) (j₁ : dOut) (i₂ : dIn) (j₂ : dOut), (M.dual (Matrix.single j₁ j₂ 1)) i₁ i₂ = (M (Matrix.single i₂ i₁ 1)) j₂ j₁ := by
    intro i₁ j₁ i₂ j₂
    have h_dual_def : (M.dual (Matrix.single j₁ j₂ 1)) i₁ i₂ = Matrix.trace (Matrix.single i₂ i₁ 1 * M.dual (Matrix.single j₁ j₂ 1)) := by
      simp [ Matrix.trace, Matrix.mul_apply ];
      simp [ Matrix.single];
      rw [ Finset.sum_eq_single i₂ ]
      · aesop
      · intro b a a_1
        simp [a_1.symm]
      · aesop
    rw [ h_dual_def, ← Dual.trace_eq ];
    rw [ Matrix.trace ];
    rw [ Finset.sum_eq_single j₂ ] <;> aesop;
  aesop

/--
If the Choi matrix of a map is positive semidefinite, then the Choi matrix of its dual is also positive semidefinite.
-/
lemma dual_choi_matrix_posSemidef_of_posSemidef (M : MatrixMap dIn dOut 𝕜) (h : M.choi_matrix.PosSemidef) :
    M.dual.choi_matrix.PosSemidef := by
  rw [ dual_choi_matrix ];
  simp +zetaDelta at *;
  apply_rules [ Matrix.PosSemidef.submatrix ];
  convert h.transpose using 1

/--
The dual of the identity map is the identity map.
-/
lemma dual_id : (MatrixMap.id dIn 𝕜).dual = MatrixMap.id dIn 𝕜 := by
  exact dual_unique (id dIn 𝕜) (id dIn 𝕜) fun A_1 => congrFun rfl

set_option maxHeartbeats 600000 in
/--
The dual of a Kronecker product of maps is the Kronecker product of their duals.
-/
lemma dual_kron {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (M : MatrixMap A B 𝕜) (N : MatrixMap C D 𝕜) :
    (M ⊗ₖₘ N).dual = M.dual ⊗ₖₘ N.dual := by
  have h_trace : ∀ (X : Matrix (A × C) (A × C) 𝕜) (Y : Matrix (B × D) (B × D) 𝕜), ( (M ⊗ₖₘ N) X * Y ).trace = ( X * (M.dual ⊗ₖₘ N.dual) Y ).trace := by
    -- By definition of dual, we know that $(M x1 * y1).trace = (x1 * M.dual y1).trace$ and $(N x2 * y2).trace = (x2 * N.dual y2).trace$.
    have h_dual : ∀ (x1 : Matrix A A 𝕜) (y1 : Matrix B B 𝕜), (M x1 * y1).trace = (x1 * M.dual y1).trace := by
      intro x1 y1
      convert MatrixMap.Dual.trace_eq M x1 y1 using 1
    have h_dual_N : ∀ (x2 : Matrix C C 𝕜) (y2 : Matrix D D 𝕜), (N x2 * y2).trace = (x2 * N.dual y2).trace := by
      exact fun x2 y2 => MatrixMap.Dual.trace_eq N x2 y2;
    intro X Y;
    -- By definition of Kronecker product, we can write X and Y as sums of Kronecker products.
    obtain ⟨X_sum, hX_sum⟩ : ∃ X_sum : Finset (Matrix A A 𝕜 × Matrix C C 𝕜), X = ∑ p ∈ X_sum, (Matrix.kroneckerMap (fun a b => a * b) p.1 p.2) := by
      refine' ⟨ Finset.univ.image fun p : A × A × C × C => ( Matrix.of fun i j => if i = p.1 ∧ j = p.2.1 then X ( p.1, p.2.2.1 ) ( p.2.1, p.2.2.2 ) else 0, Matrix.of fun i j => if i = p.2.2.1 ∧ j = p.2.2.2 then 1 else 0 ), _ ⟩;
      ext ⟨a, c⟩ ⟨a', c'⟩;
      rw [ Finset.sum_apply, Finset.sum_apply ];
      rw [ Finset.sum_eq_single ( ( Matrix.of fun i j => if i = a ∧ j = a' then X ( a, c ) ( a', c' ) else 0, Matrix.of fun i j => if i = c ∧ j = c' then 1 else 0 ) ) ] <;> simp;
      · intro a_1 b x x_1 x_2 x_3 a_2 a_3 a_4
        subst a_3 a_2
        contrapose! a_4; aesop;
      · exact fun h => False.elim ( h a a' c c' ( by ext i j; aesop ) ( by ext i j; aesop ) )
    obtain ⟨Y_sum, hY_sum⟩ : ∃ Y_sum : Finset (Matrix B B 𝕜 × Matrix D D 𝕜), Y = ∑ p ∈ Y_sum, (Matrix.kroneckerMap (fun a b => a * b) p.1 p.2) := by
      use Finset.image (fun p => (Matrix.of (fun i j => Y (i, p.1) (j, p.2)), Matrix.of (fun i j => if i = p.1 ∧ j = p.2 then 1 else 0))) (Finset.univ : Finset (D × D));
      ext ⟨i, j⟩ ⟨k, l⟩; simp [ Matrix.kroneckerMap ] ;
      rw [ Finset.sum_image ] <;> simp [ Matrix.sum_apply ];
      · rw [ Finset.sum_eq_single ( j, l ) ] <;> aesop;
      · intro p hp q hq h
        subst hX_sum
        simp_all only [Set.mem_univ, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq]
        obtain ⟨fst, snd⟩ := p
        obtain ⟨fst_1, snd_1⟩ := q
        obtain ⟨left, right⟩ := h
        simp_all only [Prod.mk.injEq]
        apply And.intro
        · have := congr_fun ( congr_fun right fst ) snd; aesop;
        · replace right := congr_fun ( congr_fun right fst ) snd; aesop;
    -- By linearity of the trace and the properties of the Kronecker product, we can expand both sides of the equation.
    have h_expand : ∀ (x1 y1 : Matrix A A 𝕜) (x2 y2 : Matrix C C 𝕜) (x3 y3 : Matrix B B 𝕜) (x4 y4 : Matrix D D 𝕜), ( (M ⊗ₖₘ N) (Matrix.kroneckerMap (fun a b => a * b) x1 x2) * Matrix.kroneckerMap (fun a b => a * b) x3 x4 ).trace = ( Matrix.kroneckerMap (fun a b => a * b) x1 x2 * (M.dual ⊗ₖₘ N.dual) (Matrix.kroneckerMap (fun a b => a * b) x3 x4) ).trace := by
      intro x1 y1 x2 y2 x3 y3 x4 y4
      simp [MatrixMap.kron_map_of_kron_state]
      convert congr_arg₂ ( · * · ) ( h_dual x1 x3 ) ( h_dual_N x2 x4 ) using 1 <;> simp [ Matrix.trace, Matrix.mul_apply, Matrix.kroneckerMap_apply ]
      · simp only [Finset.sum_sigma', Finset.sum_mul _ _ _, Finset.mul_sum];
        refine' Finset.sum_bij ( fun x _ => ⟨ ⟨ x.fst.1, x.snd.1 ⟩, ⟨ x.fst.2, x.snd.2 ⟩ ⟩ ) _ _ _ _ <;> simp [ mul_assoc, mul_comm, mul_left_comm ];
        · bound;
        · exact fun b => ⟨ _, _, _, _, rfl ⟩;
      · simp only [mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul];
        simp only [← Finset.sum_product', mul_left_comm];
        refine' Finset.sum_bij ( fun x _ => ( x.1.2, x.2.2, x.1.1, x.2.1 ) ) _ _ _ _ <;> simp;
    simp_all [ Matrix.trace_sum, Finset.sum_mul _ _ _ ];
    simp [Matrix.mul_sum, h_expand]
  apply dual_unique; assumption;

--The dual of a CompletelyPositive map is always CP, more generally it's k-positive
-- see Lemma 3.1 of https://www.math.uwaterloo.ca/~krdavids/Preprints/CDPRpositivereal.pdf
theorem IsCompletelyPositive.dual (h : M.IsCompletelyPositive) : M.dual.IsCompletelyPositive := by
  intro n
  have h_dual_pos : (MatrixMap.dual (M ⊗ₖₘ MatrixMap.id (Fin n) 𝕜)).IsPositive := by
    exact IsPositive.dual (h n);
  -- By definition of complete positivity, we know that $(M ⊗ₖₘ id) dually map = M.dual ⊗ₖₘ id.dual$.
  have h_dual_kron : (MatrixMap.dual (M ⊗ₖₘ MatrixMap.id (Fin n) 𝕜)) = (MatrixMap.dual M) ⊗ₖₘ (MatrixMap.dual (MatrixMap.id (Fin n) 𝕜)) := by
    convert dual_kron M ( MatrixMap.id ( Fin n ) 𝕜 ) using 1;
  convert h_dual_pos using 1;
  rw [ h_dual_kron, dual_id ]

/--
The composition of the dual of the inverse of the dual basis isomorphism with the dual basis isomorphism is the evaluation map.
-/
lemma Module.Basis.dualMap_toDualEquiv_symm_comp_toDualEquiv {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M] [Module.IsReflexive R M] (b : Module.Basis ι R M) :
    b.toDualEquiv.symm.toLinearMap.dualMap ∘ₗ b.toDualEquiv.toLinearMap = (Module.evalEquiv R M).toLinearMap := by
  ext x f;
  -- Since $b.toDual$ and $b.toDualEquiv.symm$ are inverses, we have $b.toDual (b.toDualEquiv.symm f) = f$.
  have h_inv : b.toDual (b.toDualEquiv.symm f) = f := by
    convert LinearEquiv.apply_symm_apply b.toDualEquiv f;
  convert congr_arg ( fun g => g x ) h_inv using 1;
  -- By definition of the dual basis, we know that $(b.toDual x) (b.toDualEquiv.symm f) = f x$.
  simp [Module.Basis.toDual];
  ac_rfl

/--
The composition of the inverse of the dual basis isomorphism with the dual of the dual basis isomorphism is the inverse of the evaluation map.
-/
lemma Module.Basis.toDualEquiv_symm_comp_dualMap_toDualEquiv {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M] [Module.IsReflexive R M] (b : Module.Basis ι R M) :
    b.toDualEquiv.symm.toLinearMap ∘ₗ b.toDualEquiv.toLinearMap.dualMap = (Module.evalEquiv R M).symm.toLinearMap := by
  simp [ LinearMap.ext_iff ];
  intro x
  obtain ⟨y, hy⟩ : ∃ y, x = (Module.evalEquiv R M).toLinearMap y := by
    exact ⟨ _, Eq.symm <| LinearEquiv.apply_symm_apply ( Module.evalEquiv R M ) x ⟩;
  rw [ hy ];
  simp [ Module.evalEquiv, LinearEquiv.symm_apply_eq ];
  ext; simp [ Module.Dual.eval ] ;
  simp [ Module.Basis.toDual ];
  ac_rfl

@[simp]
theorem dual_dual : M.dual.dual = M := by
  rw [dual, dual]
  simp only [← LinearMap.dualMap_comp_dualMap]
  have h₁ : (Matrix.stdBasis 𝕜 dOut dOut).toDualEquiv.symm.toLinearMap ∘ₗ
      ((Matrix.stdBasis 𝕜 dOut dOut).toDualEquiv).toLinearMap.dualMap =
      (Module.evalEquiv 𝕜 (Matrix dOut dOut 𝕜)).symm.toLinearMap := by
    apply Module.Basis.toDualEquiv_symm_comp_dualMap_toDualEquiv
  have h₂ : (Matrix.stdBasis 𝕜 dIn dIn).toDualEquiv.symm.toLinearMap.dualMap ∘ₗ
      (Matrix.stdBasis 𝕜 dIn dIn).toDualEquiv.toLinearMap =
      (Module.evalEquiv 𝕜 (Matrix dIn dIn 𝕜)).toLinearMap := by
    ext x y
    simp
    generalize Matrix.stdBasis 𝕜 dIn dIn = L
    -- Since $L$ is a basis, we can write $y$ as a linear combination of the basis elements.
    obtain ⟨c, hc⟩ : ∃ c : dIn × dIn → 𝕜, y = ∑ i, c i • L.toDual (L i) := by
      have h_dual_basis : ∀ y : Module.Dual 𝕜 (Matrix dIn dIn 𝕜), ∃ c : dIn × dIn → 𝕜, y = ∑ i, c i • L.toDual (L i) := by
        intro y
        have h_dual_basis : y ∈ Submodule.span 𝕜 (Set.range (fun i => L.toDual (L i))) := by
          have h_dual_basis : Submodule.span 𝕜 (Set.range (fun i => L.toDual (L i))) = ⊤ := by
            refine' Submodule.eq_top_of_finrank_eq _;
            rw [ finrank_span_eq_card ];
            · simp [ Module.finrank_eq_card_basis L ];
            · convert L.dualBasis.linearIndependent;
          exact h_dual_basis.symm ▸ Submodule.mem_top
        rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_dual_basis;
        exact ⟨ h_dual_basis.choose, by simpa [ Finsupp.sum_fintype ] using h_dual_basis.choose_spec.symm ⟩;
      exact h_dual_basis y;
    subst hc
    simp [ map_sum, map_smul ];
    congr! 2;
    simp [ Module.Basis.toDualEquiv ];
    simp [ Module.Basis.toDual ]
  rw [← Module.Dual.eval_comp_comp_evalEquiv_eq]
  rw [← Module.evalEquiv_toLinearMap]
  simp only [← LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.id_comp, h₁]
  simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.comp_id, h₂]

end MatrixMap

namespace CPTPMap

variable [DecidableEq dIn] [DecidableEq dOut]

def dual (M : CPTPMap dIn dOut) : CPUMap dOut dIn where
  toLinearMap := M.map.dual
  unital := M.TP.dual
  cp := .dual M.cp

theorem dual_pos (M : CPTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T) :
    0 ≤ M.dual T := by
  exact M.dual.pos_Hermitian hT

/-- The dual of a CPTP map preserves POVMs. Stated here just for two-element POVMs, that is, an
operator `T` between 0 and 1. -/
theorem dual.PTP_POVM (M : CPTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T ∧ T ≤ 1) :
    (0 ≤ M.dual T ∧ M.dual T ≤ 1) := by
  rcases hT with ⟨hT₁, hT₂⟩
  have hT_psd := HermitianMat.zero_le_iff.mp hT₁
  use M.dual.pos_Hermitian hT₁
  simpa using ContinuousOrderHomClass.map_monotone M.dual hT₂

/-- The defining property of a dual channel, as specialized to `MState.exp_val`. -/
theorem exp_val_Dual (ℰ : CPTPMap dIn dOut) (ρ : MState dIn) (T : HermitianMat dOut ℂ) :
    (ℰ ρ).exp_val T  = ρ.exp_val (ℰ.dual T) := by
  simp only [MState.exp_val, HermitianMat.inner_eq_re_trace, RCLike.re_to_complex]
  congr 1
  apply MatrixMap.Dual.trace_eq

end CPTPMap

section hermDual

--PULLOUT to Bundled.lean. Also use this to improve the definitions in POVM.lean.
def HPMap.ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) : HPMap dIn dOut where
  toFun x := f (realPart x) + Complex.I • f (imaginaryPart x)
  map_add' x y := by
    simp only [map_add, HermitianMat.mat_add, smul_add]
    abel
  map_smul' c m := by
    have h_expand : realPart (c • m) = c.re • realPart m - c.im • imaginaryPart m ∧
      imaginaryPart (c • m) = c.re • imaginaryPart m + c.im • realPart m := by
      simp only [Subtype.ext_iff, AddSubgroupClass.coe_sub, selfAdjoint.val_smul,
        AddSubgroup.coe_add, realPart, selfAdjointPart_apply_coe, invOf_eq_inv, star_smul, RCLike.star_def,
        smul_add, imaginaryPart, LinearMap.coe_comp, Function.comp_apply,
        skewAdjoint.negISMul_apply_coe, skewAdjointPart_apply_coe,
        ← Matrix.ext_iff, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
        Complex.ofReal_inv, Complex.ofReal_ofNat, Matrix.star_apply, RCLike.star_def,
        Matrix.sub_apply, Complex.ext_iff, Complex.add_re, Complex.mul_re, Complex.inv_re,
        Complex.normSq_ofNat, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.sub_re, Complex.sub_im, Complex.add_im, Complex.neg_re, Complex.neg_im]
      ring_nf
      simp
    ext
    simp only [h_expand, map_sub, map_smul, map_add, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, RingHom.id_apply, Complex.ext_iff, Complex.add_re, Complex.mul_re,
      Complex.I, Complex.mul_im, Complex.add_im]
    simp only [HermitianMat.mat_sub, HermitianMat.mat_smul, Matrix.sub_apply, Matrix.smul_apply,
      Complex.real_smul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, HermitianMat.mat_add, Matrix.add_apply, Complex.add_re, Complex.add_im,
      Complex.mul_im, add_zero, one_mul, zero_sub, neg_add_rev, zero_add, Complex.sub_im]
    ring_nf
    simp
  HP _ h := by
    apply Matrix.IsHermitian.add
    · apply HermitianMat.H
    · simp [IsSelfAdjoint.imaginaryPart h]

--PULLOUT
omit [Fintype dOut] in
@[simp]
theorem HPMap.linearMap_ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) :
    LinearMapClass.linearMap (HPMap.ofHermitianMat f) = f := by
  ext1 ⟨x, hx⟩
  ext1
  simp only [ofHermitianMat, LinearMap.coe_coe]
  simp only [HPMap.instFunLike, HPMap.map, HermitianMat.mat_mk,
    LinearMap.coe_mk, AddHom.coe_mk]
  conv => enter [2, 1, 2, 1]; rw [← realPart_add_I_smul_imaginaryPart x]
  suffices imaginaryPart x = 0 by simp [this]
  simp [imaginaryPart, skewAdjoint.negISMul, show star x = x from hx]

--PULLOUT
@[simp]
theorem HPMap.ofHermitianMat_linearMap (f : HPMap dIn dOut ℂ) :
    ofHermitianMat (LinearMapClass.linearMap f) = f := by
  ext : 2
  simp only [map, ofHermitianMat, instFunLike, LinearMap.coe_coe, HermitianMat.val_eq_coe,
    HermitianMat.mat_mk, LinearMap.coe_mk, AddHom.coe_mk,
    ← map_smul, ← map_add]
  simp only [map_add, map_smul]
  sorry

variable (f : HPMap dIn dOut) (A : HermitianMat dIn ℂ)

--Can define one for HPMap's that has 'easier' definitional properties, uses the inner product structure,
--doesn't go through Module.Basis the same way. Requires the equivalence between ℝ-linear maps of HermitianMats
--and ℂ-linear maps of matrices.
def HPMap.hermDual : HPMap dOut dIn :=
  HPMap.ofHermitianMat (LinearMapClass.linearMap f).adjoint

@[simp]
theorem HPMap.hermDual_hermDual : f.hermDual.hermDual = f := by
  simp [hermDual]

open RealInnerProductSpace

/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem HPMap.inner_hermDual (B : HermitianMat dOut ℂ) :
    ⟪f A, B⟫ = ⟪A, f.hermDual B⟫ := by
  change ⟪(LinearMapClass.linearMap f) A, B⟫ = ⟪A, (LinearMapClass.linearMap f.hermDual) B⟫
  rw [hermDual, ← LinearMap.adjoint_inner_right, HPMap.linearMap_ofHermitianMat]

/-- Version of `HPMap.inner_hermDual` that uses HermitiaMat.inner directly. TODO cleanup -/
theorem HPMap.inner_hermDual' (B : HermitianMat dOut ℂ) :
    ⟪f A, B⟫ = ⟪A, f.hermDual B⟫ :=
  HPMap.inner_hermDual f A B

/-- The dual of a `IsPositive` map also `IsPositive`. -/
theorem MatrixMap.IsPositive.hermDual (h : MatrixMap.IsPositive f.map) : f.hermDual.map.IsPositive := by
  unfold IsPositive at h ⊢
  intro x hx
  set xH : HermitianMat dOut ℂ := ⟨x, hx.left⟩ with hxH
  have hx' : x = xH := rfl; clear_value xH; subst x; clear hxH
  change Matrix.PosSemidef (f.hermDual xH).mat
  rw [← HermitianMat.zero_le_iff] at hx ⊢
  classical
  rw [HermitianMat.zero_le_iff_inner_pos]
  intro y hy
  rw [HermitianMat.zero_le_iff] at hy
  specialize h hy
  change Matrix.PosSemidef (f y).mat at h
  rw [← HermitianMat.zero_le_iff] at h
  rw [HPMap.inner_hermDual, HPMap.hermDual_hermDual]
  apply HermitianMat.inner_ge_zero hx h

/-- The dual of TracePreserving map is *not* trace-preserving, it's *unital*, that is, M*(I) = I. -/
theorem HPMap.hermDual_Unital [DecidableEq dIn] [DecidableEq dOut] (h : MatrixMap.IsTracePreserving f.map) :
    f.hermDual.map.Unital := by
  suffices f.hermDual 1 = 1 by --todo: make this is an accessible 'constructor' for Unital
    rw [HermitianMat.ext_iff] at this
    exact this
  open RealInnerProductSpace in
  apply ext_inner_left ℝ
  intro v
  rw [← HPMap.inner_hermDual]
  rw [HermitianMat.inner_one, HermitianMat.inner_one] --TODO change to Inner.inner
  exact congr(Complex.re $(h v)) --TODO: HPMap with IsTracePreserving give the HermitianMat.trace version

alias MatrixMap.IsTracePreserving.hermDual := HPMap.hermDual_Unital

namespace PTPMap

variable [DecidableEq dIn] [DecidableEq dOut]

def hermDual (M : PTPMap dIn dOut) : PUMap dOut dIn where
  toHPMap := M.toHPMap.hermDual
  pos := M.pos.hermDual
  unital := M.TP.hermDual

theorem hermDual_pos (M : PTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T) :
    0 ≤ M.hermDual T := by
  exact M.hermDual.pos_Hermitian hT

/-- The dual of a PTP map preserves POVMs. Stated here just for two-element POVMs, that is, an
operator `T` between 0 and 1. -/
theorem hermDual.PTP_POVM (M : PTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T ∧ T ≤ 1) :
    (0 ≤ M.hermDual T ∧ M.hermDual T ≤ 1) := by
  rcases hT with ⟨hT₁, hT₂⟩
  have hT_psd := HermitianMat.zero_le_iff.mp hT₁
  use M.hermDual.pos_Hermitian hT₁
  simpa using ContinuousOrderHomClass.map_monotone M.hermDual hT₂

/-- The defining property of a dual channel, as specialized to `MState.exp_val`. -/
theorem exp_val_hermDual (ℰ : PTPMap dIn dOut) (ρ : MState dIn) (T : HermitianMat dOut ℂ) :
    (ℰ ρ).exp_val T  = ρ.exp_val (ℰ.hermDual T) := by
  simp only [MState.exp_val]
  apply HPMap.inner_hermDual'

end PTPMap

end hermDual
