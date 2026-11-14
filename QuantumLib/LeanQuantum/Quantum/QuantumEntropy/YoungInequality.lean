import Quantum.QuantumMechanics.QuantumState
import Quantum.QuantumMechanics.QuantumChannel
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.InnerProductSpace.Trace

open QuantumState
open scoped ComplexOrder
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator

universe u

noncomputable instance matrixCStarAlgebra {ℋ : Type u} [Qudit ℋ] :
    CStarAlgebra (Matrix (Fin (Module.finrank ℂ ℋ)) (Fin (Module.finrank ℂ ℋ)) ℂ) where

lemma weighted_young_finset {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p q : ℝ) (hpq : p.HolderConjugate q)
    (x : ι → ℝ) (y : κ → ℝ) (c : ι → κ → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) (hc : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, (∑ j, c i j) = 1) (hcol : ∀ j, (∑ i, c i j) = 1) :
    (∑ i, ∑ j, x i * y j * c i j)
      ≤ (∑ i, x i ^ p) / p + (∑ j, y j ^ q) / q := by
  calc
    (∑ i, ∑ j, x i * y j * c i j)
        ≤ ∑ i, ∑ j, ((x i ^ p) / p + (y j ^ q) / q) * c i j := by
      refine Finset.sum_le_sum ?_
      intro i hi
      refine Finset.sum_le_sum ?_
      intro j hj
      have hyoung : x i * y j ≤ x i ^ p / p + y j ^ q / q :=
        Real.young_inequality_of_nonneg (hx i) (hy j) hpq
      exact mul_le_mul_of_nonneg_right hyoung (hc i j)
    _ = (∑ i, ∑ j, (x i ^ p / p) * c i j) + (∑ i, ∑ j, (y j ^ q / q) * c i j) := by
      simp [add_mul, Finset.sum_add_distrib]
    _ = (∑ i, (x i ^ p / p) * (∑ j, c i j)) + (∑ j, (y j ^ q / q) * (∑ i, c i j)) := by
      have hxpart : (∑ i, ∑ j, (x i ^ p / p) * c i j) = ∑ i, (x i ^ p / p) * (∑ j, c i j) := by
        simp [Finset.mul_sum]
      have hypart : (∑ i, ∑ j, (y j ^ q / q) * c i j) = ∑ j, (y j ^ q / q) * (∑ i, c i j) := by
        calc
          (∑ i, ∑ j, (y j ^ q / q) * c i j) = ∑ j, ∑ i, (y j ^ q / q) * c i j := by
            rw [Finset.sum_comm]
          _ = ∑ j, (y j ^ q / q) * (∑ i, c i j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [Finset.mul_sum]
      simp [hxpart, hypart]
    _ = (∑ i, x i ^ p / p) + (∑ j, y j ^ q / q) := by
      simp [hrow, hcol]
    _ = (∑ i, x i ^ p) / p + (∑ j, y j ^ q) / q := by
      simp [div_eq_mul_inv, Finset.sum_mul]

lemma trace_comp_eq_sum_eigen_right {ℋ : Type u} [Qudit ℋ] (X Y : L ℋ) (hY : Y.IsPositive) :
    Tr (X ∘ₗ Y)
      = ∑ i : Fin (Module.finrank ℂ ℋ),
          ((hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
            * inner ℂ
                (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i)
                (X (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i)) := by
  let b := hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  calc
    Tr (X ∘ₗ Y) = ∑ i : Fin (Module.finrank ℂ ℋ), inner ℂ (b i) ((X ∘ₗ Y) (b i)) := by
      simpa [QuantumState.Tr] using LinearMap.trace_eq_sum_inner (T := X ∘ₗ Y) b
    _ = ∑ i : Fin (Module.finrank ℂ ℋ), inner ℂ (b i) (X (Y (b i))) := by
      simp
    _ = ∑ i : Fin (Module.finrank ℂ ℋ),
          inner ℂ (b i)
            (X (((hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ) • b i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [b] at *
    _ = ∑ i : Fin (Module.finrank ℂ ℋ),
          ((hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
            * inner ℂ (b i) (X (b i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, inner_smul_right]

lemma tr_eq_matrix_trace_orthonormal {ℋ : Type u} [Qudit ℋ]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ) (T : L ℋ) :
    Tr T = Matrix.trace (LinearMap.toMatrixOrthonormal b T) := by
  simpa [QuantumState.Tr, LinearMap.toMatrixOrthonormal] using
    (LinearMap.trace_eq_matrix_trace (R := ℂ) (b := b.toBasis) (f := T))

set_option backward.isDefEq.respectTransparency false in
lemma toMatrixOrthonormal_rpow {ℋ : Type u} [Qudit ℋ]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ) (X : L ℋ)
    (hX : X.IsPositive) (p : ℝ) (hp : 0 ≤ p) :
    LinearMap.toMatrixOrthonormal b (CFC.rpow X p)
      = CFC.rpow (LinearMap.toMatrixOrthonormal b X) p := by
  have hXnonneg : 0 ≤ X := (LinearMap.nonneg_iff_isPositive X).2 hX
  have hXselfAdjoint : IsSelfAdjoint X := hX.isSelfAdjoint
  have hφ : Continuous (LinearMap.toMatrixOrthonormal b) :=
    (StarAlgEquiv.isometry (LinearMap.toMatrixOrthonormal b)).continuous
  have hφnonneg : 0 ≤ LinearMap.toMatrixOrthonormal b X :=
    map_nonneg (LinearMap.toMatrixOrthonormal b) hXnonneg
  have hφselfAdjoint : IsSelfAdjoint (LinearMap.toMatrixOrthonormal b X) :=
    IsSelfAdjoint.map hXselfAdjoint (LinearMap.toMatrixOrthonormal b)
  have hf : ContinuousOn (fun x : ℝ => x ^ p) (spectrum ℝ X) :=
    (Real.continuous_rpow_const hp).continuousOn
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow]
  rw [CFC.rpow_eq_cfc_real (a := X) (y := p) (ha := hXnonneg)]
  rw [CFC.rpow_eq_cfc_real (a := LinearMap.toMatrixOrthonormal b X) (y := p) (ha := hφnonneg)]
  simpa using
    (StarAlgHomClass.map_cfc
      (R := ℝ)
      (φ := LinearMap.toMatrixOrthonormal b)
      (f := fun x : ℝ => x ^ p)
      (a := X)
      (hf := hf)
      (hφ := hφ)
      (ha := hXselfAdjoint)
      (hφa := hφselfAdjoint))

set_option backward.isDefEq.respectTransparency false in
lemma matrix_trace_rpow_eq_sum_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (hA0 : 0 ≤ A) (p : ℝ) :
    Matrix.trace (CFC.rpow A p)
      = ∑ i, (((hA.eigenvalues i) ^ p : ℝ) : ℂ) := by
  rw [CFC.rpow_eq_pow]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := p) (ha := hA0)]
  have htrace :
      Matrix.trace (cfc (fun x : ℝ => x ^ p) A)
        = ((Matrix.charpoly (cfc (fun x : ℝ => x ^ p) A)).roots.sum) := by
    simpa using (Matrix.trace_eq_sum_roots_charpoly (A := cfc (fun x : ℝ => x ^ p) A))
  rw [htrace]
  rw [hA.charpoly_cfc_eq (f := fun x : ℝ => x ^ p)]
  have hroots :
      (Polynomial.roots
        (∏ i, (Polynomial.X - Polynomial.C ((((hA.eigenvalues i) ^ p : ℝ)) : ℂ))))
        = (Finset.univ.val.bind fun i =>
            Polynomial.roots
              (Polynomial.X - Polynomial.C ((((hA.eigenvalues i) ^ p : ℝ)) : ℂ))) := by
    exact Polynomial.roots_prod
      (f := fun i => (Polynomial.X - Polynomial.C ((((hA.eigenvalues i) ^ p : ℝ)) : ℂ)))
      (s := Finset.univ)
      (Finset.prod_ne_zero_iff.mpr (by
        intro i hi
        exact Polynomial.X_sub_C_ne_zero _))
  have hsum := congrArg Multiset.sum hroots
  simpa using hsum

lemma toMatrixOrthonormal_eq_diagonal_eigenvalues {ℋ : Type u} [Qudit ℋ]
    (X : L ℋ) (hX : X.IsPositive) :
    LinearMap.toMatrixOrthonormal (hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl) X
      = Matrix.diagonal (fun i =>
          (((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) : ℝ) : ℂ)) := by
  let bx := hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [LinearMap.toMatrixOrthonormal_apply_apply,
      hX.isSymmetric.apply_eigenvectorBasis, Matrix.diagonal_apply_eq]
    haveI : IsScalarTower ℝ ℂ ℋ := RestrictScalars.isScalarTower ℝ ℂ ℋ
    rw [inner_smul_right_eq_smul, inner_self_eq_one_of_norm_eq_one (bx.norm_eq_one i),
      Algebra.smul_def, mul_one]
    exact Algebra.algebraMap_self_apply _
  · simp [LinearMap.toMatrixOrthonormal_apply_apply, hij,
      hX.isSymmetric.apply_eigenvectorBasis]

lemma sum_rpow_eq_of_multiset_map_eq {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) (p : ℝ)
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    (∑ i, (f i) ^ p) = ∑ i, (g i) ^ p := by
  have hpow := congrArg (Multiset.map (fun x : ℝ => x ^ p)) h
  have hsum := congrArg Multiset.sum hpow
  simpa using hsum

set_option backward.isDefEq.respectTransparency false in
lemma trace_rpow_eq_sum_eigenvalues {ℋ : Type u} [Qudit ℋ]
    (X : L ℋ) (hX : X.IsPositive) (p : ℝ) (hp : 0 ≤ p) :
    Tr (CFC.rpow X p)
      = ((((∑ i : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) : ℝ)) : ℂ) := by
  let bx := hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  let eVals : Fin (Module.finrank ℂ ℋ) → ℝ :=
    fun i => hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i
  let M : Matrix (Fin (Module.finrank ℂ ℋ)) (Fin (Module.finrank ℂ ℋ)) ℂ :=
    LinearMap.toMatrixOrthonormal bx X
  have hXnonneg : 0 ≤ X := (LinearMap.nonneg_iff_isPositive X).2 hX
  have hMnonneg : 0 ≤ M := by
    simpa [M] using map_nonneg (LinearMap.toMatrixOrthonormal bx) hXnonneg
  have hMpsd : M.PosSemidef := (Matrix.nonneg_iff_posSemidef).1 hMnonneg
  have hMherm : M.IsHermitian := hMpsd.1
  have hrootsM :
      M.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hMherm.eigenvalues) Finset.univ.val :=
    hMherm.roots_charpoly_eq_eigenvalues
  have hrootsDiag :
      M.charpoly.roots = Multiset.map (RCLike.ofReal ∘ eVals) Finset.univ.val := by
    have hdiagM : M = Matrix.diagonal (fun i =>
      (((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) : ℝ) : ℂ)) := by
      simpa [M, eVals] using toMatrixOrthonormal_eq_diagonal_eigenvalues X hX
    rw [hdiagM, Matrix.charpoly_diagonal]
    have hroots :
        (Polynomial.roots
          (∏ i : Fin (Module.finrank ℂ ℋ),
            (Polynomial.X - Polynomial.C ((((eVals i) : ℝ) : ℂ))))
            ) = (Finset.univ.val.bind fun i : Fin (Module.finrank ℂ ℋ) =>
                Polynomial.roots (Polynomial.X - Polynomial.C ((((eVals i) : ℝ) : ℂ)))) := by
      exact Polynomial.roots_prod
        (f := fun i : Fin (Module.finrank ℂ ℋ) =>
          (Polynomial.X - Polynomial.C ((((eVals i) : ℝ) : ℂ))))
        (s := Finset.univ)
        (Finset.prod_ne_zero_iff.mpr (by
          intro i hi
          exact Polynomial.X_sub_C_ne_zero _))
    rw [hroots]
    simp
  have hrealMulti :
      Multiset.map hMherm.eigenvalues Finset.univ.val = Multiset.map eVals Finset.univ.val := by
    have hrootsEq :
        Multiset.map ((fun x : ℝ => (x : ℂ)) ∘ hMherm.eigenvalues) Finset.univ.val
          = Multiset.map ((fun x : ℝ => (x : ℂ)) ∘ eVals) Finset.univ.val := by
      exact hrootsM.symm.trans hrootsDiag
    have hre := congrArg (Multiset.map Complex.re) hrootsEq
    simpa [Function.comp, eVals] using hre
  have hsumPow :
      (∑ i : Fin (Module.finrank ℂ ℋ), (hMherm.eigenvalues i) ^ p)
        = ∑ i : Fin (Module.finrank ℂ ℋ), (eVals i) ^ p :=
    sum_rpow_eq_of_multiset_map_eq (hMherm.eigenvalues) eVals p hrealMulti
  have hsumPowC :
      (((∑ i : Fin (Module.finrank ℂ ℋ), (hMherm.eigenvalues i) ^ p) : ℝ) : ℂ)
        = (((∑ i : Fin (Module.finrank ℂ ℋ), (eVals i) ^ p) : ℝ) : ℂ) := by
    exact congrArg (fun r : ℝ => (r : ℂ)) hsumPow
  calc
    Tr (CFC.rpow X p) = Matrix.trace (LinearMap.toMatrixOrthonormal bx (CFC.rpow X p)) :=
      tr_eq_matrix_trace_orthonormal bx (CFC.rpow X p)
    _ = Matrix.trace (CFC.rpow M p) := by
      exact (by
        have hmap := toMatrixOrthonormal_rpow bx X hX p hp
        simpa [M] using congrArg Matrix.trace hmap)
    _ = ∑ i : Fin (Module.finrank ℂ ℋ), (((hMherm.eigenvalues i) ^ p : ℝ) : ℂ) := by
      exact matrix_trace_rpow_eq_sum_eigenvalues M hMherm hMnonneg p
    _ = (((∑ i : Fin (Module.finrank ℂ ℋ), (hMherm.eigenvalues i) ^ p) : ℝ) : ℂ) := by
      simp
    _ = (((∑ i : Fin (Module.finrank ℂ ℋ), (eVals i) ^ p) : ℝ) : ℂ) := hsumPowC
    _ = ((((∑ i : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) : ℝ)) : ℂ) := by
      simp [eVals]

lemma overlap_coeff_nonneg {ℋ : Type u} [Qudit ℋ]
    (bx bY : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ) :
    ∀ i j, 0 ≤ ‖inner ℂ (bx i) (bY j)‖ ^ 2 := by
  intro i j
  positivity

lemma overlap_coeff_row_sum {ℋ : Type u} [Qudit ℋ]
    (bx bY : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ) :
    ∀ i, (∑ j, ‖inner ℂ (bx i) (bY j)‖ ^ 2) = 1 := by
  intro i
  simpa [bx.norm_eq_one i] using bY.sum_sq_norm_inner_left (x := bx i)

lemma overlap_coeff_col_sum {ℋ : Type u} [Qudit ℋ]
    (bx bY : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ) :
    ∀ j, (∑ i, ‖inner ℂ (bx i) (bY j)‖ ^ 2) = 1 := by
  intro j
  simpa [bY.norm_eq_one j] using bx.sum_sq_norm_inner_right (x := bY j)

lemma weighted_young_overlap {ℋ : Type u} [Qudit ℋ] {p q : ℝ} (hpq : p.HolderConjugate q)
    (bx bY : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (x y : Fin (Module.finrank ℂ ℋ) → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) :
    (∑ i, ∑ j, x i * y j * ‖inner ℂ (bx i) (bY j)‖ ^ 2)
      ≤ (∑ i, x i ^ p) / p + (∑ j, y j ^ q) / q := by
  simpa using
    weighted_young_finset p q hpq x y
      (fun i j => ‖inner ℂ (bx i) (bY j)‖ ^ 2)
      hx hy (overlap_coeff_nonneg bx bY)
      (overlap_coeff_row_sum bx bY) (overlap_coeff_col_sum bx bY)

lemma inner_apply_eq_sum_eigen_overlap {ℋ : Type u} [Qudit ℋ]
    (X : L ℋ) (hX : X.IsPositive)
    (bY : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (j : Fin (Module.finrank ℂ ℋ)) :
    inner ℂ (bY j) (X (bY j))
      = ∑ i : Fin (Module.finrank ℂ ℋ),
          ((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
            * Complex.normSq (inner ℂ
                (hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i) (bY j)) := by
  let bx := hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  calc
    inner ℂ (bY j) (X (bY j))
        = inner ℂ (bY j) (X (∑ i : Fin (Module.finrank ℂ ℋ), inner ℂ (bx i) (bY j) • bx i)) := by
      simp [bx.sum_repr']
    _ = inner ℂ (bY j) (∑ i : Fin (Module.finrank ℂ ℋ), inner ℂ (bx i) (bY j) • X (bx i)) := by
      simp [map_sum, map_smul]
    _ = ∑ i : Fin (Module.finrank ℂ ℋ), inner ℂ (bY j) (inner ℂ (bx i) (bY j) • X (bx i)) := by
      simp
    _ = ∑ i : Fin (Module.finrank ℂ ℋ),
          inner ℂ (bx i) (bY j)
            * (((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
              * inner ℂ (bY j) (bx i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hX.isSymmetric.apply_eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i]
      haveI : IsScalarTower ℝ ℂ ℋ := RestrictScalars.isScalarTower ℝ ℂ ℋ
      rw [inner_smul_right, inner_smul_right_eq_smul]
      congr 1
    _ = ∑ i : Fin (Module.finrank ℂ ℋ),
          ((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
            * Complex.normSq (inner ℂ (bx i) (bY j)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hconj : inner ℂ (bY j) (bx i) = (starRingEnd ℂ) (inner ℂ (bx i) (bY j)) := by
        simp
      rw [hconj, Complex.normSq_eq_conj_mul_self]
      ring

lemma trace_comp_eq_double_sum_eigen_overlap {ℋ : Type u} [Qudit ℋ]
    (X Y : L ℋ) (hX : X.IsPositive) (hY : Y.IsPositive) :
    Tr (X ∘ₗ Y)
      = ∑ j : Fin (Module.finrank ℂ ℋ),
          ((hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j : ℝ) : ℂ)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                ((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
                  * Complex.normSq (inner ℂ
                      (hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i)
                      (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl j))) := by
  calc
    Tr (X ∘ₗ Y)
        = ∑ j : Fin (Module.finrank ℂ ℋ),
            ((hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j : ℝ) : ℂ)
              * inner ℂ
                  (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl j)
                  (X (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl j)) := by
      simpa [Finset.sum_mul] using trace_comp_eq_sum_eigen_right X Y hY
    _ = ∑ j : Fin (Module.finrank ℂ ℋ),
          ((hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j : ℝ) : ℂ)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                ((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
                  * Complex.normSq (inner ℂ
                      (hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i)
                      (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl j))) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [inner_apply_eq_sum_eigen_overlap X hX
        (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl) j]

set_option backward.isDefEq.respectTransparency false in
theorem trace_young_inequality {ℋ : Type u} [Qudit ℋ] {p q : ℝ} (hpq : p.HolderConjugate q)
  (X Y : L ℋ) (hX : X.IsPositive) (hY : Y.IsPositive) :
  Tr (X ∘ₗ Y) ≤ Tr (CFC.rpow X p) / p + Tr (CFC.rpow Y q) / q := by
  let bx := hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  let bY := hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  have hdouble := trace_comp_eq_double_sum_eigen_overlap X Y hX hY
  have hXnonneg :
      ∀ i : Fin (Module.finrank ℂ ℋ),
        0 ≤ hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i := by
    intro i
    exact hX.nonneg_eigenvalues (hn := (rfl : Module.finrank ℂ ℋ = Module.finrank ℂ ℋ)) i
  have hYnonneg :
      ∀ j : Fin (Module.finrank ℂ ℋ),
        0 ≤ hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j := by
    intro j
    exact hY.nonneg_eigenvalues (hn := (rfl : Module.finrank ℂ ℋ = Module.finrank ℂ ℋ)) j
  have hYoung :=
    weighted_young_overlap hpq bx bY
      (fun i => hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
      (fun j => hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
      hXnonneg hYnonneg
  have hbound_double_real :
      (∑ j : Fin (Module.finrank ℂ ℋ),
          (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                  * Complex.normSq (inner ℂ (bx i) (bY j))))
        ≤ ((∑ i : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) / p : ℝ)
            + ((∑ j : Fin (Module.finrank ℂ ℋ),
              (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ q) / q : ℝ) := by
    calc
      (∑ j : Fin (Module.finrank ℂ ℋ),
          (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                  * Complex.normSq (inner ℂ (bx i) (bY j))))
          = ∑ i : Fin (Module.finrank ℂ ℋ), ∑ j : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                * (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
                * ‖inner ℂ (bx i) (bY j)‖ ^ 2 := by
            calc
              (∑ j : Fin (Module.finrank ℂ ℋ),
                  (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
                    * (∑ i : Fin (Module.finrank ℂ ℋ),
                        (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                          * Complex.normSq (inner ℂ (bx i) (bY j))))
                  = ∑ j : Fin (Module.finrank ℂ ℋ), ∑ i : Fin (Module.finrank ℂ ℋ),
                      (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
                        * ((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                          * Complex.normSq (inner ℂ (bx i) (bY j))) := by
                    simp [Finset.mul_sum]
              _ = ∑ i : Fin (Module.finrank ℂ ℋ), ∑ j : Fin (Module.finrank ℂ ℋ),
                    (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
                      * ((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                        * Complex.normSq (inner ℂ (bx i) (bY j))) := by
                    rw [Finset.sum_comm]
              _ = ∑ i : Fin (Module.finrank ℂ ℋ), ∑ j : Fin (Module.finrank ℂ ℋ),
                    (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                      * (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
                      * ‖inner ℂ (bx i) (bY j)‖ ^ 2 := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    simp [Complex.normSq_eq_norm_sq, mul_assoc, mul_left_comm]
      _ ≤ ((∑ i : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) / p : ℝ)
            + ((∑ j : Fin (Module.finrank ℂ ℋ),
              (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ q) / q : ℝ) := hYoung
  have hbound_double_complex :
      Tr (X ∘ₗ Y)
        ≤ ((((∑ i : Fin (Module.finrank ℂ ℋ),
                (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) / p : ℝ)
              + ((∑ j : Fin (Module.finrank ℂ ℋ),
                (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ q) / q : ℝ))
              : ℂ) := by
    rw [hdouble]
    exact_mod_cast hbound_double_real
  have hp_nonneg : 0 ≤ p := hpq.nonneg
  have hq_nonneg : 0 ≤ q := hpq.symm.nonneg
  have htraceX := trace_rpow_eq_sum_eigenvalues X hX p hp_nonneg
  have htraceY := trace_rpow_eq_sum_eigenvalues Y hY q hq_nonneg
  calc
    Tr (X ∘ₗ Y)
      ≤ ((((∑ i : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) / p : ℝ)
            + ((∑ j : Fin (Module.finrank ℂ ℋ),
              (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ q) / q : ℝ)) : ℂ) :=
      hbound_double_complex
    _ = Tr (CFC.rpow X p) / p + Tr (CFC.rpow Y q) / q := by
      rw [htraceX, htraceY]
      simp [div_eq_mul_inv, mul_comm]

section ReverseYoung

/-- Bernoulli inequality for non-positive exponents: t^r ≥ 1 + r*(t - 1) for t > 0, r ≤ 0.
    Proved via exp convexity (1+x ≤ exp x) and log ≤ id-1. -/
private lemma rpow_ge_one_add_mul {t : ℝ} (ht : 0 < t) {r : ℝ} (hr : r ≤ 0) :
    1 + r * (t - 1) ≤ t ^ r := by
  have h_log_le : Real.log t ≤ t - 1 := by
    have h := Real.add_one_le_exp (Real.log t)
    rw [Real.exp_log ht] at h; linarith
  have h_rpow : r * Real.log t + 1 ≤ t ^ r := by
    have h := Real.add_one_le_exp (r * Real.log t)
    have : Real.exp (r * Real.log t) = t ^ r := by
      rw [show r * Real.log t = Real.log t * r from mul_comm _ _]
      exact (Real.rpow_def_of_pos ht r).symm
    linarith
  linarith [mul_le_mul_of_nonpos_left h_log_le hr]

/-- Scalar reverse Young inequality for strictly positive reals:
    a^r/r + b^s/s ≤ a*b when r < 0, 0 < s < 1, 1/r + 1/s = 1. -/
lemma reverse_young_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {r s : ℝ} (hr : r < 0) (hs0 : 0 < s) (hs1 : s < 1)
    (hrs : 1 / r + 1 / s = 1) :
    a ^ r / r + b ^ s / s ≤ a * b := by
  have hbs_pos : 0 < b ^ (1 - s) := Real.rpow_pos_of_pos hb _
  have ht_pos : 0 < a * b ^ (1 - s) := mul_pos ha hbs_pos
  have hBern := rpow_ge_one_add_mul ht_pos hr.le
  have hexp : (1 - s) * r = -s := by
    have h1r : 1 / r = 1 - 1 / s := by linarith
    have hr0 : r ≠ 0 := ne_of_lt hr
    have hs0' : s ≠ 0 := ne_of_gt hs0
    field_simp at h1r; nlinarith
  have h_tr : (a * b ^ (1 - s)) ^ r = a ^ r * (b ^ s)⁻¹ := by
    calc (a * b ^ (1 - s)) ^ r
        = a ^ r * (b ^ (1 - s)) ^ r := Real.mul_rpow ha.le hbs_pos.le
      _ = a ^ r * b ^ ((1 - s) * r) := by rw [← Real.rpow_mul hb.le]
      _ = a ^ r * b ^ (-s) := by rw [hexp]
      _ = a ^ r * (b ^ s)⁻¹ := by rw [Real.rpow_neg hb.le]
  have hbs_val : 0 < b ^ s := Real.rpow_pos_of_pos hb _
  rw [h_tr] at hBern
  have hBern_mul : (1 + r * (a * b ^ (1 - s) - 1)) * b ^ s ≤ a ^ r := by
    rw [← div_eq_mul_inv] at hBern
    exact (le_div_iff₀ hbs_val).mp hBern
  have hbb : b ^ (1 - s) * b ^ s = b := by
    rw [← Real.rpow_add hb]; ring_nf; exact Real.rpow_one b
  have h_expanded : (1 - r) * b ^ s + r * (a * b) ≤ a ^ r := by
    have : a * b ^ (1 - s) * b ^ s = a * b := by rw [mul_assoc, hbb]
    nlinarith
  have h_1mr_s : (1 - r) * s = -r := by
    have h1r : 1 / r = 1 - 1 / s := by linarith
    have hr0 : r ≠ 0 := ne_of_lt hr
    have hs0' : s ≠ 0 := ne_of_gt hs0
    field_simp at h1r; nlinarith
  have hrs_neg : r * s < 0 := mul_neg_of_neg_of_pos hr hs0
  rw [div_add_div _ _ (ne_of_lt hr) (ne_of_gt hs0), div_le_iff_of_neg hrs_neg]
  nlinarith [h_1mr_s, h_expanded]

/-- Scalar reverse Young inequality for a > 0, b ≥ 0. -/
lemma reverse_young_of_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    {r s : ℝ} (hr : r < 0) (hs0 : 0 < s) (hs1 : s < 1)
    (hrs : 1 / r + 1 / s = 1) :
    a ^ r / r + b ^ s / s ≤ a * b := by
  rcases eq_or_lt_of_le hb with rfl | hb_pos
  · simp only [Real.zero_rpow (ne_of_gt hs0), zero_div, add_zero, mul_zero]
    exact div_nonpos_of_nonneg_of_nonpos (Real.rpow_pos_of_pos ha _).le hr.le
  · exact reverse_young_of_pos ha hb_pos hr hs0 hs1 hrs

/-- Weighted reverse Young inequality with doubly stochastic coefficients. -/
lemma weighted_reverse_young_finset {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r s : ℝ) (hr : r < 0) (hs0 : 0 < s) (hs1 : s < 1) (hrs : 1 / r + 1 / s = 1)
    (x : ι → ℝ) (y : κ → ℝ) (c : ι → κ → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 ≤ y j) (hc : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, (∑ j, c i j) = 1) (hcol : ∀ j, (∑ i, c i j) = 1) :
    (∑ i, x i ^ r) / r + (∑ j, y j ^ s) / s
      ≤ ∑ i, ∑ j, x i * y j * c i j := by
  calc
    (∑ i, x i ^ r) / r + (∑ j, y j ^ s) / s
        = (∑ i, x i ^ r / r) + (∑ j, y j ^ s / s) := by
      simp [Finset.sum_div]
    _ = (∑ i, x i ^ r / r * (∑ j, c i j)) +
        (∑ j, y j ^ s / s * (∑ i, c i j)) := by
      simp [hrow, hcol]
    _ = (∑ i, ∑ j, x i ^ r / r * c i j) +
        (∑ i, ∑ j, y j ^ s / s * c i j) := by
      congr 1
      · simp_rw [Finset.mul_sum]
      · simp_rw [Finset.mul_sum, Finset.sum_comm (f := fun j i => y j ^ s / s * c i j)]
    _ = ∑ i, ∑ j, (x i ^ r / r + y j ^ s / s) * c i j := by
      simp_rw [← Finset.sum_add_distrib, ← add_mul]
    _ ≤ ∑ i, ∑ j, x i * y j * c i j := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      exact mul_le_mul_of_nonneg_right
        (reverse_young_of_nonneg (hx i) (hy j) hr hs0 hs1 hrs) (hc i j)

lemma weighted_reverse_young_overlap {ℋ : Type u} [Qudit ℋ] {r s : ℝ}
    (hr : r < 0) (hs0 : 0 < s) (hs1 : s < 1) (hrs : 1 / r + 1 / s = 1)
    (bx bY : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (x y : Fin (Module.finrank ℂ ℋ) → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 ≤ y j) :
    (∑ i, x i ^ r) / r + (∑ j, y j ^ s) / s
      ≤ ∑ i, ∑ j, x i * y j * ‖inner ℂ (bx i) (bY j)‖ ^ 2 := by
  simpa using
    weighted_reverse_young_finset r s hr hs0 hs1 hrs x y
      (fun i j => ‖inner ℂ (bx i) (bY j)‖ ^ 2)
      hx hy (overlap_coeff_nonneg bx bY)
      (overlap_coeff_row_sum bx bY) (overlap_coeff_col_sum bx bY)

set_option backward.isDefEq.respectTransparency false in
/-- Matrix representation of rpow for positive definite operators (any exponent). -/
lemma toMatrixOrthonormal_rpow_pd {ℋ : Type u} [Qudit ℋ]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ) (X : L ℋ)
    (hX : X.IsPositive) (hX_unit : IsUnit X) (p : ℝ) :
    LinearMap.toMatrixOrthonormal b (CFC.rpow X p)
      = CFC.rpow (LinearMap.toMatrixOrthonormal b X) p := by
  by_cases hp : 0 ≤ p
  · exact toMatrixOrthonormal_rpow b X hX p hp
  · push_neg at hp
    have hXnonneg : 0 ≤ X := (LinearMap.nonneg_iff_isPositive X).2 hX
    have hXselfAdjoint : IsSelfAdjoint X := hX.isSelfAdjoint
    have hφ : Continuous (LinearMap.toMatrixOrthonormal b) :=
      (StarAlgEquiv.isometry (LinearMap.toMatrixOrthonormal b)).continuous
    have hφnonneg : 0 ≤ LinearMap.toMatrixOrthonormal b X :=
      map_nonneg (LinearMap.toMatrixOrthonormal b) hXnonneg
    have hφselfAdjoint : IsSelfAdjoint (LinearMap.toMatrixOrthonormal b X) :=
      IsSelfAdjoint.map hXselfAdjoint (LinearMap.toMatrixOrthonormal b)
    have h_spec_nn : spectrum ℝ X ⊆ Set.Ici 0 :=
      (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hXselfAdjoint)).1 hXnonneg
    have h0_not_mem : (0 : ℝ) ∉ spectrum ℝ X :=
      (spectrum.zero_notMem_iff (R := ℝ) (A := L ℋ)).mpr hX_unit
    have hf : ContinuousOn (fun x : ℝ => x ^ p) (spectrum ℝ X) :=
      ContinuousOn.rpow_const continuousOn_id fun x hx =>
        Or.inl (ne_of_gt (lt_of_le_of_ne
          (by simpa [Set.Ici] using h_spec_nn hx)
          (fun h => h0_not_mem (h ▸ hx))))
    rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow]
    rw [CFC.rpow_eq_cfc_real (a := X) (y := p) (ha := hXnonneg)]
    rw [CFC.rpow_eq_cfc_real (a := LinearMap.toMatrixOrthonormal b X)
        (y := p) (ha := hφnonneg)]
    simpa using
      (StarAlgHomClass.map_cfc (R := ℝ)
        (φ := LinearMap.toMatrixOrthonormal b)
        (f := fun x : ℝ => x ^ p)
        (a := X) (hf := hf) (hφ := hφ)
        (ha := hXselfAdjoint) (hφa := hφselfAdjoint))

/-- Strictly positive eigenvalues for positive definite operators. -/
lemma pos_eigenvalues_of_isPositive_isUnit {ℋ : Type u} [Qudit ℋ]
    (X : L ℋ) (hX : X.IsPositive) (hX_unit : IsUnit X) :
    ∀ i, 0 < hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i := by
  intro i
  have h_nn := hX.nonneg_eigenvalues (hn := rfl) i
  refine lt_of_le_of_ne h_nn (fun h => ?_)
  have h_eigvec := hX.isSymmetric.apply_eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i
  have h_ker : X (hX.isSymmetric.eigenvectorBasis rfl i) = 0 := by
    rw [h_eigvec]
    haveI : IsScalarTower ℝ ℂ ℋ := RestrictScalars.isScalarTower ℝ ℂ ℋ
    simp [← h, Algebra.algebraMap_eq_smul_one]
  have h_ne : hX.isSymmetric.eigenvectorBasis rfl i ≠ 0 :=
    (hX.isSymmetric.eigenvectorBasis rfl).toBasis.ne_zero i
  obtain ⟨u, hu⟩ := hX_unit
  have h_inj : Function.Injective X := by
    have : Function.LeftInverse (↑u⁻¹ : L ℋ) X := by
      intro x
      change (↑u⁻¹ * X) x = x
      rw [← hu, Units.inv_mul]
      rfl
    exact this.injective
  have h_ker' : X (hX.isSymmetric.eigenvectorBasis rfl i) = X 0 := by
    rw [h_ker, map_zero]
  exact absurd (h_inj h_ker') h_ne

set_option backward.isDefEq.respectTransparency false in
/-- Trace of rpow for pd operators as sum of eigenvalue powers (all exponents). -/
lemma trace_rpow_eq_sum_eigenvalues_pd {ℋ : Type u} [Qudit ℋ]
    (X : L ℋ) (hX : X.IsPositive) (hX_unit : IsUnit X) (p : ℝ) :
    Tr (CFC.rpow X p)
      = ((((∑ i : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) : ℝ)) : ℂ) := by
  by_cases hp : 0 ≤ p
  · exact trace_rpow_eq_sum_eigenvalues X hX p hp
  · push_neg at hp
    let bx := hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
    let eVals : Fin (Module.finrank ℂ ℋ) → ℝ :=
      fun i => hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i
    let M : Matrix (Fin (Module.finrank ℂ ℋ)) (Fin (Module.finrank ℂ ℋ)) ℂ :=
      LinearMap.toMatrixOrthonormal bx X
    have hXnonneg : 0 ≤ X := (LinearMap.nonneg_iff_isPositive X).2 hX
    have hMnonneg : 0 ≤ M := by
      simpa [M] using map_nonneg (LinearMap.toMatrixOrthonormal bx) hXnonneg
    have hMpsd : M.PosSemidef := (Matrix.nonneg_iff_posSemidef).1 hMnonneg
    have hMherm : M.IsHermitian := hMpsd.1
    have hrootsM :
        M.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hMherm.eigenvalues) Finset.univ.val :=
      hMherm.roots_charpoly_eq_eigenvalues
    have hrootsDiag :
        M.charpoly.roots = Multiset.map (RCLike.ofReal ∘ eVals) Finset.univ.val := by
      have hdiagM : M = Matrix.diagonal (fun i =>
        (((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) : ℝ) : ℂ)) := by
        simpa [M, eVals] using toMatrixOrthonormal_eq_diagonal_eigenvalues X hX
      rw [hdiagM, Matrix.charpoly_diagonal]
      have hroots :
          (Polynomial.roots
            (∏ i : Fin (Module.finrank ℂ ℋ),
              (Polynomial.X - Polynomial.C ((((eVals i) : ℝ) : ℂ))))
              ) = (Finset.univ.val.bind fun i : Fin (Module.finrank ℂ ℋ) =>
                  Polynomial.roots (Polynomial.X - Polynomial.C ((((eVals i) : ℝ) : ℂ)))) := by
        exact Polynomial.roots_prod
          (f := fun i : Fin (Module.finrank ℂ ℋ) =>
            (Polynomial.X - Polynomial.C ((((eVals i) : ℝ) : ℂ))))
          (s := Finset.univ)
          (Finset.prod_ne_zero_iff.mpr (by
            intro i hi
            exact Polynomial.X_sub_C_ne_zero _))
      rw [hroots]
      simp
    have hrealMulti :
        Multiset.map hMherm.eigenvalues Finset.univ.val = Multiset.map eVals Finset.univ.val := by
      have hrootsEq :
          Multiset.map ((fun x : ℝ => (x : ℂ)) ∘ hMherm.eigenvalues) Finset.univ.val
            = Multiset.map ((fun x : ℝ => (x : ℂ)) ∘ eVals) Finset.univ.val := by
        exact hrootsM.symm.trans hrootsDiag
      have hre := congrArg (Multiset.map Complex.re) hrootsEq
      simpa [Function.comp, eVals] using hre
    have hsumPow :
        (∑ i : Fin (Module.finrank ℂ ℋ), (hMherm.eigenvalues i) ^ p)
          = ∑ i : Fin (Module.finrank ℂ ℋ), (eVals i) ^ p :=
      sum_rpow_eq_of_multiset_map_eq (hMherm.eigenvalues) eVals p hrealMulti
    have hsumPowC :
        (((∑ i : Fin (Module.finrank ℂ ℋ), (hMherm.eigenvalues i) ^ p) : ℝ) : ℂ)
          = (((∑ i : Fin (Module.finrank ℂ ℋ), (eVals i) ^ p) : ℝ) : ℂ) := by
      exact congrArg (fun r : ℝ => (r : ℂ)) hsumPow
    calc
      Tr (CFC.rpow X p) = Matrix.trace (LinearMap.toMatrixOrthonormal bx (CFC.rpow X p)) :=
        tr_eq_matrix_trace_orthonormal bx (CFC.rpow X p)
      _ = Matrix.trace (CFC.rpow M p) := by
        exact (by
          have hmap := toMatrixOrthonormal_rpow_pd bx X hX hX_unit p
          simpa [M] using congrArg Matrix.trace hmap)
      _ = ∑ i : Fin (Module.finrank ℂ ℋ), (((hMherm.eigenvalues i) ^ p : ℝ) : ℂ) := by
        exact matrix_trace_rpow_eq_sum_eigenvalues M hMherm hMnonneg p
      _ = (((∑ i : Fin (Module.finrank ℂ ℋ), (hMherm.eigenvalues i) ^ p) : ℝ) : ℂ) := by
        simp
      _ = (((∑ i : Fin (Module.finrank ℂ ℋ), (eVals i) ^ p) : ℝ) : ℂ) := hsumPowC
      _ = ((((∑ i : Fin (Module.finrank ℂ ℋ),
                (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) : ℝ)) : ℂ) := by
        simp [eVals]

set_option backward.isDefEq.respectTransparency false in
/-- Reverse trace Young inequality: for r < 0, s ∈ (0, 1), 1/r + 1/s = 1,
    M positive definite, N positive semidefinite:
    Tr(M^r)/r + Tr(N^s)/s ≤ Tr(M ∘ₗ N). -/
theorem trace_reverse_young_inequality {ℋ : Type u} [Qudit ℋ] {r s : ℝ}
    (hr : r < 0) (hs0 : 0 < s) (hs1 : s < 1) (hrs : 1 / r + 1 / s = 1)
    (M N : L ℋ) (hM : M.IsPositive) (hM_unit : IsUnit M) (hN : N.IsPositive) :
    Tr (CFC.rpow M r) / r + Tr (CFC.rpow N s) / s ≤ Tr (M ∘ₗ N) := by
  let bM := hM.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  let bN := hN.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  have hdouble := trace_comp_eq_double_sum_eigen_overlap M N hM hN
  have hMpos :
      ∀ i : Fin (Module.finrank ℂ ℋ),
        0 < hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i :=
    pos_eigenvalues_of_isPositive_isUnit M hM hM_unit
  have hNnonneg :
      ∀ j : Fin (Module.finrank ℂ ℋ),
        0 ≤ hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j := by
    intro j
    exact hN.nonneg_eigenvalues (hn := rfl) j
  have hRevYoung :=
    weighted_reverse_young_overlap hr hs0 hs1 hrs bM bN
      (fun i => hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
      (fun j => hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
      hMpos hNnonneg
  have hbound_double_real :
      ((∑ i : Fin (Module.finrank ℂ ℋ),
            (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ r) / r : ℝ)
          + ((∑ j : Fin (Module.finrank ℂ ℋ),
            (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ s) / s : ℝ)
        ≤ (∑ j : Fin (Module.finrank ℂ ℋ),
          (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                  * Complex.normSq (inner ℂ (bM i) (bN j)))) := by
    calc
      ((∑ i : Fin (Module.finrank ℂ ℋ),
            (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ r) / r : ℝ)
          + ((∑ j : Fin (Module.finrank ℂ ℋ),
            (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ s) / s : ℝ)
        ≤ ∑ i : Fin (Module.finrank ℂ ℋ), ∑ j : Fin (Module.finrank ℂ ℋ),
            (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
              * (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
              * ‖inner ℂ (bM i) (bN j)‖ ^ 2 := hRevYoung
      _ = ∑ j : Fin (Module.finrank ℂ ℋ), ∑ i : Fin (Module.finrank ℂ ℋ),
            (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
              * (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
              * ‖inner ℂ (bM i) (bN j)‖ ^ 2 := Finset.sum_comm
      _ = ∑ j : Fin (Module.finrank ℂ ℋ),
          (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                  * Complex.normSq (inner ℂ (bM i) (bN j))) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [Complex.normSq_eq_norm_sq, mul_assoc, mul_left_comm]
  have hbound_double_complex :
      Tr (CFC.rpow M r) / r + Tr (CFC.rpow N s) / s
        ≤ Tr (M ∘ₗ N) := by
    rw [hdouble]
    have htraceM := trace_rpow_eq_sum_eigenvalues_pd M hM hM_unit r
    have hs_nonneg : 0 ≤ s := hs0.le
    have htraceN := trace_rpow_eq_sum_eigenvalues N hN s hs_nonneg
    rw [htraceM, htraceN]
    exact_mod_cast hbound_double_real
  exact hbound_double_complex

end ReverseYoung
