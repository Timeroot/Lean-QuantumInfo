/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.System
public import QuantumLib.QIT.Util.Matrix
public import QuantumInfo.States.Mixed.MState

/-!
# Finite-dimensional states

A density state is `MState`: a positive unit-trace operator on a finite-dimensional Hilbert space,
here the one whose preferred orthonormal basis is indexed by the system label type. `DensityOp.m`
is its density matrix in that basis, `DensityOp.psd` and `DensityOp.tr'` the two conditions it
satisfies, and `MState.ofMatrix` builds a state from a matrix satisfying them.

Product states are represented by Kronecker products, matching tensor-product
state notation in the source material [Tomamichel2015FiniteResources,
prelim.tex:38-43], product-state usage in [Wilde2011Qst,
qit-notes.tex:7294-7299], and IID factorization in [Wilde2011Qst,
qit-notes.tex:1888-1920].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

noncomputable section
universe u v w

open QIT

namespace MState

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A positive semidefinite matrix as a `HermitianMat`. -/
def hermitianMatOfPSD (M : CMatrix a) (hM : M.PosSemidef) : HermitianMat a ℂ :=
  ⟨M, hM.isHermitian⟩

omit [Fintype a] [DecidableEq a] in
@[simp]
theorem mat_hermitianMatOfPSD (M : CMatrix a) (hM : M.PosSemidef) :
    (hermitianMatOfPSD M hM).mat = M :=
  rfl

/-- The state with a given density matrix. -/
def ofMatrix (matrix : CMatrix a) (pos : matrix.PosSemidef) (trace_eq_one : matrix.trace = 1) :
    MState a :=
  DensityOp.ofMat (hermitianMatOfPSD matrix pos) (HermitianMat.zero_le_iff.mpr pos)
    (by
      rw [HermitianMat.trace_eq_re_trace, mat_hermitianMatOfPSD, trace_eq_one]
      norm_num)

@[simp]
theorem matrix_ofMatrix (M : CMatrix a) (hM : M.PosSemidef) (htr : M.trace = 1) :
    (ofMatrix M hM htr).m = M := by
  rw [ofMatrix, DensityOp.m_ofMat]
  rfl

/-- Density states are equal when their matrices are equal. -/
@[ext]
theorem ext {rho sigma : MState a} (h : rho.m = sigma.m) : rho = sigma :=
  DensityOp.ext_m h

@[simp]
theorem ofMatrix_matrix (rho : MState a) :
    ofMatrix rho.m rho.psd rho.tr' = rho :=
  ext (by simp)

theorem trace_re_eq_one (rho : MState a) : rho.m.trace.re = 1 := by
  rw [rho.tr']
  norm_num

theorem trace_re_pos (rho : MState a) : 0 < rho.m.trace.re := by
  rw [rho.trace_re_eq_one]
  norm_num

theorem trace_re_ne_zero (rho : MState a) : rho.m.trace.re ≠ 0 :=
  rho.trace_re_pos.ne'

/-- Every normalized finite-dimensional state is bounded above by the identity operator. -/
theorem matrix_le_one (rho : MState a) : rho.m ≤ 1 :=
  Matrix.le_iff.mpr (HermitianMat.le_iff.mp rho.le_one)

/-- A normalized quantum state has a nonzero density matrix. -/
theorem matrix_ne_zero (rho : MState a) : rho.m ≠ 0 := by
  intro hzero
  have htrace : rho.m.trace = 0 := by simp [hzero]
  rw [rho.tr'] at htrace
  norm_num at htrace

/-- A system with a single label carries only one state. -/
theorem eq_of_subsingleton [Subsingleton a] (rho sigma : MState a) : rho = sigma := by
  obtain ⟨i0⟩ := rho.nonempty
  have : Unique a := ⟨⟨i0⟩, fun _ => Subsingleton.elim _ _⟩
  have h : ∀ tau : MState a, ∀ i j : a, tau.m i j = 1 := by
    intro tau i j
    have htr := tau.tr'
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    simpa [Matrix.trace] using htr
  ext i j
  rw [h rho i j, h sigma i j]

omit [DecidableEq a] in
theorem posSemidef_trace_ne_zero_of_ne_zero
    {M : CMatrix a} (hM : M.PosSemidef) (hM_ne : M ≠ 0) :
    M.trace.re ≠ 0 := by
  intro htrace_re
  have htrace : M.trace = 0 := by
    apply Complex.ext
    · exact htrace_re
    · exact (Matrix.PosSemidef.trace_nonneg hM).2.symm
  exact hM_ne ((Matrix.PosSemidef.trace_eq_zero_iff hM).mp htrace)

omit [DecidableEq a] in
theorem posSemidef_trace_pos_of_ne_zero
    {M : CMatrix a} (hM : M.PosSemidef) (hM_ne : M ≠ 0) :
    0 < M.trace.re :=
  lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hM).1
    (posSemidef_trace_ne_zero_of_ne_zero hM hM_ne).symm

/-- Normalize a positive semidefinite matrix with nonzero trace. -/
def normalizePSD (M : CMatrix a) (hM : M.PosSemidef) (htr_ne : M.trace.re ≠ 0) :
    MState a := .ofMatrix
  (matrix := (M.trace.re)⁻¹ • M)
  (pos := Matrix.PosSemidef.smul hM (by
    have htr_pos : 0 < M.trace.re :=
      lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hM).1 htr_ne.symm
    exact_mod_cast inv_nonneg.mpr htr_pos.le))
  (trace_eq_one := by
    rw [Matrix.trace_smul]
    have htrace_im : M.trace.im = 0 := (Matrix.PosSemidef.trace_nonneg hM).2.symm
    apply Complex.ext
    · simp [Complex.real_smul, htr_ne]
    · simp [Complex.real_smul, htrace_im])

@[simp]
theorem normalizePSD_matrix (M : CMatrix a) (hM : M.PosSemidef)
    (htr_ne : M.trace.re ≠ 0) :
    (normalizePSD M hM htr_ne).m = (M.trace.re)⁻¹ • M :=
  matrix_ofMatrix _ _ _

theorem normalizePSD_self (rho : MState a) :
    normalizePSD rho.m rho.psd rho.trace_re_ne_zero = rho := by
  ext i j
  simp [normalizePSD]

/-- The unique density state on the unit system. -/
def unit : MState PUnit := .ofMatrix
  (matrix := 1)
  (pos := Matrix.PosSemidef.one)
  (trace_eq_one := by
    rw [Matrix.trace_one]
    norm_num)

@[simp]
theorem unit_matrix : unit.m = (1 : CMatrix PUnit) :=
  matrix_ofMatrix _ _ _

/-- Relabel a density state along a finite basis equivalence. -/
def reindex {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (rho : MState α) (e : α ≃ β) : MState β :=
  rho.relabel e.symm

@[simp]
theorem reindex_matrix {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (rho : MState α) (e : α ≃ β) :
    (rho.reindex e).m = rho.m.submatrix e.symm e.symm :=
  MState.relabel_m rho e.symm

/-- Reindexing along `e` is relabelling along `e.symm`. -/
theorem reindex_eq_relabel {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (rho : MState α) (e : α ≃ β) :
    rho.reindex e = rho.relabel e.symm :=
  rfl

@[simp]
theorem reindex_refl (rho : MState a) :
    rho.reindex (Equiv.refl a) = rho := by
  ext i j
  simp

/-- Reindexing along `e` and then along `e.symm` returns the original state. -/
theorem reindex_reindex_symm {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (rho : MState α) (e : α ≃ β) :
    (rho.reindex e).reindex e.symm = rho := by
  ext i j
  simp

/-- Reindexing along `e.symm` and then along `e` returns the original state. -/
theorem reindex_symm_reindex {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (rho : MState β) (e : α ≃ β) :
    (rho.reindex e.symm).reindex e = rho := by
  ext i j
  simp

/-- The matrix `I_A ⊗ σ_B`, the state-level building block used by the conditional entropy
definitions. -/
def identityTensorStateMatrix (sigma : MState b) : CMatrix (a × b) :=
  Matrix.kronecker (1 : CMatrix a) sigma.m

/-- The matrix `I_A ⊗ σ_B` is positive semidefinite. -/
theorem identityTensorStateMatrix_posSemidef (sigma : MState b) :
    (identityTensorStateMatrix (a := a) sigma).PosSemidef := by
  change (Matrix.kronecker (1 : CMatrix a) sigma.m).PosSemidef
  exact Matrix.PosSemidef.one.kronecker sigma.psd

/-- `Tr_A (rho_A tensor sigma_B) = sigma_B`. -/
theorem traceLeft_prod (rho : MState a) (sigma : MState b) :
    Matrix.traceLeft (rho.prod sigma).m = sigma.m := by
  rw [← MState.traceLeft_m, MState.traceLeft_prod_eq]

/-- `Tr_B (rho_A tensor sigma_B) = rho_A`. -/
theorem traceRight_prod (rho : MState a) (sigma : MState b) :
    Matrix.traceRight (rho.prod sigma).m = rho.m := by
  rw [← MState.traceRight_m, MState.traceRight_prod_eq]

/-- Positive definiteness is preserved by relabeling the basis of a state. -/
theorem reindex_posDef (rho : MState a) (e : a ≃ b) (h : rho.m.PosDef) :
    (rho.reindex e).m.PosDef := by
  rw [MState.reindex_matrix]
  exact h.submatrix e.symm.injective

/-- The marginal on the second subsystem of a positive definite bipartite state
is positive definite. -/
theorem traceLeft_posDef_of_posDef (rho : MState (a × b)) (h : rho.m.PosDef) :
    rho.traceLeft.m.PosDef := by
  let : Nonempty a := by
    rcases rho.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  simpa [MState.traceLeft_m] using
    QIT.traceLeft_posDef_of_posDef (a := a) (b := b) (M := rho.m) h

/-- The marginal on the first subsystem of a positive definite bipartite state
is positive definite. -/
theorem traceRight_posDef_of_posDef (rho : MState (a × b)) (h : rho.m.PosDef) :
    rho.traceRight.m.PosDef := by
  let rhoBA : MState (b × a) := rho.reindex (Equiv.prodComm a b)
  have hrhoBA : rhoBA.m.PosDef := by
    simpa [rhoBA] using reindex_posDef rho (Equiv.prodComm a b) h
  have hmarg : rho.traceRight = rhoBA.traceLeft := by
    apply MState.ext
    ext i j
    simp [rhoBA, Matrix.traceLeft, Matrix.traceRight]
  rw [hmarg]
  exact traceLeft_posDef_of_posDef rhoBA hrhoBA

theorem traceRight_reindex_prodCongr {α : Type u} {β : Type v} {γ : Type w} {δ : Type _}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (ρ : MState (α × γ)) (e : α ≃ β) (f : γ ≃ δ) :
    (ρ.reindex (Equiv.prodCongr e f)).traceRight = ρ.traceRight.reindex e := by
  apply MState.ext
  ext i j
  simp [MState.reindex_matrix, Matrix.traceRight]
  apply Fintype.sum_equiv f.symm
  intro x
  rfl

variable [Fintype c] [DecidableEq c]

/-- Marginal state on `AB` from a left-associated tripartite state `ABC`. -/
def marginalAB (rho : MState ((a × b) × c)) : MState (a × b) :=
  MState.traceRight rho

/-- Marginal state on `BC` from a left-associated tripartite state `ABC`. -/
def marginalBC (rho : MState ((a × b) × c)) : MState (b × c) := .ofMatrix
  (matrix := fun bc bc' =>
    Finset.univ.sum fun i : a => rho.m ((i, bc.1), bc.2) ((i, bc'.1), bc'.2))
  (pos := by
    have heq : (fun bc bc' : b × c =>
          ∑ i : a, rho.m ((i, bc.1), bc.2) ((i, bc'.1), bc'.2)) =
        ∑ i : a, rho.m.submatrix
          (fun bc : b × c => ((i, bc.1), bc.2))
          (fun bc : b × c => ((i, bc.1), bc.2)) := by
      ext bc bc'
      simp [Matrix.sum_apply]
    rw [heq]
    exact Matrix.posSemidef_sum _ fun i _ => rho.psd.submatrix _)
  (trace_eq_one := by
    rw [← rho.tr']
    rw [Matrix.trace]
    change
      (∑ bc : b × c, ∑ i : a,
        rho.m ((i, bc.1), bc.2) ((i, bc.1), bc.2)) =
      ∑ x : (a × b) × c, rho.m x x
    calc
      (∑ bc : b × c, ∑ i : a,
          rho.m ((i, bc.1), bc.2) ((i, bc.1), bc.2)) =
          ∑ i : a, ∑ bc : b × c,
            rho.m ((i, bc.1), bc.2) ((i, bc.1), bc.2) := by
        rw [Finset.sum_comm]
      _ = ∑ x : (a × b) × c, rho.m x x := by
        simp [Fintype.sum_prod_type])

/-- Marginal state on `AC` from a left-associated tripartite state `ABC`. -/
def marginalAC (rho : MState ((a × b) × c)) : MState (a × c) := .ofMatrix
  (matrix := Matrix.of fun ac ac' =>
    Finset.univ.sum fun j : b => rho.m ((ac.1, j), ac.2) ((ac'.1, j), ac'.2))
  (pos := by
    have heq : (fun ac ac' : a × c =>
          ∑ j : b, rho.m ((ac.1, j), ac.2) ((ac'.1, j), ac'.2)) =
        ∑ j : b, rho.m.submatrix
          (fun ac : a × c => ((ac.1, j), ac.2))
          (fun ac : a × c => ((ac.1, j), ac.2)) := by
      ext ac ac'
      simp [Matrix.sum_apply]
    rw [heq]
    exact Matrix.posSemidef_sum _ fun j _ => rho.psd.submatrix _)
  (trace_eq_one := by
    rw [← rho.tr']
    rw [Matrix.trace]
    change
      (∑ ac : a × c, ∑ j : b,
        rho.m ((ac.1, j), ac.2) ((ac.1, j), ac.2)) =
      ∑ x : (a × b) × c, rho.m x x
    calc
      (∑ ac : a × c, ∑ j : b,
          rho.m ((ac.1, j), ac.2) ((ac.1, j), ac.2)) =
          ∑ j : b, ∑ ac : a × c,
            rho.m ((ac.1, j), ac.2) ((ac.1, j), ac.2) := by
        rw [Finset.sum_comm]
      _ = ∑ x : (a × b) × c, rho.m x x := by
        simp [Fintype.sum_prod_type]
        rw [Finset.sum_comm])

/-- Marginal state on `B` from a left-associated tripartite state `ABC`. -/
def marginalBOfABC (rho : MState ((a × b) × c)) : MState b :=
  rho.marginalAB.traceLeft

@[simp]
theorem marginalAB_eq_traceRight (rho : MState ((a × b) × c)) :
    rho.marginalAB = rho.traceRight := rfl

@[simp]
theorem marginalBOfABC_eq (rho : MState ((a × b) × c)) :
    rho.marginalBOfABC = rho.marginalAB.traceLeft := rfl

@[simp]
theorem marginalBC_matrix (rho : MState ((a × b) × c)) :
    rho.marginalBC.m =
      fun bc bc' =>
        Finset.univ.sum fun i : a =>
          rho.m ((i, bc.1), bc.2) ((i, bc'.1), bc'.2) :=
  matrix_ofMatrix _ _ _

@[simp]
theorem marginalAC_matrix (rho : MState ((a × b) × c)) :
    rho.marginalAC.m =
      Matrix.of fun ac ac' =>
        Finset.univ.sum fun j : b =>
          rho.m ((ac.1, j), ac.2) ((ac'.1, j), ac'.2) :=
  matrix_ofMatrix _ _ _

/-- Tracing the `AC` marginal down to `C` agrees with the direct `C` marginal
of a left-associated tripartite state. -/
theorem marginalAC_traceLeft_eq_traceLeft (rho : MState ((a × b) × c)) :
    rho.marginalAC.traceLeft = rho.traceLeft := by
  apply MState.ext
  ext x y
  simp [MState.marginalAC, Matrix.traceLeft, Fintype.sum_prod_type]

/-- Reading `(A ⊗ B) ⊗ C` as `(A ⊗ C) ⊗ B` turns the `AB` marginal into the
`AC` marginal. -/
theorem prodABCToACB_marginalAB (rho : MState ((a × b) × c)) :
    (rho.reindex (prodABCToACBEquiv a b c)).marginalAB =
      rho.marginalAC := by
  apply MState.ext
  ext ac ac'
  simp [MState.marginalAB, MState.marginalAC, prodABCToACBEquiv, Matrix.traceRight]

/-- Reading `(A ⊗ B) ⊗ C` as `(A ⊗ C) ⊗ B` turns the `AC` marginal into the
`AB` marginal. -/
theorem prodABCToACB_marginalAC (rho : MState ((a × b) × c)) :
    (rho.reindex (prodABCToACBEquiv a b c)).marginalAC =
      rho.marginalAB := by
  apply MState.ext
  ext ab ab'
  simp [MState.marginalAB, MState.marginalAC, prodABCToACBEquiv, Matrix.traceRight]

/-- Reading `(A ⊗ B) ⊗ C` as `(A ⊗ C) ⊗ B` swaps the two factors of the `BC`
marginal. -/
theorem prodABCToACB_marginalBC (rho : MState ((a × b) × c)) :
    (rho.reindex (prodABCToACBEquiv a b c)).marginalBC =
      rho.marginalBC.reindex (Equiv.prodComm b c) := by
  apply MState.ext
  ext cb cb'
  simp [MState.marginalBC_matrix, MState.reindex_matrix, prodABCToACBEquiv, Equiv.prodComm,
    Matrix.submatrix, Matrix.of_apply]

/-- Reading `(A ⊗ B) ⊗ C` as `(A ⊗ C) ⊗ B` turns the middle-system marginal
into the `C` marginal. -/
theorem prodABCToACB_marginalBOfABC (rho : MState ((a × b) × c)) :
    (rho.reindex (prodABCToACBEquiv a b c)).marginalBOfABC =
      rho.traceLeft := by
  apply MState.ext
  ext k k'
  simp [MState.marginalBOfABC, MState.marginalAB, prodABCToACBEquiv, Matrix.traceLeft,
    Matrix.traceRight, Fintype.sum_prod_type]

/-- Reading `(A ⊗ B) ⊗ C` as `(A ⊗ C) ⊗ B` turns the state on the last system
into the middle-system marginal. -/
theorem prodABCToACB_traceLeft (rho : MState ((a × b) × c)) :
    (rho.reindex (prodABCToACBEquiv a b c)).traceLeft =
      rho.marginalBOfABC := by
  apply MState.ext
  ext j j'
  simp [MState.marginalBOfABC, MState.marginalAB, prodABCToACBEquiv, Matrix.traceLeft,
    Matrix.traceRight, Fintype.sum_prod_type]

/-- IID tensor power of a density state. -/
def tensorPower (rho : MState a) : (n : ℕ) → MState (TensorPower a n)
  | 0 => unit
  | n + 1 => rho.prod (tensorPower rho n)

/-- The zeroth tensor power is the unit-system state. -/
theorem tensorPower_zero (rho : MState a) :
    tensorPower rho 0 = unit := rfl

/-- Successor tensor powers unfold as a product with one more IID factor. -/
theorem tensorPower_succ (rho : MState a) (n : ℕ) :
    tensorPower rho (n + 1) = rho.prod (tensorPower rho n) := rfl

@[simp]
theorem tensorPower_zero_matrix (rho : MState a) :
    (rho.tensorPower 0).m = (1 : CMatrix (TensorPower a 0)) :=
  unit_matrix

@[simp]
theorem tensorPower_succ_matrix (rho : MState a) (n : ℕ) :
    (rho.tensorPower (n + 1)).m =
      Matrix.kronecker rho.m (rho.tensorPower n).m :=
  MState.prod_m rho (rho.tensorPower n)

/-- IID tensor powers of a positive-definite state are positive-definite. -/
theorem tensorPower_posDef {rho : MState a} (h : rho.m.PosDef) (n : ℕ) :
    (rho.tensorPower n).m.PosDef := by
  induction n with
  | zero =>
      rw [tensorPower_zero_matrix]
      exact Matrix.PosDef.one
  | succ n ih =>
      rw [tensorPower_succ]
      exact PosDef.kron h ih

/-- IID tensor power of a bipartite state, read as `A^n × B^n`.

The underlying matrix is the ordinary IID tensor power of the `AB` state,
transported across `tensorPowerProdEquiv`.
-/
def tensorPowerBipartite (rho : MState (a × b)) (n : ℕ) :
    MState (TensorPower a n × TensorPower b n) :=
  (rho.tensorPower n).reindex (tensorPowerProdEquiv a b n)

@[simp]
theorem tensorPowerBipartite_matrix (rho : MState (a × b)) (n : ℕ) :
    (rho.tensorPowerBipartite n).m =
      (rho.tensorPower n).m.submatrix
        (tensorPowerProdEquiv a b n).symm
        (tensorPowerProdEquiv a b n).symm := by
  rw [tensorPowerBipartite, reindex_matrix]

theorem tensorPowerBipartite_traceRight_matrix (rho : MState (a × b)) (n : ℕ) :
    (rho.tensorPowerBipartite n).traceRight.m =
      Matrix.traceRight
        ((rho.tensorPower n).m.submatrix
          (tensorPowerProdEquiv a b n).symm
          (tensorPowerProdEquiv a b n).symm) := by
  rw [MState.traceRight_m, tensorPowerBipartite_matrix]

theorem tensorPowerBipartite_traceLeft_matrix (rho : MState (a × b)) (n : ℕ) :
    (rho.tensorPowerBipartite n).traceLeft.m =
      Matrix.traceLeft
        ((rho.tensorPower n).m.submatrix
          (tensorPowerProdEquiv a b n).symm
          (tensorPowerProdEquiv a b n).symm) := by
  rw [MState.traceLeft_m, tensorPowerBipartite_matrix]

/-- The `A^n` marginal of the IID bipartite tensor power is the IID tensor
power of the `A` marginal. -/
theorem tensorPowerBipartite_traceRight (rho : MState (a × b)) :
    (n : ℕ) → (rho.tensorPowerBipartite n).traceRight =
      (rho.traceRight).tensorPower n
  | 0 =>
      have : Subsingleton (TensorPower a 0) := inferInstanceAs (Subsingleton PUnit)
      eq_of_subsingleton _ _
  | n + 1 => by
      apply MState.ext
      rw [tensorPowerBipartite_traceRight_matrix, tensorPower_succ_matrix,
        tensorPower_succ_matrix]
      ext x y
      cases x with
      | mk x0 xs =>
          cases y with
          | mk y0 ys =>
              have hih := congrArg (fun σ : MState (TensorPower a n) => σ.m xs ys)
                (tensorPowerBipartite_traceRight rho n)
              simp [Matrix.traceRight] at hih
              simp [tensorPowerProdEquiv, Matrix.traceRight, Matrix.kronecker,
                Matrix.kroneckerMap_apply]
              calc
                (∑ x : b × TensorPower b n,
                    rho.m (x0, x.1) (y0, x.1) *
                      (rho.tensorPower n).m
                        ((tensorPowerProdEquiv a b n).symm (xs, x.2))
                        ((tensorPowerProdEquiv a b n).symm (ys, x.2))) =
                    ∑ i : b, ∑ rest : TensorPower b n,
                      rho.m (x0, i) (y0, i) *
                        (rho.tensorPower n).m
                          ((tensorPowerProdEquiv a b n).symm (xs, rest))
                          ((tensorPowerProdEquiv a b n).symm (ys, rest)) := by
                  simp [Fintype.sum_prod_type]
                _ = ∑ i : b,
                    rho.m (x0, i) (y0, i) *
                      (∑ rest : TensorPower b n,
                        (rho.tensorPower n).m
                          ((tensorPowerProdEquiv a b n).symm (xs, rest))
                          ((tensorPowerProdEquiv a b n).symm (ys, rest))) := by
                  simp [Finset.mul_sum]
                _ = ∑ i : b,
                    rho.m (x0, i) (y0, i) *
                      ((rho.traceRight).tensorPower n).m xs ys := by
                  simp [hih]
                _ = (∑ i : b, rho.m (x0, i) (y0, i)) *
                      ((rho.traceRight).tensorPower n).m xs ys := by
                  simpa using (Finset.sum_mul Finset.univ
                    (fun i : b => rho.m (x0, i) (y0, i))
                    (((rho.traceRight).tensorPower n).m xs ys)).symm

/-- The `B^n` marginal of the IID bipartite tensor power is the IID tensor
power of the `B` marginal. -/
theorem tensorPowerBipartite_traceLeft (rho : MState (a × b)) :
    (n : ℕ) → (rho.tensorPowerBipartite n).traceLeft =
      (rho.traceLeft).tensorPower n
  | 0 =>
      have : Subsingleton (TensorPower b 0) := inferInstanceAs (Subsingleton PUnit)
      eq_of_subsingleton _ _
  | n + 1 => by
      apply MState.ext
      rw [tensorPowerBipartite_traceLeft_matrix, tensorPower_succ_matrix,
        tensorPower_succ_matrix]
      ext x y
      cases x with
      | mk x0 xs =>
          cases y with
          | mk y0 ys =>
              have hih := congrArg (fun σ : MState (TensorPower b n) => σ.m xs ys)
                (tensorPowerBipartite_traceLeft rho n)
              simp [Matrix.traceLeft] at hih
              simp [tensorPowerProdEquiv, Matrix.traceLeft, Matrix.kronecker,
                Matrix.kroneckerMap_apply]
              calc
                (∑ x : a × TensorPower a n,
                    rho.m (x.1, x0) (x.1, y0) *
                      (rho.tensorPower n).m
                        ((tensorPowerProdEquiv a b n).symm (x.2, xs))
                        ((tensorPowerProdEquiv a b n).symm (x.2, ys))) =
                    ∑ i : a, ∑ rest : TensorPower a n,
                      rho.m (i, x0) (i, y0) *
                        (rho.tensorPower n).m
                          ((tensorPowerProdEquiv a b n).symm (rest, xs))
                          ((tensorPowerProdEquiv a b n).symm (rest, ys)) := by
                  simp [Fintype.sum_prod_type]
                _ = ∑ i : a,
                    rho.m (i, x0) (i, y0) *
                      (∑ rest : TensorPower a n,
                        (rho.tensorPower n).m
                          ((tensorPowerProdEquiv a b n).symm (rest, xs))
                          ((tensorPowerProdEquiv a b n).symm (rest, ys))) := by
                  simp [Finset.mul_sum]
                _ = ∑ i : a,
                    rho.m (i, x0) (i, y0) *
                      ((rho.traceLeft).tensorPower n).m xs ys := by
                  simp [hih]
                _ = (∑ i : a, rho.m (i, x0) (i, y0)) *
                      ((rho.traceLeft).tensorPower n).m xs ys := by
                  simpa using (Finset.sum_mul Finset.univ
                    (fun i : a => rho.m (i, x0) (i, y0))
                    (((rho.traceLeft).tensorPower n).m xs ys)).symm

/-- The IID bipartite tensor power of a positive-definite state is
positive-definite. -/
theorem tensorPowerBipartite_posDef (rho : MState (a × b)) (h : rho.m.PosDef) (n : ℕ) :
    (rho.tensorPowerBipartite n).m.PosDef := by
  unfold tensorPowerBipartite
  exact reindex_posDef (rho.tensorPower n) (tensorPowerProdEquiv a b n)
    (tensorPower_posDef h n)

/-- The `A^n` marginal of the IID bipartite tensor power is positive-definite
whenever the `A` marginal is. -/
theorem tensorPowerBipartite_traceRight_posDef (rho : MState (a × b))
    (hA : rho.traceRight.m.PosDef) (n : ℕ) :
    (rho.tensorPowerBipartite n).traceRight.m.PosDef := by
  rw [rho.tensorPowerBipartite_traceRight n]
  exact tensorPower_posDef hA n

/-- The `B^n` marginal of the IID bipartite tensor power is positive-definite
whenever the `B` marginal is. -/
theorem tensorPowerBipartite_traceLeft_posDef (rho : MState (a × b))
    (hB : rho.traceLeft.m.PosDef) (n : ℕ) :
    (rho.tensorPowerBipartite n).traceLeft.m.PosDef := by
  rw [rho.tensorPowerBipartite_traceLeft n]
  exact tensorPower_posDef hB n

end MState

namespace QIT

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Tensor power of a one-copy unitary under the repository's recursive
`TensorPower` convention. -/
def unitaryTensorPowerMatrix (U : Matrix.unitaryGroup a ℂ) :
    (n : ℕ) → Matrix.unitaryGroup (TensorPower a n) ℂ
  | 0 => 1
  | n + 1 =>
      let Un := unitaryTensorPowerMatrix U n
      ⟨Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)),
        Matrix.kronecker_mem_unitary U.2 Un.2⟩

@[simp]
theorem unitaryTensorPowerMatrix_zero (U : Matrix.unitaryGroup a ℂ) :
    unitaryTensorPowerMatrix U 0 = 1 := rfl

theorem unitaryTensorPowerMatrix_succ (U : Matrix.unitaryGroup a ℂ) (n : ℕ) :
    unitaryTensorPowerMatrix U (n + 1) =
      ⟨Matrix.kronecker (U : CMatrix a)
          (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)),
        Matrix.kronecker_mem_unitary U.2 (unitaryTensorPowerMatrix U n).2⟩ := rfl

end QIT
