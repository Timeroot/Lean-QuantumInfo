/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Classical.CQState
public import QuantumLib.QIT.Information.Renyi.ConditionalPetzRenyi
public import QuantumLib.QIT.Information.Renyi.FrankLieb.DPI

/-!
# Conditional Renyi quantities with a classical conditioning register

This is the shared source-shaped layer for `cond.tex:214-249`.  The public
ensemble is classical-first, `Y × (A × B)`, while all conditional expressions
use the explicit finite reindexing to `A × (B × Y)`.  Singular branches are
handled by support tests before an EReal value is formed; in particular this
file never defines a zero weight multiplied by `+infinity`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker NNReal
open Matrix

noncomputable section
universe u v w

open QIT

namespace QIT

namespace Classical

/-- A real power of a block diagonal PSD matrix is taken blockwise.  Zero eigenspaces are retained
by the support convention of `CFC.rpow`, so positive semidefiniteness suffices. -/
theorem blockDiagonal_rpow
    {ι : Type u} {a : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype a] [DecidableEq a]
    (blocks : ι → CMatrix a)
    (hblocks : ∀ i, (blocks i).PosSemidef) (s : ℝ) :
    CFC.rpow (blockDiagonal blocks) s =
      blockDiagonal (fun i => CFC.rpow (blocks i) s) := by
  let U : ι → Matrix.unitaryGroup a ℂ := fun i =>
    (hblocks i).isHermitian.eigenvectorUnitary
  let d : ι → a → ℝ := fun i =>
    (hblocks i).isHermitian.eigenvalues
  have hd : ∀ i j, 0 ≤ d i j := by
    intro i j
    exact (hblocks i).eigenvalues_nonneg j
  have hspec : ∀ i, blocks i =
      (U i : CMatrix a) *
          Matrix.diagonal (fun j => (d i j : ℂ)) *
        star (U i : CMatrix a) := by
    intro i
    simpa [U, d, Function.comp_def, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
      (hblocks i).isHermitian.spectral_theorem
  let Ubig : Matrix.unitaryGroup (ι × a) ℂ :=
    ⟨blockDiagonal (fun i => (U i : CMatrix a)), by
      rw [Matrix.mem_unitaryGroup_iff]
      simp only [star_eq_conjTranspose]
      rw [blockDiagonal_conjTranspose, blockDiagonal_mul]
      rw [show (1 : CMatrix (ι × a)) =
          (1 : CMatrix ι) ⊗ₖ (1 : CMatrix a) by simp]
      rw [identityTensor_eq_blockDiagonal (ι := ι) (a := a)
        (1 : CMatrix a)]
      apply congrArg blockDiagonal
      funext i
      exact Matrix.mem_unitaryGroup_iff.mp (U i).2⟩
  let dBig : (ι × a) → ℝ := fun ia => d ia.1 ia.2
  have hD : blockDiagonal (fun i =>
          Matrix.diagonal (fun j => (d i j : ℂ))) =
        Matrix.diagonal (fun ia => (dBig ia : ℂ)) := by
    ext ⟨i, j⟩ ⟨i', j'⟩
    by_cases hii : i = i'
    · subst i'
      change block (blockDiagonal (fun i =>
        Matrix.diagonal (fun j => (d i j : ℂ)))) i i j j' = _
      have h := congrFun (congrFun
        (blockDiagonal_block_self (fun i =>
          Matrix.diagonal (fun j => (d i j : ℂ))) i) j) j'
      simp [Matrix.diagonal, dBig]
    · change block (blockDiagonal (fun i =>
        Matrix.diagonal (fun j => (d i j : ℂ)))) i i' j j' = _
      have h := congrFun (congrFun
        (blockDiagonal_block_ne (fun i =>
          Matrix.diagonal (fun j => (d i j : ℂ))) hii) j) j'
      simp [Matrix.diagonal, dBig, hii]
  have hconj : blockDiagonal blocks =
        (Ubig : CMatrix (ι × a)) *
            Matrix.diagonal (fun ia => (dBig ia : ℂ)) *
          star (Ubig : CMatrix (ι × a)) := by
    calc
      blockDiagonal blocks = blockDiagonal (fun i =>
          (U i : CMatrix a) *
              Matrix.diagonal (fun j => (d i j : ℂ)) *
            star (U i : CMatrix a)) := by
          congr 1
          funext i
          exact hspec i
      _ = blockDiagonal (fun i => (U i : CMatrix a)) *
          blockDiagonal (fun i =>
            Matrix.diagonal (fun j => (d i j : ℂ))) *
          star (blockDiagonal (fun i => (U i : CMatrix a))) := by
            rw [show star (blockDiagonal (fun i => (U i : CMatrix a))) =
                blockDiagonal (fun i => star (U i : CMatrix a)) by
              change Matrix.conjTranspose (blockDiagonal
                (fun i => (U i : CMatrix a))) = _
              exact blockDiagonal_conjTranspose _]
            rw [← blockDiagonal_mul, ← blockDiagonal_mul]
      _ = (Ubig : CMatrix (ι × a)) *
            Matrix.diagonal (fun ia => (dBig ia : ℂ)) *
          star (Ubig : CMatrix (ι × a)) := by
            rw [hD]
  have hpow : ∀ i, CFC.rpow (blocks i) s =
      (U i : CMatrix a) *
          Matrix.diagonal (fun j => (((d i j) ^ s : ℝ) : ℂ)) *
        star (U i : CMatrix a) := by
    intro i
    rw [hspec i]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal
      (U i) (d i) (hd i) s
  have hDpow : blockDiagonal (fun i =>
          Matrix.diagonal (fun j => (((d i j) ^ s : ℝ) : ℂ))) =
        Matrix.diagonal (fun ia => (((dBig ia) ^ s : ℝ) : ℂ)) := by
    ext ⟨i, j⟩ ⟨i', j'⟩
    by_cases hii : i = i'
    · subst i'
      change block (blockDiagonal (fun i =>
        Matrix.diagonal (fun j => (((d i j) ^ s : ℝ) : ℂ)))) i i j j' = _
      have h := congrFun (congrFun
        (blockDiagonal_block_self (fun i =>
          Matrix.diagonal (fun j => (((d i j) ^ s : ℝ) : ℂ))) i) j) j'
      simp [Matrix.diagonal, dBig]
    · change block (blockDiagonal (fun i =>
        Matrix.diagonal (fun j => (((d i j) ^ s : ℝ) : ℂ)))) i i' j j' = _
      have h := congrFun (congrFun
        (blockDiagonal_block_ne (fun i =>
          Matrix.diagonal (fun j => (((d i j) ^ s : ℝ) : ℂ))) hii) j) j'
      simp [Matrix.diagonal, dBig, hii]
  have hconjpow : blockDiagonal (fun i => CFC.rpow (blocks i) s) =
        (Ubig : CMatrix (ι × a)) *
            Matrix.diagonal (fun ia => (((dBig ia) ^ s : ℝ) : ℂ)) *
          star (Ubig : CMatrix (ι × a)) := by
    calc
      blockDiagonal (fun i => CFC.rpow (blocks i) s) =
          blockDiagonal (fun i =>
            (U i : CMatrix a) *
                Matrix.diagonal (fun j => (((d i j) ^ s : ℝ) : ℂ)) *
              star (U i : CMatrix a)) := by
            congr 1
            funext i
            exact hpow i
      _ = blockDiagonal (fun i => (U i : CMatrix a)) *
          blockDiagonal (fun i =>
            Matrix.diagonal (fun j => (((d i j) ^ s : ℝ) : ℂ))) *
          star (blockDiagonal (fun i => (U i : CMatrix a))) := by
            rw [show star (blockDiagonal (fun i => (U i : CMatrix a))) =
                blockDiagonal (fun i => star (U i : CMatrix a)) by
              change Matrix.conjTranspose (blockDiagonal
                (fun i => (U i : CMatrix a))) = _
              exact blockDiagonal_conjTranspose _]
            rw [← blockDiagonal_mul, ← blockDiagonal_mul]
      _ = (Ubig : CMatrix (ι × a)) *
            Matrix.diagonal (fun ia => (((dBig ia) ^ s : ℝ) : ℂ)) *
          star (Ubig : CMatrix (ι × a)) := by
            rw [hDpow]
  rw [hconj]
  exact (cMatrix_rpow_unitary_conj_diagonal_ofReal Ubig dBig
    (fun ia => hd ia.1 ia.2) s).trans hconjpow.symm

/-- The blockwise power formula for positive definite blocks, where the exponent may also be
negative. -/
theorem blockDiagonal_rpow_posDef
    {ι : Type u} {a : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype a] [DecidableEq a]
    (blocks : ι → CMatrix a)
    (hblocks : ∀ i, (blocks i).PosDef) (s : ℝ) :
    CFC.rpow (blockDiagonal blocks) s =
      blockDiagonal (fun i => CFC.rpow (blocks i) s) := by
  let d : ι → a → ℝ := fun i => (hblocks i).isHermitian.eigenvalues
  let U : ι → Matrix.unitaryGroup a ℂ :=
    fun i => (hblocks i).isHermitian.eigenvectorUnitary
  let W : Matrix.unitaryGroup (ι × a) ℂ :=
    ⟨blockDiagonal (fun i => (U i : CMatrix a)), by
      rw [Matrix.mem_unitaryGroup_iff]
      simp only [star_eq_conjTranspose]
      rw [blockDiagonal_conjTranspose, blockDiagonal_mul]
      rw [show (1 : CMatrix (ι × a)) =
          (1 : CMatrix ι) ⊗ₖ (1 : CMatrix a) by simp]
      rw [identityTensor_eq_blockDiagonal (ι := ι) (a := a)
        (1 : CMatrix a)]
      apply congrArg blockDiagonal
      funext i
      exact Matrix.mem_unitaryGroup_iff.mp (U i).2⟩
  have hd_pos : ∀ i j, 0 < d i j := by
    intro i j
    exact (hblocks i).eigenvalues_pos j
  have hdiag :
      blockDiagonal blocks =
        Unitary.conjStarAlgAut ℂ _ W
          (blockDiagonal (fun i =>
            Matrix.diagonal (fun j => (d i j : ℂ)))) := by
    have hspec : blocks = fun i =>
        Unitary.conjStarAlgAut ℂ _ (U i)
          (Matrix.diagonal (fun j => (d i j : ℂ))) := by
      funext i
      simpa [d, U, Function.comp_def] using
        (hblocks i).isHermitian.spectral_theorem
    rw [hspec]
    simp [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, W,
      blockDiagonal_conjTranspose, blockDiagonal_mul]
  have hdiag_pos :
      (blockDiagonal (fun i =>
        Matrix.diagonal (fun j => (d i j : ℂ)))).PosDef := by
    have hD :
        (Matrix.diagonal (fun p : ι × a => (d p.1 p.2 : ℂ))).PosDef :=
      Matrix.PosDef.diagonal (fun p => by
        change (0 : ℂ) < (d p.1 p.2 : ℂ)
        exact_mod_cast hd_pos p.1 p.2)
    have hDblock :
        blockDiagonal (fun i =>
          Matrix.diagonal (fun j => (d i j : ℂ))) =
          Matrix.diagonal (fun p : ι × a => (d p.1 p.2 : ℂ)) := by
      ext ⟨i, j⟩ ⟨i', j'⟩
      by_cases hii : i = i'
      · subst i'
        change block (blockDiagonal (fun i =>
          Matrix.diagonal (fun j => (d i j : ℂ)))) i i j j' = _
        rw [blockDiagonal_block_self]
        simp [Matrix.diagonal]
      · change block (blockDiagonal (fun i =>
        Matrix.diagonal (fun j => (d i j : ℂ)))) i i' j j' = _
        rw [blockDiagonal_block_ne _ hii]
        simp [Matrix.diagonal, hii]
    rw [hDblock]
    exact hD
  have hpow :
      CFC.rpow (blockDiagonal blocks) s =
        Unitary.conjStarAlgAut ℂ _ W
          (blockDiagonal (fun i =>
            Matrix.diagonal (fun j => ((d i j ^ s : ℝ) : ℂ)))) := by
    rw [hdiag, cMatrix_rpow_conjStarAlgAut_posDef W hdiag_pos s]
    have hDblock :
        blockDiagonal (fun i =>
          Matrix.diagonal (fun j => (d i j : ℂ))) =
          Matrix.diagonal (fun p : ι × a => (d p.1 p.2 : ℂ)) := by
      ext ⟨i, j⟩ ⟨i', j'⟩
      by_cases hii : i = i'
      · subst i'
        change block (blockDiagonal (fun i =>
          Matrix.diagonal (fun j => (d i j : ℂ)))) i i j j' = _
        rw [blockDiagonal_block_self]
        simp [Matrix.diagonal]
      · change block (blockDiagonal (fun i =>
        Matrix.diagonal (fun j => (d i j : ℂ)))) i i' j j' = _
        rw [blockDiagonal_block_ne _ hii]
        simp [Matrix.diagonal, hii]
    rw [hDblock,
      cMatrix_rpow_diagonal_ofReal (fun p : ι × a => d p.1 p.2)
        (fun p => le_of_lt (hd_pos p.1 p.2)) s]
    have hpowblock :
        Matrix.diagonal (fun p : ι × a =>
          ((d p.1 p.2 ^ s : ℝ) : ℂ)) =
          blockDiagonal (fun i =>
            Matrix.diagonal (fun j => ((d i j ^ s : ℝ) : ℂ))) := by
      ext ⟨i, j⟩ ⟨i', j'⟩
      by_cases hii : i = i'
      · subst i'
        change _ = block (blockDiagonal (fun i =>
          Matrix.diagonal (fun j => ((d i j ^ s : ℝ) : ℂ)))) i i j j'
        rw [blockDiagonal_block_self]
        simp [Matrix.diagonal]
      · change _ = block (blockDiagonal (fun i =>
          Matrix.diagonal (fun j => ((d i j ^ s : ℝ) : ℂ)))) i i' j j'
        rw [blockDiagonal_block_ne _ hii]
        simp [Matrix.diagonal, hii]
    rw [hpowblock]
  rw [hpow]
  simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    W, blockDiagonal_conjTranspose, blockDiagonal_mul]
  apply congrArg blockDiagonal
  funext i
  have hi_spec :
      blocks i =
        Unitary.conjStarAlgAut ℂ _ (U i)
          (Matrix.diagonal (fun j => (d i j : ℂ))) := by
    simpa [d, U, Function.comp_def] using
      (hblocks i).isHermitian.spectral_theorem
  have hi_diag :
      (Matrix.diagonal (fun j => (d i j : ℂ))).PosDef :=
    Matrix.PosDef.diagonal (fun j => by
      change (0 : ℂ) < (d i j : ℂ)
      exact_mod_cast hd_pos i j)
  rw [hi_spec, cMatrix_rpow_conjStarAlgAut_posDef (U i) hi_diag s,
    cMatrix_rpow_diagonal_ofReal (d i) (fun j => le_of_lt (hd_pos i j)) s]
  rfl

/-- The trace pairing `Tr(ρ^s σ^t)` of two block diagonal positive definite matrices splits as the
sum of the blockwise pairings, at arbitrary real exponents. -/
theorem blockDiagonal_trace_decomposition_posDef
    {ι : Type u} {a : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype a] [DecidableEq a]
    (rho sigma : ι → CMatrix a)
    (hrho : ∀ i, (rho i).PosDef) (hsigma : ∀ i, (sigma i).PosDef)
    (s t : ℝ) :
    (CFC.rpow (blockDiagonal rho) s *
      CFC.rpow (blockDiagonal sigma) t).trace.re =
      ∑ i, (CFC.rpow (rho i) s * CFC.rpow (sigma i) t).trace.re := by
  rw [blockDiagonal_rpow_posDef rho hrho s,
    blockDiagonal_rpow_posDef sigma hsigma t, blockDiagonal_mul,
    blockDiagonal_trace, Complex.re_sum]

end Classical

variable {A : Type u} {B : Type v} {Y : Type w}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype Y] [DecidableEq Y]

end QIT

namespace MState

variable {A : Type u} {B : Type v} {Y : Type w}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype Y] [DecidableEq Y]

/-! ### The explicit A|BY basis and its cq blocks -/

/-- The normalized cq state in the `A × (B × Y)` grouping. -/
def cqConditioningState (E : MEnsemble (A × B) Y) : MState (A × (B × Y)) :=
  E.cqState.reindex (prodABCToBCAEquiv Y A B)

/-- Notation for `cqConditioningState` in its role as the state whose conditional Rényi entropies
are being computed. -/
abbrev conditionalRenyiState (E : MEnsemble (A × B) Y) : MState (A × (B × Y)) :=
  MState.cqConditioningState E

@[simp]
theorem cqConditioningState_matrix (E : MEnsemble (A × B) Y) :
    (MState.cqConditioningState E).m =
      E.cqState.m.submatrix
        (prodABCToBCAEquiv Y A B).symm
        (prodABCToBCAEquiv Y A B).symm :=
  MState.reindex_matrix _ _

theorem cqConditioningState_is_cq_on_Y (E : MEnsemble (A × B) Y) :
    MState.cqConditioningState E =
      E.cqState.reindex (prodABCToBCAEquiv Y A B) := rfl

/-- The `y` diagonal block after the `A × (B × Y)` reindexing. -/
def conditionalRenyiBlock (E : MEnsemble (A × B) Y) (y : Y) : CMatrix (A × B) :=
  (MState.cqConditioningState E).m.submatrix
    (fun ab : A × B => (ab.1, (ab.2, y)))
    (fun ab : A × B => (ab.1, (ab.2, y)))

@[simp]
theorem conditionalRenyiBlock_eq_weighted_state
    (E : MEnsemble (A × B) Y) (y : Y) :
    conditionalRenyiBlock E y =
      (E.probs y : ℂ) • (E.states y).m := by
  rw [conditionalRenyiBlock, cqConditioningState_matrix]
  ext ⟨a, b⟩ ⟨a', b'⟩
  change Classical.block E.cqState.m y y (a, b) (a', b') = _
  simpa [Classical.block] using
    congrFun (congrFun (Classical.cqState_block_self E y) (a, b)) (a', b')

theorem conditionalRenyiBlock_posSemidef
    (E : MEnsemble (A × B) Y) (y : Y) :
    (conditionalRenyiBlock E y).PosSemidef := by
  rw [conditionalRenyiBlock_eq_weighted_state]
  have hp : 0 ≤ (E.probs y : ℂ) := by
    exact_mod_cast NNReal.coe_nonneg (E.probs y)
  exact (E.states y).psd.smul hp

theorem conditionalRenyiBlock_trace
    (E : MEnsemble (A × B) Y) (y : Y) :
    (conditionalRenyiBlock E y).trace = (E.probs y : ℂ) := by
  rw [conditionalRenyiBlock_eq_weighted_state, Matrix.trace_smul,
    (E.states y).tr']
  simp

/-! ### Finite reindexing, products, powers, and reconstruction -/

/-- Reindexing a unitary matrix along an equivalence of index types gives a unitary matrix. -/
private theorem conditionalRenyi_reindex_mem_unitary
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.reindex e e (U : CMatrix ι) ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have hU := Matrix.mem_unitaryGroup_iff.mp U.2
  have happ := congrFun (congrFun hU (e.symm i)) (e.symm j)
  simp [Matrix.mul_apply, Matrix.star_apply] at happ ⊢
  have hsum :
      (∑ x : κ, (U : CMatrix ι) (e.symm i) (e.symm x) *
          starRingEnd ℂ ((U : CMatrix ι) (e.symm j) (e.symm x))) =
        ∑ y : ι, (U : CMatrix ι) (e.symm i) y *
          starRingEnd ℂ ((U : CMatrix ι) (e.symm j) y) := by
    exact Fintype.sum_equiv e.symm
      (fun x : κ => (U : CMatrix ι) (e.symm i) (e.symm x) *
        starRingEnd ℂ ((U : CMatrix ι) (e.symm j) (e.symm x)))
      (fun y : ι => (U : CMatrix ι) (e.symm i) y *
        starRingEnd ℂ ((U : CMatrix ι) (e.symm j) y))
      (by intro x; rfl)
  rw [hsum]
  simpa [Matrix.one_apply] using happ

/-- Real powers of a PSD matrix commute with reindexing along an equivalence of index types.  The
proof is spectral, so the zero eigenspace follows the same `0 ^ s = 0` convention as the PSD `rpow`
API. -/
theorem conditionalRenyi_rpow_reindex_posSemidef_support
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) {M : CMatrix ι} (hM : M.PosSemidef) (s : ℝ) :
    CFC.rpow (M.submatrix e.symm e.symm) s =
      (CFC.rpow M s).submatrix e.symm e.symm := by
  let U : Matrix.unitaryGroup ι ℂ := hM.isHermitian.eigenvectorUnitary
  let Ue : Matrix.unitaryGroup κ ℂ :=
    ⟨Matrix.reindex e e (U : CMatrix ι),
      conditionalRenyi_reindex_mem_unitary e U⟩
  let d : ι → ℝ := hM.isHermitian.eigenvalues
  let de : κ → ℝ := fun i => d (e.symm i)
  have hd : ∀ i, 0 ≤ d i := fun i => hM.eigenvalues_nonneg i
  have hde : ∀ i, 0 ≤ de i := fun i => hd (e.symm i)
  have hM_spec :
      M = Unitary.conjStarAlgAut ℂ _ U
        (Matrix.diagonal (fun i => (d i : ℂ))) := by
    simpa [U, d, Function.comp_def] using hM.isHermitian.spectral_theorem
  have hdiag :
      Matrix.reindex e e
          (Matrix.diagonal (fun i => (d i : ℂ)) : CMatrix ι) =
        Matrix.diagonal (fun i => (de i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [de]
    · simp [Matrix.diagonal, hij]
  have hstarU :
      Matrix.reindex e e (star (U : CMatrix ι)) =
        star (Matrix.reindex e e (U : CMatrix ι)) := by
    ext i j
    simp [Matrix.star_apply]
  have hM_reindex_spec :
      M.submatrix e.symm e.symm =
        Unitary.conjStarAlgAut ℂ _ Ue
          (Matrix.diagonal (fun i => (de i : ℂ))) := by
    rw [hM_spec]
    change (Matrix.reindexAlgEquiv ℂ ℂ e)
        (((U : CMatrix ι) * Matrix.diagonal (fun i => (d i : ℂ))) *
          star (U : CMatrix ι)) = _
    rw [map_mul, map_mul]
    rw [show (Matrix.reindexAlgEquiv ℂ ℂ e)
        (Matrix.diagonal (fun i => (d i : ℂ)) : CMatrix ι) =
          Matrix.diagonal (fun i => (de i : ℂ)) by
      simpa [Matrix.coe_reindexAlgEquiv] using hdiag]
    rw [show (Matrix.reindexAlgEquiv ℂ ℂ e) (star (U : CMatrix ι)) =
        star ((Matrix.reindexAlgEquiv ℂ ℂ e) (U : CMatrix ι)) by
      simpa [Matrix.coe_reindexAlgEquiv] using hstarU]
    rfl
  have hM_rpow :
      CFC.rpow M s = Unitary.conjStarAlgAut ℂ _ U
        (Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ))) := by
    rw [hM_spec]
    simpa [Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal U d hd s
  have hM_reindex_rpow :
      CFC.rpow (M.submatrix e.symm e.symm) s =
        Unitary.conjStarAlgAut ℂ _ Ue
          (Matrix.diagonal (fun i => ((de i ^ s : ℝ) : ℂ))) := by
    rw [hM_reindex_spec]
    simpa [Unitary.conjStarAlgAut_apply] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal Ue de hde s
  rw [hM_reindex_rpow, hM_rpow]
  have hdiag_pow :
      Matrix.reindex e e
          (Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) : CMatrix ι) =
        Matrix.diagonal (fun i => ((de i ^ s : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [de]
    · simp [Matrix.diagonal, hij]
  change ((Ue : CMatrix κ) *
      Matrix.diagonal (fun i => ((de i ^ s : ℝ) : ℂ))) *
        star (Ue : CMatrix κ) =
      (Matrix.reindexAlgEquiv ℂ ℂ e)
        (((U : CMatrix ι) *
          Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ))) *
          star (U : CMatrix ι))
  rw [map_mul, map_mul]
  rw [show (Matrix.reindexAlgEquiv ℂ ℂ e)
      (Matrix.diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) : CMatrix ι) =
        Matrix.diagonal (fun i => ((de i ^ s : ℝ) : ℂ)) by
    simpa [Matrix.coe_reindexAlgEquiv] using hdiag_pow]
  rw [show (Matrix.reindexAlgEquiv ℂ ℂ e) (star (U : CMatrix ι)) =
      star ((Matrix.reindexAlgEquiv ℂ ℂ e) (U : CMatrix ι)) by
    simpa [Matrix.coe_reindexAlgEquiv] using hstarU]
  rfl

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem conditionalRenyi_blockDiagonal_reindex
    (blocks : Y → CMatrix (A × B)) :
    (Matrix.blockDiagonal blocks).submatrix
        (Equiv.prodComm (A × B) Y).symm (Equiv.prodComm (A × B) Y).symm =
      Classical.blockDiagonal blocks := by
  ext ⟨y, ⟨a, b⟩⟩ ⟨y', ⟨a', b'⟩⟩
  by_cases hyy : y = y'
  · subst y'
    change Matrix.blockDiagonal blocks ((a, b), y) ((a', b'), y) =
      Classical.blockDiagonal blocks (y, (a, b)) (y, (a', b'))
    rw [show Matrix.blockDiagonal blocks ((a, b), y) ((a', b'), y) =
        blocks y (a, b) (a', b') by simp [Matrix.blockDiagonal]]
    exact (congrFun (congrFun (Classical.blockDiagonal_block_self blocks y)
      (a, b)) (a', b')).symm
  · change Matrix.blockDiagonal blocks ((a, b), y) ((a', b'), y') =
      Classical.blockDiagonal blocks (y, (a, b)) (y', (a', b'))
    rw [show Matrix.blockDiagonal blocks ((a, b), y) ((a', b'), y') = 0 by
      simp [Matrix.blockDiagonal, hyy]]
    rw [show
      Classical.blockDiagonal blocks (y, (a, b)) (y', (a', b')) =
        Classical.block (Classical.blockDiagonal blocks) y y' (a, b) (a', b') by
          rfl]
    rw [Classical.blockDiagonal_block_ne blocks hyy]
    rfl

/-- A `Y`-indexed family of blocks, assembled block-diagonally and reindexed into the
`A × (B × Y)` grouping used by the conditional Rényi quantities. -/
def conditionalRenyiRightBlockDiagonal
    (blocks : Y → CMatrix (A × B)) : CMatrix (A × (B × Y)) :=
  (Classical.blockDiagonal blocks).submatrix
    (prodABCToBCAEquiv Y A B).symm
    (prodABCToBCAEquiv Y A B).symm

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
@[simp]
theorem conditionalRenyiRightBlockDiagonal_block
    (blocks : Y → CMatrix (A × B)) (y : Y) :
    (conditionalRenyiRightBlockDiagonal blocks).submatrix
        (fun ab : A × B => (ab.1, (ab.2, y)))
        (fun ab : A × B => (ab.1, (ab.2, y))) = blocks y := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  change Classical.block (Classical.blockDiagonal blocks) y y (a, b) (a', b') = _
  simp

omit [DecidableEq A] [DecidableEq B] in
theorem conditionalRenyiRightBlockDiagonal_mul
    (blocks₁ blocks₂ : Y → CMatrix (A × B)) :
    conditionalRenyiRightBlockDiagonal blocks₁ *
        conditionalRenyiRightBlockDiagonal blocks₂ =
      conditionalRenyiRightBlockDiagonal (fun y => blocks₁ y * blocks₂ y) := by
  unfold conditionalRenyiRightBlockDiagonal
  rw [Matrix.submatrix_mul_equiv, Classical.blockDiagonal_mul]

omit [DecidableEq A] [DecidableEq B] in
theorem conditionalRenyiRightBlockDiagonal_trace
    (blocks : Y → CMatrix (A × B)) :
    (conditionalRenyiRightBlockDiagonal blocks).trace = ∑ y, (blocks y).trace := by
  unfold conditionalRenyiRightBlockDiagonal
  rw [Matrix.trace_submatrix, Classical.blockDiagonal_trace]

omit [DecidableEq A] [DecidableEq B] in
theorem conditionalRenyiRightBlockDiagonal_posSemidef
    (blocks : Y → CMatrix (A × B))
    (hblocks : ∀ y, (blocks y).PosSemidef) :
    (conditionalRenyiRightBlockDiagonal blocks).PosSemidef := by
  unfold conditionalRenyiRightBlockDiagonal
  exact (Classical.blockDiagonal_posSemidef blocks hblocks).submatrix _

/-- Real powers of `conditionalRenyiRightBlockDiagonal` are taken blockwise: the permutation into
the right-conditioning basis preserves the support convention at every real exponent. -/
theorem conditionalRenyiRightBlockDiagonal_rpow_support
    (blocks : Y → CMatrix (A × B))
    (hblocks : ∀ y, (blocks y).PosSemidef) (s : ℝ) :
    CFC.rpow (conditionalRenyiRightBlockDiagonal blocks) s =
      conditionalRenyiRightBlockDiagonal
        (fun y => CFC.rpow (blocks y) s) := by
  unfold conditionalRenyiRightBlockDiagonal
  rw [conditionalRenyi_rpow_reindex_posSemidef_support
      (e := prodABCToBCAEquiv Y A B)
      (M := Classical.blockDiagonal blocks)
      (Classical.blockDiagonal_posSemidef blocks hblocks) s,
    Classical.blockDiagonal_rpow blocks hblocks s]

theorem conditionalRenyiState_eq_rightBlockDiagonal (E : MEnsemble (A × B) Y) :
    (MState.cqConditioningState E).m =
      conditionalRenyiRightBlockDiagonal (conditionalRenyiBlock E) := by
  rw [cqConditioningState_matrix, conditionalRenyiRightBlockDiagonal]
  rw [show conditionalRenyiBlock E =
      (fun y => (E.probs y : ℂ) • (E.states y).m) by
        funext y
        exact conditionalRenyiBlock_eq_weighted_state E y]
  exact congrArg (fun M => M.submatrix
      (prodABCToBCAEquiv Y A B).symm
      (prodABCToBCAEquiv Y A B).symm)
    (Classical.cqState_eq_blockDiagonal E)

theorem conditionalRenyiState_trace_eq_sum_block_trace (E : MEnsemble (A × B) Y) :
    (MState.cqConditioningState E).m.trace =
      ∑ y, (conditionalRenyiBlock E y).trace := by
  rw [conditionalRenyiState_eq_rightBlockDiagonal,
    conditionalRenyiRightBlockDiagonal_trace]

theorem conditionalRenyiState_trace_eq_one (E : MEnsemble (A × B) Y) :
    (MState.cqConditioningState E).m.trace = 1 :=
  (MState.cqConditioningState E).tr'

/-! ### Marginals and support-indexed branch logic -/

end MState

namespace MEnsemble

variable {A : Type u} {B : Type v} {Y : Type w}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype Y] [DecidableEq Y]

/-- The ensemble of `B` marginals: same probabilities, each state traced over `A`. -/
def conditionalMarginalB (E : MEnsemble (A × B) Y) : MEnsemble B Y :=
  .ofProbs E.probs E.weights_sum (fun y => (E.states y).traceLeft)

omit [DecidableEq Y] in
@[simp]
theorem conditionalMarginalB_probs (E : MEnsemble (A × B) Y) (y : Y) :
    E.conditionalMarginalB.probs y = E.probs y := rfl

omit [DecidableEq Y] in
@[simp]
theorem conditionalMarginalB_states (E : MEnsemble (A × B) Y) (y : Y) :
    E.conditionalMarginalB.states y = (E.states y).traceLeft := rfl

/-- The cq state of the `B` marginal ensemble, in the `B × Y` grouping.  It is the conditioning
marginal of `conditionalRenyiState`. -/
def conditionalMarginalBYState (E : MEnsemble (A × B) Y) : MState (B × Y) :=
  E.conditionalMarginalB.cqState.reindex (Equiv.prodComm Y B)

theorem conditionalRenyiState_traceLeft_eq_conditionalMarginalBYState
    (E : MEnsemble (A × B) Y) :
    (MState.cqConditioningState E).traceLeft = E.conditionalMarginalBYState := by
  apply MState.ext
  ext ⟨b, y⟩ ⟨b', y'⟩
  simp only [MState.cqConditioningState, MState.reindex_matrix, MState.traceLeft_m,
    Matrix.traceLeft, Matrix.of_apply, Matrix.submatrix, conditionalMarginalBYState,
    MEnsemble.cqState_matrix]
  by_cases hyy : y = y'
  · subst y'
    simp [MEnsemble.conditionalMarginalB, Matrix.kroneckerMap_apply, prodABCToBCAEquiv_symm_apply,
      Matrix.sum_apply]
    conv_lhs => rw [Finset.sum_comm]
    rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
    · rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
      · simp [Matrix.traceLeft]
        rw [← Finset.smul_sum]
      · intro x _ hxy
        simp [hxy]
    · intro x _ hxy
      simp [hxy]
  · have hxy : ∀ x : Y, ¬(x = y ∧ x = y') := by
      intro x h
      exact hyy (h.1.symm.trans h.2)
    simp [MEnsemble.conditionalMarginalB, Matrix.kroneckerMap_apply, prodABCToBCAEquiv_symm_apply,
      Matrix.sum_apply, hxy]

/-- The classical labels of positive probability.  Restricting sums to it keeps the extended-real
branch values from meeting a zero weight. -/
def conditionalRenyiSupport (E : MEnsemble (A × B) Y) : Finset Y :=
  Finset.univ.filter fun y => E.probs y ≠ 0

/-- An EReal branch sum with zero-probability labels removed before the
coercion and multiplication.  This is the support-indexed form of the
classical mixture; it does not form `0 * (+infinity)`. -/
noncomputable def conditionalRenyiSupportWeightedERealSum
    (E : MEnsemble (A × B) Y) (f : Y → EReal) : EReal :=
  E.conditionalRenyiSupport.sum fun y =>
    ((E.probs y : ℝ) : EReal) * f y

omit [DecidableEq Y] in
theorem mem_conditionalRenyiSupport_iff (E : MEnsemble (A × B) Y) (y : Y) :
    y ∈ E.conditionalRenyiSupport ↔ E.probs y ≠ 0 := by
  simp [conditionalRenyiSupport]

omit [DecidableEq Y] in
theorem not_mem_conditionalRenyiSupport_iff (E : MEnsemble (A × B) Y) (y : Y) :
    y ∉ E.conditionalRenyiSupport ↔ E.probs y = 0 := by
  simp [conditionalRenyiSupport]

omit [DecidableEq Y] in
theorem conditionalRenyiSupport_weight_ne_zero
    (E : MEnsemble (A × B) Y) {y : Y} (hy : y ∈ E.conditionalRenyiSupport) :
    (E.probs y : ℂ) ≠ 0 := by
  exact_mod_cast (E.mem_conditionalRenyiSupport_iff y).mp hy

theorem conditionalRenyiBlock_eq_zero_iff
    (E : MEnsemble (A × B) Y) (y : Y) :
    MState.conditionalRenyiBlock E y = 0 ↔ E.probs y = 0 := by
  rw [MState.conditionalRenyiBlock_eq_weighted_state]
  constructor
  · intro h
    by_contra hprob
    have hscalar : (E.probs y : ℂ) ≠ 0 := by exact_mod_cast hprob
    apply hscalar
    have hstate : (E.states y).m = 0 :=
      (smul_eq_zero.mp h).resolve_left hscalar
    exact False.elim ((E.states y).matrix_ne_zero hstate)
  · intro h
    simp [h]

end MEnsemble

namespace MState

variable {A : Type u} {B : Type v} {Y : Type w}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype Y] [DecidableEq Y]

/-- A support relation `X ≤≤ I_a ⊗ N` descends through the partial trace over `a`:
`Tr_a X ≤≤ N`.  Neither matrix needs to be full rank. -/
theorem traceLeft_supports_of_identityTensor_support
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    {X : CMatrix (a × b)} {N : CMatrix b}
    (hX : Matrix.Supports X ((1 : CMatrix a) ⊗ₖ N)) :
    Matrix.Supports (Matrix.traceLeft X) N := by
  intro v hv
  ext j
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.mulVec, dotProduct]
  calc
    ∑ x, (∑ i, X (i, j) (i, x)) * v x =
        ∑ x, ∑ i, X (i, j) (i, x) * v x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
    _ = ∑ i, ∑ x, X (i, j) (i, x) * v x := by
      rw [Finset.sum_comm]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      let w : a × b → ℂ := fun z => if z.1 = i then v z.2 else 0
      have hw : ((1 : CMatrix a) ⊗ₖ N).mulVec w = 0 := by
        ext z
        rcases z with ⟨k, x⟩
        by_cases hki : k = i
        · subst k
          simp [w, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.one_apply,
            Fintype.sum_prod_type]
          simpa [Matrix.mulVec, dotProduct] using congrFun hv x
        · simp [w, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.one_apply,
            Fintype.sum_prod_type, hki]
      have hXw : X.mulVec w = 0 := hX w hw
      simpa [w, Matrix.mulVec, dotProduct, Fintype.sum_prod_type] using
        congrFun hXw (i, j)

/-- The reference `I_A ⊗ ρ_BY` of the downward entropy is block diagonal in the classical label,
with the `y` block equal to `p y • (I_A ⊗ ρ_{B|y})`. -/
theorem conditionalReference_blockDiagonal
    (E : MEnsemble (A × B) Y) :
    identityTensorStateMatrix (a := A) (MState.cqConditioningState E).traceLeft =
      conditionalRenyiRightBlockDiagonal (fun y =>
        (E.probs y : ℂ) • identityTensorStateMatrix (a := A)
          (E.states y).traceLeft) := by
  rw [MEnsemble.conditionalRenyiState_traceLeft_eq_conditionalMarginalBYState]
  ext ⟨a, b, y⟩ ⟨a', b', y'⟩
  by_cases hyy : y = y'
  · subst y'
    simp [conditionalRenyiRightBlockDiagonal, identityTensorStateMatrix,
      MEnsemble.conditionalMarginalBYState, MEnsemble.conditionalMarginalB,
      MEnsemble.cqState_matrix, MState.reindex_matrix, Matrix.kroneckerMap_apply, prodABCToBCAEquiv_symm_apply,
      Matrix.traceLeft, Matrix.sum_apply]
    simp only [Matrix.one_apply]
    rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
    · conv_rhs =>
        unfold Classical.blockDiagonal
        rw [Matrix.sum_apply]
        rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y) (by
          intro z _ hzy
          simp [hzy])]
      simp [Matrix.kroneckerMap_apply]
      by_cases haa : a = a'
      · subst a'
        rw [NNReal.smul_def]
        simp [Complex.real_smul]
      · simp [haa]
    · intro z _ hzy
      simp [hzy]
  · have hxy : ∀ x : Y, ¬(x = y ∧ x = y') := by
      intro x h
      exact hyy (h.1.symm.trans h.2)
    simp [conditionalRenyiRightBlockDiagonal, identityTensorStateMatrix,
      MEnsemble.conditionalMarginalBYState, MEnsemble.conditionalMarginalB,
      MEnsemble.cqState_matrix, MState.reindex_matrix, Matrix.kroneckerMap_apply, prodABCToBCAEquiv_symm_apply,
      Matrix.traceLeft, Matrix.sum_apply,
      Classical.blockDiagonal, hxy]

/-! ### EReal reference kernels and public conditional quantities -/

/-- The Petz Rényi divergence `log₂ Tr(ρ^α σ^(1-α)) / (α-1)` against a positive semidefinite
reference, as a real number.  It is only meaningful where the trace is positive; the extended-real
`petzRenyiReferenceE` decides that. -/
def petzRenyiReferenceFinite (ρ : MState A) (σ : CMatrix A)
    (_hσ : σ.PosSemidef) (α : ℝ) (_hα_pos : 0 < α) (_hα_ne_one : α ≠ 1) : ℝ :=
  (1 / (α - 1)) *
    log2 ((CFC.rpow ρ.m α * CFC.rpow σ (1 - α)).trace.re)

/-- The support-aware extended-real Petz Rényi divergence.  It is `⊤` when `α < 1` and the trace
`Tr(ρ^α σ^(1-α))` vanishes, and when `1 < α` and `σ` does not support `ρ`; elsewhere it is the
real value `petzRenyiReferenceFinite`. -/
noncomputable def petzRenyiReferenceE (ρ : MState A) (σ : CMatrix A)
    (hσ : σ.PosSemidef) (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : EReal := by
  classical
  let q := (CFC.rpow ρ.m α * CFC.rpow σ (1 - α)).trace.re
  by_cases hα_lt_one : α < 1
  · by_cases hq : q = 0
    · exact ⊤
    · exact (ρ.petzRenyiReferenceFinite σ hσ α hα_pos hα_ne_one : EReal)
  · by_cases hs : Matrix.Supports ρ.m σ
    · exact (ρ.petzRenyiReferenceFinite σ hσ α hα_pos hα_ne_one : EReal)
    · exact ⊤

theorem petzRenyiReferenceE_eq_top_of_lt_one_of_trace_eq_zero
    (ρ : MState A) (σ : CMatrix A) (hσ : σ.PosSemidef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (hα_lt_one : α < 1)
    (hzero : (CFC.rpow ρ.m α * CFC.rpow σ (1 - α)).trace.re = 0) :
    ρ.petzRenyiReferenceE σ hσ α hα_pos hα_ne_one = ⊤ := by
  change (ρ.m ^ α * σ ^ (1 - α)).trace.re = 0 at hzero
  simp [petzRenyiReferenceE, hα_lt_one, hzero]

theorem petzRenyiReferenceE_eq_coe_of_lt_one_of_trace_ne_zero
    (ρ : MState A) (σ : CMatrix A) (hσ : σ.PosSemidef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (hα_lt_one : α < 1)
    (hne : (CFC.rpow ρ.m α * CFC.rpow σ (1 - α)).trace.re ≠ 0) :
    ρ.petzRenyiReferenceE σ hσ α hα_pos hα_ne_one =
      (ρ.petzRenyiReferenceFinite σ hσ α hα_pos hα_ne_one : EReal) := by
  change (ρ.m ^ α * σ ^ (1 - α)).trace.re ≠ 0 at hne
  simp [petzRenyiReferenceE, hα_lt_one, hne]

@[simp]
theorem petzRenyiReferenceE_eq_coe_of_one_lt_of_supports
    (ρ : MState A) (σ : CMatrix A) (hσ : σ.PosSemidef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (hα_gt_one : 1 < α)
    (hsupport : Matrix.Supports ρ.m σ) :
    ρ.petzRenyiReferenceE σ hσ α hα_pos hα_ne_one =
      (ρ.petzRenyiReferenceFinite σ hσ α hα_pos hα_ne_one : EReal) := by
  simp [petzRenyiReferenceE, not_lt.mpr (le_of_lt hα_gt_one), hsupport]

@[simp]
theorem petzRenyiReferenceE_eq_top_of_one_lt_of_not_supports
    (ρ : MState A) (σ : CMatrix A) (hσ : σ.PosSemidef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) (hα_gt_one : 1 < α)
    (hsupport : ¬ Matrix.Supports ρ.m σ) :
    ρ.petzRenyiReferenceE σ hσ α hα_pos hα_ne_one = ⊤ := by
  simp [petzRenyiReferenceE, not_lt.mpr (le_of_lt hα_gt_one), hsupport]

/-- The downward conditional Petz Rényi entropy of a cq ensemble, extended-real and support-aware:
the Petz divergence of the cq state against `I_A ⊗ ρ_BY`, negated. -/
noncomputable def conditionalPetzRenyiDownE (E : MEnsemble (A × B) Y)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : EReal :=
  -(MState.cqConditioningState E).petzRenyiReferenceE
    (identityTensorStateMatrix (a := A) (MState.cqConditioningState E).traceLeft)
    (identityTensorStateMatrix_posSemidef
      (a := A) (MState.cqConditioningState E).traceLeft) α hα_pos hα_ne_one

/-- Bipartite downward Petz conditional Renyi entropy, extended-real and
support-aware.

This is the direct bipartite analogue of `conditionalPetzRenyiDownE`: it is
defined on `rho : MState (A × B)` with the canonical marginal `rho_B` as the
reference side, and inherits the support-aware `EReal` behaviour of
`MState.petzRenyiReferenceE`.  Because the reference kernel already tests
`Matrix.Supports` on its `> 1` branch, this wrapper needs no `PosDef`
hypothesis on `rho_B`; singular marginals are handled by the kernel rather than
by a full-rank assumption.  Matches Tomamichel2015FiniteResources,
`cond.tex:87-98`. -/
noncomputable def conditionalPetzRenyiDownGeneralE (rho : MState (A × B))
    (alpha : ℝ) (halpha_pos : 0 < alpha) (halpha_ne_one : alpha ≠ 1) : EReal :=
  -(rho.petzRenyiReferenceE
      (identityTensorStateMatrix (a := A) rho.traceLeft)
      (identityTensorStateMatrix_posSemidef (a := A) rho.traceLeft)
      alpha halpha_pos halpha_ne_one)

/-- For any bipartite state and interior parameter `alpha ∈ (0, 2) \ {1}`, the
support-aware downward wrapper reduces to the coe of the finite Petz reference.

This is the PosDef-free EReal reduction that the singular-marginal duality
relies on.  The `alpha < 1` branch is covered because a bipartite state is
supported on `I_A ⊗ rho_B` (so `Tr(rho^alpha (I ⊗ rho_B)^(1-alpha))` is
strictly positive), and the `1 < alpha` branch is covered by the same support
inclusion.  No `PosDef` hypothesis on the marginal is required. -/
theorem conditionalPetzRenyiDownGeneralE_eq_coe
    (rho : MState (A × B)) (alpha : ℝ)
    (halpha_pos : 0 < alpha) (halpha_ne_one : alpha ≠ 1) :
    rho.conditionalPetzRenyiDownGeneralE alpha halpha_pos halpha_ne_one =
      (-(rho.petzRenyiReferenceFinite
          (identityTensorStateMatrix (a := A) rho.traceLeft)
          (identityTensorStateMatrix_posSemidef (a := A) rho.traceLeft)
          alpha halpha_pos halpha_ne_one) : EReal) := by
  unfold conditionalPetzRenyiDownGeneralE
  have hsup : Matrix.Supports rho.m
      (identityTensorStateMatrix (a := A) rho.traceLeft) :=
    matrix_supports_identityTensor_traceLeft rho
  by_cases halpha_lt_one : alpha < 1
  · -- `alpha < 1`: the trace term is strictly positive, so the `< 1` coe
    -- branch of `petzRenyiReferenceE` applies.
    have hMne : CFC.rpow rho.m alpha ≠ 0 := by
      have hpow_pos : 0 < psdTracePower rho.m rho.psd (p := alpha) :=
        psdTracePower_pos_of_ne_zero rho.m rho.psd rho.matrix_ne_zero
      intro hzero
      have htrace_zero : psdTracePower rho.m rho.psd (p := alpha) = 0 := by
        simpa [psdTracePower] using
          congrArg (fun X : CMatrix (A × B) => X.trace.re) hzero
      linarith
    have htrace_pos :
        0 < ((CFC.rpow rho.m alpha *
            CFC.rpow (identityTensorStateMatrix (a := A) rho.traceLeft)
              (1 - alpha)).trace).re :=
      trace_mul_cMatrix_rpow_pos_of_support
        (cMatrix_rpow_posSemidef (A := rho.m) (s := alpha) rho.psd)
        (identityTensorStateMatrix_posSemidef (a := A) rho.traceLeft)
        hMne
        ((cMatrix_rpow_supports_self rho.psd halpha_pos).trans hsup)
        (1 - alpha)
    rw [petzRenyiReferenceE_eq_coe_of_lt_one_of_trace_ne_zero
        rho (identityTensorStateMatrix (a := A) rho.traceLeft)
        (identityTensorStateMatrix_posSemidef (a := A) rho.traceLeft)
        alpha halpha_pos halpha_ne_one halpha_lt_one htrace_pos.ne']
  · -- `1 < alpha`: the support inclusion supplies `Matrix.Supports`, so the
    -- `> 1` coe branch of `petzRenyiReferenceE` applies.
    have hle : 1 ≤ alpha := not_lt.mp halpha_lt_one
    have halpha_gt_one : 1 < alpha := lt_of_le_of_ne hle (ne_comm.mp halpha_ne_one)
    rw [petzRenyiReferenceE_eq_coe_of_one_lt_of_supports
        rho (identityTensorStateMatrix (a := A) rho.traceLeft)
        (identityTensorStateMatrix_posSemidef (a := A) rho.traceLeft)
        alpha halpha_pos halpha_ne_one halpha_gt_one hsup]

/-- The upward conditional Petz Rényi entropy of a cq ensemble: the same divergence optimized over
all conditioning states `σ_BY` rather than fixed at the marginal. -/
noncomputable def conditionalPetzRenyiUpE (E : MEnsemble (A × B) Y)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) : EReal :=
  sSup {h : EReal |
    ∃ σ : MState (B × Y),
      h = -(MState.cqConditioningState E).petzRenyiReferenceE
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef (a := A) σ)
        α hα_pos hα_ne_one}

/-- The downward conditional sandwiched Rényi entropy of a cq ensemble, against the marginal
`I_A ⊗ ρ_BY`.  Defined for `1/2 ≤ α ≠ 1`, the range in which the sandwiched divergence is
monotone under channels. -/
noncomputable def conditionalSandwichedRenyiDownE (E : MEnsemble (A × B) Y)
    (α : ℝ) (_hα : 1 / 2 ≤ α) (_hα_ne_one : α ≠ 1) : EReal :=
  -sandwichedRenyiPSDReferenceE
    (MState.cqConditioningState E)
    (identityTensorStateMatrix (a := A) (MState.cqConditioningState E).traceLeft)
    (identityTensorStateMatrix_posSemidef
      (a := A) (MState.cqConditioningState E).traceLeft) α

/-- The upward conditional sandwiched Rényi entropy of a cq ensemble, optimized over the
conditioning state. -/
noncomputable def conditionalSandwichedRenyiUpE (E : MEnsemble (A × B) Y)
    (α : ℝ) (_hα : 1 / 2 ≤ α) (_hα_ne_one : α ≠ 1) : EReal :=
  sSup {h : EReal |
    ∃ σ : MState (B × Y),
      h = -sandwichedRenyiPSDReferenceE
        (MState.cqConditioningState E)
        (identityTensorStateMatrix (a := A) σ)
        (identityTensorStateMatrix_posSemidef (a := A) σ) α}

end MState

namespace QIT

variable {A : Type u} {B : Type v} {Y : Type w}
variable [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
variable [Fintype Y] [DecidableEq Y]

end QIT
