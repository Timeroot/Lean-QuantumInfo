/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.Map
public import QuantumLib.QIT.Core.Measurement
public import QuantumInfo.Channels.CPTP

/-!
# Channels

Finite-dimensional channels are `CPTPMap`s: complex-linear matrix maps carrying complete
positivity and trace preservation data. A channel is applied to a state by the `FunLike`
action `Phi rho`, and `CPTPOp.mat_coe_eq_apply_mat` reads off the underlying matrix. Tensor
products of channels model parallel channel uses [HolevoGiovannetti2012QuantumChannels,
arxive.tex:965-974,1986-1993].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

attribute [simp] CPTPOp.mat_coe_eq_apply_mat

noncomputable section
universe u v w x y
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

open QIT

namespace CPTPOp

/-- A channel takes positive semidefinite matrices to positive semidefinite matrices. -/
theorem mapsPositive (Phi : CPTPMap a b) :
    ∀ X : CMatrix a, X.PosSemidef → (Phi.map X).PosSemidef :=
  QIT.MatrixMap.isCompletelyPositive_mapsPositive Phi.map Phi.map_cp

/-- The finite-dimensional identity channel acts as the identity matrix map. -/
theorem idChannel_map (X : CMatrix a) :
    (CPTPOp.id (dIn := a)).map X = X := by
  simp

/-- The preparation map `X ↦ ∑ x, X x x • rho x`: it reads the diagonal of a classical input and
prepares the corresponding state from the family `rho`. -/
def prepareMap {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → MState b) : QIT.MatrixMap x b where
  toFun X := ∑ x, X x x • (rho x).m
  map_add' X Y := by
    simp [Finset.sum_add_distrib, add_smul]
  map_smul' r X := by
    simp [Finset.smul_sum, smul_smul]

theorem prepareMap_single {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → MState b) (i i' : x) :
    prepareMap rho (Matrix.single i i' (1 : ℂ)) =
      if i = i' then (rho i).m else (0 : CMatrix b) := by
  ext r s
  by_cases h : i = i'
  · subst h
    rw [if_pos rfl]
    change (∑ x, Matrix.single i i (1 : ℂ) x x • (rho x).m) r s = (rho i).m r s
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    rw [Finset.sum_eq_single i]
    · simp [Matrix.single]
    · intro x _ hx
      have hxi : i ≠ x := by
        intro hxi
        exact hx hxi.symm
      simp [Matrix.single, hxi]
    · intro hi
      simp at hi
  · rw [if_neg h]
    change (∑ x, Matrix.single i i' (1 : ℂ) x x • (rho x).m) r s = 0
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : i = x
    · have hx' : i' ≠ x := by
        intro hx'
        exact h (hx.trans hx'.symm)
      simp [Matrix.single, hx, hx']
    · simp [Matrix.single, hx]

theorem prepareMap_choi {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → MState b) :
    QIT.MatrixMap.choi (prepareMap rho) =
      ∑ x, (Matrix.single x x (1 : ℂ)) ⊗ₖ (rho x).m := by
  ext xb xb'
  rcases xb with ⟨x, b1⟩
  rcases xb' with ⟨x', b2⟩
  by_cases h : x = x'
  · subst h
    rw [QIT.MatrixMap.choi, prepareMap_single rho x x, if_pos rfl]
    simp only [Matrix.sum_apply]
    rw [Finset.sum_eq_single x]
    · simp [Matrix.single]
    · intro z _ hz
      simp [Matrix.single, hz]
    · intro hx
      simp at hx
  · rw [QIT.MatrixMap.choi, prepareMap_single rho x x', if_neg h]
    simp only [Matrix.sum_apply, Matrix.single]
    symm
    refine Finset.sum_eq_zero fun z _ => ?_
    have hneq : ¬ (z = x ∧ z = x') := by
      intro hz
      exact h (hz.1.symm.trans hz.2)
    simp [hneq]

theorem prepareMap_isCompletelyPositive {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → MState b) :
    MatrixMap.IsCompletelyPositive (prepareMap rho) := by
  rw [QIT.MatrixMap.isCompletelyPositive_iff_choi, prepareMap_choi rho]
  exact Matrix.posSemidef_sum Finset.univ fun x _ =>
    (posSemidef_single x).kronecker (rho x).psd

theorem prepareMap_isTracePreserving {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → MState b) :
    MatrixMap.IsTracePreserving (prepareMap rho) := by
  intro X
  change (∑ x, X x x • (rho x).m).trace = X.trace
  calc
    (∑ x, X x x • (rho x).m).trace = ∑ x, X x x := by
      simp only [Matrix.trace_sum, Matrix.trace_smul]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp
    _ = X.trace := by
      rw [Matrix.trace]
      simp [Matrix.diag]

/-- The measurement map `X ↦ ∑ y, (X * M y).trace • |y⟩⟨y|`: it records the POVM outcome
probabilities of `M` on the diagonal of a classical output. -/
def measureMap {y : Type x} [Fintype y] [DecidableEq y]
    (M : POVM y a) : QIT.MatrixMap a y where
  toFun X := ∑ y, (X * M.effects y).trace • Matrix.single y y (1 : ℂ)
  map_add' X Y := by
    simp [Matrix.add_mul, Finset.sum_add_distrib, add_smul]
  map_smul' r X := by
    simp [Matrix.trace_smul, Finset.smul_sum]

theorem measureMap_apply {y : Type x} [Fintype y] [DecidableEq y]
    (M : POVM y a) (X : CMatrix a) :
    measureMap M X = ∑ y, (X * M.effects y).trace • Matrix.single y y (1 : ℂ) :=
  rfl

theorem measureMap_choi {y : Type x} [Fintype y] [DecidableEq y]
    (M : POVM y a) :
    QIT.MatrixMap.choi (measureMap M) =
      ∑ y, (Matrix.transpose (M.effects y)) ⊗ₖ (Matrix.single y y (1 : ℂ)) := by
  ext ay ay'
  rcases ay with ⟨a1, y1⟩
  rcases ay' with ⟨a2, y2⟩
  change
    ((∑ x, (Matrix.single a1 a2 (1 : ℂ) * M.effects x).trace • Matrix.single x x (1 : ℂ))
      y1 y2) =
      (∑ x, (Matrix.transpose (M.effects x)) ⊗ₖ (Matrix.single x x (1 : ℂ)))
        (a1, y1) (a2, y2)
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  change
    (∑ x,
      (Matrix.single a1 a2 (1 : ℂ) * M.effects x).trace *
        Matrix.single x x (1 : ℂ) y1 y2) =
      ∑ x, (M.effects x) a2 a1 * Matrix.single x x (1 : ℂ) y1 y2
  refine Finset.sum_congr rfl fun x _ => ?_
  have htrace :
      ((Matrix.single a1 a2 (1 : ℂ)) * M.effects x).trace = (M.effects x) a2 a1 := by
    simpa using (Matrix.trace_single_mul a1 a2 (1 : ℂ) (M.effects x))
  rw [htrace]

theorem measureMap_isCompletelyPositive {y : Type x} [Fintype y] [DecidableEq y]
    (M : POVM y a) :
    MatrixMap.IsCompletelyPositive (measureMap M) := by
  rw [QIT.MatrixMap.isCompletelyPositive_iff_choi, measureMap_choi M]
  exact Matrix.posSemidef_sum Finset.univ fun y _ =>
    (M.pos y).transpose.kronecker (posSemidef_single y)

theorem measureMap_isTracePreserving {y : Type x} [Fintype y] [DecidableEq y]
    (M : POVM y a) :
    MatrixMap.IsTracePreserving (measureMap M) := by
  intro X
  change (∑ y, (X * M.effects y).trace • Matrix.single y y (1 : ℂ)).trace = X.trace
  calc
    (∑ y, (X * M.effects y).trace • Matrix.single y y (1 : ℂ)).trace =
        ∑ y, (X * M.effects y).trace := by
      simp only [Matrix.trace_sum, Matrix.trace_smul]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp
    _ = (∑ y, X * M.effects y).trace := by
      rw [Matrix.trace_sum]
    _ = (X * ∑ y, M.effects y).trace := by
      congr 1
      simpa using (Matrix.mul_sum Finset.univ M.effects X).symm
    _ = (X * 1).trace := by rw [M.sum_eq_one]
    _ = X.trace := by simp

/-- A classical-quantum preparation channel from a finite register into states. -/
def prepare {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → MState b) : CPTPMap x b :=
  ofMat (prepareMap rho) (prepareMap_isCompletelyPositive rho)
    (prepareMap_isTracePreserving rho)

/-- The preparation channel acts by reading the diagonal classical weights. -/
@[simp]
theorem prepare_map {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → MState b) (X : CMatrix x) :
    (prepare rho).map X = ∑ x, X x x • (rho x).m := by
  rw [prepare, map_ofMat]
  rfl

/-- The preparation channel maps basis projectors to the prepared states. -/
theorem prepare_map_single_eq {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → MState b) (x0 : x) :
    (prepare rho).map (Matrix.single x0 x0 (1 : ℂ)) = (rho x0).m := by
  rw [prepare, map_ofMat]
  simpa using (prepareMap_single rho x0 x0)

/-- The identity channel on the unit system. -/
def unit : CPTPMap PUnit.{u + 1} PUnit.{v + 1} :=
  ofMat QIT.MatrixMap.unit QIT.MatrixMap.unit_isCompletelyPositive
    QIT.MatrixMap.unit_isTracePreserving

@[simp]
theorem unit_map : (unit : CPTPMap PUnit.{u + 1} PUnit.{v + 1}).map = QIT.MatrixMap.unit :=
  map_ofMat _ _ _

variable {c : Type w} {d : Type x}
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- The product channel acts componentwise on Kronecker products of matrices. -/
theorem prod_map_kronecker (Phi : CPTPMap a b) (Psi : CPTPMap c d)
    (X : CMatrix a) (Y : CMatrix c) :
    (prod Phi Psi).map (X ⊗ₖ Y) =
      (Phi.map X) ⊗ₖ (Psi.map Y) := by
  rw [prod_map]
  exact MatrixMap.kron_map_of_kron_state Phi.map Psi.map X Y

/-- Entrywise form of `prod_map_kronecker`. -/
theorem prod_map_kronecker_apply (Phi : CPTPMap a b) (Psi : CPTPMap c d)
    (X : CMatrix a) (Y : CMatrix c) (xb yb : b) (xd yd : d) :
    (prod Phi Psi).map (X ⊗ₖ Y) (xb, xd) (yb, yd) =
      Phi.map X xb yb * Psi.map Y xd yd := by
  rw [prod_map_kronecker]
  rfl

/-- Tracing out the first output of a product-channel output leaves the second
output marginal. -/
theorem traceLeft_applyState_prod (Phi : CPTPMap a b) (Psi : CPTPMap c d)
    (rho : MState a) (sigma : MState c) :
    Matrix.traceLeft ((Phi.prod Psi) (rho.prod sigma)).m = (Psi sigma).m := by
  rw [prod_apply_prod]
  exact MState.traceLeft_prod (Phi rho) (Psi sigma)

/-- Tracing out the second output of a product-channel output leaves the first
output marginal. -/
theorem traceRight_applyState_prod (Phi : CPTPMap a b) (Psi : CPTPMap c d)
    (rho : MState a) (sigma : MState c) :
    Matrix.traceRight ((Phi.prod Psi) (rho.prod sigma)).m = (Phi rho).m := by
  rw [prod_apply_prod]
  exact MState.traceRight_prod (Phi rho) (Psi sigma)

/-- Recursive tensor power of a channel for memoryless repeated uses. -/
def tensorPower (Phi : CPTPMap a b) :
    (n : ℕ) → CPTPMap (QIT.TensorPower a n) (QIT.TensorPower b n)
  | 0 => unit
  | n + 1 => Phi.prod (tensorPower Phi n)

/-- The zeroth channel tensor power is the unit-system identity channel. -/
theorem tensorPower_zero (Phi : CPTPMap a b) :
    tensorPower Phi 0 = unit := rfl

/-- The zeroth channel tensor power acts by the unit matrix map. -/
@[simp]
theorem tensorPower_zero_map (Phi : CPTPMap a b) :
    (tensorPower Phi 0).map =
      (QIT.MatrixMap.unit : QIT.MatrixMap (QIT.TensorPower a 0) (QIT.TensorPower b 0)) :=
  unit_map

/-- Successor channel tensor powers unfold by adding one product-channel factor. -/
theorem tensorPower_succ (Phi : CPTPMap a b) (n : ℕ) :
    tensorPower Phi (n + 1) = Phi.prod (tensorPower Phi n) := rfl

end CPTPOp

namespace POVM

variable {y : Type x} [Fintype y] [DecidableEq y]

/-- The measure-and-record channel returns the Born-rule diagonal classical state. -/
@[simp]
theorem measureDiscard_map (M : POVM y a) (X : CMatrix a) :
    M.measureDiscard.map X = ∑ y, (X * M.effects y).trace • Matrix.single y y (1 : ℂ) := by
  have hofMat :
      CPTPOp.ofMat (CPTPOp.measureMap M) (CPTPOp.measureMap_isCompletelyPositive M)
        (CPTPOp.measureMap_isTracePreserving M) = M.measureDiscard := by
    rw [CPTPOp.funext_iff]
    intro rho
    refine DensityOp.ext_m ?_
    rw [CPTPOp.mat_coe_eq_apply_mat, CPTPOp.map_ofMat, CPTPOp.measureMap_apply,
      POVM.measureDiscard_apply, MState.ofClassical, DensityOp.m_ofMat,
      HermitianMat.diagonal_mat, ← Matrix.sum_single_eq_diagonal]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    exact congrArg (Matrix.single y y) (M.coe_measure rho y).symm
  rw [← hofMat, CPTPOp.map_ofMat, CPTPOp.measureMap_apply]

/-- Measuring a state with a POVM yields a diagonal classical state. -/
theorem measureDiscard_map_state_diagonal (M : POVM y a) (rho : MState a) :
    M.measureDiscard.map rho.m =
      Matrix.diagonal (fun y => (rho.m * M.effects y).trace) := by
  rw [measureDiscard_map]
  simpa using (Matrix.sum_single_eq_diagonal fun y => (rho.m * M.effects y).trace)

end POVM

namespace MState

variable {c : Type w} [Fintype c] [DecidableEq c]

/-- Applying a channel on the right tensor factor to a product state leaves the
left factor untouched. -/
theorem applyState_id_prod_prod
    (rhoA : MState a) (sigmaB : MState b) (D : CPTPMap b c) :
    ((CPTPOp.id (dIn := a)).prod D) (rhoA.prod sigmaB) = rhoA.prod (D sigmaB) := by
  rw [CPTPOp.prod_apply_prod, CPTPOp.id_MState]

/-- Applying a channel on the left tensor factor to a product state leaves the
right factor untouched. -/
theorem applyState_prod_id_prod
    (rhoA : MState a) (sigmaB : MState b) (D : CPTPMap a c) :
    (D.prod (CPTPOp.id (dIn := b))) (rhoA.prod sigmaB) = MState.prod (D rhoA) sigmaB := by
  rw [CPTPOp.prod_apply_prod, CPTPOp.id_MState]

end MState
