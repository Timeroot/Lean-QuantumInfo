/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Map
public import QIT.Core.Measurement

/-!
# Channels

Finite-dimensional channels are complex-linear matrix maps equipped with
Choi-positive complete positivity and trace preservation data. Tensor products
of channels model parallel channel uses [HolevoGiovannetti2012QuantumChannels,
arxive.tex:965-974,1986-1993].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A finite-dimensional CPTP channel. -/
structure Channel (a : Type u) (b : Type v) [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] where
  map : MatrixMap a b
  completelyPositive : MatrixMap.IsCompletelyPositive map
  tracePreserving : MatrixMap.IsTracePreserving map
  mapsPositive : forall X : CMatrix a, X.PosSemidef -> (map X).PosSemidef

namespace Channel

def applyState (Phi : Channel a b) (rho : State a) : State b where
  matrix := Phi.map rho.matrix
  pos := Phi.mapsPositive rho.matrix rho.pos
  trace_eq_one := by
    rw [Phi.tracePreserving rho.matrix, rho.trace_eq_one]

variable {c : Type w}
variable [Fintype c] [DecidableEq c]

/-- Composition of finite-dimensional quantum channels. -/
def comp (Psi : Channel b c) (Phi : Channel a b) : Channel a c where
  map := Psi.map.comp Phi.map
  completelyPositive :=
    MatrixMap.isCompletelyPositive_comp Psi.map Phi.map
      Psi.completelyPositive Phi.completelyPositive
  tracePreserving :=
    MatrixMap.isTracePreserving_comp Psi.map Phi.map
      Psi.tracePreserving Phi.tracePreserving
  mapsPositive := by
    intro X hX
    exact Psi.mapsPositive (Phi.map X) (Phi.mapsPositive X hX)

/-- Applying a composed channel is the same as applying the two channels in
sequence. -/
theorem applyState_comp (Psi : Channel b c) (Phi : Channel a b) (rho : State a) :
    (Psi.comp Phi).applyState rho = Psi.applyState (Phi.applyState rho) := by
  apply State.ext
  rfl

def prepareMap {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → State b) : MatrixMap x b where
  toFun X := ∑ x, X x x • (rho x).matrix
  map_add' X Y := by
    simp [Finset.sum_add_distrib, add_smul]
  map_smul' r X := by
    simp [Finset.smul_sum, smul_smul]

theorem prepareMap_single {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → State b) (i i' : x) :
    prepareMap rho (Matrix.single i i' (1 : Complex)) =
      if i = i' then (rho i).matrix else (0 : CMatrix b) := by
  ext r s
  by_cases h : i = i'
  · subst h
    rw [if_pos rfl]
    change (∑ x, Matrix.single i i (1 : Complex) x x • (rho x).matrix) r s = (rho i).matrix r s
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
    change (∑ x, Matrix.single i i' (1 : Complex) x x • (rho x).matrix) r s = 0
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : i = x
    · have hx' : i' ≠ x := by
        intro hx'
        exact h (hx.trans hx'.symm)
      simp [Matrix.single, hx, hx']
    · simp [Matrix.single, hx]

theorem prepareMap_choi {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → State b) :
    MatrixMap.choi (prepareMap rho) =
      ∑ x, Matrix.kronecker (Matrix.single x x (1 : Complex)) (rho x).matrix := by
  ext xb xb'
  rcases xb with ⟨x, b1⟩
  rcases xb' with ⟨x', b2⟩
  by_cases h : x = x'
  · subst h
    rw [MatrixMap.choi, prepareMap_single rho x x, if_pos rfl]
    simp only [Matrix.sum_apply]
    rw [Finset.sum_eq_single x]
    · simp [Matrix.kronecker, Matrix.single]
    · intro z _ hz
      simp [Matrix.kronecker, Matrix.single, hz]
    · intro hx
      simp at hx
  · rw [MatrixMap.choi, prepareMap_single rho x x', if_neg h]
    simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.single]
    symm
    refine Finset.sum_eq_zero fun z _ => ?_
    have hneq : ¬ (z = x ∧ z = x') := by
      intro hz
      exact h (hz.1.symm.trans hz.2)
    simp [hneq]

theorem prepareMap_isCompletelyPositive {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → State b) :
    MatrixMap.IsCompletelyPositive (prepareMap rho) := by
  rw [MatrixMap.IsCompletelyPositive, prepareMap_choi rho]
  exact Matrix.posSemidef_sum Finset.univ fun x _ =>
    (posSemidef_single x).kronecker (rho x).pos

theorem prepareMap_isTracePreserving {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → State b) :
    MatrixMap.IsTracePreserving (prepareMap rho) := by
  intro X
  change (∑ x, X x x • (rho x).matrix).trace = X.trace
  calc
    (∑ x, X x x • (rho x).matrix).trace = ∑ x, X x x := by
      simp only [Matrix.trace_sum, Matrix.trace_smul]
      refine Finset.sum_congr rfl fun x _ => ?_
      simpa using congrArg (fun z => X x x • z) (rho x).trace_eq_one
    _ = X.trace := by
      rw [Matrix.trace]
      simp [Matrix.diag]

def measureMap {y : Type x} [Fintype y] [DecidableEq y]
    (M : POVM y a) : MatrixMap a y where
  toFun X := ∑ y, (X * M.effects y).trace • Matrix.single y y (1 : Complex)
  map_add' X Y := by
    simp [Matrix.add_mul, Finset.sum_add_distrib, add_smul]
  map_smul' r X := by
    simp [Matrix.trace_smul, Finset.smul_sum]

theorem measureMap_choi {y : Type x} [Fintype y] [DecidableEq y]
    (M : POVM y a) :
    MatrixMap.choi (measureMap M) =
      ∑ y, Matrix.kronecker (Matrix.transpose (M.effects y)) (Matrix.single y y (1 : Complex)) := by
  ext ay ay'
  rcases ay with ⟨a1, y1⟩
  rcases ay' with ⟨a2, y2⟩
  change
    ((∑ x, (Matrix.single a1 a2 (1 : Complex) * M.effects x).trace • Matrix.single x x (1 : Complex))
      y1 y2) =
      (∑ x, Matrix.kronecker (Matrix.transpose (M.effects x)) (Matrix.single x x (1 : Complex)))
        (a1, y1) (a2, y2)
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker]
  change
    (∑ x,
      (Matrix.single a1 a2 (1 : Complex) * M.effects x).trace *
        Matrix.single x x (1 : Complex) y1 y2) =
      ∑ x, (M.effects x) a2 a1 * Matrix.single x x (1 : Complex) y1 y2
  refine Finset.sum_congr rfl fun x _ => ?_
  have htrace :
      ((Matrix.single a1 a2 (1 : Complex)) * M.effects x).trace = (M.effects x) a2 a1 := by
    simpa using (Matrix.trace_single_mul a1 a2 (1 : Complex) (M.effects x))
  rw [htrace]

theorem measureMap_isCompletelyPositive {y : Type x} [Fintype y] [DecidableEq y]
    (M : POVM y a) :
    MatrixMap.IsCompletelyPositive (measureMap M) := by
  rw [MatrixMap.IsCompletelyPositive, measureMap_choi M]
  exact Matrix.posSemidef_sum Finset.univ fun y _ =>
    (M.pos y).transpose.kronecker (posSemidef_single y)

theorem measureMap_isTracePreserving {y : Type x} [Fintype y] [DecidableEq y]
    (M : POVM y a) :
    MatrixMap.IsTracePreserving (measureMap M) := by
  intro X
  change (∑ y, (X * M.effects y).trace • Matrix.single y y (1 : Complex)).trace = X.trace
  calc
    (∑ y, (X * M.effects y).trace • Matrix.single y y (1 : Complex)).trace =
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
    (rho : x → State b) : Channel x b where
  map := prepareMap rho
  completelyPositive := prepareMap_isCompletelyPositive rho
  tracePreserving := prepareMap_isTracePreserving rho
  mapsPositive :=
    MatrixMap.isCompletelyPositive_mapsPositive (prepareMap rho)
      (prepareMap_isCompletelyPositive rho)

/-- A quantum-classical measurement channel associated to a discrete POVM. -/
def measure {y : Type x} [Fintype y] [DecidableEq y]
    (M : POVM y a) : Channel a y where
  map := measureMap M
  completelyPositive := measureMap_isCompletelyPositive M
  tracePreserving := measureMap_isTracePreserving M
  mapsPositive :=
    MatrixMap.isCompletelyPositive_mapsPositive (measureMap M)
      (measureMap_isCompletelyPositive M)

/-- The preparation channel acts by reading the diagonal classical weights. -/
@[simp]
theorem prepare_map {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → State b) (X : CMatrix x) :
    (prepare rho).map X = ∑ x, X x x • (rho x).matrix := by
  show prepareMap rho X = _
  rfl

/-- The preparation channel maps basis projectors to the prepared states. -/
theorem prepare_map_single_eq {x : Type w} [Fintype x] [DecidableEq x]
    (rho : x → State b) (x0 : x) :
    (prepare rho).map (Matrix.single x0 x0 (1 : Complex)) = (rho x0).matrix := by
  simpa [prepare_map] using (prepareMap_single rho x0 x0)

/-- The measurement channel returns the Born-rule diagonal classical state. -/
@[simp]
theorem measure_map {y : Type x} [Fintype y] [DecidableEq y]
    (M : POVM y a) (X : CMatrix a) :
    (measure M).map X = ∑ y, (X * M.effects y).trace • Matrix.single y y (1 : Complex) := by
  show measureMap M X = _
  rfl

/-- The measurement channel applied to a state yields a diagonal classical state. -/
theorem measure_map_state_diagonal {y : Type x} [Fintype y] [DecidableEq y]
    (M : POVM y a) (rho : State a) :
    (measure M).map rho.matrix =
      Matrix.diagonal (fun y => (rho.matrix * M.effects y).trace) := by
  rw [measure_map]
  simpa using (Matrix.sum_single_eq_diagonal fun y => (rho.matrix * M.effects y).trace)

/-- The identity channel on the unit system. -/
def unit : Channel PUnit.{u + 1} PUnit.{v + 1} where
  map := MatrixMap.unit
  completelyPositive := MatrixMap.unit_isCompletelyPositive
  tracePreserving := MatrixMap.unit_isTracePreserving
  mapsPositive := MatrixMap.unit_mapsPositive

/-- The identity channel on an arbitrary finite system, realized as a
single-Kraus map with the identity operator as its sole Kraus operator. -/
def idChannel (a : Type u) [Fintype a] [DecidableEq a] : Channel a a where
  map := MatrixMap.ofKraus (fun (_ : Unit) => (1 : CMatrix a))
  completelyPositive := by
    rw [MatrixMap.IsCompletelyPositive, MatrixMap.choi_ofKraus]
    exact Matrix.posSemidef_sum Finset.univ (fun _ _ =>
      Matrix.posSemidef_vecMulVec_self_star
        (fun x : a × a => (1 : CMatrix a) x.2 x.1))
  tracePreserving := by
    intro X
    show (MatrixMap.ofKraus (fun (_ : Unit) => (1 : CMatrix a)) X).trace = X.trace
    simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    simp
  mapsPositive := MatrixMap.ofKraus_mapsPositive (fun (_ : Unit) => (1 : CMatrix a))

variable {c : Type w} {d : Type x}
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- An `n`-use channel surface between recursive tensor-power systems. -/
abbrev TensorPower (a : Type u) (b : Type v) [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (n : Nat) :=
  Channel (QIT.TensorPower a n) (QIT.TensorPower b n)

/-- Product channel between tensor-product systems. Tensor products of channels
model parallel or block channels and are again completely positive
[HolevoGiovannetti2012QuantumChannels, arxive.tex:965-974]. -/
def prod (Phi : Channel a b) (Psi : Channel c d) : Channel (Prod a c) (Prod b d) where
  map := MatrixMap.kron Phi.map Psi.map
  completelyPositive :=
    MatrixMap.isCompletelyPositive_kron Phi.map Psi.map
      Phi.completelyPositive Psi.completelyPositive
  tracePreserving :=
    MatrixMap.isTracePreserving_kron Phi.map Psi.map
      Phi.tracePreserving Psi.tracePreserving
  mapsPositive :=
    MatrixMap.isCompletelyPositive_mapsPositive (MatrixMap.kron Phi.map Psi.map)
      (MatrixMap.isCompletelyPositive_kron Phi.map Psi.map
        Phi.completelyPositive Psi.completelyPositive)

/-- The product channel acts componentwise on Kronecker products of matrices. -/
theorem prod_map_kronecker (Phi : Channel a b) (Psi : Channel c d)
    (X : CMatrix a) (Y : CMatrix c) :
    (prod Phi Psi).map (Matrix.kronecker X Y) =
      Matrix.kronecker (Phi.map X) (Psi.map Y) :=
  MatrixMap.kron_apply_kronecker Phi.map Psi.map X Y

/-- A product channel sends product states to product states. This derived lemma
follows from the product-channel action law and the product-state definition
[Wilde2011Qst, qit-notes.tex:7294-7299]. -/
theorem applyState_prod (Phi : Channel a b) (Psi : Channel c d)
    (rho : State a) (sigma : State c) :
    (Phi.prod Psi).applyState (rho.prod sigma) = (Phi.applyState rho).prod (Psi.applyState sigma) := by
  apply State.ext
  change (Phi.prod Psi).map (Matrix.kronecker rho.matrix sigma.matrix) =
    Matrix.kronecker (Phi.map rho.matrix) (Psi.map sigma.matrix)
  exact prod_map_kronecker Phi Psi rho.matrix sigma.matrix

/-- Tracing out the first output of a product-channel output leaves the second
output marginal. -/
theorem partialTraceA_applyState_prod (Phi : Channel a b) (Psi : Channel c d)
    (rho : State a) (sigma : State c) :
    partialTraceA (a := b) (b := d) ((Phi.prod Psi).applyState (rho.prod sigma)).matrix =
      (Psi.applyState sigma).matrix := by
  rw [applyState_prod]
  exact State.partialTraceA_prod (Phi.applyState rho) (Psi.applyState sigma)

/-- Tracing out the second output of a product-channel output leaves the first
output marginal. -/
theorem partialTraceB_applyState_prod (Phi : Channel a b) (Psi : Channel c d)
    (rho : State a) (sigma : State c) :
    partialTraceB (a := b) (b := d) ((Phi.prod Psi).applyState (rho.prod sigma)).matrix =
      (Phi.applyState rho).matrix := by
  rw [applyState_prod]
  exact State.partialTraceB_prod (Phi.applyState rho) (Psi.applyState sigma)

end Channel

namespace State

variable {c : Type w} [Fintype c] [DecidableEq c]

/-- The identity channel leaves every input state unchanged. -/
theorem idChannel_applyState (rho : State a) :
    (Channel.idChannel a).applyState rho = rho := by
  apply State.ext
  change (Channel.idChannel a).map rho.matrix = rho.matrix
  simp [Channel.idChannel, MatrixMap.ofKraus]

/-- Applying a channel on the right tensor factor to a product state leaves the
left factor untouched. -/
theorem applyState_id_prod_prod
    (rhoA : State a) (sigmaB : State b) (D : Channel b c) :
    ((Channel.idChannel a).prod D).applyState (rhoA.prod sigmaB) =
      rhoA.prod (D.applyState sigmaB) := by
  rw [Channel.applyState_prod, idChannel_applyState]

/-- Applying a channel on the left tensor factor to a product state leaves the
right factor untouched. -/
theorem applyState_prod_id_prod
    (rhoA : State a) (sigmaB : State b) (D : Channel a c) :
    (D.prod (Channel.idChannel b)).applyState (rhoA.prod sigmaB) =
      (D.applyState rhoA).prod sigmaB := by
  rw [Channel.applyState_prod, idChannel_applyState]

end State

namespace Channel

variable (Phi : Channel a b)

/-- Recursive tensor power of a channel for memoryless repeated uses. -/
def tensorPower : (n : Nat) -> TensorPower a b n
  | 0 => unit
  | n + 1 => Phi.prod (tensorPower n)

/-- The zeroth channel tensor power is the unit-system identity channel. -/
theorem tensorPower_zero :
    tensorPower Phi 0 = unit := rfl

/-- Successor channel tensor powers unfold by adding one product-channel factor. -/
theorem tensorPower_succ (n : Nat) :
    tensorPower Phi (n + 1) = Phi.prod (tensorPower Phi n) := rfl

end Channel

end

end QIT
