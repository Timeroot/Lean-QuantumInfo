/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Nonlocality.Bell
public import QIT.Measurements.Naimark

/-!
# Projective quantum realizations

This module packages the finite Naimark-family construction into a
projective-measurement Bell realization.  It is the behavior-level bridge for
the POVM-to-projective reduction recorded in
[ColadangeloGohScarani2016SelfTesting, all_pure_v2.tex:124-128] and
[MayersYao2003SelfTesting, mayers-yao-2003-self-testing.tex:307-325].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Kronecker

namespace QIT

universe uX uY uA uB

noncomputable section

namespace ProjectiveMeasurement

variable {A : Type uA} {B : Type uB} {HA HB : Type _}
variable [Fintype A] [Fintype B]
variable [Fintype HA] [Fintype HB] [DecidableEq HA] [DecidableEq HB]

/-- Tensor product of two finite projective measurements. -/
def kronecker (PA : ProjectiveMeasurement A HA) (PB : ProjectiveMeasurement B HB) :
    ProjectiveMeasurement (A × B) (HA × HB) where
  effects outcome := Matrix.kronecker (PA.effects outcome.1) (PB.effects outcome.2)
  isHermitian outcome := by
    change Matrix.conjTranspose (PA.effects outcome.1 ⊗ₖ PB.effects outcome.2) =
      PA.effects outcome.1 ⊗ₖ PB.effects outcome.2
    rw [Matrix.conjTranspose_kronecker, PA.isHermitian outcome.1, PB.isHermitian outcome.2]
  idempotent outcome := by
    change (PA.effects outcome.1 ⊗ₖ PB.effects outcome.2) *
        (PA.effects outcome.1 ⊗ₖ PB.effects outcome.2) =
      PA.effects outcome.1 ⊗ₖ PB.effects outcome.2
    rw [← Matrix.mul_kronecker_mul, PA.idempotent outcome.1, PB.idempotent outcome.2]
  orthogonal i j hij := by
    change (PA.effects i.1 ⊗ₖ PB.effects i.2) *
        (PA.effects j.1 ⊗ₖ PB.effects j.2) = 0
    rw [← Matrix.mul_kronecker_mul]
    by_cases hA : i.1 = j.1
    · have hB : i.2 ≠ j.2 := by
        intro h
        exact hij (Prod.ext hA h)
      rw [PB.orthogonal i.2 j.2 hB]
      simp
    · rw [PA.orthogonal i.1 j.1 hA]
      simp
  sum_eq_one := by
    ext i j
    rw [Matrix.sum_apply]
    change ∑ outcome : A × B,
        PA.effects outcome.1 i.1 j.1 * PB.effects outcome.2 i.2 j.2 =
      (1 : CMatrix (HA × HB)) i j
    rw [Fintype.sum_prod_type]
    calc
      ∑ x, ∑ x_1, PA.effects x i.1 j.1 * PB.effects x_1 i.2 j.2
          = (∑ x, PA.effects x i.1 j.1) * (∑ x_1, PB.effects x_1 i.2 j.2) := by
            symm
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [Finset.mul_sum]
      _ = (1 : CMatrix HA) i.1 j.1 * (1 : CMatrix HB) i.2 j.2 := by
            rw [← Matrix.sum_apply, PA.sum_eq_one, ← Matrix.sum_apply, PB.sum_eq_one]
      _ = if i = j then 1 else 0 := by
            by_cases hA : i.1 = j.1 <;> by_cases hB : i.2 = j.2 <;>
              simp [Matrix.one_apply, Prod.ext_iff, hA, hB]

@[simp]
theorem kronecker_effects (PA : ProjectiveMeasurement A HA)
    (PB : ProjectiveMeasurement B HB) (outcome : A × B) :
    (kronecker PA PB).effects outcome =
      Matrix.kronecker (PA.effects outcome.1) (PB.effects outcome.2) :=
  rfl

end ProjectiveMeasurement

namespace POVM

variable {settings : Type uX} {outcomes : Type uA} {system : Type uB}
variable [Fintype outcomes] [DecidableEq outcomes] [Inhabited outcomes]
variable [Fintype system] [DecidableEq system]

/-- Compressing a shared-family Naimark projector recovers the selected POVM effect. -/
theorem familyNaimark_compression_projector (M : settings → POVM outcomes system)
    (setting : settings) (outcome : outcomes) :
    Matrix.conjTranspose (familyNaimarkEmbedding M) *
        (familyNaimarkProjectiveMeasurement M setting).effects outcome *
        familyNaimarkEmbedding M =
      (M setting).effects outcome := by
  simpa [familyNaimarkEmbedding, familyNaimarkProjectiveMeasurement, fixedNaimarkEmbedding]
    using (M setting).fixedNaimark_compression_projector outcome

end POVM

namespace Bell

variable {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]

/--
A finite tensor-product projective quantum realization of a Bell behavior.
It mirrors `QuantumRealization`, with local and joint projective measurements.
-/
structure ProjectiveQuantumRealization
    (X : Type uX) (Y : Type uY) (A : Type uA) (B : Type uB)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] where
  HA : Type (max uX uY uA uB)
  HB : Type (max uX uY uA uB)
  [fintypeHA : Fintype HA]
  [decidableEqHA : DecidableEq HA]
  [fintypeHB : Fintype HB]
  [decidableEqHB : DecidableEq HB]
  /-- Bipartite state shared by Alice and Bob. -/
  rho : State (HA × HB)
  /-- Alice's projective measurement for each setting. -/
  alice : X → ProjectiveMeasurement A HA
  /-- Bob's projective measurement for each setting. -/
  bob : Y → ProjectiveMeasurement B HB
  /-- Joint projective measurement for each settings pair. -/
  joint : X → Y → ProjectiveMeasurement (A × B) (HA × HB)
  /-- The joint projective measurement has tensor-product effects. -/
  joint_effects : ∀ x y outcome,
    (joint x y).effects outcome =
      Matrix.kronecker ((alice x).effects outcome.1) ((bob y).effects outcome.2)

namespace ProjectiveQuantumRealization

/-- Born-rule outcome probability of a tensor-product projective realization. -/
def prob (realization : ProjectiveQuantumRealization X Y A B)
    (a : A) (b : B) (x : X) (y : Y) : ℝ≥0 :=
  letI : Fintype realization.HA := realization.fintypeHA
  letI : DecidableEq realization.HA := realization.decidableEqHA
  letI : Fintype realization.HB := realization.fintypeHB
  letI : DecidableEq realization.HB := realization.decidableEqHB
  (realization.joint x y).toPOVM.prob realization.rho (a, b)

end ProjectiveQuantumRealization

namespace QuantumRealization

variable [Inhabited A] [Inhabited B]

variable (R : QuantumRealization X Y A B)

local instance : Fintype R.HA := R.fintypeHA
local instance : DecidableEq R.HA := R.decidableEqHA
local instance : Fintype R.HB := R.fintypeHB
local instance : DecidableEq R.HB := R.decidableEqHB

/-- Alice's shared family Naimark embedding for a realization. -/
def aliceFamilyEmbedding :
    Matrix (POVM.FamilyNaimarkSpace R.alice) R.HA ℂ :=
  POVM.familyNaimarkEmbedding R.alice

/-- Bob's shared family Naimark embedding for a realization. -/
def bobFamilyEmbedding :
    Matrix (POVM.FamilyNaimarkSpace R.bob) R.HB ℂ :=
  POVM.familyNaimarkEmbedding R.bob

/-- The tensor-product embedding for the two local family dilations. -/
def jointFamilyEmbedding :
    Matrix (POVM.FamilyNaimarkSpace R.alice × POVM.FamilyNaimarkSpace R.bob)
      (R.HA × R.HB) ℂ :=
  Matrix.kronecker R.aliceFamilyEmbedding R.bobFamilyEmbedding

theorem jointFamilyEmbedding_isometry :
    Matrix.conjTranspose R.jointFamilyEmbedding * R.jointFamilyEmbedding = 1 := by
  change Matrix.conjTranspose (R.aliceFamilyEmbedding ⊗ₖ R.bobFamilyEmbedding) *
      (R.aliceFamilyEmbedding ⊗ₖ R.bobFamilyEmbedding) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    aliceFamilyEmbedding, bobFamilyEmbedding,
    POVM.familyNaimarkEmbedding_isometry R.alice,
    POVM.familyNaimarkEmbedding_isometry R.bob, Matrix.one_kronecker_one]

/-- The shared lifted bipartite state for the local family dilations. -/
def projectiveState : State
    (POVM.FamilyNaimarkSpace R.alice × POVM.FamilyNaimarkSpace R.bob) where
  matrix := R.jointFamilyEmbedding * R.rho.matrix * Matrix.conjTranspose R.jointFamilyEmbedding
  pos := R.rho.pos.mul_mul_conjTranspose_same R.jointFamilyEmbedding
  trace_eq_one := by
    rw [Matrix.trace_mul_cycle, R.jointFamilyEmbedding_isometry, Matrix.one_mul, R.rho.trace_eq_one]

@[simp]
theorem projectiveState_matrix :
    R.projectiveState.matrix =
      R.jointFamilyEmbedding * R.rho.matrix * Matrix.conjTranspose R.jointFamilyEmbedding :=
  rfl

/-- The joint projective measurement induced by the local family dilations. -/
def projectiveJoint (x : X) (y : Y) :
    ProjectiveMeasurement (A × B)
      (POVM.FamilyNaimarkSpace R.alice × POVM.FamilyNaimarkSpace R.bob) :=
  ProjectiveMeasurement.kronecker
    (POVM.familyNaimarkProjectiveMeasurement R.alice x)
    (POVM.familyNaimarkProjectiveMeasurement R.bob y)

@[simp]
theorem projectiveJoint_effects (x : X) (y : Y) (outcome : A × B) :
    (R.projectiveJoint x y).effects outcome =
      Matrix.kronecker
        ((POVM.familyNaimarkProjectiveMeasurement R.alice x).effects outcome.1)
        ((POVM.familyNaimarkProjectiveMeasurement R.bob y).effects outcome.2) :=
  rfl

/-- Convert a POVM-based quantum realization to a projective one on enlarged local spaces. -/
def toProjective : ProjectiveQuantumRealization X Y A B where
  HA := POVM.FamilyNaimarkSpace R.alice
  HB := POVM.FamilyNaimarkSpace R.bob
  rho := R.projectiveState
  alice x := POVM.familyNaimarkProjectiveMeasurement R.alice x
  bob y := POVM.familyNaimarkProjectiveMeasurement R.bob y
  joint x y := R.projectiveJoint x y
  joint_effects _ _ _ := rfl

theorem jointFamily_compression_projector (x : X) (y : Y) (outcome : A × B) :
    Matrix.conjTranspose R.jointFamilyEmbedding *
        (R.projectiveJoint x y).effects outcome *
        R.jointFamilyEmbedding =
      Matrix.kronecker ((R.alice x).effects outcome.1) ((R.bob y).effects outcome.2) := by
  change Matrix.conjTranspose (R.aliceFamilyEmbedding ⊗ₖ R.bobFamilyEmbedding) *
        (((POVM.familyNaimarkProjectiveMeasurement R.alice x).effects outcome.1) ⊗ₖ
          ((POVM.familyNaimarkProjectiveMeasurement R.bob y).effects outcome.2)) *
        (R.aliceFamilyEmbedding ⊗ₖ R.bobFamilyEmbedding) =
      (R.alice x).effects outcome.1 ⊗ₖ (R.bob y).effects outcome.2
  rw [Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [aliceFamilyEmbedding, bobFamilyEmbedding]
  rw [POVM.familyNaimark_compression_projector R.alice x outcome.1,
    POVM.familyNaimark_compression_projector R.bob y outcome.2]

theorem projective_trace_joint_eq (x : X) (y : Y) (outcome : A × B) :
    (R.projectiveState.matrix * (R.projectiveJoint x y).effects outcome).trace =
      (R.rho.matrix * (R.joint x y).effects outcome).trace := by
  calc
    (R.projectiveState.matrix * (R.projectiveJoint x y).effects outcome).trace
        =
          (R.rho.matrix *
            (Matrix.conjTranspose R.jointFamilyEmbedding *
              (R.projectiveJoint x y).effects outcome *
              R.jointFamilyEmbedding)).trace := by
            rw [projectiveState_matrix]
            calc
              ((R.jointFamilyEmbedding * R.rho.matrix *
                      Matrix.conjTranspose R.jointFamilyEmbedding) *
                    (R.projectiveJoint x y).effects outcome).trace
                  =
                    (R.jointFamilyEmbedding * R.rho.matrix *
                      (Matrix.conjTranspose R.jointFamilyEmbedding *
                        (R.projectiveJoint x y).effects outcome)).trace := by
                    rw [Matrix.mul_assoc, Matrix.mul_assoc]
              _ =
                    (R.rho.matrix *
                      ((Matrix.conjTranspose R.jointFamilyEmbedding *
                          (R.projectiveJoint x y).effects outcome) *
                        R.jointFamilyEmbedding)).trace := by
                    rw [Matrix.trace_mul_cycle]
                    rw [Matrix.trace_mul_comm]
              _ =
                    (R.rho.matrix *
                      (Matrix.conjTranspose R.jointFamilyEmbedding *
                        (R.projectiveJoint x y).effects outcome *
                        R.jointFamilyEmbedding)).trace := by
                    rw [Matrix.mul_assoc]
    _ =
        (R.rho.matrix *
          Matrix.kronecker ((R.alice x).effects outcome.1) ((R.bob y).effects outcome.2)).trace := by
          rw [R.jointFamily_compression_projector x y outcome]
    _ = (R.rho.matrix * (R.joint x y).effects outcome).trace := by
          rw [R.joint_effects x y outcome]

/-- The projectivized realization preserves every behavior probability. -/
theorem toProjective_prob_eq (a : A) (b : B) (x : X) (y : Y) :
    R.toProjective.prob a b x y = R.prob a b x y := by
  letI : Fintype R.toProjective.HA := R.toProjective.fintypeHA
  letI : DecidableEq R.toProjective.HA := R.toProjective.decidableEqHA
  letI : Fintype R.toProjective.HB := R.toProjective.fintypeHB
  letI : DecidableEq R.toProjective.HB := R.toProjective.decidableEqHB
  apply NNReal.eq
  unfold ProjectiveQuantumRealization.prob QuantumRealization.prob toProjective
  rw [POVM.prob_eq_trace_re, POVM.prob_eq_trace_re]
  change Complex.re ((R.projectiveState.matrix * (R.projectiveJoint x y).effects (a, b)).trace) =
    Complex.re ((R.rho.matrix * (R.joint x y).effects (a, b)).trace)
  rw [R.projective_trace_joint_eq x y (a, b)]

/--
Every finite tensor-product POVM realization has a behavior-equivalent
projective realization on enlarged finite local spaces.
-/
theorem exists_projective_equivalent :
    ∃ PR : ProjectiveQuantumRealization X Y A B,
      ∀ a b x y, PR.prob a b x y = R.prob a b x y :=
  ⟨R.toProjective, R.toProjective_prob_eq⟩

end QuantumRealization

end Bell

namespace SelfTesting
namespace ProjectiveRealization

variable {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B] [Inhabited A] [Inhabited B]

/-- Public catalog entrypoint for replacing finite POVM realizations by projective ones. -/
public theorem main (R : Bell.QuantumRealization X Y A B) :
    ∃ PR : Bell.ProjectiveQuantumRealization X Y A B,
      ∀ a b x y, PR.prob a b x y = R.prob a b x y :=
  Bell.QuantumRealization.exists_projective_equivalent R

end ProjectiveRealization
end SelfTesting

end

end QIT
