/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Security.Key
public import QIT.Classical.CQState

/-!
# Two-universal hashing and extractor output states

Definition-level API for finite two-universal hash families and the
classical-quantum state obtained by publishing the seed and output.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT.Security

universe uF uZ uS ue

noncomputable section

variable {F : Type uF} {Z : Type uZ} {S : Type uS} {e : Type ue}
variable [Fintype F] [DecidableEq F]
variable [Fintype Z] [DecidableEq Z]
variable [Fintype S] [DecidableEq S]
variable [Fintype e] [DecidableEq e]

/-- A finite family of hash functions with an explicit seed distribution.

[Renner2005QkdSecurity, main.tex:6909-6918] -/
structure HashFamily (F : Type uF) (Z : Type uZ) (S : Type uS)
    [Fintype F] where
  /-- The hash function selected by a seed. -/
  hash : F -> Z -> S
  /-- The seed distribution. -/
  prob : F -> ℝ≥0
  /-- The seed distribution is normalized. -/
  prob_sum : (∑ f, prob f) = 1

namespace HashFamily

variable (H : HashFamily F Z S)

/-- Weighted collision contribution for one output value. -/
def collisionWeight (z z' : Z) (s : S) : ℝ≥0 :=
  ∑ f, if H.hash f z = s ∧ H.hash f z' = s then H.prob f else 0

omit [DecidableEq F] [Fintype Z] [DecidableEq Z] [Fintype S] in
@[simp]
theorem collisionWeight_eq_sum (z z' : Z) (s : S) :
    H.collisionWeight z z' s =
      ∑ f, if H.hash f z = s ∧ H.hash f z' = s then H.prob f else 0 :=
  rfl

/-- A two-universal hash family.

[Renner2005QkdSecurity, main.tex:6909-6918] -/
def TwoUniversal : Prop :=
  ∀ z z', z ≠ z' ->
    (∑ s, H.collisionWeight z z' s) ≤ (Fintype.card S : ℝ≥0)⁻¹

omit [DecidableEq F] [Fintype Z] [DecidableEq Z] in
@[simp]
theorem twoUniversal_iff :
    H.TwoUniversal ↔
      ∀ z z', z ≠ z' ->
        (∑ s, H.collisionWeight z z' s) ≤ (Fintype.card S : ℝ≥0)⁻¹ :=
  Iff.rfl

end HashFamily

variable [Nonempty F]

/-- Uniform seed distribution over a finite nonempty seed family. -/
def uniformHashProb : F -> ℝ≥0 :=
  fun _ => (Fintype.card F : ℝ≥0)⁻¹

omit [DecidableEq F] in
theorem uniformHashProb_sum :
    (∑ f : F, uniformHashProb (F := F) f) = 1 := by
  simp [uniformHashProb, Finset.sum_const, Fintype.card_ne_zero]

/-- A uniformly seeded hash family, as a weighted `HashFamily`.

[Tomamichel2015FiniteResources, apps.tex:312-315] -/
def UniformHashFamily (hash : F -> Z -> S) : HashFamily F Z S where
  hash := hash
  prob := uniformHashProb (F := F)
  prob_sum := uniformHashProb_sum (F := F)

omit [DecidableEq F] [Fintype Z] [DecidableEq Z] [Fintype S] [DecidableEq S] in
@[simp]
theorem uniformHashFamily_hash (hash : F -> Z -> S) (f : F) (z : Z) :
    (UniformHashFamily hash).hash f z = hash f z :=
  rfl

omit [DecidableEq F] [Fintype Z] [DecidableEq Z] [Fintype S] [DecidableEq S] in
@[simp]
theorem uniformHashFamily_prob (hash : F -> Z -> S) (f : F) :
    (UniformHashFamily hash).prob f = (Fintype.card F : ℝ≥0)⁻¹ :=
  rfl

/--
The uniformly seeded full family of all functions from `Z` to `S`.

[Tomamichel2015FiniteResources, apps.tex:312-315]
-/
def FullFunctionHashFamily (Z : Type uZ) (S : Type uS)
    [Fintype Z] [DecidableEq Z] [Fintype S] [DecidableEq S] [Nonempty S] :
    HashFamily (Z -> S) Z S :=
  UniformHashFamily (F := Z -> S) (Z := Z) (S := S) fun f z => f z

@[simp]
theorem fullFunctionHashFamily_hash
    {Z : Type uZ} {S : Type uS}
    [Fintype Z] [DecidableEq Z] [Fintype S] [DecidableEq S] [Nonempty S]
    (f : Z -> S) (z : Z) :
    (FullFunctionHashFamily (Z := Z) (S := S)).hash f z = f z :=
  rfl

@[simp]
theorem fullFunctionHashFamily_prob
    {Z : Type uZ} {S : Type uS}
    [Fintype Z] [DecidableEq Z] [Fintype S] [DecidableEq S] [Nonempty S]
    (f : Z -> S) :
    (FullFunctionHashFamily (Z := Z) (S := S)).prob f =
      (Fintype.card (Z -> S) : ℝ≥0)⁻¹ :=
  rfl

/--
The full-function hash family with output alphabet `Fin ell`.

The positive-length hypothesis supplies the nonempty output alphabet required
for the uniform full-function construction.
-/
def FinFullFunctionHashFamily (Z : Type uZ) (ell : Nat)
    [Fintype Z] [DecidableEq Z] (hell : 0 < ell) :
    HashFamily (Z -> Fin ell) Z (Fin ell) := by
  letI : Nonempty (Fin ell) := ⟨⟨0, hell⟩⟩
  exact FullFunctionHashFamily (Z := Z) (S := Fin ell)

variable (H : HashFamily F Z S)

/-- Seed-input ensemble before merging classical labels through the hash output. -/
def extractorOutputEnsemble (E : Ensemble Z e) : Ensemble (Z × F) e where
  probs := fun zf => E.probs zf.1 * H.prob zf.2
  weights_sum := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ z : Z, ∑ f : F, E.probs z * H.prob f) =
          ∑ z : Z, E.probs z * (∑ f : F, H.prob f) := by
        simp [Finset.mul_sum]
      _ = ∑ z : Z, E.probs z * 1 := by rw [H.prob_sum]
      _ = ∑ z : Z, E.probs z := by simp
      _ = 1 := E.weights_sum
  states := fun zf => E.states zf.1

omit [DecidableEq F] [DecidableEq Z] [Fintype S] [DecidableEq S] [Nonempty F] in
@[simp]
theorem extractorOutputEnsemble_probs (E : Ensemble Z e) (z : Z) (f : F) :
    (extractorOutputEnsemble H E).probs (z, f) = E.probs z * H.prob f :=
  rfl

/-- Output distribution on the published `(S,F)` registers. -/
def extractorOutputProb (E : Ensemble Z e) (out : S × F) : ℝ≥0 :=
  ∑ z, if H.hash out.2 z = out.1 then E.probs z * H.prob out.2 else 0

omit [DecidableEq F] [DecidableEq Z] [Fintype S] [Nonempty F] in
@[simp]
theorem extractorOutputProb_eq_sum (E : Ensemble Z e) (out : S × F) :
    extractorOutputProb H E out =
      ∑ z, if H.hash out.2 z = out.1 then E.probs z * H.prob out.2 else 0 :=
  rfl

/-- Extractor output matrix on `S × (F × E)`.

The register order is output key, public seed, then side information. -/
def extractorOutputMatrix (E : Ensemble Z e) : CMatrix (S × (F × e)) :=
  ∑ z, ∑ f,
    (E.probs z * H.prob f) •
      Matrix.kronecker
        (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
        (Matrix.kronecker (Matrix.single f f (1 : ℂ)) (E.states z).matrix)

omit [DecidableEq Z] [Fintype S] [Nonempty F] in
@[simp]
theorem extractorOutputMatrix_eq_sum (E : Ensemble Z e) :
    extractorOutputMatrix H E =
      ∑ z, ∑ f,
        (E.probs z * H.prob f) •
          Matrix.kronecker
            (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
            (Matrix.kronecker (Matrix.single f f (1 : ℂ)) (E.states z).matrix) :=
  rfl

/-- The extractor output cq-state with registers `S × (F × E)`. -/
def extractorOutputState (E : Ensemble Z e) : State (S × (F × e)) where
  matrix := extractorOutputMatrix H E
  pos := by
    unfold extractorOutputMatrix
    exact Matrix.posSemidef_sum Finset.univ fun z _ =>
      Matrix.posSemidef_sum Finset.univ fun f _ =>
        (((posSemidef_single (H.hash f z)).kronecker
          ((posSemidef_single f).kronecker (E.states z).pos)).smul
            (NNReal.coe_nonneg (E.probs z * H.prob f)))
  trace_eq_one := by
    unfold extractorOutputMatrix
    simp only [Matrix.trace_sum, Matrix.trace_smul]
    calc
      (∑ z : Z, ∑ f : F,
          (E.probs z * H.prob f) •
            (Matrix.kronecker
              (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
              (Matrix.kronecker (Matrix.single f f (1 : ℂ)) (E.states z).matrix)).trace) =
          ∑ z : Z, ∑ f : F, ((E.probs z * H.prob f : ℝ≥0) : ℂ) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        refine Finset.sum_congr rfl fun f _ => ?_
        have htrace :
            (Matrix.kronecker
              (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
              (Matrix.kronecker (Matrix.single f f (1 : ℂ)) (E.states z).matrix)).trace =
                1 := by
          have houter :
              (Matrix.kronecker
                (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ))
                (Matrix.kronecker (Matrix.single f f (1 : ℂ)) (E.states z).matrix)).trace =
                (Matrix.single (H.hash f z) (H.hash f z) (1 : ℂ)).trace *
                  (Matrix.kronecker (Matrix.single f f (1 : ℂ))
                    (E.states z).matrix).trace :=
            Matrix.trace_kronecker _ _
          have hinner :
              (Matrix.kronecker (Matrix.single f f (1 : ℂ))
                (E.states z).matrix).trace =
                (Matrix.single f f (1 : ℂ)).trace * (E.states z).matrix.trace :=
            Matrix.trace_kronecker _ _
          rw [houter, hinner, trace_single_one, if_pos rfl,
            trace_single_one, if_pos rfl, (E.states z).trace_eq_one]
          norm_num
        rw [htrace]
        exact (Algebra.algebraMap_eq_smul_one _).symm
      _ = ↑(∑ z : Z, ∑ f : F, E.probs z * H.prob f) := by
        simp
      _ = 1 := by
        have hsum :
            (∑ z : Z, ∑ f : F, E.probs z * H.prob f) = 1 := by
          calc
            (∑ z : Z, ∑ f : F, E.probs z * H.prob f) =
                ∑ z : Z, E.probs z * (∑ f : F, H.prob f) := by
              refine Finset.sum_congr rfl fun z _ => ?_
              rw [Finset.mul_sum]
            _ = ∑ z : Z, E.probs z * 1 := by rw [H.prob_sum]
            _ = ∑ z : Z, E.probs z := by simp
            _ = 1 := E.weights_sum
        simpa using congrArg (fun r : ℝ≥0 => (r : ℂ)) hsum

omit [DecidableEq Z] [Nonempty F] in
@[simp]
theorem extractorOutputState_matrix (E : Ensemble Z e) :
    (extractorOutputState H E).matrix = extractorOutputMatrix H E :=
  rfl

end

end QIT.Security
