/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.Source.Schumacher
public import QuantumLib.QIT.Channels.Diamond
public import QuantumLib.QIT.OneShot.GentleMeasurement
public import QuantumLib.QIT.Information.Entropy.Log2Lemmas

/-!
# Schumacher compression direct achievability

The direct coding theorem for Schumacher quantum data compression: the von
Neumann entropy `S(ρ) = ρ.schumacherRate` is an achievable compression rate
for an IID quantum source `ρ` under the joint (purification) trace-distance
error criterion `jointError`.

The construction is Wilde's typical-subspace compression code
[Wilde2011Qst, qit-notes.tex:31457-31598].  See the module docstring of the
closing section for the detailed proof outline.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

noncomputable section
open Filter
universe u v
attribute [local instance] Classical.propDecidable
variable {a : Type u} [Fintype a] [DecidableEq a]

open QIT

namespace MState

/-- The compressed register for typical-subspace compression: the subtype of
`ρ^{⊗ n}` eigenvalue indices whose eigenvalue is `(n, δ)`-typical. -/
def TypicalSubspaceIndex (ρ : MState a) (n : ℕ) (δ : ℝ) : Type u :=
  { i : TensorPower a n // typicalEigenvalue ρ n δ
      ((ρ.tensorPower n).psd.isHermitian.eigenvalues i) }

instance (ρ : MState a) (n : ℕ) (δ : ℝ) :
    Fintype (TypicalSubspaceIndex ρ n δ) :=
  inferInstanceAs (Fintype { i : TensorPower a n // typicalEigenvalue ρ n δ
      ((ρ.tensorPower n).psd.isHermitian.eigenvalues i) })

instance (ρ : MState a) (n : ℕ) (δ : ℝ) :
    DecidableEq (TypicalSubspaceIndex ρ n δ) :=
  inferInstanceAs (DecidableEq { i : TensorPower a n // typicalEigenvalue ρ n δ
      ((ρ.tensorPower n).psd.isHermitian.eigenvalues i) })

/-- The atypical eigenvalue indices, indexing the encoder's correction Kraus. -/
def AtypicalSubspaceIndex (ρ : MState a) (n : ℕ) (δ : ℝ) : Type u :=
  { i : TensorPower a n // ¬ typicalEigenvalue ρ n δ
      ((ρ.tensorPower n).psd.isHermitian.eigenvalues i) }

instance (ρ : MState a) (n : ℕ) (δ : ℝ) :
    Fintype (AtypicalSubspaceIndex ρ n δ) :=
  inferInstanceAs (Fintype { i : TensorPower a n // ¬ typicalEigenvalue ρ n δ
      ((ρ.tensorPower n).psd.isHermitian.eigenvalues i) })

instance (ρ : MState a) (n : ℕ) (δ : ℝ) :
    DecidableEq (AtypicalSubspaceIndex ρ n δ) :=
  inferInstanceAs (DecidableEq { i : TensorPower a n // ¬ typicalEigenvalue ρ n δ
      ((ρ.tensorPower n).psd.isHermitian.eigenvalues i) })

/-- The eigenbasis unitary of `ρ^{⊗ n}` (columns are orthonormal eigenvectors). -/
def tensorPowerEigenvectorUnitary (ρ : MState a) (n : ℕ) : CMatrix (TensorPower a n) :=
  (ρ.tensorPower n).psd.isHermitian.eigenvectorUnitary

/-- The eigenvalue mask selecting typical indices in the eigenbasis. -/
def typicalEigenvalueMask (ρ : MState a) (n : ℕ) (δ : ℝ) :
    TensorPower a n → ℂ :=
  fun i => if typicalEigenvalue ρ n δ
      ((ρ.tensorPower n).psd.isHermitian.eigenvalues i) then 1 else 0

/-- The typical-subspace isometry `V : An → W`, selecting the typical columns
of the eigenbasis unitary. -/
def typicalIsometry (ρ : MState a) (n : ℕ) (δ : ℝ) :
    Matrix (TensorPower a n) (TypicalSubspaceIndex ρ n δ) ℂ :=
  (tensorPowerEigenvectorUnitary ρ n).submatrix (fun x => x) Subtype.val

/-- Entries of the typical-subspace isometry are eigenbasis entries. -/
theorem typicalIsometry_apply (ρ : MState a) (n : ℕ) (δ : ℝ)
    (i : TensorPower a n) (j : TypicalSubspaceIndex ρ n δ) :
    typicalIsometry ρ n δ i j = tensorPowerEigenvectorUnitary ρ n i j.val := rfl

/-- Entries of the adjoint typical-subspace isometry are eigenbasis entries. -/
theorem conjTranspose_typicalIsometry_apply (ρ : MState a) (n : ℕ) (δ : ℝ)
    (j : TypicalSubspaceIndex ρ n δ) (i : TensorPower a n) :
    Matrix.conjTranspose (typicalIsometry ρ n δ) j i =
      Matrix.conjTranspose (tensorPowerEigenvectorUnitary ρ n) j.val i := rfl

/-- Sum over a subtype equals the full-index indicator sum. -/
private theorem sum_subtype_val_eq_indicator {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [AddCommMonoid β]
    (p : α → Prop) [DecidablePred p] (f : α → β) :
    ∑ j : { x // p x }, f j.val =
      ∑ k : α, (if p k then f k else 0) := by
  classical
  conv_rhs => rw [← Fintype.sum_subtype_add_sum_subtype p
    (fun k => (if p k then f k else 0))]
  have h1 : (∑ a : { x // p x }, (if p a.val then f a.val else 0)) =
      ∑ a : { x // p x }, f a.val :=
    Finset.sum_congr rfl (fun a _ => if_pos a.prop)
  have h2 : (∑ a : { x // ¬ p x }, (if p a.val then f a.val else 0)) = 0 :=
    Finset.sum_eq_zero (fun a _ => if_neg a.prop)
  rw [h1, h2, add_zero]

/-- The cardinality of the typical register equals the trace-count dimension. -/
theorem card_typicalSubspaceIndex (ρ : MState a) (n : ℕ) (δ : ℝ) :
    (Fintype.card (TypicalSubspaceIndex ρ n δ) : ℝ) =
      ρ.typicalSubspaceDimension n δ := by
  classical
  have hcard : (Fintype.card (TypicalSubspaceIndex ρ n δ) : ℝ) =
      ∑ _j : TypicalSubspaceIndex ρ n δ, (1 : ℝ) := by
    rw [Fintype.card, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  have h := sum_subtype_val_eq_indicator
    (p := fun i => typicalEigenvalue ρ n δ
      ((ρ.tensorPower n).psd.isHermitian.eigenvalues i))
    (fun _ : TensorPower a n => (1 : ℝ))
  rw [hcard]
  exact h

/-- `V† V = I_W`: the typical columns of a unitary are orthonormal. -/
theorem typicalIsometry_conjTranspose_mul_self (ρ : MState a) (n : ℕ) (δ : ℝ) :
    Matrix.conjTranspose (typicalIsometry ρ n δ) * typicalIsometry ρ n δ = 1 := by
  classical
  let U : CMatrix (TensorPower a n) := tensorPowerEigenvectorUnitary ρ n
  have hUstarU : Matrix.conjTranspose U * U = 1 :=
    Unitary.coe_star_mul_self _
  have hVdV : Matrix.conjTranspose (typicalIsometry ρ n δ) * typicalIsometry ρ n δ =
      (Matrix.conjTranspose U * U).submatrix Subtype.val Subtype.val :=
    (Matrix.submatrix_mul (Matrix.conjTranspose U) U Subtype.val
      (fun x => x) Subtype.val Function.bijective_id).symm
  rw [hVdV, hUstarU]
  ext j k
  show ((1 : CMatrix (TensorPower a n)).submatrix Subtype.val Subtype.val) j k
      = (1 : CMatrix (TypicalSubspaceIndex ρ n δ)) j k
  rw [Matrix.submatrix_apply]
  rw [show ((1 : CMatrix (TensorPower a n)) ((j : TensorPower a n))
        ((k : TensorPower a n))) =
      if ((j : TensorPower a n) = k) then (1 : ℂ) else 0 from Matrix.one_apply]
  rw [show ((1 : CMatrix (TypicalSubspaceIndex ρ n δ)) j k) =
      if (j = k) then (1 : ℂ) else 0 from Matrix.one_apply]
  by_cases hjk : j = k
  · have : (j : TensorPower a n) = k := congrArg Subtype.val hjk
    simp [hjk]
  · have hne : ¬ ((j : TensorPower a n) = k) := fun h => hjk (Subtype.ext h)
    simp [hjk, hne]

/-- `typicalSubspaceProjector` unfolds to the eigenbasis conjugated mask. -/
theorem typicalSubspaceProjector_eq (ρ : MState a) (n : ℕ) (δ : ℝ) :
    ρ.typicalSubspaceProjector n δ =
      tensorPowerEigenvectorUnitary ρ n *
        Matrix.diagonal (typicalEigenvalueMask ρ n δ) *
        Matrix.conjTranspose (tensorPowerEigenvectorUnitary ρ n) := by
  rfl

/-- Entry expansion of `A · diag d · A†`. -/
private theorem matrix_mul_diagonal_mul_conjTranspose_apply
    {α : Type u} [Fintype α] [DecidableEq α] (A : CMatrix α) (d : α → ℂ)
    (i i' : α) :
    (A * Matrix.diagonal d * Matrix.conjTranspose A) i i' =
      ∑ k : α, d k * (A i k * Matrix.conjTranspose A k i') := by
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  congr 1 with k
  have hinner : ∑ j : α, A i j * (if j = k then d j else 0) = A i k * d k := by
    have heq : ∑ j : α, A i j * (if j = k then d j else 0) =
        A i k * (if k = k then d k else 0) :=
      Finset.sum_eq_single k (fun j _ hjk => by simp only [if_neg hjk, mul_zero])
        fun h => (h (Finset.mem_univ k)).elim
    rw [heq, if_pos rfl]
  rw [hinner]
  ring

/-- `V V† = Pi`: the typical-column outer product is the typical projector. -/
theorem typicalIsometry_mul_conjTranspose (ρ : MState a) (n : ℕ) (δ : ℝ) :
    typicalIsometry ρ n δ * Matrix.conjTranspose (typicalIsometry ρ n δ) =
      ρ.typicalSubspaceProjector n δ := by
  classical
  rw [typicalSubspaceProjector_eq]
  ext i i'
  rw [matrix_mul_diagonal_mul_conjTranspose_apply]
  simp only [Matrix.mul_apply, typicalIsometry_apply, conjTranspose_typicalIsometry_apply]
  have hconv : (∑ x : TypicalSubspaceIndex ρ n δ,
      tensorPowerEigenvectorUnitary ρ n i x.val *
      Matrix.conjTranspose (tensorPowerEigenvectorUnitary ρ n) x.val i') =
      ∑ k : TensorPower a n,
        (if typicalEigenvalue ρ n δ ((ρ.tensorPower n).psd.isHermitian.eigenvalues k)
          then tensorPowerEigenvectorUnitary ρ n i k *
            Matrix.conjTranspose (tensorPowerEigenvectorUnitary ρ n) k i' else 0) := by
    exact sum_subtype_val_eq_indicator
      (p := fun j => typicalEigenvalue ρ n δ
        ((ρ.tensorPower n).psd.isHermitian.eigenvalues j))
      (fun j => tensorPowerEigenvectorUnitary ρ n i j *
        Matrix.conjTranspose (tensorPowerEigenvectorUnitary ρ n) j i')
  rw [hconv]
  simp only [typicalEigenvalueMask]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : typicalEigenvalue ρ n δ ((ρ.tensorPower n).psd.isHermitian.eigenvalues k)
  · simp only [hk, if_true, one_mul]
  · simp only [hk, if_false, zero_mul]

/-- The encoder's atypical-correction Kraus operator `K_l = |i₀⟩⟨φ_l|`, where
`|φ_l⟩` is the `l`-th atypical eigenvector of `ρ^{⊗ n}`. -/
def atypicalEncoderKraus (ρ : MState a) (n : ℕ) (δ : ℝ)
    (i0 : TypicalSubspaceIndex ρ n δ) (l : AtypicalSubspaceIndex ρ n δ) :
    Matrix (TypicalSubspaceIndex ρ n δ) (TensorPower a n) ℂ :=
  fun w j => if w = i0 then
    star (tensorPowerEigenvectorUnitary ρ n j l.val) else 0

/-- The encoder's full Kraus family: `{V†} ∪ {K_l : l atypical}`. -/
def typicalEncoderKraus (ρ : MState a) (n : ℕ) (δ : ℝ)
    (i0 : TypicalSubspaceIndex ρ n δ) :
    (Unit ⊕ AtypicalSubspaceIndex ρ n δ) →
      Matrix (TypicalSubspaceIndex ρ n δ) (TensorPower a n) ℂ :=
  fun e => match e with
    | Sum.inl _ => Matrix.conjTranspose (typicalIsometry ρ n δ)
    | Sum.inr l => atypicalEncoderKraus ρ n δ i0 l

/-- The encoder Kraus family is trace-preserving (`Σ_e K_e† K_e = I`). -/
theorem typicalEncoderKraus_krausAdjoint_one (ρ : MState a) (n : ℕ) (δ : ℝ)
    (i0 : TypicalSubspaceIndex ρ n δ) :
    MatrixMap.krausAdjoint (typicalEncoderKraus ρ n δ i0) (1 : CMatrix _) = 1 := by
  classical
  let U : CMatrix (TensorPower a n) := tensorPowerEigenvectorUnitary ρ n
  have hUU : U * Matrix.conjTranspose U = 1 := Unitary.coe_mul_star_self _
  have hPient : ∀ i i', ρ.typicalSubspaceProjector n δ i i' =
      ∑ k : TensorPower a n,
        (if typicalEigenvalue ρ n δ ((ρ.tensorPower n).psd.isHermitian.eigenvalues k)
          then U i k * Matrix.conjTranspose U k i' else 0) := by
    intro i i'
    rw [typicalSubspaceProjector_eq, matrix_mul_diagonal_mul_conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : typicalEigenvalue ρ n δ ((ρ.tensorPower n).psd.isHermitian.eigenvalues k)
    · simp only [hk, typicalEigenvalueMask, if_true, one_mul]
      rfl
    · simp only [hk, typicalEigenvalueMask, if_false, zero_mul]
  have hAtyp : ∀ i i',
      ∑ l : AtypicalSubspaceIndex ρ n δ,
        ((Matrix.conjTranspose (atypicalEncoderKraus ρ n δ i0 l) *
            atypicalEncoderKraus ρ n δ i0 l)) i i' =
        ∑ k : TensorPower a n,
          (if ¬ typicalEigenvalue ρ n δ ((ρ.tensorPower n).psd.isHermitian.eigenvalues k)
            then U i k * Matrix.conjTranspose U k i' else 0) := by
    intro i i'
    have hstep : ∑ l : AtypicalSubspaceIndex ρ n δ,
        ((Matrix.conjTranspose (atypicalEncoderKraus ρ n δ i0 l) *
            atypicalEncoderKraus ρ n δ i0 l)) i i' =
        ∑ l : AtypicalSubspaceIndex ρ n δ,
          (U i l.val * Matrix.conjTranspose U l.val i') := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Matrix.mul_apply, Finset.sum_eq_single i0]
      · simp only [atypicalEncoderKraus, Matrix.conjTranspose_apply, if_true,
          star_star]
        rfl
      · intro w _ hw
        simp only [atypicalEncoderKraus, Matrix.conjTranspose_apply, if_neg hw, star_zero,
          mul_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    rw [hstep]
    exact sum_subtype_val_eq_indicator
      (p := fun k => ¬ typicalEigenvalue ρ n δ
        ((ρ.tensorPower n).psd.isHermitian.eigenvalues k))
      (fun k => U i k * Matrix.conjTranspose U k i')
  ext i i'
  simp only [MatrixMap.krausAdjoint, Matrix.mul_one, Matrix.sum_apply,
    Fintype.sum_sum_type, Fintype.sum_unique, typicalEncoderKraus,
    Matrix.conjTranspose_conjTranspose]
  rw [typicalIsometry_mul_conjTranspose]
  rw [hPient (i := i) (i' := i')]
  rw [hAtyp i i']
  rw [← Finset.sum_add_distrib, ← hUU, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : typicalEigenvalue ρ n δ ((ρ.tensorPower n).psd.isHermitian.eigenvalues k)
  · have hnk : ¬ ¬ typicalEigenvalue ρ n δ ((ρ.tensorPower n).psd.isHermitian.eigenvalues k) :=
      fun h => h hk
    simp only [if_pos hk, if_neg hnk, add_zero]
  · simp only [if_neg hk, if_pos hk, zero_add]

/-- The decoder: isometry channel with single Kraus `V`. -/
def typicalDecoder (ρ : MState a) (n : ℕ) (δ : ℝ) :
    CPTPMap (TypicalSubspaceIndex ρ n δ) (TensorPower a n) :=
  CPTPOp.ofMat
    (MatrixMap.ofKraus (fun _ : Unit => typicalIsometry ρ n δ))
    (MatrixMap.ofKraus_completelyPositive _)
    (MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
      (by show ∑ _ : Unit, Matrix.conjTranspose (typicalIsometry ρ n δ) * (1 : CMatrix _) *
            typicalIsometry ρ n δ = 1
          simp [Matrix.mul_one,
            typicalIsometry_conjTranspose_mul_self]))

/-- The encoder: Wilde's typical-subspace compression channel. -/
def typicalEncoder (ρ : MState a) (n : ℕ) (δ : ℝ)
    (i0 : TypicalSubspaceIndex ρ n δ) :
    CPTPMap (TensorPower a n) (TypicalSubspaceIndex ρ n δ) :=
  CPTPOp.ofMat
    (MatrixMap.ofKraus (typicalEncoderKraus ρ n δ i0))
    (MatrixMap.ofKraus_completelyPositive _)
    (MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
      (typicalEncoderKraus_krausAdjoint_one ρ n δ i0))

/-- An atypical correction branch vanishes after the typical-support decoder.
The corresponding columns of the eigenbasis unitary have disjoint typicality
predicates, hence are orthogonal. -/
private theorem atypicalEncoderKraus_mul_typicalIsometry
    (ρ : MState a) (n : ℕ) (δ : ℝ)
    (i0 : TypicalSubspaceIndex ρ n δ)
    (l : AtypicalSubspaceIndex ρ n δ) :
    atypicalEncoderKraus ρ n δ i0 l * typicalIsometry ρ n δ = 0 := by
  classical
  let U : CMatrix (TensorPower a n) := tensorPowerEigenvectorUnitary ρ n
  have hUstarU : Matrix.conjTranspose U * U = 1 :=
    Unitary.coe_star_mul_self _
  ext w j
  by_cases hw : w = i0
  · subst w
    simp only [Matrix.mul_apply, atypicalEncoderKraus, typicalIsometry_apply,
      if_pos, Matrix.zero_apply]
    have hentry := congrArg (fun M : CMatrix (TensorPower a n) => M l.val j.val) hUstarU
    have hne : l.val ≠ j.val := by
      intro h
      exact l.prop (h ▸ j.prop)
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hne] using hentry
  · simp [Matrix.mul_apply, atypicalEncoderKraus, hw]

/-- Schumacher compression is lossless on the typical register: decoding into
the typical support and immediately re-encoding is the identity channel. -/
theorem typicalEncoder_comp_typicalDecoder_eq_idChannel
    (ρ : MState a) (n : ℕ) (δ : ℝ)
    (i0 : TypicalSubspaceIndex ρ n δ) :
    (typicalEncoder ρ n δ i0) ∘ₘ (typicalDecoder ρ n δ) =
      CPTPOp.id (dIn := TypicalSubspaceIndex ρ n δ) := by
  refine CPTPOp.ext_map ?_
  rw [CPTPOp.compose_map]
  simp only [typicalEncoder, typicalDecoder, CPTPOp.map_ofMat]
  rw [MatrixMap.ofKraus_comp_ofKraus]
  ext X i j
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_unique,
    typicalEncoderKraus]
  rw [typicalIsometry_conjTranspose_mul_self]
  simp only [one_mul, Matrix.conjTranspose_one, mul_one]
  have hatyp : ∀ l : AtypicalSubspaceIndex ρ n δ,
      atypicalEncoderKraus ρ n δ i0 l * typicalIsometry ρ n δ = 0 :=
    atypicalEncoderKraus_mul_typicalIsometry ρ n δ i0
  simp [hatyp, CPTPOp.id_map]

/-- The Schumacher compression code built from the typical isometry. -/
def typicalCompressionCode (ρ : MState a) (n : ℕ) (δ : ℝ)
    (i0 : TypicalSubspaceIndex ρ n δ) :
    SchumacherCompressionCode ρ n (TypicalSubspaceIndex ρ n δ) where
  encoder := typicalEncoder ρ n δ i0
  decoder := typicalDecoder ρ n δ

/-! ### Bipartite Kraus action

Tensoring an identity channel with a Kraus-form map `(ofKraus M)` acts on a
bipartite matrix as a sum of `I ⊗ M_k` conjugations.  Proved entry-wise via the slice formula
`MatrixMap.kron_idChannel_left_apply_slice` from `QIT.Channels.Diamond`. -/

section BipartiteKraus

variable {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {κ : Type v} [Fintype κ] [DecidableEq κ]

omit [DecidableEq β] in
/-- Entry of a `(I ⊗ A) X (I ⊗ A)ᴴ` conjugation collapses to a partial slice.
Here `A` is square on `β` (the right-factor system). -/
private theorem kron_one_mul_conjTranspose_entry (A : CMatrix β)
    (X : CMatrix (α × β)) (i : α) (d d' : β) (i' : α) :
    (((1 : CMatrix α) ⊗ₖ A) * X *
        ((1 : CMatrix α) ⊗ₖ A).conjTranspose) (i, d) (i', d') =
      ∑ p : β, ∑ q : β, A d p * X (i, p) (i', q) * star (A d' q) := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ite_mul, zero_mul, one_mul]
  -- Collapse the inner `α`-sum controlled by `if i = x_2`.
  have h1 : ∀ (x : α) (x_1 : β),
      ∑ x_2 : α, ∑ x_3 : β,
          (if i = x_2 then A d x_3 * X (x_2, x_3) (x, x_1) *
              star (if i' = x then A d' x_1 else 0) else (0 : ℂ)) =
        ∑ x_3 : β,
          (if i = i then A d x_3 * X (i, x_3) (x, x_1) *
              star (if i' = x then A d' x_1 else 0) else (0 : ℂ)) := by
    intro x x_1
    apply Finset.sum_eq_single (a := i)
    · intro x_2 _ hx2
      apply Finset.sum_eq_zero
      intro x_3 _
      exact if_neg hx2.symm
    · intro h
      exact (h (Finset.mem_univ i)).elim
  simp only [h1, ↓reduceIte]
  -- Collapse the outer `α`-sum (the `if i' = x` lives inside the `star`).
  have h2 :
      ∑ x : α,
        (∑ x_1 : β, ∑ x_3 : β,
          A d x_3 * X (i, x_3) (x, x_1) *
            star (if i' = x then A d' x_1 else (0 : ℂ))) =
        ∑ x_1 : β, ∑ x_3 : β,
          A d x_3 * X (i, x_3) (i', x_1) *
            star (if i' = i' then A d' x_1 else (0 : ℂ)) := by
    apply Finset.sum_eq_single (a := i')
    · intro x _ hx
      apply Finset.sum_eq_zero
      intro x_1 _
      apply Finset.sum_eq_zero
      intro x_3 _
      rw [if_neg hx.symm]
      simp
    · intro h
      exact (h (Finset.mem_univ i')).elim
  rw [h2]
  simp only [↓reduceIte]
  -- Reorder the two `β`-sums to match the right-hand side.
  rw [Finset.sum_comm]

omit [DecidableEq κ] in
/-- Tensoring the identity channel with a Kraus-form map acts entry-wise as a
sum of `(I ⊗ M_k) X (I ⊗ M_k)ᴴ` conjugations, in the natural slice form. -/
private theorem kron_idChannel_ofKraus_apply_entry
    (M : κ → CMatrix β) (X : CMatrix (α × β)) (i : α) (d d' : β) (i' : α) :
    (MatrixMap.kron (CPTPOp.id (dIn := α)).map (MatrixMap.ofKraus M) X)
        (i, d) (i', d') =
      ∑ k : κ, ∑ q : β, (∑ p : β, M k d p * X (i, p) (i', q)) * star (M k d' q) := by
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]

omit [DecidableEq κ] in
/-- The matrix form: `kron id (ofKraus M)` is the sum of `(I⊗M_k) X (I⊗M_k)ᴴ`
Kraus conjugations. -/
private theorem kron_idChannel_ofKraus_apply
    (M : κ → CMatrix β) (X : CMatrix (α × β)) :
    MatrixMap.kron (CPTPOp.id (dIn := α)).map (MatrixMap.ofKraus M) X =
      ∑ k, ((1 : CMatrix α) ⊗ₖ (M k)) * X *
        ((1 : CMatrix α) ⊗ₖ (M k)).conjTranspose := by
  ext ⟨i, d⟩ ⟨i', d'⟩
  rw [kron_idChannel_ofKraus_apply_entry]
  rw [show ((∑ k, ((1 : CMatrix α) ⊗ₖ (M k)) * X *
        ((1 : CMatrix α) ⊗ₖ (M k)).conjTranspose) :
        CMatrix (α × β)) (i, d) (i', d') =
      ∑ k, (((1 : CMatrix α) ⊗ₖ (M k)) * X *
        ((1 : CMatrix α) ⊗ₖ (M k)).conjTranspose) (i, d) (i', d') from
    Matrix.sum_apply (i, d) (i', d') Finset.univ _]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [kron_one_mul_conjTranspose_entry, Finset.sum_comm]
  congr 1 with q
  rw [Finset.sum_mul]

end BipartiteKraus

/-! ### The fidelity bound for typical-subspace compression

This section establishes the Wilde direct-achievability fidelity bound
[Wilde2011Qst, qit-notes.tex:31457-31598] for the typical-subspace compression
code built above: the joint (purification) trace-distance error is at most
`√(atypical) + atypical/2`, and the rate is at most `S(ρ) + δ`.  These two
estimates combine at the end of the section to give `schumacher_direct_achievable`.
-/

/-- The composed compression channel's Kraus family.  Index `(encoder idx, decoder idx)`;
the decoder contributes a single Kraus `V` (the typical isometry), so each entry is
`V · (encoder Kraus)`. -/
private def typicalCompressionKraus (ρ : MState a) (n : ℕ) (δ : ℝ)
    (i0 : TypicalSubspaceIndex ρ n δ) :
    ((Unit ⊕ AtypicalSubspaceIndex ρ n δ) × Unit) → CMatrix (TensorPower a n) :=
  fun kl => typicalIsometry ρ n δ * typicalEncoderKraus ρ n δ i0 kl.1

/-- `N := (typicalCompressionCode ρ n δ i0).decoder ∘ₘ …encoder` has Kraus form
`ofKraus (typicalCompressionKraus …)`, by `ofKraus_comp_ofKraus` applied to the
decoder's single-Kraus form and the encoder's Kraus family. -/
private theorem typicalCompression_comp_map_ofKraus (ρ : MState a) (n : ℕ) (δ : ℝ)
    (i0 : TypicalSubspaceIndex ρ n δ) :
    ((typicalCompressionCode ρ n δ i0).decoder ∘ₘ
      (typicalCompressionCode ρ n δ i0).encoder).map =
      MatrixMap.ofKraus (typicalCompressionKraus ρ n δ i0) := by
  rw [CPTPOp.compose_map]
  simp only [typicalCompressionCode, typicalEncoder, typicalDecoder, CPTPOp.map_ofMat]
  rw [MatrixMap.ofKraus_comp_ofKraus]
  rfl

/-- The atypical-correction Kraus operator `K_l = V · |i₀⟩⟨φ_l|`, obtained as the
decoder's isometry `V` times the `l`-th atypical encoder Kraus. -/
private def typicalCorrectionKraus (ρ : MState a) (n : ℕ) (δ : ℝ)
    (i0 : TypicalSubspaceIndex ρ n δ) (l : AtypicalSubspaceIndex ρ n δ) :
    CMatrix (TensorPower a n) :=
  typicalIsometry ρ n δ * atypicalEncoderKraus ρ n δ i0 l

/-- `ω.m` decomposes as `PiMat · φ · PiMat + ω_corr`, where `PiMat = I ⊗ Pi` is
the lifted typical projector and `ω_corr` is a sum of `(I ⊗ K_l) φ (I ⊗ K_l)ᴴ`
conjugations over the atypical encoder Kraus operators.  This is the bipartite
Kraus lemma applied to the composed channel `N = D ∘ E`, with the `Unit`-indexed
decoder Kraus collapsed and the encoder-Kraus sum split into the `V†` branch
(giving `V · V† = Pi`) and the atypical branch. -/
private theorem typicalCompression_omega_matrix_eq (ρ : MState a) (n : ℕ) (δ : ℝ)
    (i0 : TypicalSubspaceIndex ρ n δ)
    (φ : CMatrix (TensorPower a n × TensorPower a n)) :
    MatrixMap.kron (CPTPOp.id (dIn := TensorPower a n)).map
      (MatrixMap.ofKraus (typicalCompressionKraus ρ n δ i0)) φ =
    ((1 : CMatrix (TensorPower a n)) ⊗ₖ
      (ρ.typicalSubspaceProjector n δ)) * φ *
      ((1 : CMatrix _) ⊗ₖ
        (ρ.typicalSubspaceProjector n δ)).conjTranspose +
    ∑ l : AtypicalSubspaceIndex ρ n δ,
      ((1 : CMatrix _) ⊗ₖ
        (typicalCorrectionKraus ρ n δ i0 l)) * φ *
      ((1 : CMatrix _) ⊗ₖ
        (typicalCorrectionKraus ρ n δ i0 l)).conjTranspose := by
  rw [kron_idChannel_ofKraus_apply, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [Fintype.sum_unique]
  simp only [typicalCompressionKraus, typicalEncoderKraus, typicalCorrectionKraus]
  rw [typicalIsometry_mul_conjTranspose]

set_option maxRecDepth 4000 in
/-- The joint (purification) trace-distance error of the typical-subspace code is
at most `√(atypicalSubspaceSpectralWeight) + atypicalSubspaceSpectralWeight / 2`.

This is the Wilde direct-achievability fidelity bound
[Wilde2011Qst, qit-notes.tex:31457-31598]: splitting `ω.m` into the gentle
projective part `PiMat · φ · PiMat` (controlled by `gentle_projector`) and the PSD
correction sum (whose trace is exactly the atypical spectral weight), then
applying the trace-norm triangle. -/
public theorem typicalCompressionCode_jointError_le (ρ : MState a) (n : ℕ) (δ : ℝ)
    (i0 : TypicalSubspaceIndex ρ n δ) :
    (typicalCompressionCode ρ n δ i0).jointError ≤
      Real.sqrt (ρ.atypicalSubspaceSpectralWeight n δ) +
        ρ.atypicalSubspaceSpectralWeight n δ / 2 := by
  let An := QIT.TensorPower a n
  let Pi := ρ.typicalSubspaceProjector n δ
  let PiMat : CMatrix (An × An) := (1 : CMatrix An) ⊗ₖ Pi
  let ψ : Ket (a × a) := MState.canonicalPurification ρ
  let φ : MState (An × An) := ψ.state.tensorPowerBipartite n
  let C := typicalCompressionCode ρ n δ i0
  let N : CPTPMap An An := C.decoder ∘ₘ C.encoder
  let ω : MState (An × An) := ((CPTPOp.id (dIn := An)).prod N) φ
  let ω_corr : CMatrix (An × An) :=
    ∑ l : AtypicalSubspaceIndex ρ n δ,
      ((1 : CMatrix An) ⊗ₖ (typicalCorrectionKraus ρ n δ i0 l)) *
        φ.m *
      ((1 : CMatrix An) ⊗ₖ
        (typicalCorrectionKraus ρ n δ i0 l)).conjTranspose
  -- 0. `C.jointError = ½ · traceNorm (ω.m - φ.m)`.
  have herr_def : C.jointError = (1 / 2 : ℝ) * traceNorm (ω.m - φ.m) := by
    show (1 / 2 : ℝ) * QIT.traceNormDistance ω.m φ.m = _
    rw [traceNormDistance_eq_traceNorm_sub]
  -- 1. `PiMat.PosSemidef`, hence `PiMat.conjTranspose = PiMat`.
  have hPiMat_psd : PiMat.PosSemidef :=
    Matrix.PosSemidef.one.kronecker (ρ.typicalSubspaceProjector_posSemidef n δ)
  have hPiMat_cT : PiMat.conjTranspose = PiMat :=
    hPiMat_psd.isHermitian.eq
  -- 2. `PiMat * PiMat = PiMat` (idempotence of `I ⊗ Π`).
  have hPiMat_idem : PiMat * PiMat = PiMat := by
    show ((1 : CMatrix An) ⊗ₖ Pi) * ((1 : CMatrix An) ⊗ₖ Pi) = (1 ⊗ₖ Pi)
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one,
      ρ.typicalSubspaceProjector_idempotent n δ]
  -- 3. `Matrix.traceLeft φ.m = (ρ.tensorPower n).m`.
  have hψ_mB : ψ.state.traceLeft = ρ := by
    apply MState.ext
    rw [MState.traceLeft_m]
    exact canonicalPurification_purifies ρ
  have hφ_pTA : Matrix.traceLeft φ.m = (ρ.tensorPower n).m := by
    have hφmB : φ.traceLeft = ρ.tensorPower n := by
      rw [show φ = ψ.state.tensorPowerBipartite n from rfl,
        tensorPowerBipartite_traceLeft ψ.state n, hψ_mB]
    rw [← MState.traceLeft_m, hφmB]
  -- 4. `((PiMat * φ.m).trace).re = typicalSubspaceSpectralWeight ρ n δ`.
  have htrace_PiMat_φ : ((PiMat * φ.m).trace).re =
      ρ.typicalSubspaceSpectralWeight n δ := by
    have hkey : (((1 : CMatrix An) ⊗ₖ Pi) * φ.m).trace =
        (Pi * (ρ.tensorPower n).m).trace := by
      rw [trace_kronecker_one_mul_eq_trace_mul_traceLeft, hφ_pTA]
    rw [hkey, Matrix.trace_mul_comm,
      ρ.typicalSubspaceProjector_trace_mul_re n δ]
  -- 5. `ω.m = PiMat · φ · PiMat + ω_corr`.
  have hsplit : ω.m = PiMat * φ.m * PiMat + ω_corr := by
    have hN_map : N.map = MatrixMap.ofKraus (typicalCompressionKraus ρ n δ i0) :=
      typicalCompression_comp_map_ofKraus ρ n δ i0
    have hkey : ((CPTPOp.id (dIn := An)).prod N).map φ.m =
        MatrixMap.kron (CPTPOp.id (dIn := An)).map
          (MatrixMap.ofKraus (typicalCompressionKraus ρ n δ i0)) φ.m := by
      rw [CPTPOp.prod_map, hN_map]
    rw [show ω.m = ((CPTPOp.id (dIn := An)).prod N).map φ.m from
        CPTPOp.mat_coe_eq_apply_mat _ _, hkey,
      typicalCompression_omega_matrix_eq, hPiMat_cT]
  -- 6. `ω_corr.PosSemidef` (each summand `(I⊗K) φ (I⊗K)ᴴ` is PSD via
  -- `mul_mul_conjTranspose_same`; sum of PSD is PSD).
  have hω_corr_psd : ω_corr.PosSemidef := by
    show (∑ l : AtypicalSubspaceIndex ρ n δ,
        ((1 : CMatrix An) ⊗ₖ (typicalCorrectionKraus ρ n δ i0 l)) *
          φ.m *
        ((1 : CMatrix An) ⊗ₖ
          (typicalCorrectionKraus ρ n δ i0 l)).conjTranspose).PosSemidef
    exact Matrix.posSemidef_sum Finset.univ (fun l _ =>
      φ.psd.mul_mul_conjTranspose_same _)
  -- 7. `ω_corr.trace.re = atypicalSubspaceSpectralWeight`.  Use
  -- `ω.m.trace.re = 1`, `PiMat φ PiMat` trace `.re = typical weight`
  -- (idempotence + Step 4), and the partition identity.
  have htrace_ω : (ω.m.trace).re = 1 := by
    rw [show ω.m.trace = (1 : ℂ) from ω.tr']
    simp
  have htrace_PiMat_φ_PiMat : ((PiMat * φ.m * PiMat).trace).re =
      ρ.typicalSubspaceSpectralWeight n δ := by
    have hcyc : (PiMat * φ.m * PiMat).trace = (PiMat * φ.m).trace := by
      rw [Matrix.trace_mul_cycle, hPiMat_idem]
    rw [hcyc, htrace_PiMat_φ]
  have htrace_ω_corr : (ω_corr.trace).re = ρ.atypicalSubspaceSpectralWeight n δ := by
    have hsum : ω.m.trace = (PiMat * φ.m * PiMat).trace + ω_corr.trace := by
      rw [hsplit, Matrix.trace_add]
    have hre : (ω.m.trace).re =
        ((PiMat * φ.m * PiMat).trace).re + (ω_corr.trace).re := by
      have := congrArg Complex.re hsum
      simpa using this
    rw [htrace_ω, htrace_PiMat_φ_PiMat] at hre
    linarith [ρ.typicalSubspaceSpectralWeight_add_atypical n δ]
  -- 8. Trace-norm of `ω_corr` (PSD ⇒ traceNorm = real trace).
  have htn_ω_corr : traceNorm ω_corr = ρ.atypicalSubspaceSpectralWeight n δ := by
    rw [traceNorm_posSemidef_eq_trace_re _ hω_corr_psd, htrace_ω_corr]
  -- 9. Gentle projector bound on the projective part.
  have hgentle : traceNorm (PiMat * φ.m * PiMat - φ.m) ≤
      2 * Real.sqrt (ρ.atypicalSubspaceSpectralWeight n δ) := by
    have hg := gentle_projector PiMat hPiMat_psd hPiMat_idem φ
    have hsub : 1 - ((PiMat * φ.m).trace).re =
        ρ.atypicalSubspaceSpectralWeight n δ := by
      rw [htrace_PiMat_φ]
      linarith [ρ.typicalSubspaceSpectralWeight_add_atypical n δ]
    rw [hsub] at hg
    exact hg
  -- 10. Triangle: `traceNorm (ω.m - φ.m) ≤ 2√atypical + atypical`.
  have htri_diff : ω.m - φ.m =
      (PiMat * φ.m * PiMat - φ.m) + ω_corr := by
    rw [hsplit]
    abel
  have htn_total : traceNorm (ω.m - φ.m) ≤
      2 * Real.sqrt (ρ.atypicalSubspaceSpectralWeight n δ) +
        ρ.atypicalSubspaceSpectralWeight n δ := by
    rw [htri_diff]
    calc traceNorm ((PiMat * φ.m * PiMat - φ.m) + ω_corr)
          ≤ traceNorm (PiMat * φ.m * PiMat - φ.m) + traceNorm ω_corr :=
        traceNorm_add_le _ _
      _ ≤ 2 * Real.sqrt (ρ.atypicalSubspaceSpectralWeight n δ) +
            ρ.atypicalSubspaceSpectralWeight n δ := by
        rw [htn_ω_corr]
        exact add_le_add hgentle (le_refl _)
  -- 11. Convert back to `jointError`.
  rw [herr_def]
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hdiv : (1 / 2 : ℝ) *
      (2 * Real.sqrt (ρ.atypicalSubspaceSpectralWeight n δ) +
        ρ.atypicalSubspaceSpectralWeight n δ) =
      Real.sqrt (ρ.atypicalSubspaceSpectralWeight n δ) +
        ρ.atypicalSubspaceSpectralWeight n δ / 2 := by ring
  exact (mul_le_mul_of_nonneg_left htn_total (by norm_num)).trans hdiv.le

/-- The register rate of the typical compression code is at most `S(ρ) + δ`.

Uses `card_typicalSubspaceIndex`, `typicalSubspaceDimension_le_two_pow`, and the
base-two logarithm monotonicity / inversion lemmas (QIT's custom `log2`).  The
`Nonempty` of the typical register (provided by `i0`) gives the strict
positivity of `typicalSubspaceDimension` required by `log2_mono_of_pos`. -/
public theorem typicalCompressionCode_rate_le (ρ : MState a) (n : ℕ) (δ : ℝ)
    (hn : 1 ≤ n) (i0 : TypicalSubspaceIndex ρ n δ) :
    (typicalCompressionCode ρ n δ i0).rate ≤ ρ.schumacherRate + δ := by
  have hn_ne : n ≠ 0 := by omega
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcard_pos : (0 : ℝ) < (Fintype.card (TypicalSubspaceIndex ρ n δ) : ℝ) := by
    have : 0 < Fintype.card (TypicalSubspaceIndex ρ n δ) :=
      Fintype.card_pos_iff.mpr ⟨i0⟩
    exact_mod_cast this
  show schumacherRegisterRate (TypicalSubspaceIndex ρ n δ) n ≤ ρ.schumacherRate + δ
  rw [schumacherRegisterRate, if_neg hn_ne, card_typicalSubspaceIndex,
    div_le_iff₀ hnR_pos]
  have hdim_pos : 0 < ρ.typicalSubspaceDimension n δ := by
    rw [← card_typicalSubspaceIndex]
    exact hcard_pos
  have hdim_le : ρ.typicalSubspaceDimension n δ ≤
      2 ^ ((n : ℝ) * (ρ.vonNeumann + δ)) :=
    ρ.typicalSubspaceDimension_le_two_pow n δ
  have hlog2 : log2 (ρ.typicalSubspaceDimension n δ) ≤
      (n : ℝ) * (ρ.vonNeumann + δ) :=
    (log2_mono_of_pos hdim_pos hdim_le).trans (le_of_eq (log2_two_rpow _))
  rw [mul_comm]
  exact hlog2

/-- If the typical spectral weight is strictly positive, the typical register is
nonempty (at least one eigenvalue index is typical). -/
public theorem TypicalSubspaceIndex_nonempty_of_typical_pos
    (ρ : MState a) (n : ℕ) (δ : ℝ)
    (h : 0 < ρ.typicalSubspaceSpectralWeight n δ) :
    Nonempty (TypicalSubspaceIndex ρ n δ) := by
  classical
  by_contra hne
  rw [not_nonempty_iff, isEmpty_iff] at hne
  have htyp0 : ρ.typicalSubspaceSpectralWeight n δ = 0 := by
    unfold typicalSubspaceSpectralWeight
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : typicalEigenvalue ρ n δ
        ((ρ.tensorPower n).psd.isHermitian.eigenvalues i)
    · exact (hne ⟨i, hi⟩).elim
    · simp [hi]
  linarith

/-- The Schumacher direct coding theorem: the von Neumann entropy `S(ρ)` is an
achievable compression rate for an IID quantum source `ρ` under the joint
(purification) trace-distance error criterion `jointError`
[Wilde2011Qst, qit-notes.tex:31457-31598].

The proof provides a witness family indexed by `δ, ε > 0`: for all sufficiently
large block lengths `n ≥ N(δ, ε)`, the typical-subspace compression code has
rate at most `S(ρ) + δ` and joint error at most `ε`.  The error bound uses
`tendsto_atypicalSubspaceSpectralWeight` to drive the atypical spectral weight
below `min ((ε/2)²) (min ε 1)`, which bounds `√atypical + atypical/2 ≤ ε`
(by `typicalCompressionCode_jointError_le`) and ensures the typical register is
nonempty (by `TypicalSubspaceIndex_nonempty_of_typical_pos`). -/
theorem schumacher_direct_achievable (ρ : MState a) :
    ρ.IsAchievableSchumacherRate ρ.schumacherRate := by
  apply MState.schumacher_direct_achievable_of_typicalCompressionWitness
  intro δ hδ ε hε
  -- Cap `ε` at `1` so the atypical-weight threshold can be at most `1`, forcing
  -- `atypical < 1` and hence the typical register to be nonempty.
  set ε' : ℝ := min ε 1 with hε'_def
  have hε'_pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'_le1 : ε' ≤ 1 := min_le_right _ _
  have hε'_le_ε : ε' ≤ ε := min_le_left _ _
  -- Threshold τ = min ((ε'/2)²) ε'.
  set τ : ℝ := min ((ε' / 2) ^ 2) ε' with hτ_def
  have hτ_pos : 0 < τ := lt_min (by positivity) hε'_pos
  have hτ_le1 : τ ≤ 1 := le_trans (min_le_right _ _) hε'_le1
  -- Drive the atypical spectral weight below τ.
  have hlim : Tendsto (fun n : ℕ => ρ.atypicalSubspaceSpectralWeight n δ)
      atTop (nhds 0) :=
    ρ.tendsto_atypicalSubspaceSpectralWeight hδ
  have hball : ∀ᶠ n in atTop,
      ρ.atypicalSubspaceSpectralWeight n δ ∈ Metric.ball (0 : ℝ) τ :=
    hlim.eventually (Metric.ball_mem_nhds _ hτ_pos)
  have hev : ∀ᶠ n in atTop, ρ.atypicalSubspaceSpectralWeight n δ < τ := by
    filter_upwards [hball] with n hn
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hn
    exact lt_of_le_of_lt (le_abs_self _) hn
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  -- Choose `N = max N0 1` so block lengths `n ≥ N` satisfy both the atypical
  -- bound and `n ≥ 1` (needed for the rate bound).
  refine ⟨max N0 1, fun n hn => ?_⟩
  have hn_N0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn_atyp : ρ.atypicalSubspaceSpectralWeight n δ < τ := hN0 n hn_N0
  -- Typical register is nonempty: typical weight > 0 since atypical < 1.
  have htyp_pos : 0 < ρ.typicalSubspaceSpectralWeight n δ := by
    have h_atyp_lt1 : ρ.atypicalSubspaceSpectralWeight n δ < 1 :=
      lt_of_lt_of_le hn_atyp hτ_le1
    have hadd := ρ.typicalSubspaceSpectralWeight_add_atypical n δ
    linarith
  have hWi0 : Nonempty (TypicalSubspaceIndex ρ n δ) :=
    TypicalSubspaceIndex_nonempty_of_typical_pos ρ n δ htyp_pos
  obtain ⟨i0⟩ := hWi0
  -- Build the witness.
  refine ⟨TypicalSubspaceIndex ρ n δ, inferInstance, inferInstance, ?_⟩
  refine ⟨⟨typicalCompressionCode ρ n δ i0, ?_, ?_⟩⟩
  · exact typicalCompressionCode_rate_le ρ n δ hn1 i0
  · -- jointError ≤ √atypical + atypical/2 ≤ ε'/2 + ε'/2 = ε' ≤ ε
    have hjoint := typicalCompressionCode_jointError_le ρ n δ i0
    have h_atyp_sq : ρ.atypicalSubspaceSpectralWeight n δ ≤ (ε' / 2) ^ 2 :=
      le_trans hn_atyp.le (min_le_left _ _)
    have h_atyp_e' : ρ.atypicalSubspaceSpectralWeight n δ ≤ ε' :=
      le_trans hn_atyp.le (min_le_right _ _)
    have hsqrt : Real.sqrt (ρ.atypicalSubspaceSpectralWeight n δ) ≤ ε' / 2 := by
      rw [Real.sqrt_le_iff]
      refine ⟨div_nonneg hε'_pos.le (by norm_num), h_atyp_sq⟩
    linarith

end MState
