import LeanQEC.States.PState

noncomputable section

def qub_zero : PState 1 := (Equiv.arrowCongr beq (Equiv.refl _)) ![(1 : ℂ), 0]

def qub_one : PState 1 := (Equiv.arrowCongr beq (Equiv.refl _)) ![(0 : ℂ), 1]

@[simp] lemma qub_zero_zero : qub_zero 0#1 = 1 := by
  simp [qub_zero, beq, BitVec.equivFin, Equiv.arrowCongr_apply]
  rfl

@[simp] lemma qub_zero_one : qub_zero 1#1 = 0 := by
  simp [qub_zero, beq]
  simp [BitVec.equivFin]

@[simp] lemma qub_one_zero : qub_one 0#1 = 0 := by
  simp [qub_one, beq, BitVec.equivFin, Equiv.arrowCongr_apply]
  rfl

@[simp] lemma qub_one_one : qub_one 1#1 = 1 := by
  simp [qub_one, beq]
  simp [BitVec.equivFin]

variable (ψ : PState 1)

lemma zero_one_orth : qub_zero.orth qub_one := by
  unfold PState.orth PState.dot
  simp [dotProduct, BitVec.sum_univ_one]

lemma one_qub_decomp : ψ = (ψ 0) • qub_zero + (ψ 1) • qub_one := by
  ext i
  rcases (BitVec1_cases i) with H0 | H1
  · rw [H0]; simp
  · rw [H1]; simp

-- less painful than expected
lemma ket_prodE {n₁ n₂} (ψ₁ : BitVec n₁ → ℂ) (ψ₂ : BitVec n₂ → ℂ) :
  ket_prod ψ₁ ψ₂ =
  λ(s : BitVec (n₁ + n₂)) =>
    let (s₁, s₂) := bits_cat.symm s
    ψ₁ s₁ * ψ₂ s₂ := by
  ext s; simp
  simp [ket_prod, toMat, normalized_kron, normalize_mat]

lemma sum_prod_bitvecs {n₁ n₂} (f : _ → ℂ) :
  ∑ (s : BitVec n₁ × BitVec n₂), f s =
  ∑ (s₁ : BitVec n₁), ∑ (s₂ : BitVec n₂), f (s₁, s₂) := by
  simp [<- Finset.sum_product]

lemma dot_kron {n₁ n₂} (ψ₁ φ₁ : BitVec n₁ → ℂ) (ψ₂ φ₂ : BitVec n₂ → ℂ) :
  ket_prod ψ₁ ψ₂ ⬝ᵥ (ket_prod φ₁ φ₂) =
  (ψ₁ ⬝ᵥ φ₁) * (ψ₂ ⬝ᵥ φ₂) := by
  simp [ket_prodE]
  simp [dotProduct]
  rw [Fintype.sum_equiv bits_cat.symm _ (
    λ(x' : BitVec n₁ × BitVec n₂) =>
    let (x₁, x₂) := x'
    (ψ₁ x₁ * φ₁ x₁) * (ψ₂ x₂ * φ₂ x₂)
  )]
  · simp [Finset.sum_mul_sum, sum_prod_bitvecs]
  · -- what is this nonsense?
    simp; group; simp

lemma PState.star_prod {n₁ n₂ : ℕ} (ψ₁ : PState n₁) (ψ₂ : PState n₂) :
  starRingEnd (BitVec (n₁ + n₂) → ℂ) (ψ₁ ⊗ₚ ψ₂)
    = (starRingEnd (BitVec n₁ → ℂ) ψ₁) ⊗ₚ (starRingEnd (BitVec n₂ → ℂ) ψ₂) := by
  unfold PState.kron
  ext x
  simp [Pi.conj_apply, ket_prodE]

lemma PState.prod_dot_prod' {n₁ n₂} {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} :
  (ψ₁ ⊗ₚ ψ₂) ⬝ᵥ (φ₁ ⊗ₚ φ₂) = (ψ₁ ⬝ᵥ φ₁) * (ψ₂ ⬝ᵥ φ₂) := by apply dot_kron

lemma PState.prod_dot_prod {n₁ n₂} {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} :
  (ψ₁ ⊗ₚ ψ₂).dot (φ₁ ⊗ₚ φ₂) = (ψ₁.dot φ₁) * (ψ₂.dot φ₂) := by
  unfold PState.dot
  rw [PState.star_prod]
  exact PState.prod_dot_prod'

lemma prod_orth_left {n₁ n₂} {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} (ho : ψ₁.orth φ₁)
  : (ψ₁ ⊗ₚ ψ₂).orth (φ₁ ⊗ₚ φ₂) := by
  unfold PState.orth at ⊢ ho
  rw [PState.prod_dot_prod, ho, zero_mul]

lemma prod_orth_right {n₁ n₂} {ψ₁ φ₁ : PState n₁} {ψ₂ φ₂ : PState n₂} (ho : ψ₂.orth φ₂)
  : (ψ₁ ⊗ₚ ψ₂).orth (φ₁ ⊗ₚ φ₂) := by
  unfold PState.orth at ⊢ ho
  rw [PState.prod_dot_prod, ho, mul_zero]

lemma PState.smul_kron_smul {n₁ n₂} (ψ₁ : PState n₁) (ψ₂ : PState n₂) (a b : ℂ) :
  (a • ψ₁) ⊗ₚ (b • ψ₂) = (a * b) • (ψ₁ ⊗ₚ ψ₂) := by
  unfold PState.kron
  ext x
  simp_rw [ket_prodE, Pi.smul_apply, smul_eq_mul]
  ring
