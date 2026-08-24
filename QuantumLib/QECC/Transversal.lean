/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.StabilizerFacts
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Transversal gates and the Eastin–Knill theorem

A **transversal** unitary is a tensor product of single-qubit unitaries. Such gates are the
"cheap" fault-tolerant operations. The **Eastin–Knill theorem** says no nontrivial code admits a
*universal* set of transversal logical gates.
-/

open scoped BigOperators
namespace QuantumLib
namespace PauliOp
variable {n : ℕ}

/-- A unitary is **transversal** if it factors as a tensor product `⨂ᵢ uᵢ` of single-qubit
unitaries, i.e. its matrix entries are products of single-qubit entries. -/
def IsTransversal (U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) : Prop :=
  ∃ u : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ,
    (∀ i, u i ∈ Matrix.unitaryGroup (ZMod 2) ℂ) ∧
    ∀ f g, U f g = ∏ i, u i (f i) (g i)

/-- The identity is transversal. -/
theorem isTransversal_one : IsTransversal (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) := by
  use fun _ => 1
  constructor
  · intro i
    simp
  · intro f g
    by_cases hfg : f = g
    · simp [hfg, Matrix.one_apply]
    · rw [Matrix.one_apply, if_neg hfg]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hfg
      rw [Finset.prod_eq_zero (Finset.mem_univ i)]
      simp [hi]

/-- Transversal unitaries are closed under multiplication. -/
theorem IsTransversal.mul {U V : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (hU : IsTransversal U) (hV : IsTransversal V) : IsTransversal (U * V) := by
  obtain ⟨u₁, hu₁_unit, hu₁⟩ := hU
  obtain ⟨u₂, hu₂_unit, hu₂⟩ := hV
  use fun i => u₁ i * u₂ i
  constructor
  · intro i
    exact MulMemClass.mul_mem (hu₁_unit i) (hu₂_unit i)
  · intro f g
    rw [Matrix.mul_apply]
    have h1 : ∀ j : Fin n → ZMod 2, U f j * V j g = ∏ i, (u₁ i (f i) (j i) * u₂ i (j i) (g i)) := by
      intro j
      rw [hu₁ f j, hu₂ j g]
      simp [Finset.prod_mul_distrib]
    simp_rw [h1]
    simp only [Matrix.mul_apply]
    rw [Fintype.prod_sum]

/-- A transversal unitary is unitary. -/
theorem IsTransversal.mem_unitaryGroup {U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (hU : IsTransversal U) : U ∈ Matrix.unitaryGroup (Fin n → ZMod 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  -- U * star U = 1
  obtain ⟨u, hu_unitary, hu_prod⟩ := hU
  ext f g
  simp only [Matrix.mul_apply, Matrix.star_apply]
  -- Goal: ∑ x, U f x * conj(U g x) = (1 : Matrix ...) f g
  rw [Matrix.one_apply]
  simp_rw [hu_prod]
  -- Rewrite star of product
  simp_rw [star_prod]
  -- Combine products
  have combine_prod : ∀ x : Fin n → ZMod 2,
      (∏ i, u i (f i) (x i)) * ∏ i, star (u i (g i) (x i))
        = ∏ i, (u i (f i) (x i) * star (u i (g i) (x i))) := by
    simp [Finset.prod_mul_distrib]
  simp_rw [combine_prod]
  show ∑ x : (Fin n → ZMod 2), ∏ i : Fin n, u i (f i) (x i) * star (u i (g i) (x i)) = _
  let f' : (i : Fin n) → ZMod 2 → ℂ := fun i j => u i (f i) j * star (u i (g i) j)
  show ∑ x : (Fin n → ZMod 2), ∏ i : Fin n, f' i (x i) = _
  rw [← Fintype.prod_sum]
  -- Each factor is a Kronecker delta because u i is unitary
  have unitary_row_orthogonal : ∀ i : Fin n, ∀ x y : ZMod 2,
      ∑ j, u i x j * star (u i y j) = if x = y then 1 else 0 := by
    intro i x y
    have hui := hu_unitary i
    rw [Matrix.mem_unitaryGroup_iff] at hui
    exact congr_fun (congr_fun hui x) y
  have : ∀ i : Fin n, ∑ j, f' i j = if f i = g i then 1 else 0 := by
    intro i
    show ∑ j, u i (f i) j * star (u i (g i) j) = _
    exact unitary_row_orthogonal i (f i) (g i)
  simp_rw [this]
  -- The product is 1 iff for all i, f i = g i, i.e., f = g
  by_cases hfg : f = g
  · simp [hfg]
  · rw [if_neg hfg]
    -- f ≠ g means there exists i with f i ≠ g i
    obtain ⟨i, hi⟩ : ∃ i, f i ≠ g i := Function.ne_iff.mp hfg
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    simp [hi]

/-- A single-qubit Pauli, tensored across qubits, is transversal. -/
theorem isTransversal_toMat_of_weight_le_one [NeZero n] {P : PauliOp n} (hP : weight P ≤ 1) :
    IsTransversal (toMat P) := by
  -- Weight ≤ 1 means either P is a scalar (weight 0) or P acts on exactly one qubit (weight 1)
  by_cases h0 : P.x = 0 ∧ P.z = 0
  · -- Weight 0 case: P is a scalar multiple of identity
    -- P = ⟨P.phase, 0, 0⟩, so toMat P = Complex.I ^ P.phase.val • 1
    have hP_eq : P = ⟨P.phase, 0, 0⟩ := by
      ext <;> simp [h0]
    rw [hP_eq, StabGroup.toMat_phase]
    -- A scalar multiple of identity: use u i = c^(1/n) • 1 for each i
    let c := Complex.I ^ P.phase.val
    let d := c ^ (1 / (n : ℂ))
    use fun _ => d • 1
    constructor
    · intro i
      simp [Matrix.mem_unitaryGroup_iff]
      -- Need: star d * d = 1, where d = c^(1/n) and |c| = 1
      have hc : (starRingEnd ℂ) c * c = 1 := by
        simp [c]
        have : P.phase.val < 4 := ZMod.val_lt P.phase
        interval_cases P.phase.val <;> norm_num [Complex.I_sq, pow_succ]
      -- Now show star d * d = 1 for d = c^(1/n)
      -- Simplify: star d • d • 1 = (star d * d) • 1
      simp [smul_smul]
      have hd : (starRingEnd ℂ) d * d = 1 := by
        have h1 : (starRingEnd ℂ) d * d = Complex.normSq d := by
          simp [Complex.normSq_eq_conj_mul_self]
        rw [h1, Complex.normSq_eq_norm_sq]
        suffices ‖d‖ = 1 by
          rw [this]
          norm_num
        -- We have c * conj c = 1, so ‖c‖ = 1
        have hc_norm : ‖c‖ = 1 := by
          have h1 : (starRingEnd ℂ) c = star c := by simp
          have : ‖c‖^2 = 1 := by
            rw [sq]
            calc ‖c‖ * ‖c‖ = ‖c‖ * ‖star c‖ := by rw [norm_star]
              _ = ‖c * star c‖ := by rw [norm_mul]
              _ = ‖(starRingEnd ℂ) c * c‖ := by rw [h1, mul_comm]
              _ = ‖(1 : ℂ)‖ := by rw [hc]
              _ = 1 := by norm_num
          nlinarith [sq_nonneg ‖c‖, norm_nonneg c]
        -- d = c^(1/n), so ‖d‖ = ‖c‖^(1/n) = 1
        have hc_ne : c ≠ 0 := by
          intro hc0
          rw [hc0] at hc
          simp at hc
        -- d = c^(1/n) where 1/n is real, so ‖d‖ = ‖c‖^(1/n)
        have exp_eq : (1 / (n : ℂ)) = ((1 / (n : ℝ)) : ℝ) := by simp
        show ‖c ^ (1 / (n : ℂ))‖ = 1
        rw [exp_eq, Complex.norm_cpow_real]
        rw [hc_norm]
        norm_num
      simp [hd]
    · intro f g
      simp only [Matrix.smul_apply, Matrix.one_apply]
      by_cases hfg : f = g
      · simp [hfg]
        -- Need: c = d^n
        -- d = c^(1/n), so d^n = c^(1/n * n) = c
        rw [← Complex.cpow_nat_mul c n (1 / (n : ℂ))]
        have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
        rw [mul_div_cancel₀ _ hn, Complex.cpow_one]
      · -- f ≠ g means there exists i with f i ≠ g i
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hfg
        have : (d • (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) (f i) (g i) = 0 := by simp [hi]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) this]
        simp [hfg]
  · -- Weight 1 case: P acts on exactly one qubit
    -- Since ¬(P.x = 0 ∧ P.z = 0), P has weight exactly 1
    -- We'll use u on the support of P, identity elsewhere
    -- First, establish that weight P = 1
    have hweight : weight P = 1 := by
      have h0 : weight P ≠ 0 := by
        simp [weight_eq_zero_iff, h0]
      have hle : weight P ≤ 1 := hP
      omega
    -- There exists a unique qubit j where P acts
    rw [weight_eq_card_support] at hweight
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hweight
    -- P.x and P.z are zero except at j
    have hx_zero : ∀ i ≠ j, P.x i = 0 := by
      intro i hi
      have : i ∉ Finset.univ.filter (fun i => P.x i ≠ 0 ∨ P.z i ≠ 0) := by
        rw [hj]
        simp [hi]
      simp [Finset.mem_filter] at this
      tauto
    have hz_zero : ∀ i ≠ j, P.z i = 0 := by
      intro i hi
      have : i ∉ Finset.univ.filter (fun i => P.x i ≠ 0 ∨ P.z i ≠ 0) := by
        rw [hj]
        simp [hi]
      simp [Finset.mem_filter] at this
      tauto
    -- At j, either P.x j ≠ 0 or P.z j ≠ 0
    have hj_mem : j ∈ Finset.univ.filter (fun i => P.x i ≠ 0 ∨ P.z i ≠ 0) := by
      rw [hj]
      simp
    simp [Finset.mem_filter] at hj_mem
    -- Define the scalar d = c (the full phase is at position j)
    let c := Complex.I ^ P.phase.val
    let d := c
    -- Define u: at j use d • single-qubit Pauli, elsewhere use 1
    let p : PauliSpace 1 := ((fun _ : Fin 1 => P.x j), (fun _ : Fin 1 => P.z j))
    -- Convert pauliOp on Fin 1 → ZMod 2 to matrix on ZMod 2 via equivalence
    let equiv : (Fin 1 → ZMod 2) ≃ ZMod 2 := Equiv.funUnique (Fin 1) (ZMod 2)
    let upauli : Matrix (ZMod 2) (ZMod 2) ℂ := Matrix.reindex equiv equiv (pauliOp p)
    use fun i => if i = j then d • upauli else 1
    constructor
    · intro i
      by_cases hij : i = j
      · subst hij
        simp [Matrix.mem_unitaryGroup_iff]
        have hpauli_u := pauliOp_mem_unitaryGroup p
        -- upauli is also unitary since reindex preserves unitarity
        have hupauli_u : upauli ∈ Matrix.unitaryGroup (ZMod 2) ℂ := by
          simp only [upauli]
          -- reindexing preserves unitarity
          have hpauli_u := pauliOp_mem_unitaryGroup p
          rw [Matrix.mem_unitaryGroup_iff] at hpauli_u ⊢
          -- hpauli_u : pauliOp p * star (pauliOp p) = 1
          -- Convert to conjTranspose form
          simp_rw [Matrix.star_eq_conjTranspose] at hpauli_u ⊢
          -- A * Aᴴ = 1 => reindex(A) * reindex(Aᴴ) = 1
          have h_equiv : ((Matrix.reindex equiv equiv) (pauliOp p)).conjTranspose =
                         (Matrix.reindex equiv equiv) (pauliOp p).conjTranspose :=
            Matrix.conjTranspose_reindex equiv equiv _
          have reindex_mul : (Matrix.reindex equiv equiv) (pauliOp p) *
               (Matrix.reindex equiv equiv) ((pauliOp p).conjTranspose) =
               (Matrix.reindex equiv equiv) ((pauliOp p) * (pauliOp p).conjTranspose) := by
            ext a b
            simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
            rw [← Fintype.sum_equiv equiv.symm]
            intro x
            rfl
          calc (Matrix.reindex equiv equiv) (pauliOp p) *
               (Matrix.reindex equiv equiv) (pauliOp p).conjTranspose
             = (Matrix.reindex equiv equiv) (pauliOp p) *
               ((Matrix.reindex equiv equiv) (pauliOp p)).conjTranspose := by rw [h_equiv]
           _ = (Matrix.reindex equiv equiv) ((pauliOp p) * (pauliOp p).conjTranspose) := reindex_mul
           _ = (Matrix.reindex equiv equiv) 1 := by rw [hpauli_u]
           _ = 1 := by simp
        -- Need: (star d) * d = 1 (since |d| = 1)
        rw [Matrix.mem_unitaryGroup_iff] at hupauli_u
        rw [hupauli_u]
        simp [smul_smul]
        have hd : (starRingEnd ℂ) d * d = 1 := by
          -- We have c * conj c = 1, so ‖c‖ = 1
          have hc : (starRingEnd ℂ) c * c = 1 := by
            simp [c]
            have : P.phase.val < 4 := ZMod.val_lt P.phase
            interval_cases P.phase.val <;> norm_num [Complex.I_sq, pow_succ]
          have h1 : (starRingEnd ℂ) d * d = Complex.normSq d := by
            simp [Complex.normSq_eq_conj_mul_self]
          rw [h1, Complex.normSq_eq_norm_sq]
          suffices ‖d‖ = 1 by
            rw [this]
            norm_num
          -- d = c, so ‖d‖ = ‖c‖ = 1
          have hc_norm : ‖c‖ = 1 := by
            have h1 : (starRingEnd ℂ) c = star c := by simp
            have : ‖c‖^2 = 1 := by
              rw [sq]
              calc ‖c‖ * ‖c‖ = ‖c‖ * ‖star c‖ := by rw [norm_star]
                _ = ‖c * star c‖ := by rw [norm_mul]
                _ = ‖(starRingEnd ℂ) c * c‖ := by rw [h1, mul_comm]
                _ = ‖(1 : ℂ)‖ := by rw [hc]
                _ = 1 := by norm_num
            nlinarith [sq_nonneg ‖c‖, norm_nonneg c]
          rw [hc_norm]
        simp [hd]
      · simp [hij]
    · intro f g
      -- The RHS simplifies: for i ≠ j we get
      -- (1 : Matrix _ _ _) (f i) (g i) = if f i = g i then 1 else 0
      -- For i = j we get d • upauli (f j) (g j) = d * upauli (f j) (g j)
      have rhs_eq : ∏ i, (if i = j then d • upauli else 1) (f i) (g i) =
          (if ∀ i ≠ j, f i = g i then d * upauli (f j) (g j) else 0) := by
        by_cases hall : ∀ i ≠ j, f i = g i
        · -- All f i = g i for i ≠ j
          have h1 : (if ∀ i ≠ j, f i = g i then d * upauli (f j) (g j) else 0)
              = d * upauli (f j) (g j) := by
            simp only [if_pos hall]
          rw [h1]
          -- For i ≠ j, f i = g i, so (1 : Matrix ..) (f i) (g i) = 1
          -- For i = j, we get (d • upauli) (f j) (g j) = d * upauli (f j) (g j)
          have heq : ∀ i, (if i = j then d • upauli else 1) (f i) (g i) =
            if i = j then d * upauli (f j) (g j) else 1 := by
            intro i
            by_cases hij : i = j
            · simp [hij]
            · simp [hij, Matrix.one_apply, hall i hij]
          simp_rw [heq]
          simp [Finset.prod_ite_eq']
        · -- There exists i ≠ j with f i ≠ g i
          have h2 : (if ∀ i ≠ j, f i = g i then d * upauli (f j) (g j) else 0) = 0 := by
            simp [hall]
          rw [h2]
          push Not at hall
          obtain ⟨i, hi_nej, hi_fne⟩ := hall
          rw [Finset.prod_eq_zero (Finset.mem_univ i)]
          rw [if_neg hi_nej, Matrix.one_apply]
          simp [hi_fne]
      rw [rhs_eq]
      -- Now we need to show:
      -- (if ∀ i ≠ j, f i = g i then d * upauli (f j) (g j) else 0) = toMat P f g
      -- toMat P = c • pauliOp (P.x, P.z), and upauli is the single-qubit pauliOp at j
      -- We need to relate pauliOp (P.x, P.z) f g to upauli (f j) (g j)
      by_cases hall : ∀ i ≠ j, f i = g i
      · -- All f i = g i for i ≠ j
        rw [if_pos hall]
        -- Need: c • pauliOp (P.x, P.z) f g = d * upauli (f j) (g j)
        -- Since d = c, we need: pauliOp (P.x, P.z) f g = upauli (f j) (g j)
        have hc : d = c := rfl
        rw [hc]
        -- Simplify both sides
        show c * (pauliOp (P.x, P.z) f g) = c * upauli (f j) (g j)
        congr 1
        -- Now show pauliOp (P.x, P.z) f g = upauli (f j) (g j)
        -- Both reduce to: if f j = g j + P.x j then (-1)^(P.z j * g j).val else 0
        simp only [pauliOp, Matrix.of_apply]
        -- Key: f = g + P.x iff f j = g j + P.x j (since f i = g i and P.x i = 0 for i ≠ j)
        have hfeq : f = g + P.x ↔ f j = g j + P.x j := by
          constructor
          · intro heq
            exact congr_fun heq j
          · intro hj
            ext i
            by_cases hij : i = j
            · subst hij
              simp [hj]
            · rw [Pi.add_apply, hx_zero i hij, add_zero]
              exact hall i hij
        simp only [hfeq]
        -- Also simplify the product: all terms except i = j are 1
        have hprod : ∏ i : Fin n, (-1 : ℂ) ^ (P.z i * g i).val = (-1 : ℂ) ^ (P.z j * g j).val := by
          apply Finset.prod_eq_single j
          · intro i _ hi_nej
            rw [hz_zero i hi_nej, zero_mul, ZMod.val_zero, pow_zero]
          · intro hx
            exact absurd (Finset.mem_univ j) hx
        rw [hprod]
        -- Now simplify upauli (f j) (g j)
        simp only [upauli, Matrix.reindex_apply, pauliOp]
        -- Simplify equiv.symm
        have hem : ∀ a : ZMod 2, equiv.symm a = fun _ : Fin 1 => a := fun a => rfl
        simp [hem]
        -- Show the conditions and values match
        have hcond : (fun _ : Fin 1 => f j) = (fun _ : Fin 1 => g j) + p.1 ↔ f j = (g + P.x) j := by
          simp only [show p.1 = fun _ => P.x j from rfl, Pi.add_apply]
          exact ⟨fun h => by simpa using congr_fun h 0, fun h => funext fun _ => h⟩
        have hpz : p.2 0 = P.z j := rfl
        simp [hcond, hpz]
      · -- There exists i ≠ j with f i ≠ g i
        rw [if_neg hall]
        -- P.toMat = c • pauliOp (P.x, P.z), and pauliOp returns 0 when f ≠ g + P.x
        simp [toMat, Matrix.smul_apply]
        -- Need to show pauliOp (P.x, P.z) f g = 0, which happens when f ≠ g + P.x
        simp [pauliOp, Matrix.of_apply]
        -- Need: ¬(f = g + P.x)
        have hne : ¬(f = g + P.x) := by
          push Not at hall
          obtain ⟨i, hi_nej, hi_fne⟩ := hall
          intro heq
          have := congr_fun heq i
          rw [Pi.add_apply] at this
          rw [hx_zero i hi_nej] at this
          simp at this
          exact hi_fne this
        simp [hne]

namespace StabGroup
variable (S : StabGroup n)

/-- `U` **implements** the logical unitary `V` if there is an encoding isometry `W` onto the code
space intertwining them: `star W * W = 1`, `Π·W = W`, and `U·W = W·V`.

**Caveat.** The encoding is existentially quantified, so `V` is pinned down only up to an arbitrary
change of logical basis (see `ImplementsLogical.conj`). That makes this notion unsuitable for any
*discreteness* statement about the set of logical actions; for those, fix an encoding and use
`ImplementsLogicalWith` / `transversalLogicalsWith`. -/
def ImplementsLogical (U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) : Prop :=
  ∃ W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ,
    W.conjTranspose * W = 1 ∧ stabProj S * W = W ∧ U * W = W * V

/-- **Basis scrambling.** If `U` implements `V`, it also implements every unitary conjugate of `V`
— replace the encoding `W` by `W·Xᴴ`. Consequently the set `transversalLogicals` below is a union
of full conjugacy classes of `U(2ᵏ)`, hence contains continuum-many pairwise non-proportional
elements arbitrarily close together as soon as it contains one non-scalar element. -/
theorem ImplementsLogical.conj {U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (h : S.ImplementsLogical U V)
    {X : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (hX : X ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ) :
    S.ImplementsLogical U (X * V * X.conjTranspose) := by
  obtain ⟨W, hWiso, hWproj, hUW⟩ := h
  have hXX : X * X.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hX
  have hXX' : X.conjTranspose * X = 1 := Matrix.mem_unitaryGroup_iff'.mp hX
  refine ⟨W * X.conjTranspose, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc W.conjTranspose W X.conjTranspose, hWiso, Matrix.one_mul, hXX]
  · rw [← Matrix.mul_assoc, hWproj]
  · have key : X.conjTranspose * (X * V * X.conjTranspose) = V * X.conjTranspose := by
      rw [Matrix.mul_assoc X V, ← Matrix.mul_assoc X.conjTranspose X, hXX', Matrix.one_mul]
    calc U * (W * X.conjTranspose)
        = U * W * X.conjTranspose := (Matrix.mul_assoc _ _ _).symm
      _ = W * V * X.conjTranspose := by rw [hUW]
      _ = W * (V * X.conjTranspose) := Matrix.mul_assoc _ _ _
      _ = W * (X.conjTranspose * (X * V * X.conjTranspose)) := by rw [key]
      _ = W * X.conjTranspose * (X * V * X.conjTranspose) := (Matrix.mul_assoc _ _ _).symm

/-! ### Existence of an encoding isometry

The code space is the range of the Hermitian idempotent `stabProj S`, of dimension `2ᵏ` where `k`
is the number of logical qubits. Diagonalising the projector produces an honest encoding isometry
`W` with `Wᴴ·W = 1` and `W·Wᴴ = Π`; that isometry is what turns "preserves the code space" into
"implements a logical unitary". -/

/-- A transversal gate that preserves the code space implements *some* logical unitary. -/
theorem exists_logical_of_transversal_preserving
    {U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (_hU : IsTransversal U) (hpres : stabProj S * U * stabProj S = U * stabProj S) :
    ∃ V, S.ImplementsLogical U V := by
  obtain ⟨W, hiso, hWW⟩ := exists_isometry_stabProj S (two_pow_numLogical_mul_card_carrier S)
  have hproj : stabProj S * W = W := by rw [← hWW, Matrix.mul_assoc, hiso, Matrix.mul_one]
  refine ⟨W.conjTranspose * U * W, W, hiso, hproj, ?_⟩
  calc U * W = U * (stabProj S * W) := by rw [hproj]
    _ = (stabProj S * U * stabProj S) * W := by rw [hpres, Matrix.mul_assoc]
    _ = stabProj S * U * (stabProj S * W) := by rw [Matrix.mul_assoc]
    _ = (W * W.conjTranspose) * (U * W) := by rw [hproj, hWW, Matrix.mul_assoc]
    _ = W * (W.conjTranspose * U * W) := by simp only [Matrix.mul_assoc]

/-- The set of logical unitaries implementable by *some* transversal gate, in *some* logical basis.
Conjugation-closed by `ImplementsLogical.conj`, so never discrete; see `transversalLogicalsWith`. -/
def transversalLogicals :
    Set (Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) :=
  {V | ∃ U, IsTransversal U ∧ S.ImplementsLogical U V}

/-! ### Logical action relative to a fixed encoding

Everything about *discreteness* of the transversal logical group has to be said relative to a
single fixed encoding isometry: with the encoding existentially quantified,
`ImplementsLogical.conj` closes the set of logical actions under conjugation, so it contains whole
conjugacy classes of `U(2ᵏ)` and is never discrete. -/

/-- `W` is an **encoding isometry** for `S`: an isometry whose range is the code space. -/
def IsEncoding (W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) : Prop :=
  W.conjTranspose * W = 1 ∧ stabProj S * W = W

/-- Every stabilizer code has an encoding isometry. -/
theorem exists_isEncoding : ∃ W, S.IsEncoding W := by
  obtain ⟨W, hiso, hWW⟩ := exists_isometry_stabProj S (two_pow_numLogical_mul_card_carrier S)
  refine ⟨W, hiso, ?_⟩
  rw [← hWW, Matrix.mul_assoc, hiso, Matrix.mul_one]

/-- `U` implements the logical unitary `V` **relative to the fixed encoding** `W`. -/
def ImplementsLogicalWith (W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ)
    (U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) : Prop :=
  U * W = W * V

/-- The logical unitaries implemented by transversal gates, relative to a fixed encoding `W`. -/
def transversalLogicalsWith (W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) :
    Set (Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) :=
  {V | ∃ U, IsTransversal U ∧ S.ImplementsLogicalWith W U V}

/-- Relative to a fixed encoding the logical action is *unique* — this is exactly what fails for
`ImplementsLogical`. -/
theorem logical_unique {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (hW : S.IsEncoding W) {U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    {V V' : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (h : S.ImplementsLogicalWith W U V) (h' : S.ImplementsLogicalWith W U V') : V = V' := by
  have hc : W.conjTranspose * (W * V) = W.conjTranspose * (W * V') := by rw [← h, ← h']
  rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, hW.1, Matrix.one_mul, Matrix.one_mul] at hc

/-- The identity is a transversal logical. -/
theorem one_mem_transversalLogicalsWith
    {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ} :
    (1 : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) ∈
      S.transversalLogicalsWith W :=
  ⟨1, isTransversal_one, (Matrix.one_mul W).trans (Matrix.mul_one W).symm⟩

/-- Relative to a fixed encoding the transversal logicals are closed under multiplication, so they
form a genuine group — which is what makes the Eastin–Knill statement meaningful. -/
theorem mul_mem_transversalLogicalsWith
    {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    {V V' : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (hV : V ∈ S.transversalLogicalsWith W) (hV' : V' ∈ S.transversalLogicalsWith W) :
    V * V' ∈ S.transversalLogicalsWith W := by
  obtain ⟨U, hU, hUW⟩ := hV
  obtain ⟨U', hU', hUW'⟩ := hV'
  refine ⟨U * U', hU.mul hU', ?_⟩
  -- Rectangular products pick up the `CStarMatrix` `HMul` instance inconsistently, so `rw` cannot
  -- match them; each rewrite is isolated in a `congrArg` and the `calc` steps are glued by defeq.
  have h1 : U * (U' * W) = U * (W * V') := congrArg (fun M => U * M) hUW'
  have h2 : U * W * V' = W * V * V' := congrArg (fun M => M * V') hUW
  calc U * U' * W = U * (U' * W) := Matrix.mul_assoc _ _ _
    _ = U * (W * V') := h1
    _ = U * W * V' := (Matrix.mul_assoc _ _ _).symm
    _ = W * V * V' := h2
    _ = W * (V * V') := Matrix.mul_assoc _ _ _

/-- **Eastin–Knill reduction step.** If only finitely many logical unitaries are transversally
implementable, then transversal gates cannot be universal — because the logical unitary group is
infinite, so it cannot be contained in a finite set. -/
theorem not_universal_of_transversalLogicals_finite
    (hfin : S.transversalLogicals.Finite)
    (hinf : {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ |
        V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ}.Infinite) :
    ¬ ∀ V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ,
        ∃ U, IsTransversal U ∧ S.ImplementsLogical U V := by
  intro hall
  exact hinf (hfin.subset (fun V hV => hall V hV))

open scoped Matrix.Norms.L2Operator

/-- **General topology:** a set sitting inside a compact set whose distinct points are uniformly
`ε`-separated is finite. -/
theorem finite_of_separated {X : Type*} [PseudoMetricSpace X] {K G : Set X}
    (hK : IsCompact K) (hGK : G ⊆ K) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ x ∈ G, ∀ y ∈ G, x ≠ y → ε ≤ dist x y) : G.Finite := by
  -- Use ε/3-balls to cover K (so two points in same ball have dist < ε)
  let ε' : NNReal := ⟨ε / 3, by linarith⟩
  have hε' : ε' ≠ 0 := by
    have hpos : (0 : ℝ) < (ε' : ℝ) := by
      show (0 : ℝ) < ε / 3
      linarith
    exact_mod_cast hpos.ne'
  obtain ⟨N, hNád, hNfin, hNcover⟩ := Metric.exists_finite_isCover_of_isCompact hε' hK
  -- Each point of G is covered by some ball centered at a point of N
  -- Metric.IsCover ε' K N means ∀ x ∈ K, ∃ y ∈ N, edist x y ≤ ε'
  have hNcover_G : ∀ g ∈ G, ∃ n ∈ N, edist g n ≤ ε' := fun g hg => hNcover (hGK hg)
  -- Define a choice function from G to N
  choose f hf using hNcover_G
  -- Show that f is injective on G
  have hf_inj : ∀ g₁ (hg₁ : g₁ ∈ G), ∀ g₂ (hg₂ : g₂ ∈ G), f g₁ hg₁ = f g₂ hg₂ → g₁ = g₂ := by
    intro g₁ hg₁ g₂ hg₂ hfg
    by_contra hne
    have hf1 : edist g₁ (f g₁ hg₁) ≤ ε' := (hf g₁ hg₁).2
    have hf2 : edist g₂ (f g₂ hg₂) ≤ ε' := (hf g₂ hg₂).2
    have hf2' : edist g₂ (f g₁ hg₁) ≤ ε' := by rwa [← hfg] at hf2
    have hdist : edist g₁ g₂ ≤ ↑ε' + ↑ε' := by
      calc edist g₁ g₂ ≤ edist g₁ (f g₁ hg₁) + edist (f g₁ hg₁) g₂ := edist_triangle _ _ _
        _ = edist g₁ (f g₁ hg₁) + edist g₂ (f g₁ hg₁) := by rw [edist_comm (f g₁ hg₁) g₂]
        _ ≤ ↑ε' + ↑ε' := add_le_add hf1 hf2'
    -- But dist g₁ g₂ ≥ ε by separation, and dist ≤ edist, and ε' + ε' = ε
    have hsep' : dist g₁ g₂ ≥ ε := hsep g₁ hg₁ g₂ hg₂ hne
    have hle : ENNReal.ofReal (dist g₁ g₂) = edist g₁ g₂ := (edist_dist g₁ g₂).symm
    have hcoerce :
        ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) = ENNReal.ofReal (2 * ε / 3) := by
      rw [← ENNReal.ofReal_add (by linarith : 0 ≤ ε / 3) (by linarith : 0 ≤ ε / 3)]
      congr 1
      ring
    have hε'_eq : ↑ε' = ENNReal.ofReal (ε / 3) := by
      exact ENNReal.coe_nnreal_eq ε'
    have hdist' : edist g₁ g₂ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := by
      simpa only [hε'_eq] using hdist
    have hfinal : edist g₁ g₂ ≤ ENNReal.ofReal (2 * ε / 3) := le_trans hdist' hcoerce.le
    have hdist_le : dist g₁ g₂ ≤ 2 * ε / 3 := by
      have h : ENNReal.ofReal (dist g₁ g₂) ≤ ENNReal.ofReal (2 * ε / 3) := hle.le.trans hfinal
      rw [ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ 2 * ε / 3)] at h
      exact h
    linarith [hsep', hdist_le, hε]
  -- G injects into N, so G is finite since N is finite
  set I : G → N := fun g => ⟨f g g.2, (hf g g.2).1⟩ with hI_def
  have hI_inj : Function.Injective I := by
    intro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ hIeq
    have : f g₁ hg₁ = f g₂ hg₂ := Subtype.ext_iff.mp hIeq
    have heq : g₁ = g₂ := hf_inj g₁ hg₁ g₂ hg₂ this
    exact Subtype.ext heq
  have : Finite N := Set.Finite.to_subtype hNfin
  have : Finite G := Finite.of_injective I hI_inj
  exact Set.finite_coe_iff.mpr this

/-- The unitary group of a finite-dimensional complex Hilbert space is compact: it is closed, being
the preimage of `{1}` under `V ↦ V·Vᴴ`, and bounded, a unitary having operator norm one. -/
theorem _root_.QuantumLib.isCompact_unitaryGroup {m : Type*} [Fintype m] [DecidableEq m]
    [Nonempty m] :
    IsCompact {V : Matrix m m ℂ | V ∈ Matrix.unitaryGroup m ℂ} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have h : {V : Matrix m m ℂ | V ∈ Matrix.unitaryGroup m ℂ} = {V | V * star V = 1} := by
      ext V
      simp only [Set.mem_ofPred_eq]
      exact Matrix.mem_unitaryGroup_iff
    rw [h]
    have : {V : Matrix m m ℂ | V * star V = 1} = (fun V : Matrix m m ℂ => V * star V) ⁻¹' {1} := rfl
    rw [this]
    exact isClosed_singleton.preimage (by fun_prop)
  · -- Unitaries have operator norm one, so they lie in the closed unit ball.
    have hc : Bornology.IsBounded (Metric.closedBall (0 : Matrix m m ℂ) 1) :=
      Metric.isBounded_closedBall
    exact hc.subset (fun V hV => by
      rw [Metric.mem_closedBall, dist_zero_right]
      have hV_unitary : V ∈ unitary (Matrix m m ℂ) := by
        rw [Unitary.mem_iff]
        exact ⟨Matrix.mem_unitaryGroup_iff'.mp hV, Matrix.mem_unitaryGroup_iff.mp hV⟩
      exact (CStarRing.norm_of_mem_unitary hV_unitary).le)

/-- The unitary group of the logical space is compact. -/
theorem unitaryGroup_isCompact :
    IsCompact {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ |
      V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ} :=
  QuantumLib.isCompact_unitaryGroup

/-- Every transversally-implemented logical unitary is unitary (so lands in the compact group). -/
theorem transversalLogicals_subset_unitary :
    S.transversalLogicals ⊆
      {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ |
        V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ} := by
  intro V hV
  obtain ⟨U, hU_trans, W, hW_unit, _, hUV⟩ := hV
  simp only [Set.mem_ofPred_eq]
  rw [Matrix.mem_unitaryGroup_iff']
  have hun : U.conjTranspose * U = 1 := by
    have hu := IsTransversal.mem_unitaryGroup hU_trans
    exact Matrix.UnitaryGroup.star_mul_self ⟨U, hu⟩
  have eq1 : V.conjTranspose * W.conjTranspose = W.conjTranspose * U.conjTranspose := by
    have : (W * V).conjTranspose = (U * W).conjTranspose := by rw [hUV]
    simp only [Matrix.conjTranspose_mul] at this
    exact this
  have hstar : star V = W.conjTranspose * U.conjTranspose * W := by
    simp only [Matrix.star_eq_conjTranspose]
    calc V.conjTranspose = V.conjTranspose * 1 := by rw [mul_one]
      _ = V.conjTranspose * (W.conjTranspose * W) := by rw [hW_unit]
      _ = (V.conjTranspose * W.conjTranspose) * W :=
            (Matrix.mul_assoc V.conjTranspose W.conjTranspose W).symm
      _ = W.conjTranspose * U.conjTranspose * W := by rw [eq1]
  have haux : star V * V = W.conjTranspose * W := by
    rw [hstar]
    have h1 : W.conjTranspose * U.conjTranspose * W * V =
              W.conjTranspose * U.conjTranspose * (W * V) := by exact Matrix.mul_assoc _ _ _
    rw [h1, ← hUV]
    have h2 : W.conjTranspose * U.conjTranspose * (U * W)
        = W.conjTranspose * (U.conjTranspose * U) * W := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [h2, hun]
    simp
  rw [haux, hW_unit]

/-- Every transversally-implemented logical unitary is unitary, fixed-encoding version. -/
theorem transversalLogicalsWith_subset_unitary
    {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ} (hW : S.IsEncoding W) :
    S.transversalLogicalsWith W ⊆
      {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ |
        V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ} := by
  rintro V ⟨U, hU, hUW⟩
  simp only [Set.mem_ofPred_eq]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hUu : U.conjTranspose * U = 1 :=
    Matrix.UnitaryGroup.star_mul_self ⟨U, hU.mem_unitaryGroup⟩
  have h1 : V.conjTranspose * V = (W * V).conjTranspose * (W * V) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc W.conjTranspose W V, hW.1, Matrix.one_mul]
  have h2 : (U * W).conjTranspose * (U * W) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc U.conjTranspose U W, hUu, Matrix.one_mul, hW.1]
  calc V.conjTranspose * V = (W * V).conjTranspose * (W * V) := h1
    _ = (U * W).conjTranspose * (U * W) :=
        (congrArg (fun M : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ =>
          M.conjTranspose * M) hUW).symm
    _ = 1 := h2

/-! ### The compression engine

`compress_scalar_of_weight_lt` says a low-weight Pauli acts as a scalar on the code space. The
lemmas here convert that into statements about *logical actions*: anything whose compression to the
code space is a scalar multiple of `Π` can only implement a global phase. -/

/-- If the compression of `U` to the code space is a scalar multiple of the projector, then every
logical unitary `U` implements is that same scalar. -/
theorem isScalar_of_compress_scalar {U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ} {c : ℂ}
    (hcomp : stabProj S * U * stabProj S = c • stabProj S)
    {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (hV : S.ImplementsLogical U V) : V = c • 1 := by
  obtain ⟨W, hWiso, hWproj, hUW⟩ := hV
  -- `Wᴴ·Π = Wᴴ`, by conjugate-transposing `Π·W = W` and using that `Π` is Hermitian.
  have hWproj' : W.conjTranspose * stabProj S = W.conjTranspose := by
    have := congrArg Matrix.conjTranspose hWproj
    rwa [Matrix.conjTranspose_mul, (stabProj_isHermitian S).eq] at this
  calc V = W.conjTranspose * W * V := by rw [hWiso, Matrix.one_mul]
    _ = W.conjTranspose * (U * W) := by rw [Matrix.mul_assoc, hUW]
    _ = W.conjTranspose * stabProj S * U * (stabProj S * W) := by
        rw [hWproj', hWproj, Matrix.mul_assoc]
    _ = W.conjTranspose * (stabProj S * U * stabProj S) * W := by
        simp only [Matrix.mul_assoc]
    _ = W.conjTranspose * (c • stabProj S) * W := by rw [hcomp]
    _ = c • (W.conjTranspose * stabProj S * W) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul]
    _ = c • 1 := by rw [hWproj', hWiso]

/-- Compression is linear, so *any* linear combination of Paulis of weight below the distance
compresses to a scalar on the code space. -/
theorem compress_scalar_of_lowWeight_sum {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (P : ι → PauliOp n) (hw : ∀ i ∈ s, weight (P i) < S.distance) :
    ∃ c : ℂ, stabProj S * (∑ i ∈ s, a i • toMat (P i)) * stabProj S = c • stabProj S := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert j t hj ih =>
      obtain ⟨c, hc⟩ := ih fun i hi => hw i (Finset.mem_insert_of_mem hi)
      obtain ⟨d, hd⟩ := S.compress_scalar_of_weight_lt (hw j (Finset.mem_insert_self j t))
      refine ⟨a j * d + c, ?_⟩
      rw [Finset.sum_insert hj, Matrix.mul_add, Matrix.add_mul, hc, Matrix.mul_smul,
        Matrix.smul_mul, hd, smul_smul, ← add_smul]

/-- **The algebraic heart of Eastin–Knill.** A gate that is a linear combination of Pauli errors of
weight below the distance implements only a global phase — no Lie theory needed, just
`compress_scalar_of_weight_lt` plus linearity.

The weight hypothesis cannot be traded for a norm bound on the logical action: the Steane code has
a transversal gate implementing logical `S`, and `e^{-iπ/4}·S` is within `2 sin(π/8) < 1` of the
identity without being scalar. -/
theorem implementsLogical_isScalar_of_lowWeight_sum {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (P : ι → PauliOp n) (hw : ∀ i ∈ s, weight (P i) < S.distance)
    {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (hV : S.ImplementsLogical (∑ i ∈ s, a i • toMat (P i)) V) :
    ∃ c : ℂ, V = c • 1 := by
  obtain ⟨c, hc⟩ := S.compress_scalar_of_lowWeight_sum s a P hw
  exact ⟨c, S.isScalar_of_compress_scalar hc hV⟩

/-- Single-Pauli specialisation: a Pauli error of weight below the distance implements only a
global phase. -/
theorem implementsLogical_isScalar_of_weight_lt {D : PauliOp n} (hw : weight D < S.distance)
    {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (hV : S.ImplementsLogical (toMat D) V) : ∃ c : ℂ, V = c • 1 := by
  obtain ⟨c, hc⟩ := S.compress_scalar_of_weight_lt hw
  exact ⟨c, S.isScalar_of_compress_scalar hc hV⟩

/-! ### One-parameter transversal flows

The Hamiltonian of a one-parameter group of *transversal* gates is a sum `∑ᵢ 1 ⊗ ⋯ ⊗ hᵢ ⊗ ⋯ ⊗ 1`
of single-qubit terms, hence a linear combination of Paulis of weight at most one: a *low-weight
generator* as soon as `2 ≤ S.distance`. Two facts about such a flow are proved here.

* Differentiating the code-preservation identity at `t = 0` upgrades the compression statement
  `Π·A·Π = c·Π` to the exact identity `A·Π = c·Π`: the generator acts on the code space by a
  scalar, not merely after compression.
* Summing the exponential series then shows that the whole flow acts on the code space by the
  phase `e^{tc}`, so every gate it produces implements only a global phase.

Together these are the differential half of Eastin–Knill. -/

section Flow

open NormedSpace
open scoped Nat

/-- `A` is a **low-weight generator**: a linear combination of Pauli operators of weight below the
distance. A transversal Hamiltonian is of this form whenever `2 ≤ S.distance`, since each of its
single-qubit terms expands in the Pauli basis into operators of weight at most one. -/
def IsLowWeightGen (A : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) : Prop :=
  ∃ (s : Finset (PauliOp n)) (a : PauliOp n → ℂ),
    (∀ P ∈ s, weight P < S.distance) ∧ A = ∑ P ∈ s, a P • toMat P

theorem isLowWeightGen_zero : S.IsLowWeightGen 0 :=
  ⟨∅, fun _ => 0, by simp, by simp⟩

theorem IsLowWeightGen.add {A B : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (hA : S.IsLowWeightGen A) (hB : S.IsLowWeightGen B) : S.IsLowWeightGen (A + B) := by
  classical
  obtain ⟨s, a, hs, rfl⟩ := hA
  obtain ⟨t, b, ht, rfl⟩ := hB
  refine ⟨s ∪ t, fun P => (if P ∈ s then a P else 0) + (if P ∈ t then b P else 0), ?_, ?_⟩
  · intro P hP
    rcases Finset.mem_union.mp hP with h | h
    · exact hs P h
    · exact ht P h
  · rw [Finset.sum_congr rfl fun P _ =>
      add_smul (if P ∈ s then a P else 0) (if P ∈ t then b P else 0) (toMat P),
      Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_subset Finset.subset_union_left
        (fun P _ hP => by rw [if_neg hP, zero_smul])]
      exact Finset.sum_congr rfl fun P hP => by rw [if_pos hP]
    · rw [← Finset.sum_subset Finset.subset_union_right
        (fun P _ hP => by rw [if_neg hP, zero_smul])]
      exact Finset.sum_congr rfl fun P hP => by rw [if_pos hP]

theorem IsLowWeightGen.smul {A : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ} (c : ℂ)
    (hA : S.IsLowWeightGen A) : S.IsLowWeightGen (c • A) := by
  obtain ⟨s, a, hs, rfl⟩ := hA
  refine ⟨s, fun P => c * a P, hs, ?_⟩
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun P _ => smul_smul c (a P) (toMat P)

/-- The low-weight generators form a submodule: `IsLowWeightGen` says exactly that a matrix lies in
the span of the Pauli operators of weight below the distance. -/
def lowWeightGens : Submodule ℂ (Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) where
  carrier := {A | S.IsLowWeightGen A}
  add_mem' := IsLowWeightGen.add S
  zero_mem' := S.isLowWeightGen_zero
  smul_mem' c _ hA := IsLowWeightGen.smul S c hA

@[simp]
theorem mem_lowWeightGens {A : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ} :
    A ∈ S.lowWeightGens ↔ S.IsLowWeightGen A := Iff.rfl

theorem IsLowWeightGen.sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (hf : ∀ i ∈ s, S.IsLowWeightGen (f i)) :
    S.IsLowWeightGen (∑ i ∈ s, f i) :=
  Submodule.sum_mem S.lowWeightGens hf

/-- Anything in the span of the Pauli operators of weight at most `k`, for `k` below the distance,
is a low-weight generator. -/
theorem isLowWeightGen_of_mem_span {k : ℕ} (hk : k < S.distance)
    {A : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (hA : A ∈ Submodule.span ℂ (Set.range fun P : {P : PauliOp n // weight P ≤ k} => toMat P.1)) :
    S.IsLowWeightGen A := by
  refine (Submodule.span_le (p := S.lowWeightGens)).mpr ?_ hA
  rintro _ ⟨P, rfl⟩
  exact ⟨{P.1}, fun _ => 1, fun Q hQ => by
    rw [Finset.mem_singleton.mp hQ]; exact lt_of_le_of_lt P.2 hk, by simp⟩

/-- A low-weight generator compresses to a scalar on the code space. -/
theorem compress_scalar_of_isLowWeightGen {A : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (hA : S.IsLowWeightGen A) : ∃ c : ℂ, stabProj S * A * stabProj S = c • stabProj S := by
  obtain ⟨s, a, hw, rfl⟩ := hA
  exact S.compress_scalar_of_lowWeight_sum s a id hw

/-- `A` generates a **code-preserving flow**: every `exp (t · A)` maps the code space into
itself. -/
def PreservesCodeFlow (A : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) : Prop :=
  ∀ t : ℝ, stabProj S * exp (t • A) * stabProj S = exp (t • A) * stabProj S

/-- **Differentiating the flow.** Code preservation is an identity between two curves in the
matrix algebra; taking derivatives at `t = 0`, where `d/dt exp (t·A) = A`, gives the infinitesimal
form `Π·A·Π = A·Π`. -/
theorem mul_stabProj_of_preservesCodeFlow {A : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (h : S.PreservesCodeFlow A) : stabProj S * A * stabProj S = A * stabProj S := by
  have h0 : HasDerivAt (fun t : ℝ => exp (t • A)) A 0 := by
    simpa using hasDerivAt_exp_smul_const A (0 : ℝ)
  have hL := (h0.const_mul (stabProj S)).mul_const (stabProj S)
  have hR := h0.mul_const (stabProj S)
  rw [funext h] at hL
  exact hL.unique hR

/-- **The differential heart of Eastin–Knill.** A low-weight generator of a code-preserving flow
acts on the code space by an honest scalar: the compression `Π·A·Π = c·Π` supplied by the distance
and the infinitesimal code preservation `Π·A·Π = A·Π` combine to `A·Π = c·Π`. -/
theorem exists_scalar_of_lowWeightGen_flow {A : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (hA : S.IsLowWeightGen A) (hflow : S.PreservesCodeFlow A) :
    ∃ c : ℂ, A * stabProj S = c • stabProj S := by
  obtain ⟨c, hc⟩ := S.compress_scalar_of_isLowWeightGen hA
  exact ⟨c, (S.mul_stabProj_of_preservesCodeFlow hflow).symm.trans hc⟩

/-- A generator acting on the code space by `c` sends every power to the corresponding power
of `c`. -/
theorem pow_mul_stabProj {A : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ} {c : ℂ}
    (h : A * stabProj S = c • stabProj S) (k : ℕ) :
    A ^ k * stabProj S = c ^ k • stabProj S := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc A ^ (k + 1) * stabProj S = A * (A ^ k * stabProj S) := by
            rw [pow_succ', Matrix.mul_assoc]
        _ = A * (c ^ k • stabProj S) := by rw [ih]
        _ = c ^ k • (A * stabProj S) := Matrix.mul_smul _ _ _
        _ = c ^ (k + 1) • stabProj S := by rw [h, smul_smul, pow_succ]

/-- **Exponentiating the scalar action.** A generator acting on the code space by `c` exponentiates
term by term, so the flow acts on the code space by the phase `e^{tc}`. -/
theorem exp_smul_mul_stabProj {A : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ} {c : ℂ}
    (h : A * stabProj S = c • stabProj S) (t : ℝ) :
    exp (t • A) * stabProj S = Complex.exp (t * c) • stabProj S := by
  have hterm : ∀ k : ℕ, ((k ! : ℂ)⁻¹ • (t • A) ^ k) * stabProj S
      = ((k ! : ℂ)⁻¹ • ((t : ℂ) * c) ^ k) • stabProj S := by
    intro k
    rw [smul_pow, Matrix.smul_mul, Matrix.smul_mul, S.pow_mul_stabProj h k,
      ← algebraMap_smul (R := ℝ) ℂ ((t : ℝ) ^ k), smul_smul, smul_smul]
    congr 1
    push_cast [smul_eq_mul, mul_pow]
    exact mul_assoc _ _ _
  calc exp (t • A) * stabProj S
      = (∑' k : ℕ, ((k ! : ℂ)⁻¹ • (t • A) ^ k)) * stabProj S := by
        simp only [exp_eq_tsum (𝕂 := ℂ)]
    _ = ∑' k : ℕ, (((k ! : ℂ)⁻¹ • (t • A) ^ k) * stabProj S) :=
        ((expSeries_summable' (𝕂 := ℂ) (t • A)).tsum_mul_right _).symm
    _ = ∑' k : ℕ, ((k ! : ℂ)⁻¹ • ((t : ℂ) * c) ^ k) • stabProj S := tsum_congr hterm
    _ = (∑' k : ℕ, (k ! : ℂ)⁻¹ • ((t : ℂ) * c) ^ k) • stabProj S :=
        (expSeries_summable' (𝕂 := ℂ) ((t : ℂ) * c)).tsum_smul_const _
    _ = Complex.exp (t * c) • stabProj S := by
        simp only [Complex.exp_eq_exp_ℂ, exp_eq_tsum (𝕂 := ℂ)]

/-- `U` **acts by a scalar** on the code space: `U·Π = c·Π`. Unlike the compressed form
`Π·U·Π = c·Π` this is closed under multiplication, so the gates acting by a scalar form a
submonoid. -/
def ActsByScalar (U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) : Prop :=
  ∃ c : ℂ, U * stabProj S = c • stabProj S

theorem actsByScalar_one : S.ActsByScalar 1 := ⟨1, by rw [Matrix.one_mul, one_smul]⟩

theorem actsByScalar_mul {U U' : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (h : S.ActsByScalar U) (h' : S.ActsByScalar U') : S.ActsByScalar (U * U') := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  refine ⟨c' * c, ?_⟩
  rw [Matrix.mul_assoc, hc', Matrix.mul_smul, hc, smul_smul]

/-- Acting by a scalar is stronger than compressing to a scalar, `Π` being idempotent. -/
theorem actsByScalar_compress {U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (h : S.ActsByScalar U) : ∃ c : ℂ, stabProj S * U * stabProj S = c • stabProj S := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by rw [Matrix.mul_assoc, hc, Matrix.mul_smul, stabProj_idem]⟩

/-- A gate acting on the code space by a scalar implements only a global phase. -/
theorem isScalar_of_actsByScalar {U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (h : S.ActsByScalar U)
    {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (hV : S.ImplementsLogical U V) : ∃ c : ℂ, V = c • 1 := by
  obtain ⟨c, hc⟩ := S.actsByScalar_compress h
  exact ⟨c, S.isScalar_of_compress_scalar hc hV⟩

/-- `D` is a **flow gate**: the time-`t` map of a code-preserving flow with a low-weight
generator. -/
def IsFlowGate (D : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) : Prop :=
  ∃ (A : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (t : ℝ),
    S.IsLowWeightGen A ∧ S.PreservesCodeFlow A ∧ D = exp (t • A)

/-- Every flow gate acts on the code space by a scalar — the phase `e^{tc}` of
`exp_smul_mul_stabProj`. -/
theorem actsByScalar_of_isFlowGate {D : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (h : S.IsFlowGate D) : S.ActsByScalar D := by
  obtain ⟨A, t, hA, hflow, rfl⟩ := h
  obtain ⟨c, hc⟩ := S.exists_scalar_of_lowWeightGen_flow hA hflow
  exact ⟨Complex.exp (t * c), S.exp_smul_mul_stabProj hc t⟩

/-- Any product of flow gates acts on the code space by a scalar. -/
theorem actsByScalar_prod {l : List (Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)}
    (hl : ∀ D ∈ l, S.IsFlowGate D) : S.ActsByScalar l.prod := by
  induction l with
  | nil => simpa using S.actsByScalar_one
  | cons D l ih =>
      rw [List.prod_cons]
      exact S.actsByScalar_mul (S.actsByScalar_of_isFlowGate (hl D (List.mem_cons_self ..)))
        (ih fun D' hD' => hl D' (List.mem_cons_of_mem _ hD'))

end Flow

/-- `W` is a **full encoding**: an isometry whose range is *all* of the code space, `Wᴴ·W = 1` and
`W·Wᴴ = Π`. Stronger than `IsEncoding`, which only puts the range inside the code space; the
difference matters because a gate implementing a logical unitary relative to a full encoding
necessarily preserves the code space. -/
def IsFullEncoding (W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) : Prop :=
  W.conjTranspose * W = 1 ∧ W * W.conjTranspose = stabProj S

theorem IsFullEncoding.isEncoding {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (h : S.IsFullEncoding W) : S.IsEncoding W :=
  ⟨h.1, by rw [← h.2, Matrix.mul_assoc, h.1, Matrix.mul_one]⟩

/-- Diagonalising the stabilizer projector produces a full encoding. -/
theorem exists_isFullEncoding : ∃ W, S.IsFullEncoding W :=
  exists_isometry_stabProj S (two_pow_numLogical_mul_card_carrier S)

/-- Relative to a full encoding, implementing a logical unitary *is* preserving the code space:
`Π = W·Wᴴ`, so `Π·U·Π = W·V·Wᴴ = U·Π`. -/
theorem preservesCode_of_implementsLogicalWith
    {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ} (hW : S.IsFullEncoding W)
    {U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (h : S.ImplementsLogicalWith W U V) :
    stabProj S * U * stabProj S = U * stabProj S := by
  have h1 : U * W * W.conjTranspose = W * V * W.conjTranspose :=
    congrArg (fun M => M * W.conjTranspose) h
  have h2 : W.conjTranspose * (W * V) = V := by
    rw [← Matrix.mul_assoc, hW.1, Matrix.one_mul]
  calc stabProj S * U * stabProj S
      = W * (W.conjTranspose * (U * W)) * W.conjTranspose := by
        rw [← hW.2]
        simp only [Matrix.mul_assoc]
    _ = W * (W.conjTranspose * (W * V)) * W.conjTranspose := by
        rw [show U * W = W * V from h]
    _ = W * V * W.conjTranspose := by rw [h2]
    _ = U * W * W.conjTranspose := h1.symm
    _ = U * stabProj S := by rw [Matrix.mul_assoc, hW.2]

/-- **Discreteness up to phase (fixed encoding).** For the encoding `W`, some uniform `ε > 0`
separates any two non-proportional transversal logicals.

This is the analytic input to Eastin–Knill, and it is the projective form of the classical
argument: the transversal unitaries preserving the code space are a closed — hence, by Cartan's
closed-subgroup theorem, Lie — subgroup of the compact group `U(2)ⁿ`, and the logical action is a
continuous homomorphism to `PU(2ᵏ)` whose differential vanishes, because a one-parameter
transversal subgroup has a weight-`1` Hamiltonian generator and weight-`1` operators compress to
scalars on the code space once `2 ≤ distance` (`compress_scalar_of_weight_lt`). A homomorphism with
vanishing differential is locally constant, so the image is discrete.

The vanishing-differential half of that argument is proved above, in
`exists_scalar_of_lowWeightGen_flow`; `FinitelyManyTransversalComponents` below states the
remaining Lie-theoretic half in group-theoretic rather than metric form.

The fixed encoding `W` matters: with `W` existentially quantified the logical actions form a
conjugation-closed set, which no `ε` separates. -/
def SeparatedTransversalLogicals
    (W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ V ∈ S.transversalLogicalsWith W, ∀ V' ∈ S.transversalLogicalsWith W,
    (∀ c : ℂ, V ≠ c • V') → ε ≤ ‖V - V'‖

/-- The separation hypothesis holds outright for a code all of whose transversal logicals are
proportional to one another — the generic case, where only global phases act transversally. -/
theorem separatedTransversalLogicals_of_proportional
    {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (h : ∀ V ∈ S.transversalLogicalsWith W, ∀ V' ∈ S.transversalLogicalsWith W,
      ∃ c : ℂ, V = c • V') :
    S.SeparatedTransversalLogicals W := by
  refine ⟨1, one_pos, fun V hV V' hV' hnp => ?_⟩
  obtain ⟨c, hc⟩ := h V hV V' hV'
  exact absurd hc (hnp c)

/-- The transversal logical gates are finite *up to global phase* — the sharp form of Eastin–Knill.
Given discreteness up to phase (`SeparatedTransversalLogicals`), the transversal logicals live in
the compact unitary group, so any pairwise non-proportional family is `ε`-separated inside a
compact set, hence finite. -/
theorem transversal_logical_finite
    {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ} (hW : S.IsEncoding W)
    (hsep' : S.SeparatedTransversalLogicals W)
    (T : Set (Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ))
    (hT : T ⊆ S.transversalLogicalsWith W)
    (hpair : ∀ V ∈ T, ∀ V' ∈ T, V ≠ V' → ∀ c : ℂ, V ≠ c • V') :
    T.Finite := by
  obtain ⟨ε, hε, hsep⟩ := hsep'
  refine finite_of_separated S.unitaryGroup_isCompact
    (fun V hV => S.transversalLogicalsWith_subset_unitary hW (hT hV)) hε ?_
  intro V hV V' hV' hne
  rw [dist_eq_norm]
  exact hsep V (hT hV) V' (hT hV') (hpair V hV V' hV' hne)

/-- The logical unitary group (dimension `2^k ≥ 2` when `k ≥ 1`) contains an infinite family of
*pairwise non-proportional* unitaries — e.g. the diagonals `diag(1,…,e^{iθ},…,1)`, which agree at
one basis vector and differ at another, so no scalar relates two of them. -/
theorem exists_infinite_nonproportional_unitary (hk : 1 ≤ S.numLogical) :
    ∃ T : Set (Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ),
      (∀ V ∈ T, V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ) ∧
      (∀ V ∈ T, ∀ V' ∈ T, V ≠ V' → ∀ c : ℂ, V ≠ c • V') ∧ T.Infinite := by
  classical
  -- The index type is nontrivial (dimension `2^k ≥ 2`).
  have hnt : Nontrivial (Fin S.numLogical → ZMod 2) := by
    rw [← Fintype.one_lt_card_iff_nontrivial]
    have hc : Fintype.card (Fin S.numLogical → ZMod 2) = 2 ^ S.numLogical := by
      simp [Fintype.card_pi, ZMod.card, Finset.prod_const]
    rw [hc]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ S.numLogical := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Fin S.numLogical → ZMod 2)
  -- Distinct unit-modulus complex numbers `z m` (Cayley transform), with injective real part.
  have hpos : ∀ m : ℕ, (0 : ℝ) < 1 + (m : ℝ) ^ 2 := fun m => by positivity
  set z : ℕ → ℂ := fun m => ⟨(1 - (m : ℝ) ^ 2) / (1 + (m : ℝ) ^ 2),
                             (2 * (m : ℝ)) / (1 + (m : ℝ) ^ 2)⟩ with hz
  have hnorm : ∀ m, Complex.normSq (z m) = 1 := by
    intro m
    have h := (hpos m).ne'
    rw [hz, Complex.normSq_mk]
    field_simp
    ring
  have hstar : ∀ m, star (z m) * z m = 1 := by
    intro m
    rw [mul_comm, show star (z m) = (starRingEnd ℂ) (z m) from rfl, Complex.mul_conj, hnorm,
      Complex.ofReal_one]
  have hzinj : Function.Injective z := by
    intro m m' h
    have hre : (z m).re = (z m').re := congrArg Complex.re h
    simp only [hz] at hre
    rw [div_eq_div_iff (hpos m).ne' (hpos m').ne'] at hre
    have hmm : (m : ℝ) ^ 2 = (m' : ℝ) ^ 2 := by nlinarith [hre]
    have : (m : ℝ) = (m' : ℝ) := by
      nlinarith [sq_nonneg ((m : ℝ) - m'), sq_nonneg ((m : ℝ) + m'), hmm]
    exact_mod_cast this
  -- The diagonal family `D m = diag(1,…,z m,…,1)` (entry `z m` at index `b`).
  set d : ℕ → (Fin S.numLogical → ZMod 2) → ℂ := fun m i => if i = b then z m else 1 with hd
  set D : ℕ → Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ :=
    fun m => Matrix.diagonal (d m) with hD
  have hUnit : ∀ m, D m ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ := by
    intro m
    rw [Matrix.mem_unitaryGroup_iff', hD, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply, hd]
    by_cases hi : i = b
    · simp only [hi, if_true]
      exact hstar m
    · simp only [hi, if_false, star_one, mul_one]
  have hDbb : ∀ m, D m b b = z m := by
    intro m
    simp only [hD, Matrix.diagonal_apply_eq, hd, if_pos]
  have hDaa : ∀ m, D m a a = 1 := by
    intro m
    simp only [hD, Matrix.diagonal_apply_eq, hd, if_neg hab]
  refine ⟨Set.range D, ?_, ?_, ?_⟩
  · rintro V ⟨m, rfl⟩
    exact hUnit m
  · rintro V ⟨m, rfl⟩ V' ⟨m', rfl⟩ hne c hc
    have ha : D m a a = c * D m' a a := by rw [hc, Matrix.smul_apply, smul_eq_mul]
    rw [hDaa, hDaa, mul_one] at ha            -- ha : 1 = c
    have hb : D m b b = c * D m' b b := by rw [hc, Matrix.smul_apply, smul_eq_mul]
    rw [hDbb, hDbb, ← ha, one_mul] at hb      -- hb : z m = z m'
    exact hne (by rw [hzinj hb])
  · apply Set.infinite_range_of_injective
    intro m m' h
    have hb : D m b b = D m' b b := by rw [h]
    rw [hDbb, hDbb] at hb
    exact hzinj hb

/-- **Eastin–Knill theorem.** For a code whose transversal logicals are discrete up to phase
(`SeparatedTransversalLogicals` for the encoding `W`) and which encodes at least one logical qubit,
the transversal gates are *not universal*: some logical unitary cannot be implemented
transversally.

Proof: the logical unitary group contains an infinite pairwise-non-proportional family
(`exists_infinite_nonproportional_unitary`); if transversal gates were universal, that whole family
would be transversally implementable, contradicting `transversal_logical_finite` (transversal
logicals are finite up to global phase). The algebraic engine behind the finiteness is
`StabGroup.compress_scalar_of_weight_lt`. -/
theorem eastin_knill_of_separated {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (hW : S.IsEncoding W) (hsep : S.SeparatedTransversalLogicals W) (hk : 1 ≤ S.numLogical) :
    ¬ ∀ V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ,
        ∃ U, IsTransversal U ∧ S.ImplementsLogicalWith W U V := by
  intro hall
  obtain ⟨T, hTunit, hTpair, hTinf⟩ := S.exists_infinite_nonproportional_unitary hk
  exact hTinf (S.transversal_logical_finite hW hsep T (fun V hV => hall V (hTunit V hV)) hTpair)

/-! ### Eastin–Knill from the closed-subgroup theorem

The route above assumes discreteness of the logical actions in metric form. The route below takes
instead the structural statement that Cartan's closed-subgroup theorem provides, and derives
discreteness from it: the code-preserving transversal gates form a closed subgroup `G` of the
compact group `U(2)ⁿ`, hence a compact Lie group, so `G` has finitely many connected components and
its identity component is generated by one-parameter subgroups `exp (t·A)` with `A` in the Lie
algebra of `G` — a transversal, code-preserving Hamiltonian, i.e. a low-weight generator. That
statement is `FinitelyManyTransversalComponents`; it is proved for every code of distance at least
two in `QuantumLib.QECC.TransversalGroup`, which also gives the unconditional Eastin–Knill theorem
`StabGroup.eastin_knill`. That each one-parameter factor acts on the code space by a scalar is
`actsByScalar_of_isFlowGate`. -/

/-- **The Lie-theoretic input to Eastin–Knill.** There is a finite set `F` of code-preserving
gates — one per connected component — such that every transversal gate preserving the code space
along with its adjoint factors as an element of `F` times a flow gate.

For a compact Lie group this is Cartan's closed-subgroup theorem together with the fact that the
identity component of a Lie group is the exponential image of its Lie algebra; the code-preserving
transversal gates form such a group, and `StabGroup.finitelyManyTransversalComponents` proves the
statement for every code of distance at least two. -/
def FinitelyManyTransversalComponents : Prop :=
  ∃ F : Finset (Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ),
    (∀ f ∈ F, stabProj S * f * stabProj S = f * stabProj S) ∧
      ∀ U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ, IsTransversal U →
        stabProj S * U * stabProj S = U * stabProj S →
        stabProj S * U.conjTranspose * stabProj S = U.conjTranspose * stabProj S →
          ∃ f ∈ F, ∃ D, S.IsFlowGate D ∧ U = f * D

/-- The adjoint of a transversal gate implementing a logical unitary implements the adjoint logical
unitary, so it too preserves the code space. -/
theorem preservesCode_conjTranspose_of_implementsLogicalWith
    {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ} (hW : S.IsFullEncoding W)
    {U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ} (hU : IsTransversal U)
    {V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ}
    (h : S.ImplementsLogicalWith W U V) :
    stabProj S * U.conjTranspose * stabProj S = U.conjTranspose * stabProj S := by
  have hUu : U.conjTranspose * U = 1 :=
    Matrix.UnitaryGroup.star_mul_self ⟨U, hU.mem_unitaryGroup⟩
  have hVu : V * V.conjTranspose = 1 := by
    have : V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ :=
      S.transversalLogicalsWith_subset_unitary hW.isEncoding ⟨U, hU, h⟩
    exact Matrix.mem_unitaryGroup_iff.mp this
  refine S.preservesCode_of_implementsLogicalWith hW (V := V.conjTranspose) ?_
  -- `Uᴴ·W = Uᴴ·(U·W)·Vᴴ = W·Vᴴ`.
  calc U.conjTranspose * W
      = U.conjTranspose * (W * (V * V.conjTranspose)) := by rw [hVu, Matrix.mul_one]
    _ = U.conjTranspose * ((W * V) * V.conjTranspose) :=
        congrArg (fun M => U.conjTranspose * M) (Matrix.mul_assoc W V V.conjTranspose).symm
    _ = U.conjTranspose * ((U * W) * V.conjTranspose) :=
        congrArg (fun M : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ =>
          U.conjTranspose * (M * V.conjTranspose)) h.symm
    _ = (U.conjTranspose * U) * (W * V.conjTranspose) := by simp only [Matrix.mul_assoc]
    _ = W * V.conjTranspose := by rw [hUu, Matrix.one_mul]

/-- **Finitely many transversal logicals, up to phase.** Writing a transversal gate as `f·D` with
`f` a component representative and `D` a flow gate, the flow part contributes only the scalar by
which it acts on the code space, so the logical action is a scalar multiple of the logical action
`Wᴴ·f·W` of the representative. -/
theorem exists_finset_smul_of_components
    {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ} (hW : S.IsFullEncoding W)
    (hcomp : S.FinitelyManyTransversalComponents) :
    ∃ F : Finset (Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ),
      ∀ V ∈ S.transversalLogicalsWith W, ∃ f ∈ F, ∃ c : ℂ,
        V = c • (W.conjTranspose * f * W) := by
  obtain ⟨F, -, hFdec⟩ := hcomp
  refine ⟨F, ?_⟩
  rintro V ⟨U, hU, hUW⟩
  obtain ⟨f, hf, D, hD, rfl⟩ := hFdec U hU (S.preservesCode_of_implementsLogicalWith hW hUW)
    (S.preservesCode_conjTranspose_of_implementsLogicalWith hW hU hUW)
  obtain ⟨c, hc⟩ := S.actsByScalar_of_isFlowGate hD
  refine ⟨f, hf, c, ?_⟩
  -- The flow gate acts on the code space by the scalar `c`, and `Π·W = W`.
  have key : D * W = c • W := by
    calc D * W = D * (stabProj S * W) := by rw [hW.isEncoding.2]
      _ = D * stabProj S * W := (Matrix.mul_assoc ..).symm
      _ = (c • stabProj S) * W := by rw [hc]
      _ = c • (stabProj S * W) := Matrix.smul_mul ..
      _ = c • W := by rw [hW.isEncoding.2]
  have h2 : W.conjTranspose * (W * V) = V := by
    rw [← Matrix.mul_assoc, hW.1, Matrix.one_mul]
  have hVal : W.conjTranspose * (f * D * W) = V :=
    (congrArg (fun M => W.conjTranspose * M) hUW).trans h2
  -- Rectangular products pick up the `CStarMatrix` `HMul` instance inconsistently, so `rw` cannot
  -- match them; each rewrite is isolated in a `congrArg` and the `calc` steps are glued by defeq.
  calc V = W.conjTranspose * (f * D * W) := hVal.symm
    _ = W.conjTranspose * (f * (D * W)) :=
        congrArg (fun M => W.conjTranspose * M) (Matrix.mul_assoc f D W)
    _ = W.conjTranspose * (f * (c • W)) :=
        congrArg (fun M : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ =>
          W.conjTranspose * (f * M)) key
    _ = c • (W.conjTranspose * (f * W)) := by
        rw [Matrix.mul_smul f, Matrix.mul_smul W.conjTranspose]
    _ = c • (W.conjTranspose * f * W) :=
        congrArg (fun M : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ =>
          c • M) (Matrix.mul_assoc W.conjTranspose f W).symm

/-- The transversal logicals are finite up to global phase, with the number of components as the
bound: pairwise non-proportional transversal logicals come from distinct components, since two
sharing a component are scalar multiples of the same matrix. -/
theorem transversal_logical_finite_of_components
    {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ} (hW : S.IsFullEncoding W)
    (hcomp : S.FinitelyManyTransversalComponents)
    (T : Set (Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ))
    (hT : T ⊆ S.transversalLogicalsWith W)
    (hpair : ∀ V ∈ T, ∀ V' ∈ T, V ≠ V' → ∀ c : ℂ, V ≠ c • V') : T.Finite := by
  classical
  obtain ⟨F, hF⟩ := S.exists_finset_smul_of_components hW hcomp
  have key : ∀ V : T, ∃ f : F, ∃ c : ℂ,
      (V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ)
        = c • (W.conjTranspose * (f : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) * W) := by
    intro V
    obtain ⟨f, hf, c, hc⟩ := hF V (hT V.2)
    exact ⟨⟨f, hf⟩, c, hc⟩
  choose g c hgc using key
  -- Logical actions are unitary, so the scalars are nonzero.
  have hne0 : ∀ V : T,
      (V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) ≠ 0 := by
    intro V h0
    have hu : (V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) ∈
        Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ :=
      S.transversalLogicalsWith_subset_unitary hW.isEncoding (hT V.2)
    rw [Matrix.mem_unitaryGroup_iff', h0] at hu
    simp at hu
  have hinj : Function.Injective g := by
    intro V V' hgg
    by_contra hne
    have hVne : (V : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ)
        ≠ (V' : Matrix (Fin S.numLogical → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ) :=
      fun h => hne (Subtype.ext h)
    have hc' : c V' ≠ 0 := fun h0 => hne0 V' (by rw [hgc V', h0, zero_smul])
    refine hpair V V.2 V' V'.2 hVne (c V / c V') ?_
    rw [hgc V, hgc V', hgg, smul_smul, div_mul_cancel₀ _ hc']
  exact Set.finite_coe_iff.mp (Finite.of_injective g hinj)

/-- **Eastin–Knill theorem, closed-subgroup form.** For a code with at least one logical qubit
whose transversal gates have finitely many components in the sense of
`FinitelyManyTransversalComponents`, the transversal gates are not universal.

Everything here is proved from that single Lie-theoretic hypothesis: the flows inside a component
act on the code space by a phase because their generators have weight below the distance
(`actsByScalar_of_isFlowGate`), so the transversal logicals are finite up to phase, while the
logical unitary group contains an infinite pairwise non-proportional family. -/
theorem eastin_knill_of_components
    {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ} (hW : S.IsFullEncoding W)
    (hcomp : S.FinitelyManyTransversalComponents) (hk : 1 ≤ S.numLogical) :
    ¬ ∀ V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ,
        ∃ U, IsTransversal U ∧ S.ImplementsLogicalWith W U V := by
  intro hall
  obtain ⟨T, hTunit, hTpair, hTinf⟩ := S.exists_infinite_nonproportional_unitary hk
  exact hTinf (S.transversal_logical_finite_of_components hW hcomp T
    (fun V hV => hall V (hTunit V hV)) hTpair)
end StabGroup
end PauliOp
end QuantumLib
