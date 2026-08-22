/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.Defs
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef

/-!
# The Knill–Laflamme theorem

The fundamental theorem of quantum error correction: a code space, given by an encoding isometry
`W`, is protected against a noise channel `N` exactly when the Kraus operators `E a` of `N` satisfy
the **Knill–Laflamme conditions**
`Wᴴ (E a)ᴴ (E b) W = c a b • 1`.
-/

open scoped Matrix ComplexOrder

namespace QuantumLib

variable {H H2 K κ ι : Type*} [Fintype H] [DecidableEq H] [Fintype H2] [DecidableEq H2]
  [Fintype K] [DecidableEq K] [Fintype κ] [Fintype ι]

/-! ### Preliminaries on Kraus families -/

namespace Kraus

/-- A finite sum `∑ |zₖ|²` vanishes only if every `zₖ` does, phrased with `z * conj z`. -/
theorem eq_zero_of_sum_mul_conj_eq_zero {z : κ → ℂ}
    (h : ∑ k, z k * (starRingEnd ℂ) (z k) = 0) (k : κ) : z k = 0 := by
  have h' : ((∑ k, Complex.normSq (z k) : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_sum]
    simpa only [Complex.mul_conj] using h
  have h0 : ∑ k, Complex.normSq (z k) = 0 := by exact_mod_cast h'
  exact Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg (z i)).mp h0 k
      (Finset.mem_univ k))

/-- The trace-preservation condition on a Kraus family: `∑ (M k)ᴴ (M k) = 1`. -/
theorem sum_conjTranspose_mul_self {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (M : κ → Matrix B A ℂ) (hTP : (MatrixMap.of_kraus M M).IsTracePreserving) :
    ∑ k, (M k)ᴴ * M k = 1 := by
  ext i j
  have h := hTP (Matrix.of fun x y => if x = j then if y = i then (1 : ℂ) else 0 else 0)
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] at h
  convert h using 1
  · simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      MatrixMap.of_kraus, LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]
    rw [Finset.sum_comm]
    congr! 2 with k _
    simp only [Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, ite_mul, zero_mul]
    ring
  · simp [Matrix.one_apply, eq_comm]

/-- **Kraus operators of the identity channel are scalars.** If `∑ k, A k * X * (A k)ᴴ = X` for
every `X`, then each `A k` is a multiple of the identity matrix. -/
theorem eq_smul_one_of_kraus_eq_id (A : κ → Matrix K K ℂ)
    (h : ∀ X : Matrix K K ℂ, ∑ k, A k * X * (A k)ᴴ = X) (k : κ) :
    ∃ lam : ℂ, A k = lam • 1 := by
  -- entrywise form of the hypothesis, tested on the matrix units `single p q 1`
  have hentry : ∀ p q i j : K, ∑ k, A k i p * (starRingEnd ℂ) (A k j q)
      = if p = i ∧ q = j then (1 : ℂ) else 0 := by
    intro p q i j
    have hX := congrFun₂ (h (Matrix.single p q (1 : ℂ))) i j
    rw [Matrix.single_apply] at hX
    rw [← hX]
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.single_apply, mul_ite, mul_one, mul_zero, ite_and, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rfl
  -- off-diagonal entries vanish
  have hoff : ∀ p i : K, i ≠ p → A k i p = 0 := by
    intro p i hip
    refine eq_zero_of_sum_mul_conj_eq_zero (z := fun k => A k i p) ?_ k
    rw [hentry p p i i]
    simp [hip.symm]
  -- diagonal entries do not depend on the index
  have hdiag : ∀ p q : K, A k p p = A k q q := by
    intro p q
    have hd : ∀ r s : K, ∑ k, A k r r * (starRingEnd ℂ) (A k s s) = 1 := by
      intro r s
      simpa using hentry r s r s
    refine sub_eq_zero.mp (eq_zero_of_sum_mul_conj_eq_zero
      (z := fun k => A k p p - A k q q) ?_ k)
    have expand : ∀ k, (A k p p - A k q q) * (starRingEnd ℂ) (A k p p - A k q q)
        = A k p p * (starRingEnd ℂ) (A k p p) - A k p p * (starRingEnd ℂ) (A k q q)
          - A k q q * (starRingEnd ℂ) (A k p p) + A k q q * (starRingEnd ℂ) (A k q q) := by
      intro k
      rw [map_sub]
      ring
    rw [Finset.sum_congr rfl fun k _ => expand k, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, hd p p, hd p q, hd q p, hd q q]
    ring
  rcases isEmpty_or_nonempty K with hK | hK
  · exact ⟨0, by ext i j; exact (hK.false i).elim⟩
  · obtain ⟨k₀⟩ := hK
    refine ⟨A k k₀ k₀, ?_⟩
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp [hdiag i k₀]
    · simp [Matrix.one_apply_ne hij, hoff j i hij]

end Kraus

/-! ### Scalar matrices -/

omit [Fintype K] [Fintype H] [DecidableEq H] in
/-- A scalar multiple of the identity determines its scalar. -/
theorem smul_one_inj [Nonempty K] {x y : ℂ} (h : x • (1 : Matrix K K ℂ) = y • 1) : x = y := by
  obtain ⟨k₀⟩ := ‹Nonempty K›
  simpa [Matrix.one_apply] using congrFun₂ h k₀ k₀

/-! ### The Knill–Laflamme conditions -/

/-- The **Knill–Laflamme conditions** for a family of error operators `E` and an encoding isometry
`W`: the compressions `Wᴴ (E a)ᴴ (E b) W` of all products of errors to the code space are scalars. -/
def IsKnillLaflamme (W : Matrix H K ℂ) (E : ι → Matrix H2 H ℂ) : Prop :=
  ∃ c : ι → ι → ℂ, ∀ a b, Wᴴ * (E a)ᴴ * E b * W = c a b • 1

/-! ### Necessity -/

/-- **Necessity of the Knill–Laflamme conditions.** If some recovery channel `R` undoes the noise
`N` on the code space of the isometry `W`, then the Kraus operators of `N` satisfy the
Knill–Laflamme conditions. -/
theorem isKnillLaflamme_of_recovery [Nonempty K] {W : Matrix H K ℂ} (hW : Wᴴ * W = 1)
    {E : ι → Matrix H2 H ℂ} {N : CPTPMap H H2} (hN : N.map = MatrixMap.of_kraus E E)
    {R : CPTPMap H2 K} (hR : R ∘ₘ N ∘ₘ CPTPMap.ofIsometry W hW = CPTPMap.id) :
    IsKnillLaflamme W E := by
  obtain ⟨M, hM⟩ := R.cp.exists_kraus _
  have hM' : R.map = MatrixMap.of_kraus M M := hM
  have hMTP : ∑ j, (M j)ᴴ * M j = 1 :=
    Kraus.sum_conjTranspose_mul_self M (hM ▸ R.TP)
  set A : (K × H2) × ι → Matrix K K ℂ := fun p => M p.1 * E p.2 * W with hAdef
  have hkey : ∀ X : Matrix K K ℂ, ∑ p, A p * X * (A p)ᴴ = X := by
    intro X
    have h1 : R.map (N.map ((CPTPMap.ofIsometry W hW).map X)) = X :=
      congrArg (fun Λ : CPTPMap K K => Λ.map X) hR
    rw [CPTPMap.ofIsometry_map, hN, CPTPMap.of_kraus_apply, hM', CPTPMap.of_kraus_apply] at h1
    conv_rhs => rw [← h1]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [hAdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  choose lam hlam using Kraus.eq_smul_one_of_kraus_eq_id A hkey
  have hstep : ∀ a b, ∑ j : K × H2, (A (j, a))ᴴ * A (j, b) = Wᴴ * (E a)ᴴ * E b * W := by
    intro a b
    calc ∑ j : K × H2, (A (j, a))ᴴ * A (j, b)
        = Wᴴ * (E a)ᴴ * (∑ j : K × H2, (M j)ᴴ * M j) * (E b * W) := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by
            simp [hAdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Wᴴ * (E a)ᴴ * E b * W := by rw [hMTP]; simp [Matrix.mul_assoc]
  refine ⟨fun a b => ∑ j : K × H2, (starRingEnd ℂ) (lam (j, a)) * lam (j, b), fun a b => ?_⟩
  rw [← hstep a b, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hlam (j, a), hlam (j, b)]
  simp [Matrix.conjTranspose_smul, smul_smul, mul_comm]

/-- **Cross conditions from correcting two unitary errors.** A decoder that undoes each of the two
unitary channels `X · Xᴴ` and `Y · Yᴴ` also undoes their equal mixture, whose Kraus family is
`{X/√2, Y/√2}`; necessity of the Knill–Laflamme conditions for that mixture makes the cross term
`Wᴴ Xᴴ Y W` a scalar. -/
theorem exists_scalar_of_recovery_two_unitaries [Nonempty K] {W : Matrix H K ℂ} (hW : Wᴴ * W = 1)
    {X Y : Matrix H H ℂ} (hX : Xᴴ * X = 1) (hY : Yᴴ * Y = 1) {D : CPTPMap H K}
    {N₁ N₂ : CPTPMap H H} (hN₁ : N₁.map = MatrixMap.of_kraus (fun _ : Unit => X) fun _ => X)
    (hN₂ : N₂.map = MatrixMap.of_kraus (fun _ : Unit => Y) fun _ => Y)
    (h₁ : D ∘ₘ N₁ ∘ₘ CPTPMap.ofIsometry W hW = CPTPMap.id)
    (h₂ : D ∘ₘ N₂ ∘ₘ CPTPMap.ofIsometry W hW = CPTPMap.id) :
    ∃ z : ℂ, Wᴴ * Xᴴ * Y * W = z • 1 := by
  obtain ⟨r, hrr, hrs⟩ : ∃ r : ℂ, r * r = 2⁻¹ ∧ star r = r := by
    refine ⟨((Real.sqrt 2)⁻¹ : ℝ), ?_, Complex.conj_ofReal _⟩
    have h2 : ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ : ℝ) = 2⁻¹ := by
      rw [← Real.sqrt_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    rw [← Complex.ofReal_mul, h2]
    norm_num
  set E : Bool → Matrix H H ℂ := fun b => r • (bif b then X else Y) with hEdef
  have hsmul : ∀ Z : Matrix H H ℂ, Zᴴ * Z = 1 → (r • Z)ᴴ * (r • Z) = (2 : ℂ)⁻¹ • 1 := by
    intro Z hZ
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hZ, smul_smul, hrs, hrr]
  have hE : ∀ b, (E b)ᴴ * E b = (2 : ℂ)⁻¹ • 1 := by
    intro b
    cases b
    · exact hsmul Y hY
    · exact hsmul X hX
  have hTP : ∑ b, (E b)ᴴ * E b = 1 := by
    rw [Fintype.sum_bool, hE, hE, ← add_smul, show (2 : ℂ)⁻¹ + 2⁻¹ = 1 from by norm_num, one_smul]
  set N : CPTPMap H H := CPTPMap.of_kraus_CPTPMap E hTP with hNdef
  have hNmap : N.map = MatrixMap.of_kraus E E := rfl
  have hR : D ∘ₘ N ∘ₘ CPTPMap.ofIsometry W hW = CPTPMap.id := by
    refine CPTPMap.ext (LinearMap.ext fun Z => ?_)
    show D.map (N.map ((CPTPMap.ofIsometry W hW).map Z)) = Z
    have e₁ : D.map (N₁.map ((CPTPMap.ofIsometry W hW).map Z)) = Z :=
      congrArg (fun Λ : CPTPMap K K => Λ.map Z) h₁
    have e₂ : D.map (N₂.map ((CPTPMap.ofIsometry W hW).map Z)) = Z :=
      congrArg (fun Λ : CPTPMap K K => Λ.map Z) h₂
    have hsplit : ∀ M : Matrix H H ℂ, N.map M = (2 : ℂ)⁻¹ • N₁.map M + (2 : ℂ)⁻¹ • N₂.map M := by
      intro M
      rw [hNmap, CPTPMap.of_kraus_apply, Fintype.sum_bool, hN₁, hN₂, CPTPMap.of_kraus_apply,
        CPTPMap.of_kraus_apply]
      simp only [hEdef, cond_true, cond_false, Fintype.sum_unique, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.conjTranspose_smul, smul_smul, hrs, hrr]
    rw [hsplit, map_add, map_smul, map_smul, e₁, e₂, ← add_smul,
      show (2 : ℂ)⁻¹ + 2⁻¹ = 1 from by norm_num, one_smul]
  obtain ⟨c, hc⟩ := isKnillLaflamme_of_recovery hW hNmap hR
  have h := hc true false
  have hlhs : Wᴴ * (E true)ᴴ * E false * W = (2 : ℂ)⁻¹ • (Wᴴ * Xᴴ * Y * W) := by
    simp only [hEdef, cond_true, cond_false, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hrs, hrr]
  rw [hlhs] at h
  refine ⟨2 * c true false, ?_⟩
  calc Wᴴ * Xᴴ * Y * W = (2 : ℂ) • ((2 : ℂ)⁻¹ • (Wᴴ * Xᴴ * Y * W)) := by
        rw [smul_smul, show (2 : ℂ) * 2⁻¹ = 1 from by norm_num, one_smul]
    _ = (2 * c true false) • 1 := by rw [h, smul_smul]

/-! ### Sufficiency -/

omit [DecidableEq H] in
/-- If `Bᴴ B` is a scalar matrix, that scalar is nonnegative. -/
theorem nonneg_of_conjTranspose_mul_self_eq_smul_one [Nonempty K] {B : Matrix H K ℂ} {z : ℂ}
    (h : Bᴴ * B = z • (1 : Matrix K K ℂ)) : 0 ≤ z := by
  obtain ⟨k₀⟩ := ‹Nonempty K›
  have hp := (Matrix.posSemidef_conjTranspose_mul_self B).dotProduct_mulVec_nonneg
    (Pi.single k₀ 1)
  rw [h] at hp
  simpa using hp

omit [DecidableEq H] in
/-- **The Knill–Laflamme recovery.** If every compression `Wᴴ (E a)ᴴ (E b) W` is the scalar
`c a b`, then a single channel `R` inverts the whole error family at once, in the bilinear sense
`R (E a * ρ * (E b)ᴴ) = conj (c a b) • X` for every encoded state `ρ = W X Wᴴ`. Summing this
identity against a trace-preserving noise channel is what turns it into exact correction. -/
theorem exists_recovery_bilinear [Nonempty K] {W : Matrix H K ℂ}
    {E : ι → Matrix H2 H ℂ} {c : ι → ι → ℂ}
    (hc : ∀ a b, Wᴴ * (E a)ᴴ * E b * W = c a b • 1) :
    ∃ R : CPTPMap H2 K, ∀ (a b : ι) (X : Matrix K K ℂ),
      R.map (E a * (W * X * Wᴴ) * (E b)ᴴ) = (starRingEnd ℂ) (c a b) • X := by
  classical
  obtain ⟨k₀⟩ := ‹Nonempty K›
  have hEW : ∀ a b, (E a * W)ᴴ * (E b * W) = c a b • (1 : Matrix K K ℂ) := fun a b => by
    rw [← hc a b]; simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  -- the matrix of Knill–Laflamme coefficients is Hermitian, hence unitarily diagonalizable
  have hcstar : ∀ a b, (starRingEnd ℂ) (c a b) = c b a := by
    intro a b
    refine smul_one_inj (K := K) ?_
    have h := congrArg Matrix.conjTranspose (hEW a b)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hEW b a] at h
    simpa using h.symm
  set C : Matrix ι ι ℂ := Matrix.of c with hCdef
  have hCherm : C.IsHermitian := by
    show Cᴴ = C
    ext i j
    simpa [hCdef] using hcstar j i
  set U : Matrix ι ι ℂ := (hCherm.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  set dd : ι → ℝ := hCherm.eigenvalues with hdddef
  have hUU : U * Uᴴ = 1 := by
    simpa [hUdef, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hCherm.eigenvectorUnitary
  have hUrow : ∀ a b, (∑ i, U a i * (starRingEnd ℂ) (U b i)) = if a = b then (1 : ℂ) else 0 := by
    intro a b
    have h := congrFun₂ hUU a b
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  have hspec : Uᴴ * C * U = Matrix.diagonal (fun i => (dd i : ℂ)) := by
    have h := hCherm.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa [hUdef, hdddef, Matrix.star_eq_conjTranspose, Function.comp_def] using h
  have hUC : Uᴴ * C = Matrix.diagonal (fun i => (dd i : ℂ)) * Uᴴ := by
    have h : Uᴴ * C * U * Uᴴ = Matrix.diagonal (fun i => (dd i : ℂ)) * Uᴴ := by rw [hspec]
    rwa [Matrix.mul_assoc (Uᴴ * C), hUU, Matrix.mul_one] at h
  have hCUD : C = U * Matrix.diagonal (fun i => (dd i : ℂ)) * Uᴴ := by
    rw [← hspec]
    calc C = (U * Uᴴ) * C * (U * Uᴴ) := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
      _ = U * (Uᴴ * C * U) * Uᴴ := by simp [Matrix.mul_assoc]
  -- the rotated error operators, whose compressions are diagonal
  set F : ι → Matrix H2 H ℂ := fun i => ∑ a, U a i • E a with hFdef
  have hDapply : ∀ i j, (Uᴴ * C * U) i j
      = ∑ a, ∑ b, (starRingEnd ℂ) (U a i) * (c a b * U b j) := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hCdef, Matrix.of_apply,
      Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have hFW : ∀ i j, (F i * W)ᴴ * (F j * W)
      = (if i = j then (dd i : ℂ) else 0) • (1 : Matrix K K ℂ) := by
    intro i j
    have expand : (F i * W)ᴴ * (F j * W)
        = ∑ a, ∑ b, ((starRingEnd ℂ) (U a i) * (c a b * U b j)) • (1 : Matrix K K ℂ) := by
      simp only [hFdef, Matrix.sum_mul, Matrix.smul_mul, Matrix.conjTranspose_sum,
        Matrix.conjTranspose_smul, Matrix.mul_sum, Matrix.mul_smul, hEW, smul_smul,
        Finset.smul_sum]
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        congr 1
        simp only [starRingEnd_apply]
        ring
    rw [expand]
    simp only [← Finset.sum_smul]
    rw [← hDapply i j, hspec, Matrix.diagonal_apply]
  have hd0 : ∀ i, 0 ≤ dd i := by
    intro i
    have hz : (F i * W)ᴴ * (F i * W) = ((dd i : ℂ)) • (1 : Matrix K K ℂ) := by
      simpa using hFW i i
    exact Complex.zero_le_real.mp (nonneg_of_conjTranspose_mul_self_eq_smul_one hz)
  have hFW0 : ∀ i, dd i = 0 → F i * W = 0 := by
    intro i hi
    refine Matrix.conjTranspose_mul_self_eq_zero.mp ?_
    simpa [hi] using hFW i i
  have hEF : ∀ a, ∑ i, (starRingEnd ℂ) (U a i) • F i = E a := by
    intro a
    have expand : ∀ i, (starRingEnd ℂ) (U a i) • F i
        = ∑ b, ((starRingEnd ℂ) (U a i) * U b i) • E b := by
      intro i
      simp only [hFdef, Finset.smul_sum, smul_smul]
    have hrow : ∀ b, ∑ i, ((starRingEnd ℂ) (U a i) * U b i) • E b
        = (if b = a then (1 : ℂ) else 0) • E b := by
      intro b
      rw [← Finset.sum_smul, ← hUrow b a]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [Finset.sum_congr rfl fun i _ => expand i, Finset.sum_comm,
      Finset.sum_congr rfl fun b _ => hrow b]
    simp
  -- the partial isometries carrying the code space into the syndrome subspaces
  set rt : ι → ℂ := fun i => ((Real.sqrt (dd i) : ℝ) : ℂ) with hrtdef
  have hrt : ∀ i, rt i * rt i = (dd i : ℂ) := by
    intro i
    simp only [hrtdef]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hd0 i)]
  have hrtstar : ∀ i, star (rt i) = rt i := fun i => Complex.conj_ofReal _
  have hrtne : ∀ i, dd i ≠ 0 → rt i ≠ 0 := by
    intro i hi
    have hpos : 0 < dd i := lt_of_le_of_ne (hd0 i) (Ne.symm hi)
    simpa [hrtdef] using Real.sqrt_ne_zero'.mpr hpos
  set V : ι → Matrix H2 K ℂ := fun i => (rt i)⁻¹ • (F i * W) with hVdef
  set ee : ι → ℂ := fun i => if dd i = 0 then 0 else 1 with heedef
  have hV0 : ∀ i, dd i = 0 → V i = 0 := by
    intro i hi
    simp [hVdef, hFW0 i hi]
  have hFWV : ∀ i, F i * W = rt i • V i := by
    intro i
    rcases eq_or_ne (dd i) 0 with h | h
    · simp [hVdef, hFW0 i h, hrtdef, h]
    · rw [hVdef]
      simp only [smul_smul, mul_inv_cancel₀ (hrtne i h), one_smul]
  have hVV : ∀ i j, (V i)ᴴ * V j = (if i = j then ee i else 0) • (1 : Matrix K K ℂ) := by
    intro i j
    rw [hVdef]
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hFW i j]
    rcases eq_or_ne i j with rfl | hij
    · rcases eq_or_ne (dd i) 0 with h | h
      · simp [heedef, h, hrtdef]
      · have hne := hrtne i h
        have hs : (rt i)⁻¹ * (star ((rt i)⁻¹) * (dd i : ℂ)) = ee i := by
          rw [star_inv₀, hrtstar i, ← hrt i, heedef]
          simp only [if_neg h]
          field_simp
        rw [if_pos rfl, if_pos rfl, hs]
    · simp [hij]
  -- each error operator maps the code space into the span of the `V i`
  have hVE : ∀ i a, (V i)ᴴ * (E a * W)
      = (rt i * (starRingEnd ℂ) (U a i)) • (1 : Matrix K K ℂ) := by
    intro i a
    rcases eq_or_ne (dd i) 0 with h | h
    · rw [hV0 i h]
      simp [hrtdef, h]
    · have e2 : ∑ b, (starRingEnd ℂ) (U b i) * c b a
          = (dd i : ℂ) * (starRingEnd ℂ) (U a i) := by
        have h2 := congrFun₂ hUC i a
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, hCdef, Matrix.diagonal_apply,
          Finset.sum_ite_eq, ite_mul] using h2
      have hFE : (F i * W)ᴴ * (E a * W)
          = ((dd i : ℂ) * (starRingEnd ℂ) (U a i)) • (1 : Matrix K K ℂ) := by
        have e1 : (F i * W)ᴴ * (E a * W)
            = ∑ b, ((starRingEnd ℂ) (U b i) * c b a) • (1 : Matrix K K ℂ) := by
          simp only [hFdef, Matrix.sum_mul, Matrix.smul_mul, Matrix.conjTranspose_sum,
            Matrix.conjTranspose_smul, hEW, smul_smul, starRingEnd_apply]
        rw [e1, ← Finset.sum_smul, e2]
      rw [hVdef]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, hFE, smul_smul, star_inv₀, hrtstar i]
      congr 1
      rw [← hrt i]
      field_simp
  -- the recovery channel
  set P : Matrix H2 H2 ℂ := ∑ i, V i * (V i)ᴴ with hPdef
  set Q : Matrix H2 H2 ℂ := 1 - P with hQdef
  have hPV : ∀ j, P * V j = V j := by
    intro j
    rw [hPdef, Matrix.sum_mul]
    have hterm : ∀ i, (V i * (V i)ᴴ) * V j = (if i = j then ee i else 0) • V i := by
      intro i
      rw [Matrix.mul_assoc, hVV i j, Matrix.mul_smul, Matrix.mul_one]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases eq_or_ne (dd j) 0 with h | h
    · simp [hV0 j h]
    · simp [heedef, h]
  have hQV : ∀ j, Q * V j = 0 := by
    intro j
    rw [hQdef, Matrix.sub_mul, Matrix.one_mul, hPV j, sub_self]
  have hQE : ∀ a, Q * (E a * W) = 0 := by
    intro a
    rw [← hEF a, Matrix.sum_mul, Matrix.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hFWV i, Matrix.mul_smul, hQV i, smul_zero, smul_zero]
  have hQh : Qᴴ = Q := by
    have hPh : Pᴴ = P := by
      rw [hPdef, Matrix.conjTranspose_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [hQdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh]
  have hQQ : Q * Q = Q := by
    have hPP : P * P = P := by
      conv_lhs => rw [hPdef]
      rw [Matrix.mul_sum]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans hPdef.symm
      rw [← Matrix.mul_assoc, hPV i]
    have h : Q * Q = 1 - P - P + P * P := by rw [hQdef]; noncomm_ring
    rw [h, hPP, hQdef]
    abel
  set RK : ι ⊕ H2 → Matrix K H2 ℂ :=
    Sum.elim (fun i => (V i)ᴴ) (fun x => Matrix.single k₀ x (1 : ℂ) * Q) with hRKdef
  have hRKTP : ∑ k, (RK k)ᴴ * RK k = 1 := by
    rw [Fintype.sum_sum_type]
    have h1 : ∑ i, (RK (Sum.inl i))ᴴ * RK (Sum.inl i) = P := by
      rw [hPdef]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [hRKdef, Sum.elim_inl, Matrix.conjTranspose_conjTranspose]
    have h2 : ∑ x, (RK (Sum.inr x))ᴴ * RK (Sum.inr x) = Q := by
      have hterm : ∀ x : H2, (RK (Sum.inr x))ᴴ * RK (Sum.inr x)
          = Q * Matrix.single x x (1 : ℂ) * Q := by
        intro x
        simp only [hRKdef, Sum.elim_inr]
        rw [Matrix.conjTranspose_mul, hQh, Matrix.conjTranspose_single, star_one, Matrix.mul_assoc,
          ← Matrix.mul_assoc (Matrix.single x k₀ (1 : ℂ)), Matrix.single_mul_single_same, mul_one,
          ← Matrix.mul_assoc]
      calc ∑ x, (RK (Sum.inr x))ᴴ * RK (Sum.inr x)
          = Q * (∑ x : H2, Matrix.single x x (1 : ℂ)) * Q := by
            rw [Matrix.mul_sum, Matrix.sum_mul]
            exact Finset.sum_congr rfl fun x _ => hterm x
        _ = Q := by rw [CPTPMap.sum_single_diag, Matrix.mul_one, hQQ]
    rw [h1, h2, hQdef]
    abel
  refine ⟨CPTPMap.of_kraus_CPTPMap RK hRKTP, fun a b X => ?_⟩
  show MatrixMap.of_kraus RK RK (E a * (W * X * Wᴴ) * (E b)ᴴ) = _
  have hY : E a * (W * X * Wᴴ) * (E b)ᴴ = (E a * W) * X * (E b * W)ᴴ := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hY, CPTPMap.of_kraus_apply, Fintype.sum_sum_type]
  have hjunk : ∑ x : H2, RK (Sum.inr x) * ((E a * W) * X * (E b * W)ᴴ) * (RK (Sum.inr x))ᴴ = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    have h0 : RK (Sum.inr x) * ((E a * W) * X * (E b * W)ᴴ) = 0 := by
      simp only [hRKdef, Sum.elim_inr]
      calc Matrix.single k₀ x (1 : ℂ) * Q * ((E a * W) * X * (E b * W)ᴴ)
          = (Matrix.single k₀ x (1 : ℂ) * (Q * (E a * W))) * (X * (E b * W)ᴴ) := by
            simp [Matrix.mul_assoc]
        _ = 0 := by rw [hQE a]; simp
    rw [h0, Matrix.zero_mul]
  have hmain : ∑ i, RK (Sum.inl i) * ((E a * W) * X * (E b * W)ᴴ) * (RK (Sum.inl i))ᴴ
      = (starRingEnd ℂ) (c a b) • X := by
    have step : ∀ i, RK (Sum.inl i) * ((E a * W) * X * (E b * W)ᴴ) * (RK (Sum.inl i))ᴴ
        = ((starRingEnd ℂ) (U a i) * ((dd i : ℂ) * U b i)) • X := by
      intro i
      simp only [hRKdef, Sum.elim_inl, Matrix.conjTranspose_conjTranspose]
      have hassoc : (V i)ᴴ * ((E a * W) * X * (E b * W)ᴴ) * V i
          = ((V i)ᴴ * (E a * W)) * X * ((V i)ᴴ * (E b * W))ᴴ := by
        simp [Matrix.mul_assoc, Matrix.conjTranspose_mul]
      rw [hassoc, hVE i a, hVE i b]
      simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
      congr 1
      rw [← hrt i]
      simp only [starRingEnd_apply, star_mul', star_star, hrtstar i]
      ring
    have hcoeff : ∑ i, (starRingEnd ℂ) (U a i) * ((dd i : ℂ) * U b i)
        = (starRingEnd ℂ) (c a b) := by
      have h := congrFun₂ hCUD a b
      have hc' : c a b = ∑ i, U a i * ((dd i : ℂ) * (starRingEnd ℂ) (U b i)) := by
        simpa [hCdef, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
          Finset.sum_mul, mul_assoc, Finset.sum_ite_eq, ite_mul] using h
      rw [hc', map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    rw [Finset.sum_congr rfl fun i _ => step i, ← Finset.sum_smul, hcoeff]
  rw [hmain, hjunk, add_zero]

universe v

/-- **Sufficiency of the Knill–Laflamme conditions, uniformly in the noise.** If the error family
`E` satisfies the Knill–Laflamme conditions for the encoding isometry `W`, then a *single* recovery
channel corrects every noise channel whose Kraus operators lie in the span of `E`: correctability
depends on the errors only through the subspace they span. -/
theorem exists_recovery_span [Nonempty K] {W : Matrix H K ℂ} (hW : Wᴴ * W = 1)
    {E : ι → Matrix H2 H ℂ} (hKL : IsKnillLaflamme W E) :
    ∃ R : CPTPMap H2 K,
      ∀ {ι' : Type v} [Fintype ι'] (E' : ι' → Matrix H2 H ℂ) (N : CPTPMap H H2),
      (∀ b, E' b ∈ Submodule.span ℂ (Set.range E)) → N.map = MatrixMap.of_kraus E' E' →
      R ∘ₘ N ∘ₘ CPTPMap.ofIsometry W hW = CPTPMap.id := by
  classical
  obtain ⟨c, hc⟩ := hKL
  obtain ⟨R, hR⟩ := exists_recovery_bilinear (W := W) hc
  refine ⟨R, ?_⟩
  intro ι' _ E' N hspan hN
  refine CPTPMap.ext (LinearMap.ext fun X => ?_)
  show R.map (N.map ((CPTPMap.ofIsometry W hW).map X)) = X
  rw [CPTPMap.ofIsometry_map, hN, CPTPMap.of_kraus_apply]
  choose μ hμ using fun b => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan b)
  have hTP : ∑ b, (E' b)ᴴ * E' b = 1 := Kraus.sum_conjTranspose_mul_self E' (hN ▸ N.TP)
  -- the total weight of the Knill–Laflamme coefficients is fixed by trace preservation
  have hone : ∑ b, ∑ a, ∑ a', (starRingEnd ℂ) (μ b a) * μ b a' * c a a' = 1 := by
    refine smul_one_inj (K := K) ?_
    have hb : ∀ b, Wᴴ * (E' b)ᴴ * E' b * W
        = (∑ a, ∑ a', (starRingEnd ℂ) (μ b a) * μ b a' * c a a') • (1 : Matrix K K ℂ) := by
      intro b
      rw [← hμ b]
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.mul_sum,
        Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hc, smul_smul, Finset.smul_sum,
        ← Finset.sum_smul, starRingEnd_apply]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => by ring
    calc (∑ b, ∑ a, ∑ a', (starRingEnd ℂ) (μ b a) * μ b a' * c a a') • (1 : Matrix K K ℂ)
        = ∑ b, Wᴴ * (E' b)ᴴ * E' b * W := by
          rw [Finset.sum_smul]
          exact Finset.sum_congr rfl fun b _ => (hb b).symm
      _ = Wᴴ * (∑ b, (E' b)ᴴ * E' b) * W := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by simp [Matrix.mul_assoc]
      _ = (1 : ℂ) • (1 : Matrix K K ℂ) := by rw [hTP]; simp [hW]
  have hexpand : ∀ b, E' b * (W * X * Wᴴ) * (E' b)ᴴ
      = ∑ a, ∑ a', (μ b a * (starRingEnd ℂ) (μ b a')) • (E a * (W * X * Wᴴ) * (E a')ᴴ) := by
    intro b
    rw [← hμ b]
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul, Matrix.mul_sum, Matrix.mul_smul, smul_smul, Finset.smul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => by
      congr 1
      simp only [starRingEnd_apply]
      ring
  have hfinal : R.map (∑ b, E' b * (W * X * Wᴴ) * (E' b)ᴴ)
      = ((starRingEnd ℂ) (∑ b, ∑ a, ∑ a', (starRingEnd ℂ) (μ b a) * μ b a' * c a a')) • X := by
    rw [Finset.sum_congr rfl fun b _ => hexpand b, map_sum, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_sum, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [map_smul, hR a a' X, smul_smul, map_mul, map_mul, Complex.conj_conj]
  rw [hfinal, hone, map_one, one_smul]

/-- **Sufficiency of the Knill–Laflamme conditions.** If the Kraus operators of the noise `N`
satisfy the Knill–Laflamme conditions for the encoding isometry `W`, then there is a recovery
channel undoing `N` on the code space. -/
theorem exists_recovery_of_isKnillLaflamme [Nonempty K] {W : Matrix H K ℂ} (hW : Wᴴ * W = 1)
    {E : ι → Matrix H2 H ℂ} {N : CPTPMap H H2} (hN : N.map = MatrixMap.of_kraus E E)
    (hKL : IsKnillLaflamme W E) :
    ∃ R : CPTPMap H2 K, R ∘ₘ N ∘ₘ CPTPMap.ofIsometry W hW = CPTPMap.id := by
  obtain ⟨R, hR⟩ := exists_recovery_span hW hKL
  exact ⟨R, hR E N (fun a => Submodule.subset_span ⟨a, rfl⟩) hN⟩

/-! ### The theorem -/

/-- **The Knill–Laflamme theorem.** A noise channel `N` with Kraus operators `E` can be corrected on
the code space of the encoding isometry `W` — that is, some recovery channel `R` restores every
logical state after the noise — exactly when the Knill–Laflamme conditions
`Wᴴ (E a)ᴴ (E b) W = c a b • 1` hold. -/
theorem knill_laflamme_iff [Nonempty K] {W : Matrix H K ℂ} (hW : Wᴴ * W = 1)
    {E : ι → Matrix H2 H ℂ} {N : CPTPMap H H2} (hN : N.map = MatrixMap.of_kraus E E) :
    (∃ R : CPTPMap H2 K, R ∘ₘ N ∘ₘ CPTPMap.ofIsometry W hW = CPTPMap.id) ↔ IsKnillLaflamme W E :=
  ⟨fun ⟨_, hR⟩ => isKnillLaflamme_of_recovery hW hN hR, exists_recovery_of_isKnillLaflamme hW hN⟩

/-- The Knill–Laflamme conditions depend only on the channel, not on the Kraus family chosen to
represent it. -/
theorem isKnillLaflamme_congr [Nonempty K] {W : Matrix H K ℂ} (hW : Wᴴ * W = 1)
    {E : ι → Matrix H2 H ℂ} {E' : κ → Matrix H2 H ℂ} {N : CPTPMap H H2}
    (hE : N.map = MatrixMap.of_kraus E E) (hE' : N.map = MatrixMap.of_kraus E' E') :
    IsKnillLaflamme W E ↔ IsKnillLaflamme W E' :=
  (knill_laflamme_iff hW hE).symm.trans (knill_laflamme_iff hW hE')

/-- **The Knill–Laflamme theorem for a `QECC` with an isometric encoder.** Such a code admits a
decoder correcting the noise `N` exactly when the Kraus operators of `N` satisfy the Knill–Laflamme
conditions for the encoding isometry. -/
theorem QECC.exists_decoder_iff_isKnillLaflamme {d1 i d2 : Type*} [Fintype i] [DecidableEq i]
    [Fintype d1] [DecidableEq d1] [Nonempty d1] [Fintype d2] [DecidableEq d2] {C : QECC d1 i d2}
    {W : Matrix (i → d2) d1 ℂ} (hW : Wᴴ * W = 1) (hC : C.encoder = CPTPMap.ofIsometry W hW)
    {E : ι → Matrix (i → d2) (i → d2) ℂ} {N : CPTPMap (i → d2) (i → d2)}
    (hN : N.map = MatrixMap.of_kraus E E) :
    (∃ D : CPTPMap (i → d2) d1, D ∘ₘ N ∘ₘ C.encoder = CPTPMap.id) ↔ IsKnillLaflamme W E := by
  rw [hC]
  exact knill_laflamme_iff hW hN

end QuantumLib
