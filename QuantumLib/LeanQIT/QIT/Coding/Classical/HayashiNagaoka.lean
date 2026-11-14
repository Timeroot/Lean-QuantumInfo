/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.PosSqrt
public import QIT.States.PosSqrtOrder

/-!
# Hayashi--Nagaoka operator inequality

This module proves the operator inequality underlying the square-root
measurement error analysis of the packing lemma. For positive semidefinite
matrices `S ≤ I` and `T ≥ 0`,
`I − (S+T)^{−1/2} S (S+T)^{−1/2} ≤ 2(I − S) + 4T`,
the per-codeword error split (the `c = 1` specialization of the
Hayashi--Nagaoka family) that drives the packing-lemma achievability bound.

The argument expands `(A − B)†(A − B) ≥ 0` with `A = √T · R` and
`B = √T · (1 − R)` (no scalar parameter), giving the integer-coefficient
core `T ≤ 2 R†TR + 2 (1−R)†T(1−R)`. Specializing to `R = (S+T)^{1/2}`,
using `S^{1/2} ≤ (S+T)^{1/2}` (operator-monotone square root) and the
support-projector identity `(S+T)^{−1/2}(S+T)(S+T)^{−1/2} = Π_{S+T} ≤ I`
for `psdInvSqrt`, yields the stated bound. Here `psdSqrt M` and
`psdInvSqrt M h` are both continuous-functional-calculus images of the same
Hermitian `M`, hence commute; this commutativity is established once and for
all in `psdInvSqrt_mul_psdSqrt` via the shared spectral basis.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u

noncomputable section

-- The Hayashi--Nagaoka argument expands several large matrix expressions
-- (with `ST = R²` substitutions) via `noncomm_ring`; raise the heartbeats
-- limit so these normalizations complete.
set_option maxHeartbeats 4000000


variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Auxiliary: the inverse square root on the support and the square root of a
positive semidefinite matrix commute, since both are realized in the same
eigenbasis (continuous-functional-calculus images of the same Hermitian). -/
theorem psdInvSqrt_mul_psdSqrt {M : CMatrix a} (hM : M.PosSemidef) :
    psdInvSqrt M hM.isHermitian * psdSqrt M =
      psdSqrt M * psdInvSqrt M hM.isHermitian := by
  let U : CMatrix a := hM.isHermitian.eigenvectorUnitary
  have hU : star U * U = (1 : CMatrix a) :=
    by simp [U, Unitary.coe_star_mul_self hM.isHermitian.eigenvectorUnitary]
  have hdiag_comm (D₁ D₂ : CMatrix a) :
      U * D₁ * star U * (U * D₂ * star U) = U * (D₁ * D₂) * star U := by
    calc (U * D₁ * star U) * (U * D₂ * star U)
        = U * D₁ * (star U * U) * D₂ * star U := by noncomm_ring
      _ = U * D₁ * 1 * D₂ * star U := by rw [hU]
      _ = U * (D₁ * D₂) * star U := by noncomm_ring
  have hRspec : psdSqrt M =
      U * Matrix.diagonal (fun i =>
        (↑((hM.isHermitian.eigenvalues i) ^ ((1:ℝ)/2) : ℝ) : ℂ)) * star U := by
    show CFC.sqrt M = _
    rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real (a := M) (y := (1:ℝ)/2)
        (Matrix.nonneg_iff_posSemidef.mpr hM),
      Matrix.IsHermitian.cfc_eq hM.isHermitian, Matrix.IsHermitian.cfc]
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def]
    rfl
  have hBspec : psdInvSqrt M hM.isHermitian =
      U * Matrix.diagonal (fun i : a =>
        if 0 < hM.isHermitian.eigenvalues i
        then (↑(Real.rpow (hM.isHermitian.eigenvalues i) (-(1:ℝ)/2)) : ℂ) else (0 : ℂ)) * star U := by
    rfl
  simp only [hRspec, hBspec]
  set Dinv : CMatrix a := Matrix.diagonal (fun i : a =>
    if 0 < hM.isHermitian.eigenvalues i
    then (↑(Real.rpow (hM.isHermitian.eigenvalues i) (-(1:ℝ)/2)) : ℂ) else (0 : ℂ)) with _
  set Dsqrt : CMatrix a := Matrix.diagonal (fun i =>
    (↑((hM.isHermitian.eigenvalues i) ^ ((1:ℝ)/2) : ℝ) : ℂ)) with _
  have hdiag_comm' : (U * Dinv * star U) * (U * Dsqrt * star U) = U * (Dinv * Dsqrt) * star U :=
    hdiag_comm Dinv Dsqrt
  have hdiag_comm'' : (U * Dsqrt * star U) * (U * Dinv * star U) = U * (Dsqrt * Dinv) * star U :=
    hdiag_comm Dsqrt Dinv
  have hDD : Dinv * Dsqrt = Dsqrt * Dinv := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
        Dinv, Dsqrt, reduceIte]
      exact mul_comm _ _
    · simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Dinv, Dsqrt, hij, if_false]
  rw [hdiag_comm', hdiag_comm'', hDD]

/-- Core lemma (integer `c = 1`): for positive semidefinite `T` and any square
`R`, `T ≤ 2 • (R† T R) + 2 • ((1−R)† T (1−R))`. This is the `(A−B)†(A−B) ≥ 0`
expansion with `A = √T · R`, `B = √T · (1 − R)`, combined with the partition
`T = R†TR + R†T(1−R) + (1−R)†TR + (1−R)†T(1−R)`. Stated in Loewner form
`(2 • (R†TR) + 2 • ((1−R)†T(1−R)) − T).PosSemidef`.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
theorem psd_core_conjugation_bound (T R : CMatrix a) (hT : T.PosSemidef) :
    ((2 : ℝ) • (star R * T * R) + (2 : ℝ) • (star (1 - R) * T * (1 - R)) - T).PosSemidef := by
  -- Let `sT := psdSqrt T`; then `sT * sT = T` and `star sT = sT` (Hermitian).
  set sT : CMatrix a := psdSqrt T with hsT_def
  have hsT_sq : sT * sT = T := psdSqrt_mul_self_of_posSemidef hT
  have hsT_star : star sT = sT := (psdSqrt_isHermitian T).eq
  -- The PSD seed: `(A − B)† (A − B) ≥ 0` for `A = sT·R`, `B = sT·(1−R)`.
  have hseed : (star (sT * R - sT * (1 - R)) * (sT * R - sT * (1 - R))).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self _
  -- Algebraic identity `2•C₁ + 2•C₄ − T = (A−B)†(A−B)` (the `(A−B)†(A−B) ≥ 0`
  -- expansion plus the partition `T = C₁+C₂+C₃+C₄`). We rewrite `T → sT·sT`,
  -- normalize `star` so it wraps only atoms (`star(1−R) → 1 − star R`,
  -- `star sT → sT`), flatten integer smul into sums, and close with `noncomm_ring`.
  have hkey : (2 : ℝ) • (star R * T * R) + (2 : ℝ) • (star (1 - R) * T * (1 - R)) - T =
      star (sT * R - sT * (1 - R)) * (sT * R - sT * (1 - R)) := by
    conv_lhs => rw [← hsT_sq]
    conv_rhs =>
      rw [show star (sT * R - sT * (1 - R)) = star R * sT - star (1 - R) * sT from by
          simp only [star_sub, StarMul.star_mul, hsT_star, star_one]]
    simp only [star_sub, star_one] at *
    simp only [two_smul]
    noncomm_ring
  rw [hkey]
  exact hseed

/-- For positive semidefinite `M` with square root `R = psdSqrt M` and
inverse-square-root-on-support `B = psdInvSqrt M`, the product `B * R` equals
the spectral support projector of `M` (it is `λ^{-1/2}·λ^{1/2} = 1` on the
support and `0` on the kernel). This is the same diagonal mask appearing in
`psdInvSqrt_support_eq`, since `B = U·diag(λ^{-1/2})·U†` and
`R = U·diag(λ^{1/2})·U†` share the eigenvector basis `U`.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
theorem psdInvSqrt_mul_psdSqrt_eq_support {M : CMatrix a} (hM : M.PosSemidef) :
    psdInvSqrt M hM.isHermitian * psdSqrt M =
      (hM.isHermitian.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i : a =>
          if 0 < hM.isHermitian.eigenvalues i then (1 : ℂ) else 0) *
        star (hM.isHermitian.eigenvectorUnitary : CMatrix a) := by
  let U : CMatrix a := hM.isHermitian.eigenvectorUnitary
  let Dinv : CMatrix a := Matrix.diagonal (fun i : a =>
    if 0 < hM.isHermitian.eigenvalues i
    then (↑(Real.rpow (hM.isHermitian.eigenvalues i) (-(1:ℝ)/2)) : ℂ) else (0 : ℂ))
  let Dsqrt : CMatrix a := Matrix.diagonal (fun i =>
    (↑((hM.isHermitian.eigenvalues i) ^ ((1:ℝ)/2) : ℝ) : ℂ))
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hM.isHermitian.eigenvectorUnitary]
  have hBspec : psdInvSqrt M hM.isHermitian = U * Dinv * star U := by rfl
  have hRspec : psdSqrt M = U * Dsqrt * star U := by
    show CFC.sqrt M = _
    rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real (a := M) (y := (1:ℝ)/2)
        (Matrix.nonneg_iff_posSemidef.mpr hM),
      Matrix.IsHermitian.cfc_eq hM.isHermitian, Matrix.IsHermitian.cfc]
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def]
    rfl
  have hDD : Dinv * Dsqrt =
      Matrix.diagonal (fun i : a =>
        if 0 < hM.isHermitian.eigenvalues i then (1 : ℂ) else 0) := by
    show (Matrix.diagonal _ * Matrix.diagonal _) =
      Matrix.diagonal (fun i : a =>
        if 0 < hM.isHermitian.eigenvalues i then (1 : ℂ) else 0)
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
      by_cases hi : 0 < hM.isHermitian.eigenvalues i
      · -- positive eigenvalue: λ^{-1/2} · λ^{1/2} = 1.
        simp only [hi, ↓reduceIte]
        have hreal : (hM.isHermitian.eigenvalues i) ^ (-(1:ℝ)/2) *
            (hM.isHermitian.eigenvalues i) ^ ((1:ℝ)/2) = 1 := by
          have hsum : (-(1:ℝ)/2) + (1:ℝ)/2 = 0 := by ring
          rw [← Real.rpow_add hi, hsum, Real.rpow_zero]
        exact_mod_cast hreal
      · -- non-positive eigenvalue: by PSD this is zero, so the `Dinv` side
        -- takes the `else 0` branch, and the RHS diagonal entry is also `0`.
        have heig_nn : 0 ≤ hM.isHermitian.eigenvalues i := hM.eigenvalues_nonneg i
        have heig_zero : hM.isHermitian.eigenvalues i = 0 := by linarith
        simp only [heig_zero, reduceIte]
        -- `0 < 0` is decidable-false; reduce both `if`s to their `else` branch.
        have hn : ¬ (0 : ℝ) < 0 := lt_irrefl _
        simp only [hn, ↓reduceIte]
        exact zero_mul _
    · -- off-diagonal
      simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, hij, ↓reduceIte]
  rw [hBspec, hRspec]
  calc (U * Dinv * star U) * (U * Dsqrt * star U)
      = U * Dinv * (star U * U) * Dsqrt * star U := by noncomm_ring
    _ = U * Dinv * 1 * Dsqrt * star U := by rw [hU]
    _ = U * (Dinv * Dsqrt) * star U := by noncomm_ring
    _ = U * Matrix.diagonal (fun i : a =>
          if 0 < hM.isHermitian.eigenvalues i then (1 : ℂ) else 0) * star U := by rw [hDD]

/-- Auxiliary: a positive semidefinite matrix `A` with a zero diagonal entry
`A i i = 0` has its entire `i`-th row and column equal to zero. From
`PosSemidef.dotProduct_mulVec_zero_iff`, the quadratic form `eᵢ† A eᵢ = Aᵢᵢ = 0`
forces `A eᵢ = 0` (zero column), and Hermiticity gives the zero row.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
private lemma PosSemidef.zero_diag_zero_row_col
    {n : Type u} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {i : n} (hii : A i i = 0) (j : n) :
    A i j = 0 ∧ A j i = 0 := by
  -- The `i`-th standard basis vector `eᵢ = Pi.single i 1`.
  set e : n → ℂ := Pi.single i 1 with he
  have hei : e i = (1:ℂ) := by rw [he, Pi.single_apply, if_pos rfl]
  have hek : ∀ k, k ≠ i → e k = 0 := fun k hk => by
    rw [he, Pi.single_apply, if_neg hk]
  -- `A *ᵥ eᵢ` is the `i`-th column of `A`.
  have hmulVec : Matrix.mulVec A e = fun k => A k i := by
    ext k
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
    · simp [hei]
    · intro m _ hm; simp [hek m hm]
    · simp [hei]
  -- The quadratic form `eᵢ† A eᵢ = Aᵢᵢ = 0` forces `A eᵢ = 0` (zero column).
  have hform : dotProduct (star e) (Matrix.mulVec A e) = A i i := by
    rw [hmulVec, dotProduct, Finset.sum_eq_single i]
    · simp [hei]
    · intro k _ hk; simp [hek k hk]
    · simp [hei]
  have hcol : Matrix.mulVec A e = 0 :=
    (hA.dotProduct_mulVec_zero_iff e).mp (by rw [hform, hii])
  -- Column `i` is zero: `A j i` is the `j`-th entry of `A *ᵥ eᵢ`.
  have hji : A j i = 0 := by
    have h1 : (fun k => A k i) j = 0 := by rw [← hmulVec, hcol]; simp
    exact h1
  refine ⟨?_, hji⟩
  -- Hermiticity: `A i j = (star A) i j = star (A j i) = star 0 = 0`.
  have hherm : star A = A := hA.isHermitian.eq
  have hij : A i j = star (A j i) := by
    rw [show A i j = star A i j from by rw [hherm], Matrix.star_apply A i j]
  rw [hij, hji, star_zero]

/-- If `X ≤ M` with `M, X` positive semidefinite, the spectral support projector
`Π = M^{-1/2} M M^{-1/2}` of `M` fixes `X`: `Π X = X` and `X Π = X`. Indeed
`X`'s range lies inside the support of `M` (since `X ≤ M`): in the eigenbasis of
`M` (eigenvalues `λ`), `X'` vanishes on rows/cols where `λ = 0` (from
`X' ≤ diag(λ)` plus `X' ≥ 0` and `zero_diag_zero_row_col`), so the support
projector leaves `X'` invariant.
[Wilde2011Qst, qit-notes.tex:29562-29630] -/
private lemma support_proj_fixes_of_le {M X : CMatrix a}
    (hM : M.PosSemidef) (hXM : X ≤ M) (hX : X.PosSemidef) :
    (psdInvSqrt M hM.isHermitian * M * psdInvSqrt M hM.isHermitian) * X = X ∧
      X * (psdInvSqrt M hM.isHermitian * M * psdInvSqrt M hM.isHermitian) = X := by
  set B : CMatrix a := psdInvSqrt M hM.isHermitian
  set Pi : CMatrix a := B * M * B
  -- Eigenbasis of `M`: `U`, `Λ = diag(λ)`, `P = diag(1_{λ>0})`.
  let U : CMatrix a := hM.isHermitian.eigenvectorUnitary
  have hUstarU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hM.isHermitian.eigenvectorUnitary]
  have hUUstar : U * star U = 1 := by
    simp [U]
  set Λ : CMatrix a := Matrix.diagonal (fun i => (hM.isHermitian.eigenvalues i : ℂ)) with hΛ_def
  set P : CMatrix a := Matrix.diagonal (fun i =>
    if 0 < hM.isHermitian.eigenvalues i then (1:ℂ) else 0) with hP_def
  have hMdiag : M = U * Λ * star U := by
    simpa [U, Λ, Function.comp_def, Unitary.conjStarAlgAut_apply]
      using hM.isHermitian.spectral_theorem
  have hPi_spec : Pi = U * P * star U := psdInvSqrt_support_eq hM
  set X' : CMatrix a := star U * X * U with hX'_def
  have hX'psd : X'.PosSemidef := by
    rw [hX'_def, Matrix.IsUnit.posSemidef_star_left_conjugate_iff (Unitary.isUnit_coe :
      IsUnit (U : CMatrix a))]
    exact hX
  have hΛsubX' : (Λ - X').PosSemidef := by
    have hconj : star U * (M - X) * U = Λ - X' := by
      rw [hMdiag]
      calc star U * (U * Λ * star U - X) * U
          = (star U * U) * Λ * (star U * U) - star U * X * U := by noncomm_ring
        _ = 1 * Λ * 1 - star U * X * U := by rw [hUstarU]
        _ = Λ - X' := by rw [← hX'_def]; noncomm_ring
    have hpsd : (star U * (M - X) * U).PosSemidef := by
      rw [Matrix.IsUnit.posSemidef_star_left_conjugate_iff (Unitary.isUnit_coe :
        IsUnit (U : CMatrix a))]
      rw [Matrix.le_iff] at hXM; exact hXM
    rw [← hconj]; exact hpsd
  have hΛii : ∀ i, Λ i i = (hM.isHermitian.eigenvalues i : ℂ) :=
    fun i => by simp [Λ]
  -- `X'` vanishes on row `i` whenever `λ_i = 0`.
  have hX'row_zero : ∀ i, hM.isHermitian.eigenvalues i = 0 → ∀ j, X' i j = 0 := by
    intro i hi j
    have hneg : 0 ≤ (Λ - X') i i := Matrix.PosSemidef.diag_nonneg hΛsubX' (i := i)
    have hpos : 0 ≤ X' i i := Matrix.PosSemidef.diag_nonneg hX'psd (i := i)
    have hX'le0 : X' i i ≤ 0 := by
      have hsub : (Λ - X') i i = Λ i i - X' i i := rfl
      rw [hsub, hΛii, hi, Complex.ofReal_zero] at hneg
      simpa using hneg
    have hX'ii : X' i i = 0 := le_antisymm hX'le0 hpos
    exact (PosSemidef.zero_diag_zero_row_col hX'psd hX'ii j).1
  -- `(1 - P) * X' = 0` (P masks out the zero-eigenvalue rows).
  have hmask : (1 - P) * X' = 0 := by
    ext i j
    -- `(1 - P) * X'` entry `(i,j)`: only the `k = i` term survives (P diagonal).
    rw [Matrix.mul_apply]
    have hentry (k) : (1 - P) i k =
        if i = k then (if 0 < hM.isHermitian.eigenvalues i then (0:ℂ) else 1) else 0 := by
      show ((1 : CMatrix a) i k - (P : CMatrix a) i k) = _
      rw [Matrix.one_apply]
      show ((if i = k then (1:ℂ) else 0) - (Matrix.diagonal _ : CMatrix a) i k) = _
      rw [Matrix.diagonal_apply]
      by_cases hik : i = k
      · -- `i = k`: all three `if i = k` reduce to their `then`-branch.
        rw [if_pos hik, if_pos hik, if_pos hik]
        split_ifs <;> ring
      · -- `i ≠ k`: all three `if i = k` reduce to `0`.
        rw [if_neg hik, if_neg hik, if_neg hik]; ring
    rw [Finset.sum_eq_single i]
    · rw [hentry i, if_pos rfl]
      simp only [Matrix.zero_apply]
      by_cases hpos : 0 < hM.isHermitian.eigenvalues i
      · rw [if_pos hpos]; ring
      · have hpos0 : hM.isHermitian.eigenvalues i = 0 := by
          have nn : 0 ≤ hM.isHermitian.eigenvalues i := hM.eigenvalues_nonneg i
          exact le_antisymm (not_lt.mp hpos) nn
        rw [if_neg hpos, one_mul]
        exact hX'row_zero i hpos0 j
    · intro k _ hk; rw [hentry k, if_neg (ne_comm.mp hk), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- Therefore `(1 - Pi) * X = 0`, hence `Pi * X = X`.
  have hXspec : X = U * X' * star U := by
    rw [hX'_def]
    have h1 : U * star U = (1 : CMatrix a) := hUUstar
    have h2 : (U * star U) * X * (U * star U) = X := by rw [h1]; noncomm_ring
    calc X = (U * star U) * X * (U * star U) := h2.symm
      _ = U * (star U * X * U) * star U := by noncomm_ring
  have h1PiX : (1 - Pi) * X = 0 := by
    rw [hPi_spec, hXspec]
    -- `1 - U·P·U† = U·(1-P)·U†` since `U·U† = 1`.
    have h1 : (1 - (U * P * star U)) = U * (1 - P) * star U := by
      have : U * (1 - P) * star U = U * 1 * star U - U * P * star U := by noncomm_ring
      rw [this, mul_one, hUUstar]
    rw [h1]
    have h2 : U * (1 - P) * star U * (U * X' * star U) = U * ((1 - P) * X') * star U := by
      calc U * (1 - P) * star U * (U * X' * star U)
          = U * ((1 - P) * (star U * U) * X') * star U := by noncomm_ring
        _ = U * ((1 - P) * 1 * X') * star U := by rw [hUstarU]
        _ = U * ((1 - P) * X') * star U := by noncomm_ring
    rw [h2, hmask]; simp
  have hPiX : Pi * X = X := by
    have h1PiX' : (1 - Pi) * X = 0 := h1PiX
    have key : Pi * X + (1 - Pi) * X = X := by
      have : Pi * X + (1 - Pi) * X = 1 * X := by noncomm_ring
      simpa using this
    calc Pi * X = Pi * X + 0 := by rw [add_zero]
      _ = Pi * X + ((1 - Pi) * X) := by rw [h1PiX]
      _ = X := key
  -- `X * Pi = X` by Hermitian adjoint (`Pi`, `X` Hermitian).
  have hXPi : X * Pi = X := by
    have hstar : star (Pi * X) = star X := by rw [hPiX]
    rw [star_mul] at hstar
    rw [show star Pi = Pi from (psdInvSqrt_support_isHermitian hM).eq,
        show star X = X from hX.isHermitian.eq] at hstar
    exact hstar
  exact ⟨hPiX, hXPi⟩

/-- The Hayashi--Nagaoka operator inequality at `c = 1`: for positive
semidefinite `S, T` with `S ≤ I`,
`I − (S+T)^{−1/2} S (S+T)^{−1/2} ≤ 2(I − S) + 4T`,
stated in Loewner form `(2•(I−S) + 4•T − (I − (S+T)^{−1/2} S (S+T)^{−1/2})).PosSemidef`.
The inverse square root is `psdInvSqrt (S+T) (hS.add hT).isHermitian`.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
theorem hayashi_nagaoka_one (S T : CMatrix a) (hS : S.PosSemidef) (hT : T.PosSemidef)
    (hSI : (1 - S).PosSemidef) :
    ((2 : ℝ) • (1 - S) + (4 : ℝ) • T -
      (1 - psdInvSqrt (S + T) (hS.add hT).isHermitian * S *
          psdInvSqrt (S + T) (hS.add hT).isHermitian)).PosSemidef := by
  -- Notation. `R := psdSqrt (S+T)`, `B := psdInvSqrt (S+T)`, `Π := B (S+T) B`
  -- (support projector of `S+T`). All Hermitian; `B` and `R` commute and their
  -- product is `Π`. We follow the c = 1 chain of [Wilde2011Qst, qit-notes.tex:29562-29630].
  set ST : CMatrix a := S + T
  set B : CMatrix a := psdInvSqrt ST (hS.add hT).isHermitian
  set R : CMatrix a := psdSqrt ST
  set Pi : CMatrix a := B * ST * B
  have hST : ST = S + T := rfl
  have hST_psd : ST.PosSemidef := hS.add hT
  have hST_herm : ST.IsHermitian := hST_psd.isHermitian
  have hB_herm : B.IsHermitian := psdInvSqrt_isHermitian ST hST_herm
  have hBstar : star B = B := hB_herm.eq
  have hR_herm : R.IsHermitian := psdSqrt_isHermitian ST
  have hRstar : star R = R := hR_herm.eq
  have hRR : R * R = ST := psdSqrt_mul_self_of_posSemidef hST_psd
  have hBR : B * R = Pi := by
    -- `B * R` and `B * ST * B` both reduce, in the eigenbasis of `ST`, to the
    -- same diagonal support mask (`λ^{-1/2}·λ^{1/2} = 1` vs `λ^{-1/2}·λ·λ^{-1/2}
    -- = 1` on positive eigenvalues, `0` on zero eigenvalues).
    rw [psdInvSqrt_mul_psdSqrt_eq_support hST_psd]
    exact (psdInvSqrt_support_eq hST_psd).symm
  have hRB : R * B = Pi := by
    rw [← hBR, psdInvSqrt_mul_psdSqrt hST_psd]
  -- Π facts: Hermitian, idempotent, `Π ≤ 1`.
  have hPi_herm : Pi.IsHermitian := psdInvSqrt_support_isHermitian hST_psd
  have hPi_star : star Pi = Pi := hPi_herm.eq
  have hPi_idem : Pi * Pi = Pi := psdInvSqrt_support_idempotent hST_psd
  have hPi_le_one : Pi ≤ 1 := psdInvSqrt_support_le_one hST_psd
  -- S, T live inside the support of S+T: `Π S Π = S`, `Π T Π = T`, `Π S = S Π`.
  -- (Their ranges lie in the support of `S+T` because `S,T ≤ S+T`.)
  have hST_le : S ≤ ST := by
    rw [Matrix.le_iff, hST]
    have key : S + T - S = T := by noncomm_ring
    rw [key]; exact hT
  have hTT_le : T ≤ ST := by
    rw [Matrix.le_iff, hST]
    have key : S + T - T = S := by noncomm_ring
    rw [key]; exact hS
  -- `Π S Π = S`, `Π T Π = T`: `S, T ≤ S+T`, so their ranges lie in `supp(S+T)`,
  -- which the support projector `Π` fixes (`support_proj_fixes_of_le`).
  have hPi_S_Pi : Pi * S * Pi = S := by
    have hPiS : Pi * S = S := (support_proj_fixes_of_le hST_psd hST_le hS).1
    have hSPi : S * Pi = S := (support_proj_fixes_of_le hST_psd hST_le hS).2
    rw [hPiS]; exact hSPi
  have hPi_T_Pi : Pi * T * Pi = T := by
    have hPiT : Pi * T = T := (support_proj_fixes_of_le hST_psd hTT_le hT).1
    have hTPi : T * Pi = T := (support_proj_fixes_of_le hST_psd hTT_le hT).2
    rw [hPiT]; exact hTPi
  -- The c = 1 √-form bound `T ≤ R (4•T + 2•(I − S)) R` (tex eq. 29622).
  -- Derived from `psd_core_conjugation_bound` with `R = psdSqrt (S+T)` plus the
  -- operator-monotone steps `S ≤ √S ≤ √(S+T)`.
  have hSqrtForm : T ≤ R * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * R := by
    -- Step 1: core bound `T ≤ 2•(R T R) + 2•((1-R) T (1-R))` (R Hermitian).
    have hCore0 : Matrix.PosSemidef
        ((2 : ℝ) • (star R * T * R) + (2 : ℝ) • (star (1 - R) * T * (1 - R)) - T) :=
      psd_core_conjugation_bound T R hT
    have hRstar' : star R = R := hRstar
    have h1Rstar : star (1 - R) = 1 - R := by rw [star_sub, star_one, hRstar]
    rw [hRstar', h1Rstar] at hCore0
    -- Step 5 (operator-monotone): `S ≤ R = √(S+T)` via `S ≤ √S ≤ √(S+T)`.
    have hS_le_R : S ≤ R :=
      le_trans (posSemidef_le_psdSqrt_of_le_one hS (by simpa [Matrix.le_iff] using hSI))
        (psdSqrt_le_psdSqrt_of_le hST_le)
    -- Step 2: `T ≤ ST`, so `(1-R)(ST - T)(1-R) ≥ 0`; this lets us replace the
    -- `(1-R) T (1-R)` term in `hCore0` by the larger `(1-R) ST (1-R)`:
    --   `2•((1-R) T (1-R)) ≤ 2•((1-R) ST (1-R))`.
    have hSTsubT : Matrix.PosSemidef (ST - T) := by
      rw [Matrix.le_iff] at hTT_le; exact hTT_le
    have hconj : Matrix.PosSemidef ((1 - R) * (ST - T) * (1 - R)) := by
      have h1R : (star (1 - R) : CMatrix a) = 1 - R := by
        rw [star_sub, star_one, hRstar]
      have key : ((1 - R) * (ST - T) * (1 - R) : CMatrix a) =
          star (1 - R) * (ST - T) * (1 - R) := by rw [h1R]
      rw [key]
      exact Matrix.PosSemidef.conjTranspose_mul_mul_same hSTsubT (1 - R)
    have h2conj := Matrix.PosSemidef.smul hconj (by norm_num : (0 : ℝ) ≤ 2)
    -- `hCore0 + h2conj` (both PSD) gives the slack to rewrite the `(1-R)T(1-R)` term:
    --   `2•(RTR) + 2•((1-R)T(1-R)) - T + 2•((1-R)(ST-T)(1-R))`
    --   `= 2•(RTR) - T + 2•((1-R)ST(1-R))`  (PSD).
    have hmid : Matrix.PosSemidef
        ((2 : ℝ) • (R * T * R) - T + (2 : ℝ) • ((1 - R) * ST * (1 - R))) := by
      have hdist : (1 - R) * (ST - T) * (1 - R) =
          (1 - R) * ST * (1 - R) - (1 - R) * T * (1 - R) := by
        rw [mul_sub, sub_mul, sub_mul]; noncomm_ring
      have hkey : (2 : ℝ) • (R * T * R) + (2 : ℝ) • ((1 - R) * T * (1 - R)) - T +
          (2 : ℝ) • ((1 - R) * (ST - T) * (1 - R)) =
          (2 : ℝ) • (R * T * R) - T + (2 : ℝ) • ((1 - R) * ST * (1 - R)) := by
        rw [hdist, smul_sub]; noncomm_ring
      rw [← hkey]; exact hCore0.add h2conj
    -- `(1-R) ST (1-R) = (1-R) R² (1-R) = R (1-R)² R` (R commutes with R and (1-R)).
    -- So `hmid` = `2•(RTR) - T + 2•(R (1-R)² R) = R (2T + 2(1-R)²) R - T` (PSD).
    have hRsq : (1 - R) * ST * (1 - R) = R * ((1 - R) * (1 - R)) * R := by
      rw [← hRR]; noncomm_ring
    rw [hRsq] at hmid
    -- Step 4: `2T + 2(1-R)² = 4T + 2(1+S-2R)` since `(1-R)² = 1-2R+R² = 1-2R+S+T`.
    -- Step 5: `1+S-2R ≤ 1-S` (S ≤ R), so `4T + 2(1+S-2R) ≤ 4T + 2(1-S)`; conjugate
    -- by R (PSD). Assemble: `R (4T + 2(1-S)) R - T` =
    --   `[R (2T + 2(1-R)²) R - T] + 2 R ((1-S) - (1+S-2R)) R`
    --   `= hmid + 2 R (2(R - S)) R = hmid + 4 R (R - S) R`.
    have hRS_psd : Matrix.PosSemidef (R - S) := by
      rw [Matrix.le_iff] at hS_le_R; exact hS_le_R
    have hRRS : Matrix.PosSemidef (R * (R - S) * R) := by
      have key : (R * (R - S) * R : CMatrix a) = star R * (R - S) * R := by rw [hRstar]
      rw [key]
      exact Matrix.PosSemidef.conjTranspose_mul_mul_same hRS_psd R
    rw [Matrix.le_iff]
    -- The goal matrix equals `hmid`'s matrix plus `4•(R(R-S)R)`. We verify the
    -- identity in small `noncomm_ring` steps (the full expression is too large
    -- for a single call): first reduce `LHS − RHS` to `2•R·[T + S − ST]·R`
    -- using distributivity, then to `0` using `ST = S + T`.
    have hexpand1 : R * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * R - T -
        (((2 : ℝ) • (R * T * R) - T + (2 : ℝ) • (R * ((1 - R) * (1 - R)) * R)) +
          (4 : ℝ) • (R * (R - S) * R)) =
        (2 : ℝ) • (R * (T + S - R * R) * R) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, mul_sub,
        sub_mul, mul_add, add_mul, mul_one, one_mul]
      module
    have hexpand2 : (2 : ℝ) • (R * (T + S - R * R) * R) = 0 := by
      rw [hRR, hST]; noncomm_ring; exact smul_zero _
    have hfinal : R * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * R - T =
        ((2 : ℝ) • (R * T * R) - T + (2 : ℝ) • (R * ((1 - R) * (1 - R)) * R)) +
        (4 : ℝ) • (R * (R - S) * R) := by
      have h1 := hexpand1
      rw [hexpand2] at h1
      exact eq_of_sub_eq_zero h1
    rw [hfinal]
    exact hmid.add (Matrix.PosSemidef.smul hRRS (by norm_num : (0 : ℝ) ≤ 4))
  -- Conjugate the √-form bound by `B` (order-preserving) and use `B R = Π`:
  -- `B T B ≤ Π (4•T + 2•(I−S)) Π = 4 T + 2(Π − S)`.
  have hBTB : B * T * B ≤ (4 : ℝ) • T + (2 : ℝ) • (Pi - S) := by
    -- Conjugate `hSqrtForm : T ≤ R (4•T + 2•(1-S)) R` by `B` (order-preserving).
    rw [Matrix.le_iff] at hSqrtForm
    -- `B T B ≤ B (R (4•T+2•(1-S)) R) B = (B R)(4•T+2•(1-S))(R B) = Pi M Pi`.
    have hconj : Matrix.PosSemidef (B * (R * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * R - T) * B) := by
      have hB : (star B : CMatrix a) = B := hBstar
      have key : (B * (R * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * R - T) * B : CMatrix a) =
          star B * (R * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * R - T) * B := by rw [hB]
      rw [key]
      exact Matrix.PosSemidef.conjTranspose_mul_mul_same hSqrtForm B
    -- `B R = Pi` and `R B = Pi`; `Pi M Pi = 4•(Pi T Pi) + 2•(Pi (1-S) Pi)`
    -- `= 4•T + 2•(Pi - Pi S Pi) = 4•T + 2•(Pi - S)`.
    have hkey : B * (R * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * R - T) * B =
        ((4 : ℝ) • T + (2 : ℝ) • (Pi - S)) - B * T * B := by
      have hL : B * (R * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * R) * B =
          Pi * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * Pi := by
        have h1 : B * (R * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * R) * B =
            B * R * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * R * B := by noncomm_ring
        rw [h1, hBR]
        rw [show Pi * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * R * B =
            Pi * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * (R * B) from by noncomm_ring]
        rw [hRB]
      simp only [mul_sub, sub_mul]
      rw [hL]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, mul_add,
        add_mul, mul_sub, sub_mul, mul_assoc, mul_one, hPi_T_Pi,
        hPi_S_Pi, hPi_idem]
    rw [Matrix.le_iff]
    rw [show ((4 : ℝ) • T + (2 : ℝ) • (Pi - S)) - B * T * B =
        B * (R * ((4 : ℝ) • T + (2 : ℝ) • (1 - S)) * R - T) * B from hkey.symm]
    exact hconj
  -- Decompose the goal: `1 − B S B = (1 − Π) + B T B`.
  have hDecomp : 1 - B * S * B = (1 - Pi) + B * T * B := by
    have h1 : B * S * B = Pi - B * T * B := by
      have : S = ST - T := by rw [hST]; noncomm_ring
      calc B * S * B = B * (ST - T) * B := by rw [this]
        _ = B * ST * B - B * T * B := by noncomm_ring
        _ = Pi - B * T * B := rfl
    rw [h1]; noncomm_ring
  -- Final assembly. After `rw [hDecomp]` the goal is
  -- `(2•(1−S) + 4•T − ((1−Π) + B T B)).PosSemidef`. Use the decomposition
  --   `2•(1−S) + 4•T − (1−Π) − B T B = (4•T + 2•(Π−S) − B T B) + (1 − Π)`,
  -- where the first summand is PSD by `hBTB` and the second by `Π ≤ 1`.
  rw [hDecomp]
  have hsum1 : Matrix.PosSemidef ((4 : ℝ) • T + (2 : ℝ) • (Pi - S) - B * T * B) :=
    Matrix.le_iff.mp hBTB
  have hsum2 : Matrix.PosSemidef (1 - Pi) :=
    Matrix.le_iff.mp hPi_le_one
  have hgoal : (2 : ℝ) • (1 - S) + (4 : ℝ) • T - ((1 - Pi) + B * T * B) =
      ((4 : ℝ) • T + (2 : ℝ) • (Pi - S) - B * T * B) + (1 - Pi) := by
    simp only [smul_sub, sub_add, sub_sub]
    module
  rw [hgoal]
  exact hsum1.add hsum2

end

end QIT
