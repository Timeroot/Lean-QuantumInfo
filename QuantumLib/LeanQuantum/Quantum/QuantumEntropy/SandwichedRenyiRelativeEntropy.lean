/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.YoungInequality
import Quantum.QuantumMechanics.QuantumChannel
import Quantum.TraceInequality.LiebAndoTrace
import Quantum.QuantumEntropy.TensorCFC
import Quantum.QuantumEntropy.HaarUnitary
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

open QuantumState
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy

section Definition

open LiebAndoTrace GeneralizedPerspectiveFunction

universe uDef

variable {ℋ : Type uDef} [Qudit ℋ]

/-- Sandwiched quasi-relative entropy:
    `Q_α(ρ‖σ) = Tr((σ^{(1-α)/(2α)} ρ σ^{(1-α)/(2α)})^α)`. -/
noncomputable def sandwichedQuasi (α : ℝ) (ρ σ : L ℋ) : ℂ :=
  Tr (CFC.rpow (CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))) α)

/-- The variational functional (equivalent QHQ form):
    `F(H) = α Tr(Hρ) - (α-1) Tr((σ^{(α-1)/(2α)} H σ^{(α-1)/(2α)})^{α/(α-1)})`. -/
noncomputable def quasiVar (α : ℝ) (ρ σ H : L ℋ) : ℂ :=
  (α : ℂ) * Tr (H * ρ)
    - ((α - 1 : ℝ) : ℂ) * Tr (CFC.rpow
        (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α)))
        (α / (α - 1)))

/-- Sandwiched Rényi relative entropy for `α ∈ (0,1) ∪ (1,∞)`:
    `D_α(ρ‖σ) = (1/(α-1)) · log(Q_α(ρ‖σ) / Tr ρ)`. -/
noncomputable def sandwichedRenyiDiv (α : ℝ) (ρ σ : L ℋ) : ℝ :=
  (1 / (α - 1)) * Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re)

variable [Nontrivial ℋ]

/-- Strictly positive operators as `QuantumState.L ℋ`, pulled back from the CLM `pdSet`. -/
def pdSetLM : Set (L ℋ) :=
  { A | A.toContinuousLinearMap ∈ pdSet (ℋ := ℋ) }

/-- Lieb trace functional on linear maps, via the continuous-linear model in `LiebAndoTrace`. -/
noncomputable def liebTraceMapLM (s : ℝ) (K A B : L ℋ) : ℝ :=
  liebTraceMap (ℋ := ℋ) s K.toContinuousLinearMap A.toContinuousLinearMap B.toContinuousLinearMap

/-- `toContinuousLinearMap` as a `StarAlgHom`. -/
noncomputable def toCLMStarAlgHom :
    (L ℋ) →⋆ₐ[ℂ] (LownerHeinzTheorem.L ℋ) where
  toFun := LinearMap.toContinuousLinearMap
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  commutes' _ := by ext; rfl
  map_star' := by
    intro f
    change f.adjoint.toContinuousLinearMap = star f.toContinuousLinearMap
    rw [LinearMap.adjoint_toContinuousLinearMap, ContinuousLinearMap.star_eq_adjoint]

/-- Trace of the conjugated power `A ↦ Re Tr((B† · A^p · B)^{1/p})`. -/
noncomputable def traceConjPow (p : ℝ) (B A : L ℋ) : ℝ :=
  (Tr (CFC.rpow (star B * CFC.rpow A p * B) (1 / p))).re

/-- Variational (Legendre-type) functional associated to `traceConjPow`:
    `F(A, X) = liebTraceMapLM(p, B†, A, X) − (1−p) · Re Tr X`.
    For `p < 0`: `p · traceConjPow = inf_X F`; for `p > 0`: `p · traceConjPow = sup_X F`. -/
noncomputable def traceConjPowVar (p : ℝ) (B A X : L ℋ) : ℝ :=
  liebTraceMapLM (ℋ := ℋ) p (star B) A X - (1 - p) * (Tr X).re

end Definition

section VariationalRepresentation

universe u

variable {ℋ : Type u} [Qudit ℋ]

set_option linter.style.longLine false

/-- Conjugation by a self-adjoint operator preserves positivity: A * B * A ≥ 0 when A† = A, B ≥ 0. -/
private lemma conj_isPositive {A : L ℋ} (hA : IsSelfAdjoint A) {B : L ℋ} (hB : B.IsPositive) :
    (A * B * A).IsPositive := by
  have hadj : LinearMap.adjoint A = A := by
    rw [← LinearMap.star_eq_adjoint]; exact hA.star_eq
  have h := hB.conj_adjoint A
  rw [hadj] at h
  exact h

/-- Cyclic trace with unit cancellation:
    Tr((P ρ P)(Q H Q)) = Tr(H ρ) when P Q = 1 and Q P = 1. -/
private lemma trace_mul_comm (f g : L ℋ) : Tr (f * g) = Tr (g * f) :=
  LinearMap.trace_comp_comm' g f

private lemma trace_conj_cancel {P Q ρ H : L ℋ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Tr ((P * ρ * P) * (Q * H * Q)) = Tr (H * ρ) := by
  have h1 : (P * ρ * P) * (Q * H * Q) = P * (ρ * H) * Q := by
    have : P * (ρ * (P * (Q * (H * Q)))) = P * (ρ * (H * Q)) := by
      congr 2; rw [show P * (Q * (H * Q)) = (P * Q) * (H * Q) from by
        simp only [mul_assoc]]; rw [hPQ, one_mul]
    simp only [mul_assoc] at this ⊢; exact this
  rw [h1]
  rw [show P * (ρ * H) * Q = P * (ρ * H) * Q from rfl]
  rw [trace_mul_comm (P * (ρ * H)) Q, ← mul_assoc Q P, hQP, one_mul]
  exact (trace_mul_comm H ρ).symm

/-- rpow self-adjointness for positive operators. -/
private lemma rpow_isSelfAdjoint {σ : L ℋ} (_hσ : σ.IsPositive) (s : ℝ) :
    IsSelfAdjoint (CFC.rpow σ s) :=
  IsSelfAdjoint.of_nonneg CFC.rpow_nonneg

/-- Algebraic rearrangement: from Young's form to variational form.
    If a ≤ b/p + c/q with p, q Hölder conjugates, then p·a - (p-1)·c ≤ b. -/
private lemma young_to_variational {a b c : ℂ} {p q : ℝ}
    (hp : 1 < p) (hpq : p.HolderConjugate q)
    (h : a ≤ b / ↑p + c / ↑q) :
    ↑p * a - ↑(p - 1) * c ≤ b := by
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp_nn : (0 : ℂ) ≤ ↑p := by exact_mod_cast le_of_lt hp_pos
  have hp_ne : (p : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp_pos
  have hq_ne : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpq.right_pos
  rw [sub_le_iff_le_add]
  calc ↑p * a
      ≤ ↑p * (b / ↑p + c / ↑q) := mul_le_mul_of_nonneg_left h hp_nn
    _ = b + ↑p * c / ↑q := by rw [mul_add, mul_div_assoc]; congr 1; field_simp
    _ = b + ↑(p - 1) * c := by
        congr 1; rw [show (p - 1 : ℝ) = p - 1 from rfl]
        rw [show q = p / (p - 1) from hpq.conjugate_eq]; push_cast; field_simp

/-- Upper bound on the variational functional for `α > 1`:
    for all positive `H`, `quasiVar α ρ σ H ≤ sandwichedQuasi α ρ σ`.
    Proof by the Young-inequality argument. -/
theorem quasiVar_le_quasi {α : ℝ} (hα : 1 < α) {ρ σ H : L ℋ}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive) (hH : H.IsPositive)
    (hσ_unit : IsUnit σ) :
    quasiVar α ρ σ H ≤ sandwichedQuasi α ρ σ := by
  -- β' = (1-α)/(2α), P = σ^β', Q = σ^{-β'} = σ^{(α-1)/(2α)}
  set β' : ℝ := (1 - α) / (2 * α) with hβ'_def
  set P := CFC.rpow σ β' with hP_def
  set Q := CFC.rpow σ (-β') with hQ_def
  set X := P * ρ * P with hX_def
  set Y := Q * H * Q with hY_def
  have hσ_nn : (0 : L ℋ) ≤ σ := (LinearMap.nonneg_iff_isPositive σ).mpr hσ
  have hP_sa : IsSelfAdjoint P := rpow_isSelfAdjoint hσ β'
  have hQ_sa : IsSelfAdjoint Q := rpow_isSelfAdjoint hσ (-β')
  have hX_pos : X.IsPositive := conj_isPositive hP_sa hρ
  have hY_pos : Y.IsPositive := conj_isPositive hQ_sa hH
  -- P * Q = 1 and Q * P = 1
  have hPQ : P * Q = 1 := by
    change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
    exact CFC.rpow_mul_rpow_neg β' hσ_unit
  have hQP : Q * P = 1 := by
    change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
    exact CFC.rpow_neg_mul_rpow β' hσ_unit
  -- Hölder conjugates: α and α/(α-1)
  set q := α / (α - 1) with hq_def
  have hpq : α.HolderConjugate q := Real.HolderConjugate.conjExponent hα
  -- Young's inequality: Tr(X ∘ₗ Y) ≤ Tr(X^α)/α + Tr(Y^q)/q
  have hYoung := trace_young_inequality hpq X Y hX_pos hY_pos
  -- Tr(X * Y) = Tr(H * ρ) by cyclic trace + cancellation
  have h_xy : Tr (X * Y) = Tr (H * ρ) := trace_conj_cancel hPQ hQP
  -- Tr(X^α) = sandwichedQuasi α ρ σ (by definition)
  have h_Xα : Tr (CFC.rpow X α) = sandwichedQuasi α ρ σ := rfl
  -- Tr(Y^q) = the QHQ expression (definitional after exponent arithmetic)
  have h_Yq : Tr (CFC.rpow Y q) =
      Tr (CFC.rpow (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α))) q) := by
    have hexp : -β' = (α - 1) / (2 * α) := by rw [hβ'_def]; ring
    rw [hY_def, hQ_def, hexp]
  -- Algebraic rearrangement: from Young to the variational form
  unfold quasiVar
  rw [← h_Yq, ← h_xy]
  exact young_to_variational hα hpq hYoung

/-- Attainment for `α > 1`: the variational supremum equals `sandwichedQuasi`,
    realized at `H_opt = σ^{-β}(σ^{-β} ρ σ^{-β})^{α-1} σ^{-β}` with `β = (α-1)/(2α)`. -/
theorem exists_quasiVar_eq_quasi_gt {α : ℝ} (hα : 1 < α) {ρ σ : L ℋ}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive)
    (hσ_unit : IsUnit σ) :
    ∃ H : L ℋ, H.IsPositive ∧ quasiVar α ρ σ H = sandwichedQuasi α ρ σ := by
  -- Abbreviations
  set β' : ℝ := (1 - α) / (2 * α) with hβ'_def
  set P := CFC.rpow σ β' with hP_def
  set Q := CFC.rpow σ (-β') with hQ_def
  set X := P * ρ * P with hX_def
  -- H_opt makes Y_opt = Q * H_opt * Q = X^{α-1}, hence:
  -- H_opt = P * X^{α-1} * P = P * (PρP)^{α-1} * P
  set H_opt := P * CFC.rpow X (α - 1) * P with hH_opt_def
  refine ⟨H_opt, ?_, ?_⟩
  · -- H_opt is positive: conjugation of positive operator
    exact conj_isPositive (rpow_isSelfAdjoint hσ β')
      ((LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg)
  · -- F(H_opt) = sandwichedQuasi α ρ σ
    have hσ_nn : (0 : L ℋ) ≤ σ := (LinearMap.nonneg_iff_isPositive σ).mpr hσ
    have hX_pos : X.IsPositive := conj_isPositive (rpow_isSelfAdjoint hσ β') hρ
    have hX_nn : (0 : L ℋ) ≤ X := (LinearMap.nonneg_iff_isPositive X).mpr hX_pos
    -- P * Q = 1 and Q * P = 1
    have hPQ : P * Q = 1 := by
      change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
      exact CFC.rpow_mul_rpow_neg β' hσ_unit
    have hQP : Q * P = 1 := by
      change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
      exact CFC.rpow_neg_mul_rpow β' hσ_unit
    -- Q * H_opt * Q = X^{α-1}
    have hY_opt : Q * H_opt * Q = CFC.rpow X (α - 1) := by
      rw [hH_opt_def]
      have : Q * (P * CFC.rpow X (α - 1) * P) * Q =
          (Q * P) * CFC.rpow X (α - 1) * (P * Q) := by simp only [mul_assoc]
      rw [this, hQP, hPQ, one_mul, mul_one]
    -- NNReal exponents for rpow composition (avoids IsUnit requirement)
    have hα_sub_pos : (0 : ℝ) < α - 1 := by linarith
    have hα_pos : (0 : ℝ) < α := by linarith
    -- (X^{α-1})^{α/(α-1)} = X^α
    have hYq_eq : CFC.rpow (CFC.rpow X (α - 1)) (α / (α - 1)) = CFC.rpow X α := by
      simp only [CFC.rpow_eq_pow]
      set s : NNReal := ⟨α - 1, by linarith⟩
      set t : NNReal := ⟨α / (α - 1), le_of_lt (div_pos hα_pos hα_sub_pos)⟩
      set r : NNReal := ⟨α, by linarith⟩
      have hs0 : (0 : NNReal) < s := by exact_mod_cast hα_sub_pos
      have ht0 : (0 : NNReal) < t := by exact_mod_cast div_pos hα_pos hα_sub_pos
      have hr0 : (0 : NNReal) < r := by exact_mod_cast hα_pos
      have hst : s * t = r := by
        ext; change (α - 1) * (α / (α - 1)) = α
        rw [mul_comm]; exact div_mul_cancel₀ α (by linarith : (α - 1 : ℝ) ≠ 0)
      change (X ^ (↑s : ℝ)) ^ (↑t : ℝ) = X ^ (↑r : ℝ)
      rw [← CFC.nnrpow_eq_rpow hs0, ← CFC.nnrpow_eq_rpow ht0,
          ← CFC.nnrpow_eq_rpow hr0, CFC.nnrpow_nnrpow, hst]
    -- X * X^{α-1} = X^α
    have hXX_eq : X * CFC.rpow X (α - 1) = CFC.rpow X α := by
      simp only [CFC.rpow_eq_pow]
      set s : NNReal := ⟨α - 1, by linarith⟩
      set r : NNReal := ⟨α, by linarith⟩
      have hs0 : (0 : NNReal) < s := by exact_mod_cast hα_sub_pos
      have hr0 : (0 : NNReal) < r := by exact_mod_cast hα_pos
      have h1s : (1 : NNReal) + s = r := by ext; change (1 : ℝ) + (α - 1) = α; ring
      change X * X ^ (↑s : ℝ) = X ^ (↑r : ℝ)
      conv_lhs => lhs; rw [show X = X ^ (1 : NNReal) from by
        rw [CFC.nnrpow_eq_rpow one_pos, NNReal.coe_one]; exact (CFC.rpow_one X hX_nn).symm]
      rw [← CFC.nnrpow_eq_rpow hs0, ← CFC.nnrpow_eq_rpow hr0,
          ← CFC.nnrpow_add one_pos hs0, h1s]
    -- Tr(H_opt * ρ) = Tr(X * X^{α-1}) via cyclic trace
    have hTr_Hρ : Tr (H_opt * ρ) = Tr (X * CFC.rpow X (α - 1)) := by
      rw [hH_opt_def]
      have : Tr (P * CFC.rpow X (α - 1) * P * ρ) =
          Tr (P * ρ * P * CFC.rpow X (α - 1)) := by
        calc Tr (P * CFC.rpow X (α - 1) * P * ρ)
            = Tr (ρ * (P * CFC.rpow X (α - 1) * P)) := (trace_mul_comm _ _).symm
          _ = Tr (ρ * P * (CFC.rpow X (α - 1) * P)) := by simp only [mul_assoc]
          _ = Tr ((CFC.rpow X (α - 1) * P) * (ρ * P)) := trace_mul_comm _ _
          _ = Tr (CFC.rpow X (α - 1) * (P * (ρ * P))) := by simp only [mul_assoc]
          _ = Tr (P * (ρ * P) * CFC.rpow X (α - 1)) := (trace_mul_comm _ _).symm
          _ = Tr (P * ρ * P * CFC.rpow X (α - 1)) := by simp only [mul_assoc]
      rw [this, hX_def]
    -- Connect exponents
    have hexp : (α - 1 : ℝ) / (2 * α) = -β' := by rw [hβ'_def]; ring
    -- Unfold and compute
    unfold quasiVar sandwichedQuasi
    rw [hexp, hY_opt, hYq_eq, hTr_Hρ, hXX_eq]
    set T := Tr (CFC.rpow X α)
    push_cast; ring

/-- Algebraic rearrangement: from reverse Young's form to variational form.
    If b/r + c/s ≤ a with 0 < s < 1 and 1/r + 1/s = 1, then c ≤ s·a - (s-1)·b. -/
private lemma reverse_young_to_variational {a b c : ℂ} {r s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hrs : 1 / r + 1 / s = 1)
    (h : b / ↑r + c / ↑s ≤ a) :
    c ≤ ↑s * a - ↑(s - 1) * b := by
  have hs_nn : (0 : ℂ) ≤ ↑s := by exact_mod_cast le_of_lt hs0
  have hs_ne : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs0
  have hr_ne : (r : ℂ) ≠ 0 := by
    suffices r ≠ 0 by exact_mod_cast this
    intro hr0; simp [hr0] at hrs; linarith [one_div_pos.mpr hs0]
  rw [le_sub_iff_add_le, add_comm]
  have key : ↑(s - 1) * b + c = ↑s * (b / ↑r + c / ↑s) := by
    have h_sr : (s - 1 : ℝ) = s / r := by
      have h1 : 1 / r = 1 - 1 / s := by linarith
      field_simp at h1 ⊢; linarith
    have h_cast : (↑(s - 1) : ℂ) = ↑s / ↑r := by
      rw [h_sr]; push_cast; ring
    rw [h_cast]; field_simp
  rw [key]
  exact mul_le_mul_of_nonneg_left h hs_nn

/-- Lower bound on the variational functional for `0 < α < 1`:
    for all invertible positive `H`, `sandwichedQuasi α ρ σ ≤ quasiVar α ρ σ H`.
    Proof by the reverse Young inequality. -/
theorem quasi_le_quasiVar {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ σ H : L ℋ}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive) (hH : H.IsPositive)
    (hσ_unit : IsUnit σ) (hH_unit : IsUnit H) :
    sandwichedQuasi α ρ σ ≤ quasiVar α ρ σ H := by
  set β' : ℝ := (1 - α) / (2 * α) with hβ'_def
  set P := CFC.rpow σ β' with hP_def
  set Q := CFC.rpow σ (-β') with hQ_def
  set X := P * ρ * P with hX_def
  set Y := Q * H * Q with hY_def
  have hσ_nn : (0 : L ℋ) ≤ σ := (LinearMap.nonneg_iff_isPositive σ).mpr hσ
  have hP_sa : IsSelfAdjoint P := rpow_isSelfAdjoint hσ β'
  have hQ_sa : IsSelfAdjoint Q := rpow_isSelfAdjoint hσ (-β')
  have hX_pos : X.IsPositive := conj_isPositive hP_sa hρ
  have hY_pos : Y.IsPositive := conj_isPositive hQ_sa hH
  have hPQ : P * Q = 1 := by
    change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
    exact CFC.rpow_mul_rpow_neg β' hσ_unit
  have hQP : Q * P = 1 := by
    change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
    exact CFC.rpow_neg_mul_rpow β' hσ_unit
  have hQ_unit : IsUnit Q := hσ_unit.cfcRpow (-β') hσ_nn
  have hY_unit : IsUnit Y := (hQ_unit.mul hH_unit).mul hQ_unit
  set r := α / (α - 1) with hr_def
  have hr_neg : r < 0 := by rw [hr_def]; exact div_neg_of_pos_of_neg hα0 (by linarith)
  have hrs : 1 / r + 1 / α = 1 := by
    rw [hr_def]; field_simp; ring
  have hRevYoung := _root_.trace_reverse_young_inequality hr_neg hα0 hα1 hrs Y X
    hY_pos hY_unit hX_pos
  have h_yx : Tr (Y * X) = Tr (H * ρ) := by
    rw [trace_mul_comm Y X]; exact trace_conj_cancel hPQ hQP
  have h_Yr : Tr (CFC.rpow Y r) =
      Tr (CFC.rpow (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α))) r) := by
    have hexp : -β' = (α - 1) / (2 * α) := by rw [hβ'_def]; ring
    rw [hY_def, hQ_def, hexp]
  unfold quasiVar
  rw [← h_Yr, ← h_yx]
  exact reverse_young_to_variational hα0 hα1 hrs hRevYoung

/-- Attainment for `0 < α < 1`: the variational infimum equals `sandwichedQuasi`,
    realized at `H_opt = σ^{β'}(σ^{β'} ρ σ^{β'})^{α-1} σ^{β'}` with `β' = (1−α)/(2α)`. -/
theorem exists_quasiVar_eq_quasi_lt {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ σ : L ℋ}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive)
    (hσ_unit : IsUnit σ) (hρ_unit : IsUnit ρ) :
    ∃ H : L ℋ, H.IsPositive ∧ quasiVar α ρ σ H = sandwichedQuasi α ρ σ := by
  set β' : ℝ := (1 - α) / (2 * α) with hβ'_def
  set P := CFC.rpow σ β' with hP_def
  set Q := CFC.rpow σ (-β') with hQ_def
  set X := P * ρ * P with hX_def
  set H_opt := P * CFC.rpow X (α - 1) * P with hH_opt_def
  refine ⟨H_opt, ?_, ?_⟩
  · exact conj_isPositive (rpow_isSelfAdjoint hσ β')
      ((LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg)
  · have hσ_nn : (0 : L ℋ) ≤ σ := (LinearMap.nonneg_iff_isPositive σ).mpr hσ
    have hX_pos : X.IsPositive := conj_isPositive (rpow_isSelfAdjoint hσ β') hρ
    have hX_nn : (0 : L ℋ) ≤ X := (LinearMap.nonneg_iff_isPositive X).mpr hX_pos
    have hP_unit : IsUnit P := hσ_unit.cfcRpow β' hσ_nn
    have hρ_nn : (0 : L ℋ) ≤ ρ := (LinearMap.nonneg_iff_isPositive ρ).mpr hρ
    have hX_unit : IsUnit X := (hP_unit.mul hρ_unit).mul hP_unit
    have hPQ : P * Q = 1 := by
      change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
      exact CFC.rpow_mul_rpow_neg β' hσ_unit
    have hQP : Q * P = 1 := by
      change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
      exact CFC.rpow_neg_mul_rpow β' hσ_unit
    have hY_opt : Q * H_opt * Q = CFC.rpow X (α - 1) := by
      rw [hH_opt_def]
      have : Q * (P * CFC.rpow X (α - 1) * P) * Q =
          (Q * P) * CFC.rpow X (α - 1) * (P * Q) := by simp only [mul_assoc]
      rw [this, hQP, hPQ, one_mul, mul_one]
    have hα_sub_neg : (α - 1 : ℝ) < 0 := by linarith
    have hα_sub_ne : (α - 1 : ℝ) ≠ 0 := ne_of_lt hα_sub_neg
    have hα_pos : (0 : ℝ) < α := hα0
    have hYq_eq : CFC.rpow (CFC.rpow X (α - 1)) (α / (α - 1)) = CFC.rpow X α := by
      simp only [CFC.rpow_eq_pow]
      rw [CFC.rpow_rpow X (α - 1) (α / (α - 1)) hX_unit hα_sub_ne]
      congr 1
      rw [mul_comm]; exact div_mul_cancel₀ α hα_sub_ne
    have hXX_eq : X * CFC.rpow X (α - 1) = CFC.rpow X α := by
      simp only [CFC.rpow_eq_pow]
      conv_lhs => lhs; rw [show X = X ^ (1 : ℝ) from (CFC.rpow_one X hX_nn).symm]
      rw [← CFC.rpow_add hX_unit]
      congr 1; ring
    have hTr_Hρ : Tr (H_opt * ρ) = Tr (X * CFC.rpow X (α - 1)) := by
      rw [hH_opt_def]
      have : Tr (P * CFC.rpow X (α - 1) * P * ρ) =
          Tr (P * ρ * P * CFC.rpow X (α - 1)) := by
        calc Tr (P * CFC.rpow X (α - 1) * P * ρ)
            = Tr (ρ * (P * CFC.rpow X (α - 1) * P)) := (trace_mul_comm _ _).symm
          _ = Tr (ρ * P * (CFC.rpow X (α - 1) * P)) := by simp only [mul_assoc]
          _ = Tr ((CFC.rpow X (α - 1) * P) * (ρ * P)) := trace_mul_comm _ _
          _ = Tr (CFC.rpow X (α - 1) * (P * (ρ * P))) := by simp only [mul_assoc]
          _ = Tr (P * (ρ * P) * CFC.rpow X (α - 1)) := (trace_mul_comm _ _).symm
          _ = Tr (P * ρ * P * CFC.rpow X (α - 1)) := by simp only [mul_assoc]
      rw [this, hX_def]
    have hexp : (α - 1 : ℝ) / (2 * α) = -β' := by rw [hβ'_def]; ring
    unfold quasiVar sandwichedQuasi
    rw [hexp, hY_opt, hYq_eq, hTr_Hρ, hXX_eq]
    set T := Tr (CFC.rpow X α)
    push_cast; ring

end VariationalRepresentation

section LiebAndoLinearMap

open LiebAndoTrace GeneralizedPerspectiveFunction

universe u'

variable {ℋ : Type u'} [Qudit ℋ]
variable [Nontrivial ℋ]

omit [Nontrivial ℋ] in
private lemma toContinuousLinearMap_convex_combo (A₁ A₂ : L ℋ) (θ : ℝ) :
    ((1 - θ) • A₁ + θ • A₂).toContinuousLinearMap =
      (1 - θ) • A₁.toContinuousLinearMap + θ • A₂.toContinuousLinearMap := by
  ext x; rfl

/-- Joint concavity of `liebTraceMapLM` on `pdSetLM`, from `liebTrace_jointlyConcaveOn_pdSet`. -/
theorem liebTrace_jointlyConcaveOn_pdSet_lm {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (K : L ℋ) :
    JointlyConcaveOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ)) (liebTraceMapLM (ℋ := ℋ) s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  dsimp [pdSetLM, liebTraceMapLM] at hA₁ hA₂ hB₁ hB₂ ⊢
  have h :=
    liebTrace_jointlyConcaveOn_pdSet (ℋ := ℋ) hs0 hs1 K.toContinuousLinearMap
      (A₁ := A₁.toContinuousLinearMap) (A₂ := A₂.toContinuousLinearMap)
      (B₁ := B₁.toContinuousLinearMap) (B₂ := B₂.toContinuousLinearMap) (θ := θ)
      hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  simpa [liebTraceMapLM, toContinuousLinearMap_convex_combo, smul_eq_mul, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using h

/-- Joint convexity of `liebTraceMapLM` on `pdSetLM`, from `liebTrace_jointlyConvexOn_pdSet`. -/
theorem liebTrace_jointlyConvexOn_pdSet_lm {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (K : L ℋ) :
    JointlyConvexOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ)) (liebTraceMapLM (ℋ := ℋ) s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  dsimp [pdSetLM, liebTraceMapLM] at hA₁ hA₂ hB₁ hB₂ ⊢
  have h :=
    liebTrace_jointlyConvexOn_pdSet (ℋ := ℋ) hs1 hs2 K.toContinuousLinearMap
      (A₁ := A₁.toContinuousLinearMap) (A₂ := A₂.toContinuousLinearMap)
      (B₁ := B₁.toContinuousLinearMap) (B₂ := B₂.toContinuousLinearMap) (θ := θ)
      hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  simpa [liebTraceMapLM, toContinuousLinearMap_convex_combo, smul_eq_mul, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using h

/-- Convex combinations stay in `pdSetLM` (from the CLM `pdSet_convexCombo`). -/
theorem pdSetLM_convexCombo {A₁ A₂ : L ℋ} (hA₁ : A₁ ∈ pdSetLM (ℋ := ℋ))
    (hA₂ : A₂ ∈ pdSetLM (ℋ := ℋ)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) • A₁ + θ • A₂ ∈ pdSetLM (ℋ := ℋ) := by
  dsimp [pdSetLM] at hA₁ hA₂ ⊢
  rw [toContinuousLinearMap_convex_combo]
  exact pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1

end LiebAndoLinearMap

section TraceConjPowConcavity

open LiebAndoTrace GeneralizedPerspectiveFunction

universe u''

variable {ℋ : Type u''} [Qudit ℋ] [Nontrivial ℋ]

set_option linter.style.longLine false

/-- `pdSetLM` is convex. -/
private lemma pdSetLM_convex : Convex ℝ (pdSetLM (ℋ := ℋ)) := by
  intro x hx y hy a b ha hb hab
  rw [show a = 1 - b from by linarith]
  exact pdSetLM_convexCombo hx hy hb (by linarith)

omit [Nontrivial ℋ] in
private lemma star_toCLM (f : L ℋ) :
    (star f).toContinuousLinearMap = star (f.toContinuousLinearMap) := by
  change f.adjoint.toContinuousLinearMap = star f.toContinuousLinearMap
  rw [LinearMap.adjoint_toContinuousLinearMap, ContinuousLinearMap.star_eq_adjoint]

omit [Nontrivial ℋ] in
lemma nonneg_of_pdSetLM {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) : (0 : L ℋ) ≤ A := by
  have h_clm_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap := by
    obtain ⟨hA_sa, hA_spec⟩ := hA
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hA_sa)).2
      (fun r hr => (hA_spec hr).le)
  rw [LinearMap.nonneg_iff_isPositive]
  have h := (ContinuousLinearMap.nonneg_iff_isPositive _).mp h_clm_nn
  exact ⟨fun x y => h.1 x y, fun x => h.2 x⟩

omit [Nontrivial ℋ] in
private lemma isUnit_toCLM_of_isUnit {A : L ℋ} (h : IsUnit A.toContinuousLinearMap) :
    IsUnit A := by
  obtain ⟨u, hu⟩ := h
  let B := (u⁻¹ : (LownerHeinzTheorem.L ℋ)ˣ).val.toLinearMap
  have h1 : A * B = 1 := by
    ext x
    have h := ContinuousLinearMap.ext_iff.mp u.val_inv x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h
    rw [hu] at h
    exact h
  have h2 : B * A = 1 := by
    ext x
    have h := ContinuousLinearMap.ext_iff.mp u.inv_val x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h
    rw [hu] at h
    exact h
  exact ⟨⟨A, B, h1, h2⟩, rfl⟩

omit [Nontrivial ℋ] in
lemma isUnit_of_pdSetLM {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) : IsUnit A := by
  obtain ⟨hA_sa, hA_spec⟩ := hA
  have h0 : (0 : ℝ) ∉ spectrum ℝ A.toContinuousLinearMap := by
    intro h; exact absurd (Set.mem_Ioi.mp (hA_spec h)) (lt_irrefl 0)
  exact isUnit_toCLM_of_isUnit
    ((spectrum.zero_notMem_iff (R := ℝ) (A := LownerHeinzTheorem.L ℋ)).mp h0)

omit [Nontrivial ℋ] in
lemma pdSetLM_conj {A B : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) (hB : IsUnit B) :
    star B * A * B ∈ pdSetLM (ℋ := ℋ) := by
  obtain ⟨hA_sa, hA_spec⟩ := hA
  have hA_nn_clm : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hA_sa)).2
      (fun r hr => (hA_spec hr).le)
  have h_prod_clm : (star B * A * B).toContinuousLinearMap =
      star B.toContinuousLinearMap * A.toContinuousLinearMap * B.toContinuousLinearMap := by
    ext v; rfl
  have hM_nn_clm : (0 : LownerHeinzTheorem.L ℋ) ≤
      star B.toContinuousLinearMap * A.toContinuousLinearMap * B.toContinuousLinearMap :=
    star_left_conjugate_nonneg hA_nn_clm _
  have hB_clm_unit : IsUnit B.toContinuousLinearMap :=
    (toCLMStarAlgHom (ℋ := ℋ)).toRingHom.isUnit_map hB
  have hA_clm_unit : IsUnit A.toContinuousLinearMap :=
    (toCLMStarAlgHom (ℋ := ℋ)).toRingHom.isUnit_map (isUnit_of_pdSetLM ⟨hA_sa, hA_spec⟩)
  have hM_clm_unit : IsUnit (star B.toContinuousLinearMap * A.toContinuousLinearMap *
      B.toContinuousLinearMap) :=
    (hB_clm_unit.star.mul hA_clm_unit).mul hB_clm_unit
  have hM_sa : IsSelfAdjoint (star B.toContinuousLinearMap * A.toContinuousLinearMap *
      B.toContinuousLinearMap) := IsSelfAdjoint.of_nonneg hM_nn_clm
  constructor
  · rw [h_prod_clm]; exact hM_sa
  · rw [h_prod_clm]
    intro r hr
    have h_nn : (0 : ℝ) ≤ r := by
      have h_spec_nn : spectrum ℝ (star B.toContinuousLinearMap *
          A.toContinuousLinearMap * B.toContinuousLinearMap) ⊆ Set.Ici 0 :=
        (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hM_sa)).1 hM_nn_clm
      simpa [Set.Ici] using h_spec_nn hr
    rcases lt_or_eq_of_le h_nn with h | h
    · exact h
    · exfalso
      rw [← h] at hr
      exact (spectrum.zero_notMem_iff (R := ℝ)).mpr hM_clm_unit hr

omit [Nontrivial ℋ] in
lemma pdSetLM_rpow_ne {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) {p : ℝ} :
    CFC.rpow A p ∈ pdSetLM (ℋ := ℋ) := by
  have hA_nn := nonneg_of_pdSetLM hA
  have hA_unit := isUnit_of_pdSetLM hA
  have hAp_nn : (0 : L ℋ) ≤ CFC.rpow A p := CFC.rpow_nonneg
  have hAp_unit : IsUnit (CFC.rpow A p) := hA_unit.cfcRpow p hA_nn
  have hAp_sa : IsSelfAdjoint (CFC.rpow A p) := IsSelfAdjoint.of_nonneg hAp_nn
  have hAp_clm_nn : (0 : LownerHeinzTheorem.L ℋ) ≤
      (CFC.rpow A p).toContinuousLinearMap := by
    change (0 : LownerHeinzTheorem.L ℋ) ≤ (toCLMStarAlgHom (ℋ := ℋ)) (CFC.rpow A p)
    exact map_nonneg (toCLMStarAlgHom (ℋ := ℋ)) hAp_nn
  have hAp_clm_unit : IsUnit (CFC.rpow A p).toContinuousLinearMap := by
    change IsUnit ((toCLMStarAlgHom (ℋ := ℋ)) (CFC.rpow A p))
    exact (toCLMStarAlgHom (ℋ := ℋ)).toRingHom.isUnit_map hAp_unit
  have hAp_clm_sa : IsSelfAdjoint (CFC.rpow A p).toContinuousLinearMap :=
    IsSelfAdjoint.of_nonneg hAp_clm_nn
  refine ⟨hAp_clm_sa, ?_⟩
  intro r hr
  have h_spec_nn : spectrum ℝ (CFC.rpow A p).toContinuousLinearMap ⊆ Set.Ici 0 :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hAp_clm_sa)).1 hAp_clm_nn
  rcases lt_or_eq_of_le (by simpa [Set.Ici] using h_spec_nn hr) with h | h
  · exact h
  · exfalso; rw [← h] at hr
    exact (spectrum.zero_notMem_iff (R := ℝ)).mpr hAp_clm_unit hr

omit [Nontrivial ℋ] in
private lemma pdSetLM_rpow {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) {p : ℝ} :
    CFC.rpow A p ∈ pdSetLM (ℋ := ℋ) :=
  pdSetLM_rpow_ne hA

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
private lemma rpow_toCLM {A : L ℋ} {p : ℝ} (hp : 0 ≤ p)
    (hA : (0 : L ℋ) ≤ A) :
    (CFC.rpow A p).toContinuousLinearMap = CFC.rpow A.toContinuousLinearMap p := by
  have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hφ_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap :=
    map_nonneg (toCLMStarAlgHom (ℋ := ℋ)) hA
  have hφ_sa : IsSelfAdjoint A.toContinuousLinearMap :=
    IsSelfAdjoint.map hA_sa (toCLMStarAlgHom (ℋ := ℋ))
  have hcont : Continuous (toCLMStarAlgHom (ℋ := ℋ)) :=
    (toCLMStarAlgHom (ℋ := ℋ)).toAlgHom.toLinearMap.continuous_of_finiteDimensional
  have hf : ContinuousOn (fun x : ℝ => x ^ p) (spectrum ℝ A) :=
    (Real.continuous_rpow_const hp).continuousOn
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow]
  rw [CFC.rpow_eq_cfc_real (a := A) (ha := hA)]
  rw [CFC.rpow_eq_cfc_real (a := A.toContinuousLinearMap) (ha := hφ_nn)]
  exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ)
    (toCLMStarAlgHom (ℋ := ℋ)) (fun x : ℝ => x ^ p) A
    (hf := hf) (hφ := hcont) (ha := hA_sa) (hφa := hφ_sa)

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
private lemma rpow_toCLM_pd {A : L ℋ} {p : ℝ}
    (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    (CFC.rpow A p).toContinuousLinearMap = CFC.rpow A.toContinuousLinearMap p := by
  have hA_nn := nonneg_of_pdSetLM hA
  by_cases hp : 0 ≤ p
  · exact rpow_toCLM hp hA_nn
  · push_neg at hp
    obtain ⟨hA_sa_clm, hA_spec⟩ := hA
    have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA_nn
    have hφ_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap :=
      map_nonneg (toCLMStarAlgHom (ℋ := ℋ)) hA_nn
    have hφ_sa : IsSelfAdjoint A.toContinuousLinearMap :=
      IsSelfAdjoint.map hA_sa (toCLMStarAlgHom (ℋ := ℋ))
    have hcont : Continuous (toCLMStarAlgHom (ℋ := ℋ)) :=
      (toCLMStarAlgHom (ℋ := ℋ)).toAlgHom.toLinearMap.continuous_of_finiteDimensional
    have hA_unit := isUnit_of_pdSetLM ⟨hA_sa_clm, hA_spec⟩
    have h_spec_lm_nn : spectrum ℝ A ⊆ Set.Ici 0 :=
      (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hA_sa)).1 hA_nn
    have h0_not_mem : (0 : ℝ) ∉ spectrum ℝ A :=
      (spectrum.zero_notMem_iff (R := ℝ) (A := L ℋ)).mpr hA_unit
    have hf : ContinuousOn (fun x : ℝ => x ^ p) (spectrum ℝ A) :=
      ContinuousOn.rpow_const continuousOn_id fun x hx =>
        Or.inl (ne_of_gt (lt_of_le_of_ne
          (by simpa [Set.Ici] using h_spec_lm_nn hx)
          (fun h => h0_not_mem (h ▸ hx))))
    rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow]
    rw [CFC.rpow_eq_cfc_real (a := A) (ha := hA_nn)]
    rw [CFC.rpow_eq_cfc_real (a := A.toContinuousLinearMap) (ha := hφ_nn)]
    exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ)
      (toCLMStarAlgHom (ℋ := ℋ)) (fun x : ℝ => x ^ p) A
      (hf := hf) (hφ := hcont) (ha := hA_sa) (hφa := hφ_sa)

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
private lemma liebTraceMapLM_as_lm_trace_pd {p : ℝ}
    (B A X : L ℋ)
    (hA : A ∈ pdSetLM (ℋ := ℋ)) (hX : X ∈ pdSetLM (ℋ := ℋ))
    (h1p : 0 ≤ 1 - p) :
    liebTraceMapLM (ℋ := ℋ) p (star B) A X =
      (Tr (star B * CFC.rpow A p * B * CFC.rpow X (1 - p))).re := by
  have hX_nn := nonneg_of_pdSetLM hX
  unfold liebTraceMapLM liebTraceMap
  simp only [star_toCLM, star_star]
  have h1 : A.toContinuousLinearMap ^ p = (CFC.rpow A p).toContinuousLinearMap :=
    (rpow_toCLM_pd hA).symm
  have h2 : X.toContinuousLinearMap ^ (1 - p) = (CFC.rpow X (1 - p)).toContinuousLinearMap :=
    (rpow_toCLM h1p hX_nn).symm
  have h3 : star (B.toContinuousLinearMap) = (star B).toContinuousLinearMap :=
    (star_toCLM B).symm
  rw [h1, h2, h3]
  simp only [traceRe]
  have h_prod : ((CFC.rpow A p).toContinuousLinearMap * B.toContinuousLinearMap *
      (CFC.rpow X (1 - p)).toContinuousLinearMap *
      (star B).toContinuousLinearMap).toLinearMap =
    CFC.rpow A p * B * CFC.rpow X (1 - p) * star B := by ext v; rfl
  rw [h_prod]
  congr 1
  rw [trace_mul_comm (CFC.rpow A p * B * CFC.rpow X (1 - p)) (star B)]
  simp only [mul_assoc]

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
private lemma liebTraceMapLM_as_lm_trace {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (B A X : L ℋ) (hA : (0 : L ℋ) ≤ A) (hX : (0 : L ℋ) ≤ X) :
    liebTraceMapLM (ℋ := ℋ) p (star B) A X =
      (Tr (star B * CFC.rpow A p * B * CFC.rpow X (1 - p))).re := by
  unfold liebTraceMapLM liebTraceMap
  simp only [star_toCLM, star_star]
  have h1 : A.toContinuousLinearMap ^ p = (CFC.rpow A p).toContinuousLinearMap :=
    (rpow_toCLM hp0 hA).symm
  have h2 : X.toContinuousLinearMap ^ (1 - p) = (CFC.rpow X (1 - p)).toContinuousLinearMap :=
    (rpow_toCLM (by linarith) hX).symm
  have h3 : star (B.toContinuousLinearMap) = (star B).toContinuousLinearMap :=
    (star_toCLM B).symm
  rw [h1, h2, h3]
  simp only [traceRe]
  have h_prod : ((CFC.rpow A p).toContinuousLinearMap * B.toContinuousLinearMap *
      (CFC.rpow X (1 - p)).toContinuousLinearMap *
      (star B).toContinuousLinearMap).toLinearMap =
    CFC.rpow A p * B * CFC.rpow X (1 - p) * star B := by ext v; rfl
  rw [h_prod]
  congr 1
  rw [trace_mul_comm (CFC.rpow A p * B * CFC.rpow X (1 - p)) (star B)]
  simp only [mul_assoc]

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
/-- Variational inequality (−1 ≤ p < 0):
    ∀ X ∈ pdSetLM, p · traceConjPow(p,B,A) ≤ F(A,X).
    Follows from the reverse trace Young inequality with M = B†A^pB. -/
private lemma traceConjPowVar_le_neg {p : ℝ} (hp0 : p < 0)
    {B A X : L ℋ} (hB : IsUnit B) (hA : A ∈ pdSetLM (ℋ := ℋ)) (hX : X ∈ pdSetLM (ℋ := ℋ)) :
    p * traceConjPow (ℋ := ℋ) p B A ≤ traceConjPowVar (ℋ := ℋ) p B A X := by
  have hA_nn := nonneg_of_pdSetLM hA
  have hX_nn := nonneg_of_pdSetLM hX
  have hpne : (p : ℝ) ≠ 0 := ne_of_lt hp0
  set M := star B * CFC.rpow A p * B with hM_def
  set N := CFC.rpow X (1 - p) with hN_def
  have hApd : CFC.rpow A p ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hA
  have hMpd : M ∈ pdSetLM (ℋ := ℋ) := pdSetLM_conj hApd hB
  have hM_unit : IsUnit M := isUnit_of_pdSetLM hMpd
  have hM_nn : (0 : L ℋ) ≤ M := star_left_conjugate_nonneg CFC.rpow_nonneg _
  have hN_nn : (0 : L ℋ) ≤ N := CFC.rpow_nonneg
  have hM_pos : M.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hM_nn
  have hN_pos : N.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hN_nn
  have h1_sub_p_pos : 0 < 1 - p := by linarith
  have h_bridge := liebTraceMapLM_as_lm_trace_pd B A X hA hX (by linarith)
  set r := 1 / p with hr_def
  set s := 1 / (1 - p) with hs_def
  have hr_neg : r < 0 := by rw [hr_def]; exact div_neg_of_pos_of_neg one_pos hp0
  have hs_pos : 0 < s := by rw [hs_def]; positivity
  have hs_lt_1 : s < 1 := by
    rw [hs_def]; rw [div_lt_one h1_sub_p_pos]; linarith
  have hrs : 1 / r + 1 / s = 1 := by
    rw [hr_def, hs_def]; field_simp; ring
  have hMr : CFC.rpow M r = CFC.rpow (star B * CFC.rpow A p * B) (1 / p) := by
    rw [hM_def]
  have hNs : CFC.rpow N s = X := by
    rw [hN_def, hs_def, CFC.rpow_eq_pow, CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow_of_exponent_nonneg X (1 - p) (1 / (1 - p))
      (by linarith) (by positivity)]
    rw [show (1 - p) * (1 / (1 - p)) = 1 from by field_simp]
    exact CFC.rpow_one X hX_nn
  have hRevYoung := _root_.trace_reverse_young_inequality hr_neg hs_pos hs_lt_1 hrs M N
    hM_pos hM_unit hN_pos
  have hRevYoung_re : (Tr (CFC.rpow M r) / ↑r + Tr (CFC.rpow N s) / ↑s).re ≤
      (Tr (M ∘ₗ N)).re :=
    (RCLike.le_iff_re_im.mp hRevYoung).1
  rw [Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re, hNs] at hRevYoung_re
  have hMN_eq : (Tr (M ∘ₗ N)).re = (Tr (M * N)).re := rfl
  rw [hMN_eq] at hRevYoung_re
  have hr_eq : (Tr (CFC.rpow M r)).re / r = p * (Tr (CFC.rpow M r)).re := by
    rw [hr_def]; field_simp
  have hs_eq : (Tr X).re / s = (1 - p) * (Tr X).re := by
    rw [hs_def]; field_simp
  rw [hr_eq, hs_eq, hMr] at hRevYoung_re
  simp only [traceConjPowVar, traceConjPow, h_bridge]
  linarith

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
/-- Variational attainment (−1 ≤ p < 0):
    ∃ X_opt ∈ pdSetLM achieving equality; the optimizer is X_opt = (B†A^pB)^{1/p}. -/
private lemma exists_traceConjPowVar_eq_neg {p : ℝ} (hp0 : p < 0)
    {B A : L ℋ} (hB : IsUnit B) (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    ∃ X ∈ pdSetLM (ℋ := ℋ),
      p * traceConjPow (ℋ := ℋ) p B A = traceConjPowVar (ℋ := ℋ) p B A X := by
  have hA_nn := nonneg_of_pdSetLM hA
  have hpne : (p : ℝ) ≠ 0 := ne_of_lt hp0
  have hApd : CFC.rpow A p ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hA
  set M := star B * CFC.rpow A p * B with hM_def
  have hM_nn : (0 : L ℋ) ≤ M := star_left_conjugate_nonneg CFC.rpow_nonneg _
  have hMpd : M ∈ pdSetLM (ℋ := ℋ) := pdSetLM_conj hApd hB
  have hM_unit : IsUnit M := isUnit_of_pdSetLM hMpd
  have h1p_ne : (1 : ℝ) / p ≠ 0 := by positivity
  set X_opt := CFC.rpow M (1 / p) with hX_opt_def
  have hX_opt_pd : X_opt ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hMpd
  refine ⟨X_opt, hX_opt_pd, ?_⟩
  have hX_opt_nn := nonneg_of_pdSetLM hX_opt_pd
  have h1_sub_p_nn : 0 ≤ 1 - p := by linarith
  have h_bridge := liebTraceMapLM_as_lm_trace_pd B A X_opt hA hX_opt_pd h1_sub_p_nn
  have hrpow_comp : CFC.rpow X_opt (1 - p) = CFC.rpow M ((1 - p) / p) := by
    rw [hX_opt_def, CFC.rpow_eq_pow, CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow M (1 / p) (1 - p) hM_unit (by positivity)]
    congr 1; ring
  have hrpow_mul : M * CFC.rpow M ((1 - p) / p) = X_opt := by
    have h1 : CFC.rpow M 1 = M := CFC.rpow_one M hM_nn
    have hexp : (1 : ℝ) + (1 - p) / p = 1 / p := by field_simp; ring
    have hadd : CFC.rpow M 1 * CFC.rpow M ((1 - p) / p) =
        CFC.rpow M (1 + (1 - p) / p) := by
      simp only [CFC.rpow_eq_pow]
      exact (CFC.rpow_add hM_unit).symm
    conv_lhs => lhs; rw [← h1]
    rw [hadd, hexp]
  unfold traceConjPowVar traceConjPow
  rw [h_bridge, hrpow_comp, ← hM_def, hrpow_mul]
  ring

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
/-- Variational inequality (0 < p ≤ 1):
    ∀ X ∈ pdSetLM, F(A,X) ≤ p · traceConjPow(p,B,A).
    Follows from the trace Young inequality. -/
private lemma traceConjPowVar_le_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {B A X : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) (hX : X ∈ pdSetLM (ℋ := ℋ)) :
    traceConjPowVar (ℋ := ℋ) p B A X ≤ p * traceConjPow (ℋ := ℋ) p B A := by
  have hA_nn := nonneg_of_pdSetLM hA
  have hX_nn := nonneg_of_pdSetLM hX
  set M := star B * CFC.rpow A p * B with hM_def
  set N := CFC.rpow X (1 - p) with hN_def
  have hM_nn : (0 : L ℋ) ≤ M := star_left_conjugate_nonneg CFC.rpow_nonneg _
  have hN_nn : (0 : L ℋ) ≤ N := CFC.rpow_nonneg
  have hM_pos : M.IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp hM_nn
  have hN_pos : N.IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp hN_nn
  have h_bridge : liebTraceMapLM (ℋ := ℋ) p (star B) A X = (Tr (M * N)).re :=
    liebTraceMapLM_as_lm_trace hp0.le hp1 B A X hA_nn hX_nn
  have hp1' : p < 1 ∨ p = 1 := lt_or_eq_of_le hp1
  rcases hp1' with hp1' | rfl
  · have h1p : 0 < 1 - p := by linarith
    set r := 1 / p with hr_def
    set s := 1 / (1 - p) with hs_def
    have hpq : r.HolderConjugate s :=
      Real.holderConjugate_one_div hp0 h1p (by ring)
    have hYoung := trace_young_inequality hpq M N hM_pos hN_pos
    have hMr : CFC.rpow M r = CFC.rpow (star B * CFC.rpow A p * B) (1 / p) := by
      rw [hM_def]
    have hNs : CFC.rpow N s = X := by
      rw [hN_def, hs_def, CFC.rpow_eq_pow, CFC.rpow_eq_pow]
      rw [CFC.rpow_rpow_of_exponent_nonneg X (1 - p) (1 / (1 - p))
        (by linarith) (by positivity)]
      rw [show (1 - p) * (1 / (1 - p)) = 1 from by field_simp]
      exact CFC.rpow_one X hX_nn
    have hYoung_re : (Tr (M ∘ₗ N)).re ≤
        (Tr (CFC.rpow M r) / ↑r + Tr (CFC.rpow N s) / ↑s).re :=
      (RCLike.le_iff_re_im.mp hYoung).1
    rw [Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re, hNs] at hYoung_re
    have hMN_eq : (Tr (M ∘ₗ N)).re = (Tr (M * N)).re := by rfl
    rw [hMN_eq] at hYoung_re
    have hr_eq : (Tr (CFC.rpow M r)).re / r = p * (Tr (CFC.rpow M r)).re := by
      rw [hr_def]; field_simp
    have hs_eq : (Tr X).re / s = (1 - p) * (Tr X).re := by
      rw [hs_def]; field_simp
    rw [hr_eq, hs_eq, hMr] at hYoung_re
    simp only [traceConjPowVar, traceConjPow, h_bridge]
    linarith
  · have hN1 : N = 1 := by rw [hN_def, sub_self]; exact CFC.rpow_zero X hX_nn
    have hMN : (Tr (M * N)).re = (Tr M).re := by rw [hN1, mul_one]
    have hM1 : CFC.rpow M 1 = M := CFC.rpow_one M hM_nn
    have hFun : traceConjPow (ℋ := ℋ) 1 B A = (Tr M).re := by
      unfold traceConjPow
      rw [← hM_def, show (1 : ℝ) / 1 = 1 from by norm_num, hM1]
    have hVar : traceConjPowVar (ℋ := ℋ) 1 B A X = (Tr (M * N)).re := by
      unfold traceConjPowVar
      rw [h_bridge, sub_self, zero_mul, sub_zero]
    rw [hVar, hFun, hMN, one_mul]

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
/-- Variational attainment (0 < p ≤ 1):
    ∃ X_opt ∈ pdSetLM achieving equality. -/
private lemma exists_traceConjPowVar_eq_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {B A : L ℋ} (hB : IsUnit B) (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    ∃ X ∈ pdSetLM (ℋ := ℋ),
      p * traceConjPow (ℋ := ℋ) p B A = traceConjPowVar (ℋ := ℋ) p B A X := by
  rcases eq_or_lt_of_le hp1 with rfl | hp1'
  · -- p = 1: traceConjPowVar 1 B A X = Tr(B† A B).re, = 1 * traceConjPow
    refine ⟨A, hA, ?_⟩
    have hA_nn := nonneg_of_pdSetLM hA
    have hM_nn : (0 : L ℋ) ≤ star B * A * B := star_left_conjugate_nonneg hA_nn _
    have h1 : (1 : ℝ) / 1 = (1 : ℝ) := by norm_num
    have eq1 : CFC.rpow A (1 : ℝ) = A := CFC.rpow_one _ hA_nn
    have eq2 : CFC.rpow (star B * A * B) (1 : ℝ) = star B * A * B :=
      CFC.rpow_one _ hM_nn
    have hfun : traceConjPow (ℋ := ℋ) 1 B A = (Tr (star B * A * B)).re := by
      simp only [traceConjPow, h1, eq1, eq2]
    have hvar : traceConjPowVar (ℋ := ℋ) 1 B A A = (Tr (star B * A * B)).re := by
      unfold traceConjPowVar
      have h0 : (1 : ℝ) - 1 = 0 := by ring
      rw [h0, zero_mul, sub_zero]
      have eq0 : CFC.rpow A (0 : ℝ) = 1 := CFC.rpow_zero _ hA_nn
      have h_bridge := liebTraceMapLM_as_lm_trace (by linarith : (0 : ℝ) ≤ 1) le_rfl B A A hA_nn hA_nn
      simp only [h0, eq0, eq1, mul_one] at h_bridge
      exact h_bridge
    rw [hfun, hvar, one_mul]
  · -- 0 < p < 1
    have hA_nn := nonneg_of_pdSetLM hA
    set M := star B * CFC.rpow A p * B with hM_def
    have hM_nn : (0 : L ℋ) ≤ M := star_left_conjugate_nonneg CFC.rpow_nonneg _
    have hApd : CFC.rpow A p ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow hA
    have hMpd : M ∈ pdSetLM (ℋ := ℋ) := pdSetLM_conj hApd hB
    have hM_unit : IsUnit M := isUnit_of_pdSetLM hMpd
    set X_opt := CFC.rpow M (1 / p) with hX_opt_def
    have h1p_pos : 0 < 1 / p := by positivity
    have hX_opt_pd : X_opt ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow hMpd
    refine ⟨X_opt, hX_opt_pd, ?_⟩
    have hX_opt_nn := nonneg_of_pdSetLM hX_opt_pd
    have h_bridge := liebTraceMapLM_as_lm_trace hp0.le hp1 B A X_opt hA_nn hX_opt_nn
    have h1_sub_p_nn : 0 ≤ 1 - p := by linarith
    have hrpow_comp : CFC.rpow X_opt (1 - p) = CFC.rpow M ((1 - p) / p) := by
      rw [hX_opt_def]
      simp only [CFC.rpow_eq_pow]
      rw [CFC.rpow_rpow_of_exponent_nonneg M (1 / p) (1 - p) (by positivity) h1_sub_p_nn]
      congr 1; ring
    have hrpow_mul : M * CFC.rpow M ((1 - p) / p) = X_opt := by
      have h1 : CFC.rpow M 1 = M := CFC.rpow_one M hM_nn
      have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
      have hexp : (1 : ℝ) + (1 - p) / p = 1 / p := by field_simp; ring
      have hadd : CFC.rpow M 1 * CFC.rpow M ((1 - p) / p) =
          CFC.rpow M (1 + (1 - p) / p) := by
        simp only [CFC.rpow_eq_pow]
        exact (CFC.rpow_add hM_unit).symm
      conv_lhs => lhs; rw [← h1]
      rw [hadd, hexp]
    unfold traceConjPowVar traceConjPow
    rw [h_bridge, hrpow_comp, ← hM_def, hrpow_mul]
    ring

omit [Nontrivial ℋ] in
private lemma real_smul_eq_complex_smul (r : ℝ) (X : L ℋ) :
    (r • X : L ℋ) = ((↑r : ℂ) • X : L ℋ) :=
  LinearMap.ext fun x => by
    simp only [LinearMap.smul_apply]
    change r • X x = (↑r : ℂ) • X x
    haveI : IsScalarTower ℝ ℂ ℋ := ⟨fun r c x => by
      change (r • c) • x = ((r : ℂ)) • c • x
      rw [Algebra.smul_def, mul_smul]; simp [RCLike.algebraMap_eq_ofReal]⟩
    exact algebraMap_smul ℂ r (X x)

omit [Nontrivial ℋ] in
private lemma traceRe_real_smul (r : ℝ) (X : L ℋ) :
    (LinearMap.trace ℂ ℋ (r • X)).re = r * (LinearMap.trace ℂ ℋ X).re := by
  rw [real_smul_eq_complex_smul r X, map_smul, smul_eq_mul, Complex.re_ofReal_mul]

omit [Nontrivial ℋ] in
private lemma trace_re_convex_combo (θ : ℝ) (X₁ X₂ : L ℋ) :
    (Tr ((1 - θ) • X₁ + θ • X₂)).re =
      (1 - θ) * (Tr X₁).re + θ * (Tr X₂).re := by
  rw [map_add, Complex.add_re, traceRe_real_smul, traceRe_real_smul]

omit [Nontrivial ℋ] in
/-- Cyclic trace: Tr(A^s K† B^{1-s} K) = Tr(B^{1-s} K A^s K†).
    Equivalently: liebTraceMapLM(s,K,A,B) = liebTraceMapLM(1−s,star K,B,A). -/
private lemma traceRe_mul_comm (X Y : LownerHeinzTheorem.L ℋ) :
    traceRe (ℋ := ℋ) (X * Y) = traceRe (ℋ := ℋ) (Y * X) := by
  simp only [traceRe]
  exact congrArg Complex.re
    (LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) X.toLinearMap Y.toLinearMap)

omit [Nontrivial ℋ] in
private lemma liebTraceMapLM_cyclic (s : ℝ) (K A B : L ℋ) :
    liebTraceMapLM (ℋ := ℋ) s K A B =
      liebTraceMapLM (ℋ := ℋ) (1 - s) (star K) B A := by
  simp only [liebTraceMapLM, liebTraceMap]
  rw [star_toCLM, star_star, show (1 : ℝ) - (1 - s) = s from by ring]
  change traceRe (ℋ := ℋ)
      (A.toContinuousLinearMap ^ s * star K.toContinuousLinearMap *
        B.toContinuousLinearMap ^ (1 - s) * K.toContinuousLinearMap) =
    traceRe (ℋ := ℋ)
      (B.toContinuousLinearMap ^ (1 - s) * K.toContinuousLinearMap *
        A.toContinuousLinearMap ^ s * star K.toContinuousLinearMap)
  have h := traceRe_mul_comm (ℋ := ℋ)
    (A.toContinuousLinearMap ^ s * star K.toContinuousLinearMap)
    (B.toContinuousLinearMap ^ (1 - s) * K.toContinuousLinearMap)
  simp only [mul_assoc] at h ⊢
  exact h

private lemma traceConjPowVar_jointlyConvex {p : ℝ} (hpm1 : -1 ≤ p) (hp0 : p < 0) (B : L ℋ) :
    JointlyConvexOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ))
      (fun A X => traceConjPowVar (ℋ := ℋ) p B A X) := by
  intro A₁ A₂ X₁ X₂ θ hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [smul_eq_mul, traceConjPowVar]
  simp only [liebTraceMapLM_cyclic p (star B), star_star]
  have h_ando := liebTrace_jointlyConvexOn_pdSet_lm (show (1 : ℝ) ≤ 1 - p by linarith)
    (show 1 - p ≤ 2 by linarith) (B : L ℋ)
  have h_swap : JointlyConvexOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ))
      (fun A X => liebTraceMapLM (ℋ := ℋ) (1 - p) B X A) :=
    fun _ _ _ _ _ h1 h2 h3 h4 h5 h6 => h_ando h3 h4 h1 h2 h5 h6
  have h_conv := h_swap hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [smul_eq_mul] at h_conv
  have h_tr := trace_re_convex_combo θ X₁ X₂
  nlinarith

/-- Joint concavity of `traceConjPowVar` for 0 < p < 1.
    By Lieb's concavity theorem liebTraceMapLM(p, B†, A, X) is jointly concave,
    and the trace penalty is linear, so the functional is jointly concave. -/
private lemma traceConjPowVar_jointlyConcave {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (B : L ℋ) :
    JointlyConcaveOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ))
      (fun A X => traceConjPowVar (ℋ := ℋ) p B A X) := by
  intro A₁ A₂ X₁ X₂ θ hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [smul_eq_mul, traceConjPowVar]
  have h_lieb := liebTrace_jointlyConcaveOn_pdSet_lm hp0 hp1 (star B : L ℋ)
    hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [smul_eq_mul] at h_lieb
  have h_tr := trace_re_convex_combo θ X₁ X₂
  nlinarith

set_option backward.isDefEq.respectTransparency false in
/-- Concavity of `A ↦ Tr((B† A^p B)^{1/p})` on `pdSetLM` for `−1 ≤ p < 0`.
    Proof: The variational functional `F(A, X)` is jointly convex in `(A, X)` by Ando's theorem.
    Since `p · traceConjPow = inf_X F`, the function `p · traceConjPow` is convex.
    Dividing by `p < 0` gives concavity of `traceConjPow`. -/
theorem traceConjPow_concave_neg {p : ℝ} (hpm1 : -1 ≤ p) (hp0 : p < 0) (B : L ℋ) (hB : IsUnit B) :
    ConcaveOn ℝ (pdSetLM (ℋ := ℋ)) (traceConjPow (ℋ := ℋ) p B) := by
  refine ⟨pdSetLM_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hab' : a = 1 - b := by linarith
  have hb1 : b ≤ 1 := by linarith
  obtain ⟨Xx, hXx_mem, hXx_eq⟩ := exists_traceConjPowVar_eq_neg hp0 hB hx
  obtain ⟨Xy, hXy_mem, hXy_eq⟩ := exists_traceConjPowVar_eq_neg hp0 hB hy
  have h_combo : a • x + b • y ∈ pdSetLM (ℋ := ℋ) := by
    rw [hab']; exact pdSetLM_convexCombo hx hy hb hb1
  have h_Xcombo : a • Xx + b • Xy ∈ pdSetLM (ℋ := ℋ) := by
    rw [hab']; exact pdSetLM_convexCombo hXx_mem hXy_mem hb hb1
  have step1 : p * traceConjPow (ℋ := ℋ) p B (a • x + b • y) ≤
      traceConjPowVar (ℋ := ℋ) p B (a • x + b • y) (a • Xx + b • Xy) := by
    rw [hab'] at h_combo h_Xcombo ⊢; exact traceConjPowVar_le_neg hp0 hB h_combo h_Xcombo
  rw [hab'] at step1
  have step2 := traceConjPowVar_jointlyConvex hpm1 hp0 B hx hy hXx_mem hXy_mem hb hb1
  simp only [smul_eq_mul] at step2
  have step3 : (1 - b) * traceConjPowVar (ℋ := ℋ) p B x Xx + b * traceConjPowVar (ℋ := ℋ) p B y Xy =
      p * ((1 - b) * traceConjPow (ℋ := ℋ) p B x + b * traceConjPow (ℋ := ℋ) p B y) := by
    rw [← hXx_eq, ← hXy_eq]; ring
  have h_chain : p * traceConjPow (ℋ := ℋ) p B ((1 - b) • x + b • y) ≤
      p * ((1 - b) * traceConjPow (ℋ := ℋ) p B x + b * traceConjPow (ℋ := ℋ) p B y) :=
    calc p * traceConjPow (ℋ := ℋ) p B ((1 - b) • x + b • y)
        ≤ traceConjPowVar (ℋ := ℋ) p B ((1 - b) • x + b • y) ((1 - b) • Xx + b • Xy) := step1
      _ ≤ (1 - b) * traceConjPowVar (ℋ := ℋ) p B x Xx + b * traceConjPowVar (ℋ := ℋ) p B y Xy := step2
      _ = p * ((1 - b) * traceConjPow (ℋ := ℋ) p B x + b * traceConjPow (ℋ := ℋ) p B y) := step3
  rw [hab']
  by_contra h_neg
  push_neg at h_neg
  have := mul_lt_mul_of_neg_left h_neg hp0
  linarith

set_option backward.isDefEq.respectTransparency false in
/-- Concavity of `A ↦ Tr((B† A^p B)^{1/p})` on `pdSetLM` for `0 < p ≤ 1`.
    Proof: `F` is jointly concave by Lieb's theorem; `p · traceConjPow = sup_X F` is concave;
    dividing by `p > 0` preserves concavity. -/
theorem traceConjPow_concave_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (B : L ℋ) (hB : IsUnit B) :
    ConcaveOn ℝ (pdSetLM (ℋ := ℋ)) (traceConjPow (ℋ := ℋ) p B) := by
  refine ⟨pdSetLM_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hab' : a = 1 - b := by linarith
  have hb1 : b ≤ 1 := by linarith
  have hp1' : p < 1 ∨ p = 1 := lt_or_eq_of_le hp1
  obtain ⟨Xx, hXx_mem, hXx_eq⟩ := exists_traceConjPowVar_eq_pos hp0 hp1 hB hx
  obtain ⟨Xy, hXy_mem, hXy_eq⟩ := exists_traceConjPowVar_eq_pos hp0 hp1 hB hy
  have h_combo : a • x + b • y ∈ pdSetLM (ℋ := ℋ) := by
    rw [hab']; exact pdSetLM_convexCombo hx hy hb hb1
  have h_Xcombo : a • Xx + b • Xy ∈ pdSetLM (ℋ := ℋ) := by
    rw [hab']; exact pdSetLM_convexCombo hXx_mem hXy_mem hb hb1
  have step1 : traceConjPowVar (ℋ := ℋ) p B (a • x + b • y) (a • Xx + b • Xy) ≤
      p * traceConjPow (ℋ := ℋ) p B (a • x + b • y) := by
    rw [hab'] at h_combo h_Xcombo ⊢; exact traceConjPowVar_le_pos hp0 hp1 h_combo h_Xcombo
  rw [hab'] at step1
  rcases hp1' with hp1' | rfl
  · have step2 := traceConjPowVar_jointlyConcave hp0 hp1' B hx hy hXx_mem hXy_mem hb hb1
    simp only [smul_eq_mul] at step2
    have step3 : p * ((1 - b) * traceConjPow (ℋ := ℋ) p B x + b * traceConjPow (ℋ := ℋ) p B y) =
        (1 - b) * traceConjPowVar (ℋ := ℋ) p B x Xx + b * traceConjPowVar (ℋ := ℋ) p B y Xy := by
      rw [← hXx_eq, ← hXy_eq]; ring
    have h_chain : p * ((1 - b) * traceConjPow (ℋ := ℋ) p B x + b * traceConjPow (ℋ := ℋ) p B y) ≤
        p * traceConjPow (ℋ := ℋ) p B ((1 - b) • x + b • y) :=
      calc p * ((1 - b) * traceConjPow (ℋ := ℋ) p B x + b * traceConjPow (ℋ := ℋ) p B y)
          = (1 - b) * traceConjPowVar (ℋ := ℋ) p B x Xx + b * traceConjPowVar (ℋ := ℋ) p B y Xy := step3
        _ ≤ traceConjPowVar (ℋ := ℋ) p B ((1 - b) • x + b • y) ((1 - b) • Xx + b • Xy) := step2
        _ ≤ p * traceConjPow (ℋ := ℋ) p B ((1 - b) • x + b • y) := step1
    rw [hab']
    by_contra h_neg
    push_neg at h_neg
    have := mul_lt_mul_of_pos_left h_neg hp0
    linarith
  · -- p = 1: A ↦ Tr(B†AB) is affine, hence concave
    have nn_of_pd_lm : ∀ {A : L ℋ}, A ∈ pdSetLM (ℋ := ℋ) → (0 : L ℋ) ≤ A := by
      intro A hA
      have h_clm_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap := by
        obtain ⟨hA_sa, hA_spec⟩ := hA
        exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hA_sa)).2
          (fun r hr => (hA_spec hr).le)
      rw [LinearMap.nonneg_iff_isPositive]
      have h := (ContinuousLinearMap.nonneg_iff_isPositive _).mp h_clm_nn
      exact ⟨fun x y => h.1 x y, fun x => h.2 x⟩
    have hfun : ∀ {A : L ℋ}, A ∈ pdSetLM (ℋ := ℋ) →
        traceConjPow (ℋ := ℋ) 1 B A = (Tr (star B * A * B)).re := by
      intro A hA
      unfold traceConjPow
      have h1 : (1 : ℝ) / 1 = (1 : ℝ) := by norm_num
      have eq1 : CFC.rpow A 1 = A := CFC.rpow_one _ (nn_of_pd_lm hA)
      have eq2 : CFC.rpow (star B * A * B) 1 = star B * A * B :=
        CFC.rpow_one _ (star_left_conjugate_nonneg (nn_of_pd_lm hA) _)
      simp only [h1, eq1, eq2]
    rw [hfun hx, hfun hy, hfun h_combo]
    have hmul : (star B * (a • x + b • y) * B : L ℋ) =
        a • (star B * x * B) + b • (star B * y * B) := by
      simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
    rw [hmul, map_add, Complex.add_re, traceRe_real_smul, traceRe_real_smul]

set_option backward.isDefEq.respectTransparency false in
/-- For a fixed operator `B`, the map `A ↦ Tr((B† A^p B)^{1/p})` is concave
    on positive-definite operators for `−1 ≤ p ≤ 1`, `p ≠ 0` (Frank–Lieb concavity). -/
theorem traceConjPow_concave {p : ℝ} (hp_neg : -1 ≤ p) (hp_pos : p ≤ 1) (hp_ne : p ≠ 0) (B : L ℋ)
    (hB : IsUnit B) :
    ConcaveOn ℝ (pdSetLM (ℋ := ℋ)) (traceConjPow (ℋ := ℋ) p B) := by
  rcases lt_or_ge p 0 with hp | hp
  · exact traceConjPow_concave_neg hp_neg hp B hB
  · exact traceConjPow_concave_pos (lt_of_le_of_ne hp (Ne.symm hp_ne)) hp_pos B hB

end TraceConjPowConcavity

section JointConvexity

open LiebAndoTrace GeneralizedPerspectiveFunction
open scoped MatrixOrder

universe u₃

variable {ℋ : Type u₃} [Qudit ℋ] [Nontrivial ℋ]

set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false

omit [Nontrivial ℋ] in
/-- Eigenvalue similarity: CC† and C†C have identical rpow traces.
    Both CC† and C†C have the same non-zero eigenvalues, so Tr(f(CC†)) = Tr(f(C†C))
    for any CFC function f (including rpow). -/
private lemma trace_rpow_star_mul_comm {C : L ℋ} (hC : IsUnit C) (q : ℝ) :
    Tr (CFC.rpow (star C * C) q) = Tr (CFC.rpow (C * star C) q) := by
  have h1_nn : (0 : L ℋ) ≤ 1 :=
    (LinearMap.nonneg_iff_isPositive 1).mpr LinearMap.isPositive_one
  have h_sCC_nn : (0 : L ℋ) ≤ star C * C := by
    have := star_left_conjugate_nonneg h1_nn C; rwa [mul_one] at this
  have h_CsC_nn : (0 : L ℋ) ≤ C * star C := by
    have := star_left_conjugate_nonneg h1_nn (star C); rwa [star_star, mul_one] at this
  have h_sCC_pos := (LinearMap.nonneg_iff_isPositive _).mp h_sCC_nn
  have h_CsC_pos := (LinearMap.nonneg_iff_isPositive _).mp h_CsC_nn
  have h_sCC_unit : IsUnit (star C * C) := hC.star.mul hC
  have h_CsC_unit : IsUnit (C * star C) := hC.mul hC.star
  let b := stdOrthonormalBasis ℂ ℋ
  set M := LinearMap.toMatrixOrthonormal b C
  have hH1 : (star M * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hH2 : (M * star M).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self M
  have hNN1 : 0 ≤ star M * M := (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  have hNN2 : 0 ≤ M * star M := (Matrix.posSemidef_self_mul_conjTranspose M).nonneg
  have h_φ_sCC : LinearMap.toMatrixOrthonormal b (star C * C) = star M * M := by
    rw [map_mul, map_star]
  have h_φ_CsC : LinearMap.toMatrixOrthonormal b (C * star C) = M * star M := by
    rw [map_mul, map_star]
  have h_eig : hH1.eigenvalues = hH2.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    exact Matrix.charpoly_mul_comm (star M) M
  calc Tr (CFC.rpow (star C * C) q)
      = Matrix.trace (LinearMap.toMatrixOrthonormal b (CFC.rpow (star C * C) q)) :=
        tr_eq_matrix_trace_orthonormal b _
    _ = Matrix.trace (CFC.rpow (LinearMap.toMatrixOrthonormal b (star C * C)) q) := by
        rw [toMatrixOrthonormal_rpow_pd b _ h_sCC_pos h_sCC_unit q]
    _ = Matrix.trace (CFC.rpow (star M * M) q) := by rw [h_φ_sCC]
    _ = ∑ i, (((hH1.eigenvalues i) ^ q : ℝ) : ℂ) :=
        matrix_trace_rpow_eq_sum_eigenvalues _ hH1 hNN1 q
    _ = ∑ i, (((hH2.eigenvalues i) ^ q : ℝ) : ℂ) := by rw [h_eig]
    _ = Matrix.trace (CFC.rpow (M * star M) q) :=
        (matrix_trace_rpow_eq_sum_eigenvalues _ hH2 hNN2 q).symm
    _ = Matrix.trace (CFC.rpow (LinearMap.toMatrixOrthonormal b (C * star C)) q) := by
        rw [h_φ_CsC]
    _ = Matrix.trace (LinearMap.toMatrixOrthonormal b (CFC.rpow (C * star C) q)) := by
        rw [toMatrixOrthonormal_rpow_pd b _ h_CsC_pos h_CsC_unit q]
    _ = Tr (CFC.rpow (C * star C) q) :=
        (tr_eq_matrix_trace_orthonormal b _).symm

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
/-- The σ-dependent part of quasiVar equals traceConjPow via eigenvalue similarity:
    Re Tr((σ^β H σ^β)^q) = traceConjPow((α-1)/α, H^{1/2}, σ)
    where β = (α-1)/(2α), q = α/(α-1). -/
private lemma quasiVar_sigma_eq_traceConjPow {α : ℝ} (hα0 : 0 < α)
    {H σ : L ℋ} (hH : H ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    (Tr (CFC.rpow (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α)))
         (α / (α - 1)))).re =
    traceConjPow (ℋ := ℋ) ((α - 1) / α) (CFC.rpow H (1/2)) σ := by
  set P := CFC.rpow σ ((α - 1) / (2 * α))
  set Q := CFC.rpow H (1/2)
  set C := P * Q
  have hH_nn := nonneg_of_pdSetLM hH
  have hσ_nn := nonneg_of_pdSetLM hσ
  have hH_unit := isUnit_of_pdSetLM hH
  have hσ_unit := isUnit_of_pdSetLM hσ
  have hP_sa : IsSelfAdjoint P := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hQ_sa : IsSelfAdjoint Q := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hP_unit : IsUnit P := hσ_unit.cfcRpow _ hσ_nn
  have hQ_unit : IsUnit Q := hH_unit.cfcRpow _ hH_nn
  have hC_unit : IsUnit C := hP_unit.mul hQ_unit
  have h_QQ : Q * Q = H := by
    change CFC.rpow H (1/2) * CFC.rpow H (1/2) = H
    have : CFC.rpow H (1/2) * CFC.rpow H (1/2) = CFC.rpow H (1/2 + 1/2) := by
      simp only [CFC.rpow_eq_pow]; exact (CFC.rpow_add hH_unit).symm
    rw [this, show (1 : ℝ)/2 + 1/2 = 1 from by norm_num]
    exact CFC.rpow_one H hH_nn
  have h_PP : P * P = CFC.rpow σ ((α - 1) / α) := by
    change CFC.rpow σ ((α - 1) / (2 * α)) * CFC.rpow σ ((α - 1) / (2 * α)) =
      CFC.rpow σ ((α - 1) / α)
    have : CFC.rpow σ ((α - 1) / (2 * α)) * CFC.rpow σ ((α - 1) / (2 * α)) =
        CFC.rpow σ ((α - 1) / (2 * α) + (α - 1) / (2 * α)) := by
      simp only [CFC.rpow_eq_pow]; exact (CFC.rpow_add hσ_unit).symm
    rw [this]; congr 1; field_simp; ring
  have h_star_C : star C = Q * P := by
    change star (P * Q) = Q * P
    rw [star_mul, hP_sa.star_eq, hQ_sa.star_eq]
  have h_CsC : C * star C = P * H * P := by
    rw [h_star_C]
    change P * Q * (Q * P) = P * H * P
    rw [← mul_assoc (P * Q) Q P, mul_assoc P Q Q, h_QQ]
  have h_sCC : star C * C = Q * CFC.rpow σ ((α - 1) / α) * Q := by
    rw [h_star_C]
    change Q * P * (P * Q) = Q * CFC.rpow σ ((α - 1) / α) * Q
    rw [← mul_assoc (Q * P) P Q, mul_assoc Q P P, h_PP]
  suffices h : Tr (CFC.rpow (P * H * P) (α / (α - 1))) =
    Tr (CFC.rpow (Q * CFC.rpow σ ((α - 1) / α) * Q) (α / (α - 1))) by
    unfold traceConjPow
    rw [hQ_sa.star_eq, show (1 : ℝ) / ((α - 1) / α) = α / (α - 1) from by field_simp]
    exact congrArg Complex.re h
  calc Tr (CFC.rpow (P * H * P) (α / (α - 1)))
      = Tr (CFC.rpow (C * star C) (α / (α - 1))) := by rw [← h_CsC]
    _ = Tr (CFC.rpow (star C * C) (α / (α - 1))) :=
        (trace_rpow_star_mul_comm hC_unit _).symm
    _ = Tr (CFC.rpow (Q * CFC.rpow σ ((α - 1) / α) * Q) (α / (α - 1))) := by
        rw [h_sCC]

set_option backward.isDefEq.respectTransparency false in
/-- Concavity of the σ-term on `pdSetLM`: `σ ↦ Re Tr((σ^β H σ^β)^q)` is concave
    for `1/2 ≤ α`, `α ≠ 1` and `H ∈ pdSetLM`.
    Uses `traceConjPow_concave` and eigenvalue similarity. -/
lemma sigma_term_concaveOn {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1) (hα_ge : 1 / 2 ≤ α)
    {H : L ℋ} (hH : H ∈ pdSetLM (ℋ := ℋ)) :
    ConcaveOn ℝ (pdSetLM (ℋ := ℋ)) (fun σ =>
      (Tr (CFC.rpow (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α)))
           (α / (α - 1)))).re) := by
  set p := (α - 1) / α with hp_def
  have hp_ge : -1 ≤ p := by rw [hp_def]; rw [le_div_iff₀ hα0]; linarith
  have hp_le : p ≤ 1 := by rw [hp_def]; rw [div_le_one hα0]; linarith
  have hp_ne : p ≠ 0 := by rw [hp_def]; exact div_ne_zero (sub_ne_zero.mpr hα_ne1) (ne_of_gt hα0)
  have hH_nn := nonneg_of_pdSetLM hH
  have hH_unit := isUnit_of_pdSetLM hH
  have hHsq_unit : IsUnit (CFC.rpow H (1/2)) := hH_unit.cfcRpow (1/2) hH_nn
  have h_concave := traceConjPow_concave hp_ge hp_le hp_ne (CFC.rpow H (1/2)) hHsq_unit
  refine ⟨pdSetLM_convex, ?_⟩
  intro σ₁ hσ₁ σ₂ hσ₂ a b ha hb hab
  simp only [smul_eq_mul]
  have h_combo : a • σ₁ + b • σ₂ ∈ pdSetLM (ℋ := ℋ) := by
    rw [show a = 1 - b from by linarith]
    exact pdSetLM_convexCombo hσ₁ hσ₂ hb (by linarith)
  rw [quasiVar_sigma_eq_traceConjPow hα0 hH hσ₁,
      quasiVar_sigma_eq_traceConjPow hα0 hH hσ₂,
      quasiVar_sigma_eq_traceConjPow hα0 hH h_combo]
  exact h_concave.2 hσ₁ hσ₂ ha hb hab

/-- The variational optimizer: `H_opt = P (P ρ P)^{α-1} P` with `P = σ^{(1-α)/(2α)}`. -/
noncomputable def quasiVarOpt (α : ℝ) (ρ σ : L ℋ) : L ℋ :=
  CFC.rpow σ ((1 - α) / (2 * α)) *
    CFC.rpow (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
      CFC.rpow σ ((1 - α) / (2 * α))) (α - 1) *
    CFC.rpow σ ((1 - α) / (2 * α))

omit [Nontrivial ℋ] in
private lemma rpow_conj_pdSetLM {β q : ℝ}
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    star (CFC.rpow σ β) * CFC.rpow (star (CFC.rpow σ β) * ρ *
      CFC.rpow σ β) q * CFC.rpow σ β ∈ pdSetLM (ℋ := ℋ) := by
  have hP_pd : CFC.rpow σ β ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hσ
  have hP_unit := isUnit_of_pdSetLM hP_pd
  exact pdSetLM_conj (pdSetLM_rpow_ne (pdSetLM_conj hρ hP_unit)) hP_unit

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
lemma quasiVarOpt_pdSetLM {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    quasiVarOpt α ρ σ ∈ pdSetLM (ℋ := ℋ) := by
  have hβ'_ne : (1 - α) / (2 * α) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (Ne.symm hα_ne1)) (by positivity)
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα_ne1
  have hP_sa : IsSelfAdjoint (CFC.rpow σ ((1 - α) / (2 * α))) :=
    IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have key := rpow_conj_pdSetLM (β := (1 - α) / (2 * α)) (q := α - 1) hρ hσ
  rwa [hP_sa.star_eq] at key

set_option maxHeartbeats 400000 in
-- heartbeats raised: section-level backward.isDefEq.respectTransparency false increases whnf cost
omit [Nontrivial ℋ] in
lemma quasiVarOpt_eq_quasi_gt {α : ℝ} (hα : 1 < α)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    quasiVar α ρ σ (quasiVarOpt α ρ σ) = sandwichedQuasi α ρ σ := by
  have hρ_pos := (LinearMap.nonneg_iff_isPositive ρ).mp (nonneg_of_pdSetLM hρ)
  have hσ_pos := (LinearMap.nonneg_iff_isPositive σ).mp (nonneg_of_pdSetLM hσ)
  have hσ_unit := isUnit_of_pdSetLM hσ
  have hρ_unit := isUnit_of_pdSetLM hρ
  have hσ_nn := nonneg_of_pdSetLM hσ
  have hρ_nn := nonneg_of_pdSetLM hρ
  unfold quasiVarOpt
  set β' : ℝ := (1 - α) / (2 * α) with hβ'_def
  set P := CFC.rpow σ β' with hP_def
  set Q := CFC.rpow σ (-β') with hQ_def
  set X := P * ρ * P with hX_def
  set H_opt := P * CFC.rpow X (α - 1) * P with hH_opt_def
  have hX_pos : X.IsPositive := conj_isPositive (rpow_isSelfAdjoint hσ_pos β') hρ_pos
  have hX_nn : (0 : L ℋ) ≤ X := (LinearMap.nonneg_iff_isPositive X).mpr hX_pos
  have hP_unit : IsUnit P := hσ_unit.cfcRpow β' hσ_nn
  have hX_unit : IsUnit X := (hP_unit.mul hρ_unit).mul hP_unit
  have hPQ : P * Q = 1 := by
    change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
    exact CFC.rpow_mul_rpow_neg β' hσ_unit
  have hQP : Q * P = 1 := by
    change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
    exact CFC.rpow_neg_mul_rpow β' hσ_unit
  have hY_opt : Q * H_opt * Q = CFC.rpow X (α - 1) := by
    rw [hH_opt_def]
    have : Q * (P * CFC.rpow X (α - 1) * P) * Q =
        (Q * P) * CFC.rpow X (α - 1) * (P * Q) := by simp only [mul_assoc]
    rw [this, hQP, hPQ, one_mul, mul_one]
  have hα_sub_pos : (0 : ℝ) < α - 1 := by linarith
  have hα_pos : (0 : ℝ) < α := by linarith
  have hYq_eq : CFC.rpow (CFC.rpow X (α - 1)) (α / (α - 1)) = CFC.rpow X α := by
    simp only [CFC.rpow_eq_pow]
    set s : NNReal := ⟨α - 1, by linarith⟩
    set t : NNReal := ⟨α / (α - 1), le_of_lt (div_pos hα_pos hα_sub_pos)⟩
    set r : NNReal := ⟨α, by linarith⟩
    have hs0 : (0 : NNReal) < s := by exact_mod_cast hα_sub_pos
    have ht0 : (0 : NNReal) < t := by exact_mod_cast div_pos hα_pos hα_sub_pos
    have hr0 : (0 : NNReal) < r := by exact_mod_cast hα_pos
    have hst : s * t = r := by
      ext; change (α - 1) * (α / (α - 1)) = α
      rw [mul_comm]; exact div_mul_cancel₀ α (by linarith : (α - 1 : ℝ) ≠ 0)
    change (X ^ (↑s : ℝ)) ^ (↑t : ℝ) = X ^ (↑r : ℝ)
    rw [← CFC.nnrpow_eq_rpow hs0, ← CFC.nnrpow_eq_rpow ht0,
        ← CFC.nnrpow_eq_rpow hr0, CFC.nnrpow_nnrpow, hst]
  have hXX_eq : X * CFC.rpow X (α - 1) = CFC.rpow X α := by
    simp only [CFC.rpow_eq_pow]
    set s : NNReal := ⟨α - 1, by linarith⟩
    set r : NNReal := ⟨α, by linarith⟩
    have hs0 : (0 : NNReal) < s := by exact_mod_cast hα_sub_pos
    have hr0 : (0 : NNReal) < r := by exact_mod_cast hα_pos
    have h1s : (1 : NNReal) + s = r := by ext; change (1 : ℝ) + (α - 1) = α; ring
    change X * X ^ (↑s : ℝ) = X ^ (↑r : ℝ)
    conv_lhs => lhs; rw [show X = X ^ (1 : NNReal) from by
      rw [CFC.nnrpow_eq_rpow one_pos, NNReal.coe_one]; exact (CFC.rpow_one X hX_nn).symm]
    rw [← CFC.nnrpow_eq_rpow hs0, ← CFC.nnrpow_eq_rpow hr0,
        ← CFC.nnrpow_add one_pos hs0, h1s]
  have hTr_Hρ : Tr (H_opt * ρ) = Tr (X * CFC.rpow X (α - 1)) := by
    rw [hH_opt_def]
    have : Tr (P * CFC.rpow X (α - 1) * P * ρ) =
        Tr (P * ρ * P * CFC.rpow X (α - 1)) := by
      calc Tr (P * CFC.rpow X (α - 1) * P * ρ)
          = Tr (ρ * (P * CFC.rpow X (α - 1) * P)) := (trace_mul_comm _ _).symm
        _ = Tr (ρ * P * (CFC.rpow X (α - 1) * P)) := by simp only [mul_assoc]
        _ = Tr ((CFC.rpow X (α - 1) * P) * (ρ * P)) := trace_mul_comm _ _
        _ = Tr (CFC.rpow X (α - 1) * (P * (ρ * P))) := by simp only [mul_assoc]
        _ = Tr (P * (ρ * P) * CFC.rpow X (α - 1)) := (trace_mul_comm _ _).symm
        _ = Tr (P * ρ * P * CFC.rpow X (α - 1)) := by simp only [mul_assoc]
    rw [this, hX_def]
  have hexp : (α - 1 : ℝ) / (2 * α) = -β' := by rw [hβ'_def]; ring
  unfold quasiVar sandwichedQuasi
  rw [hexp, hY_opt, hYq_eq, hTr_Hρ, hXX_eq]
  set T := Tr (CFC.rpow X α)
  push_cast; ring

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
private lemma quasiVarOpt_eq_quasi_lt {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    quasiVar α ρ σ (quasiVarOpt α ρ σ) = sandwichedQuasi α ρ σ := by
  have hρ_pos := (LinearMap.nonneg_iff_isPositive ρ).mp (nonneg_of_pdSetLM hρ)
  have hσ_pos := (LinearMap.nonneg_iff_isPositive σ).mp (nonneg_of_pdSetLM hσ)
  have hσ_unit := isUnit_of_pdSetLM hσ
  have hρ_unit := isUnit_of_pdSetLM hρ
  have hσ_nn := nonneg_of_pdSetLM hσ
  have hρ_nn := nonneg_of_pdSetLM hρ
  unfold quasiVarOpt
  set β' : ℝ := (1 - α) / (2 * α) with hβ'_def
  set P := CFC.rpow σ β' with hP_def
  set Q := CFC.rpow σ (-β') with hQ_def
  set X := P * ρ * P with hX_def
  set H_opt := P * CFC.rpow X (α - 1) * P with hH_opt_def
  have hX_pos : X.IsPositive := conj_isPositive (rpow_isSelfAdjoint hσ_pos β') hρ_pos
  have hX_nn : (0 : L ℋ) ≤ X := (LinearMap.nonneg_iff_isPositive X).mpr hX_pos
  have hP_unit : IsUnit P := hσ_unit.cfcRpow β' hσ_nn
  have hX_unit : IsUnit X := (hP_unit.mul hρ_unit).mul hP_unit
  have hPQ : P * Q = 1 := by
    change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
    exact CFC.rpow_mul_rpow_neg β' hσ_unit
  have hQP : Q * P = 1 := by
    change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
    exact CFC.rpow_neg_mul_rpow β' hσ_unit
  have hY_opt : Q * H_opt * Q = CFC.rpow X (α - 1) := by
    rw [hH_opt_def]
    have : Q * (P * CFC.rpow X (α - 1) * P) * Q =
        (Q * P) * CFC.rpow X (α - 1) * (P * Q) := by simp only [mul_assoc]
    rw [this, hQP, hPQ, one_mul, mul_one]
  have hα_sub_neg : (α - 1 : ℝ) < 0 := by linarith
  have hα_sub_ne : (α - 1 : ℝ) ≠ 0 := ne_of_lt hα_sub_neg
  have hα_pos : (0 : ℝ) < α := hα0
  have hYq_eq : CFC.rpow (CFC.rpow X (α - 1)) (α / (α - 1)) = CFC.rpow X α := by
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow X (α - 1) (α / (α - 1)) hX_unit hα_sub_ne]
    congr 1
    rw [mul_comm]; exact div_mul_cancel₀ α hα_sub_ne
  have hXX_eq : X * CFC.rpow X (α - 1) = CFC.rpow X α := by
    simp only [CFC.rpow_eq_pow]
    conv_lhs => lhs; rw [show X = X ^ (1 : ℝ) from (CFC.rpow_one X hX_nn).symm]
    rw [← CFC.rpow_add hX_unit]
    congr 1; ring
  have hTr_Hρ : Tr (H_opt * ρ) = Tr (X * CFC.rpow X (α - 1)) := by
    rw [hH_opt_def]
    have : Tr (P * CFC.rpow X (α - 1) * P * ρ) =
        Tr (P * ρ * P * CFC.rpow X (α - 1)) := by
      calc Tr (P * CFC.rpow X (α - 1) * P * ρ)
          = Tr (ρ * (P * CFC.rpow X (α - 1) * P)) := (trace_mul_comm _ _).symm
        _ = Tr (ρ * P * (CFC.rpow X (α - 1) * P)) := by simp only [mul_assoc]
        _ = Tr ((CFC.rpow X (α - 1) * P) * (ρ * P)) := trace_mul_comm _ _
        _ = Tr (CFC.rpow X (α - 1) * (P * (ρ * P))) := by simp only [mul_assoc]
        _ = Tr (P * (ρ * P) * CFC.rpow X (α - 1)) := (trace_mul_comm _ _).symm
        _ = Tr (P * ρ * P * CFC.rpow X (α - 1)) := by simp only [mul_assoc]
    rw [this, hX_def]
  have hexp : (α - 1 : ℝ) / (2 * α) = -β' := by rw [hβ'_def]; ring
  unfold quasiVar sandwichedQuasi
  rw [hexp, hY_opt, hYq_eq, hTr_Hρ, hXX_eq]
  set T := Tr (CFC.rpow X α)
  push_cast; ring

omit [Nontrivial ℋ] in
private lemma isPositive_of_pdSetLM {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    A.IsPositive :=
  (LinearMap.nonneg_iff_isPositive A).mp (nonneg_of_pdSetLM hA)

omit [Nontrivial ℋ] in
lemma trace_H_mul_combo_re (H ρ₁ ρ₂ : L ℋ) (θ : ℝ) :
    (Tr (H * ((1 - θ) • ρ₁ + θ • ρ₂))).re =
    (1 - θ) * (Tr (H * ρ₁)).re + θ * (Tr (H * ρ₂)).re := by
  rw [mul_add, mul_smul_comm, mul_smul_comm]
  exact trace_re_convex_combo θ (H * ρ₁) (H * ρ₂)

/-- Joint convexity of `(ρ, σ) ↦ Re quasiVar α ρ σ H` on `pdSetLM × pdSetLM` for a fixed
    pd `H` and `α > 1`. The `ρ`-term is linear, the `σ`-term concave with coefficient
    `−(α−1) < 0`. (Used to extend joint convexity to the psd cone in the DPI proof.) -/
theorem quasiVar_re_jointlyConvex_pdSetLM {α : ℝ} (hα : 1 < α)
    {H : L ℋ} (hH : H ∈ pdSetLM (ℋ := ℋ)) :
    JointlyConvexOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ))
      (fun ρ σ => (quasiVar α ρ σ H).re) := by
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [smul_eq_mul]
  have hα0 : (0 : ℝ) < α := by linarith
  have hα_ne1 : α ≠ 1 := ne_of_gt hα
  have hα_ge : (1 : ℝ) / 2 ≤ α := by linarith
  set ρ_c := (1 - θ) • ρ₁ + θ • ρ₂ with hρc_def
  set σ_c := (1 - θ) • σ₁ + θ • σ₂ with hσc_def
  have h_sigma_concave := sigma_term_concaveOn hα0 hα_ne1 hα_ge hH
  have h_sigma_ineq : (1 - θ) * (Tr (CFC.rpow (CFC.rpow σ₁ ((α - 1) / (2 * α)) * H *
          CFC.rpow σ₁ ((α - 1) / (2 * α))) (α / (α - 1)))).re +
      θ * (Tr (CFC.rpow (CFC.rpow σ₂ ((α - 1) / (2 * α)) * H *
          CFC.rpow σ₂ ((α - 1) / (2 * α))) (α / (α - 1)))).re ≤
      (Tr (CFC.rpow (CFC.rpow σ_c ((α - 1) / (2 * α)) * H *
          CFC.rpow σ_c ((α - 1) / (2 * α))) (α / (α - 1)))).re :=
    h_sigma_concave.2 hσ₁ hσ₂ (by linarith : (0 : ℝ) ≤ 1 - θ) hθ0 (by linarith)
  have h_trace_lin : (Tr (H * ρ_c)).re = (1 - θ) * (Tr (H * ρ₁)).re + θ * (Tr (H * ρ₂)).re := by
    change (Tr (H * ((1 - θ) • ρ₁ + θ • ρ₂))).re = _
    exact trace_H_mul_combo_re H ρ₁ ρ₂ θ
  change (quasiVar α ρ_c σ_c H).re ≤
    (1 - θ) * (quasiVar α ρ₁ σ₁ H).re + θ * (quasiVar α ρ₂ σ₂ H).re
  unfold quasiVar
  simp only [Complex.sub_re, Complex.re_ofReal_mul]
  have hα1_pos : (0 : ℝ) < α - 1 := by linarith
  nlinarith [h_trace_lin, h_sigma_ineq]

set_option backward.isDefEq.respectTransparency false in
/-- Joint convexity of `(ρ, σ) ↦ Re Q_α(ρ‖σ)` on `pdSetLM × pdSetLM` for `α > 1`. -/
theorem sandwichedQuasi_re_jointlyConvex {α : ℝ} (hα : 1 < α) :
    JointlyConvexOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ))
      (fun ρ σ => (sandwichedQuasi (ℋ := ℋ) α ρ σ).re) := by
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [smul_eq_mul]
  set ρ_c := (1 - θ) • ρ₁ + θ • ρ₂
  set σ_c := (1 - θ) • σ₁ + θ • σ₂
  have hρ_c : ρ_c ∈ pdSetLM (ℋ := ℋ) := pdSetLM_convexCombo hρ₁ hρ₂ hθ0 hθ1
  have hσ_c : σ_c ∈ pdSetLM (ℋ := ℋ) := pdSetLM_convexCombo hσ₁ hσ₂ hθ0 hθ1
  set H_c := quasiVarOpt α ρ_c σ_c
  have hH_c_pd := quasiVarOpt_pdSetLM (by linarith : (0 : ℝ) < α) (ne_of_gt hα) hρ_c hσ_c
  have hH_c_pos := isPositive_of_pdSetLM hH_c_pd
  have hH_c_eq := quasiVarOpt_eq_quasi_gt hα hρ_c hσ_c
  have h_combo_eq : (sandwichedQuasi α ρ_c σ_c).re = (quasiVar α ρ_c σ_c H_c).re := by
    rw [← hH_c_eq]
  have h_ub1 : (quasiVar α ρ₁ σ₁ H_c).re ≤ (sandwichedQuasi α ρ₁ σ₁).re :=
    (RCLike.le_iff_re_im.mp (quasiVar_le_quasi hα (isPositive_of_pdSetLM hρ₁)
      (isPositive_of_pdSetLM hσ₁) hH_c_pos (isUnit_of_pdSetLM hσ₁))).1
  have h_ub2 : (quasiVar α ρ₂ σ₂ H_c).re ≤ (sandwichedQuasi α ρ₂ σ₂).re :=
    (RCLike.le_iff_re_im.mp (quasiVar_le_quasi hα (isPositive_of_pdSetLM hρ₂)
      (isPositive_of_pdSetLM hσ₂) hH_c_pos (isUnit_of_pdSetLM hσ₂))).1
  have hα0 : (0 : ℝ) < α := by linarith
  have hα_ne1 : α ≠ 1 := ne_of_gt hα
  have hα_ge : (1 : ℝ) / 2 ≤ α := by linarith
  have h_sigma_concave := sigma_term_concaveOn hα0 hα_ne1 hα_ge hH_c_pd
  have h_sigma_ineq : (1 - θ) * (Tr (CFC.rpow (CFC.rpow σ₁ ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ₁ ((α - 1) / (2 * α))) (α / (α - 1)))).re +
      θ * (Tr (CFC.rpow (CFC.rpow σ₂ ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ₂ ((α - 1) / (2 * α))) (α / (α - 1)))).re ≤
      (Tr (CFC.rpow (CFC.rpow σ_c ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ_c ((α - 1) / (2 * α))) (α / (α - 1)))).re :=
    h_sigma_concave.2 hσ₁ hσ₂ (by linarith : 0 ≤ 1 - θ) hθ0 (by linarith)
  have h_trace_lin : (Tr (H_c * ρ_c)).re =
      (1 - θ) * (Tr (H_c * ρ₁)).re + θ * (Tr (H_c * ρ₂)).re := by
    change (Tr (H_c * ((1 - θ) • ρ₁ + θ • ρ₂))).re = _
    exact trace_H_mul_combo_re H_c ρ₁ ρ₂ θ
  have h_convex : (quasiVar α ρ_c σ_c H_c).re ≤
      (1 - θ) * (quasiVar α ρ₁ σ₁ H_c).re + θ * (quasiVar α ρ₂ σ₂ H_c).re := by
    unfold quasiVar
    simp only [Complex.sub_re, Complex.re_ofReal_mul]
    have hα1_pos : (0 : ℝ) < α - 1 := by linarith
    nlinarith [h_trace_lin, h_sigma_ineq]
  rw [h_combo_eq]
  calc (quasiVar α ρ_c σ_c H_c).re
      ≤ (1 - θ) * (quasiVar α ρ₁ σ₁ H_c).re + θ * (quasiVar α ρ₂ σ₂ H_c).re := h_convex
    _ ≤ (1 - θ) * (sandwichedQuasi α ρ₁ σ₁).re + θ * (sandwichedQuasi α ρ₂ σ₂).re := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h_ub1 (by linarith)
        · exact mul_le_mul_of_nonneg_left h_ub2 hθ0

set_option backward.isDefEq.respectTransparency false in
/-- Joint concavity of `(ρ, σ) ↦ Re Q_α(ρ‖σ)` on `pdSetLM × pdSetLM` for `1/2 ≤ α < 1`. -/
theorem sandwichedQuasi_re_jointlyConcave {α : ℝ} (hα_ge : 1 / 2 ≤ α) (hα_lt : α < 1) :
    JointlyConcaveOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ))
      (fun ρ σ => (sandwichedQuasi (ℋ := ℋ) α ρ σ).re) := by
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [smul_eq_mul]
  set ρ_c := (1 - θ) • ρ₁ + θ • ρ₂
  set σ_c := (1 - θ) • σ₁ + θ • σ₂
  have hρ_c : ρ_c ∈ pdSetLM (ℋ := ℋ) := pdSetLM_convexCombo hρ₁ hρ₂ hθ0 hθ1
  have hσ_c : σ_c ∈ pdSetLM (ℋ := ℋ) := pdSetLM_convexCombo hσ₁ hσ₂ hθ0 hθ1
  have hα0 : (0 : ℝ) < α := by linarith
  have hα_ne1 : α ≠ 1 := ne_of_lt hα_lt
  set H_c := quasiVarOpt α ρ_c σ_c
  have hH_c_pd := quasiVarOpt_pdSetLM hα0 hα_ne1 hρ_c hσ_c
  have hH_c_pos := isPositive_of_pdSetLM hH_c_pd
  have hH_c_unit := isUnit_of_pdSetLM hH_c_pd
  have hH_c_eq := quasiVarOpt_eq_quasi_lt hα0 hα_lt hρ_c hσ_c
  have h_combo_eq : (sandwichedQuasi α ρ_c σ_c).re = (quasiVar α ρ_c σ_c H_c).re := by
    rw [← hH_c_eq]
  have h_lb1 : (sandwichedQuasi α ρ₁ σ₁).re ≤ (quasiVar α ρ₁ σ₁ H_c).re :=
    (RCLike.le_iff_re_im.mp (quasi_le_quasiVar hα0 hα_lt (isPositive_of_pdSetLM hρ₁)
      (isPositive_of_pdSetLM hσ₁) hH_c_pos (isUnit_of_pdSetLM hσ₁) hH_c_unit)).1
  have h_lb2 : (sandwichedQuasi α ρ₂ σ₂).re ≤ (quasiVar α ρ₂ σ₂ H_c).re :=
    (RCLike.le_iff_re_im.mp (quasi_le_quasiVar hα0 hα_lt (isPositive_of_pdSetLM hρ₂)
      (isPositive_of_pdSetLM hσ₂) hH_c_pos (isUnit_of_pdSetLM hσ₂) hH_c_unit)).1
  have h_sigma_concave := sigma_term_concaveOn hα0 hα_ne1 hα_ge hH_c_pd
  have h_sigma_ineq : (1 - θ) * (Tr (CFC.rpow (CFC.rpow σ₁ ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ₁ ((α - 1) / (2 * α))) (α / (α - 1)))).re +
      θ * (Tr (CFC.rpow (CFC.rpow σ₂ ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ₂ ((α - 1) / (2 * α))) (α / (α - 1)))).re ≤
      (Tr (CFC.rpow (CFC.rpow σ_c ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ_c ((α - 1) / (2 * α))) (α / (α - 1)))).re :=
    h_sigma_concave.2 hσ₁ hσ₂ (by linarith : 0 ≤ 1 - θ) hθ0 (by linarith)
  have h_trace_lin : (Tr (H_c * ρ_c)).re =
      (1 - θ) * (Tr (H_c * ρ₁)).re + θ * (Tr (H_c * ρ₂)).re := by
    change (Tr (H_c * ((1 - θ) • ρ₁ + θ • ρ₂))).re = _
    exact trace_H_mul_combo_re H_c ρ₁ ρ₂ θ
  have h_concave : (1 - θ) * (quasiVar α ρ₁ σ₁ H_c).re + θ * (quasiVar α ρ₂ σ₂ H_c).re ≤
      (quasiVar α ρ_c σ_c H_c).re := by
    unfold quasiVar
    simp only [Complex.sub_re, Complex.re_ofReal_mul]
    have hα1_neg : α - 1 < (0 : ℝ) := by linarith
    nlinarith [h_trace_lin, h_sigma_ineq]
  rw [h_combo_eq]
  calc (1 - θ) * (sandwichedQuasi α ρ₁ σ₁).re + θ * (sandwichedQuasi α ρ₂ σ₂).re
      ≤ (1 - θ) * (quasiVar α ρ₁ σ₁ H_c).re + θ * (quasiVar α ρ₂ σ₂ H_c).re := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h_lb1 (by linarith)
        · exact mul_le_mul_of_nonneg_left h_lb2 hθ0
    _ ≤ (quasiVar α ρ_c σ_c H_c).re := h_concave

end JointConvexity

section UnitaryInvariance

universe u₄

variable {ℋ : Type u₄} [Qudit ℋ]

open scoped NNReal

instance : IsScalarTower ℝ≥0 ℂ (L ℋ) where
  smul_assoc r c x := by
    change (algebraMap ℝ≥0 ℂ r * c) • x = (algebraMap ℝ≥0 ℂ r) • (c • x)
    rw [mul_smul]

/-- Trace is invariant under unitary conjugation: Tr(U A U†) = Tr(A). -/
lemma trace_unitary_conj (A : L ℋ) (U : unitary (L ℋ)) :
    Tr ((U : L ℋ) * A * (star U : L ℋ)) = Tr A :=
  LinearMap.trace_map (Unitary.conjStarAlgAut ℂ (L ℋ) U) A

/-- CFC.rpow commutes with unitary conjugation: (U A U†)^p = U A^p U†. -/
private lemma rpow_unitary_conj (U : unitary (L ℋ)) (A : L ℋ) (p : ℝ) :
    CFC.rpow ((U : L ℋ) * A * (star U : L ℋ)) p =
      (U : L ℋ) * CFC.rpow A p * (star U : L ℋ) := by
  let φ := Unitary.conjStarAlgAut ℂ (L ℋ) U
  simp only [CFC.rpow]
  let f : ℝ≥0 → ℝ≥0 := fun x => x ^ p
  change cfc f (φ A) = φ (cfc f A)
  have hnn : (0 : L ℋ) ≤ φ A ↔ (0 : L ℋ) ≤ A := by
    conv_lhs => rw [show (0 : L ℋ) = φ 0 from (map_zero φ).symm]
    exact OrderIsoClass.map_le_map_iff φ
  have hspec : spectrum ℝ≥0 (φ A) = spectrum ℝ≥0 A :=
    AlgEquiv.spectrum_eq (φ.restrictScalars ℝ≥0).toAlgEquiv A
  by_cases h : (0 ≤ A) ∧ ContinuousOn f (spectrum ℝ≥0 A)
  · exact (StarAlgHomClass.map_cfc (S := ℂ) φ f A h.2 (map_continuous φ) h.1
      (hnn.mpr h.1)).symm
  · rw [cfc_apply_of_not_and A h, map_zero, cfc_apply_of_not_and]
    rwa [hnn, hspec]

/-- Unitary invariance of sandwichedQuasi:
    Q_α(U ρ U†‖U σ U†) = Q_α(ρ‖σ). -/
theorem sandwichedQuasi_unitary_conj (α : ℝ) (ρ σ : L ℋ) (U : unitary (L ℋ)) :
    sandwichedQuasi α ((U : L ℋ) * ρ * (star U : L ℋ))
        ((U : L ℋ) * σ * (star U : L ℋ)) =
      sandwichedQuasi α ρ σ := by
  let φ := Unitary.conjStarAlgAut ℂ (L ℋ) U
  change sandwichedQuasi α (φ ρ) (φ σ) = sandwichedQuasi α ρ σ
  unfold sandwichedQuasi
  set β := (1 - α) / (2 * α)
  set P := CFC.rpow σ β
  rw [show CFC.rpow (φ σ) β = φ (CFC.rpow σ β) from rpow_unitary_conj U σ β]
  have h_inner : φ P * φ ρ * φ P = φ (P * ρ * P) := by
    simp only [map_mul]
  rw [h_inner, show CFC.rpow (φ (P * ρ * P)) α = φ (CFC.rpow (P * ρ * P) α)
    from rpow_unitary_conj U (P * ρ * P) α]
  exact trace_unitary_conj _ U

/-- Unitary invariance of sandwiched Rényi relative entropy:
    D_α(U ρ U†‖U σ U†) = D_α(ρ‖σ). -/
theorem sandwichedRenyiDiv_unitary_conj (α : ℝ) (ρ σ : L ℋ) (U : unitary (L ℋ)) :
    sandwichedRenyiDiv α ((U : L ℋ) * ρ * (star U : L ℋ))
        ((U : L ℋ) * σ * (star U : L ℋ)) =
      sandwichedRenyiDiv α ρ σ := by
  unfold sandwichedRenyiDiv
  rw [sandwichedQuasi_unitary_conj, trace_unitary_conj]

end UnitaryInvariance

section TensorMultiplicativity

open QuantumChannel TensorProduct

variable {ℋ₁ : Type*} {ℋ₂ : Type*} [Qudit ℋ₁] [Qudit ℋ₂]

set_option backward.isDefEq.respectTransparency false in
/-- Tensor multiplicativity of sandwichedQuasi:
    Q_α(ρ₁ ⊗ ρ₂ ‖ σ₁ ⊗ σ₂) = Q_α(ρ₁ ‖ σ₁) · Q_α(ρ₂ ‖ σ₂). -/
theorem sandwichedQuasi_tensor (α : ℝ) (ρ₁ σ₁ : L ℋ₁) (ρ₂ σ₂ : L ℋ₂)
    (hρ₁ : 0 ≤ ρ₁) (hσ₁ : 0 ≤ σ₁) (hρ₂ : 0 ≤ ρ₂) (hσ₂ : 0 ≤ σ₂) :
    sandwichedQuasi α (TensorProduct.map ρ₁ ρ₂ : L (ℋ₁ ⊗[ℂ] ℋ₂))
        (TensorProduct.map σ₁ σ₂) =
      sandwichedQuasi α ρ₁ σ₁ * sandwichedQuasi α ρ₂ σ₂ := by
  unfold sandwichedQuasi
  set β := (1 - α) / (2 * α)
  set P₁ := CFC.rpow σ₁ β
  set P₂ := CFC.rpow σ₂ β
  rw [TensorCFC.rpow_tensorProduct σ₁ σ₂ β hσ₁ hσ₂,
    show TensorProduct.map P₁ P₂ * TensorProduct.map ρ₁ ρ₂ * TensorProduct.map P₁ P₂ =
      TensorProduct.map (P₁ * ρ₁ * P₁) (P₂ * ρ₂ * P₂) from by
        rw [← TensorProduct.map_mul, ← TensorProduct.map_mul],
    TensorCFC.rpow_tensorProduct (P₁ * ρ₁ * P₁) (P₂ * ρ₂ * P₂) α
      (conjugate_nonneg_of_nonneg hρ₁ CFC.rpow_nonneg)
      (conjugate_nonneg_of_nonneg hρ₂ CFC.rpow_nonneg)]
  exact LinearMap.trace_tensorProduct'
    (CFC.rpow (P₁ * ρ₁ * P₁) α) (CFC.rpow (P₂ * ρ₂ * P₂) α)

/-- Tensor additivity of sandwichedRenyiDiv:
    D_α(ρ₁ ⊗ ρ₂ ‖ σ₁ ⊗ σ₂) = D_α(ρ₁ ‖ σ₁) + D_α(ρ₂ ‖ σ₂). -/
theorem sandwichedRenyiDiv_tensor (α : ℝ) (ρ₁ σ₁ : L ℋ₁) (ρ₂ σ₂ : L ℋ₂)
    (hρ₁ : 0 ≤ ρ₁) (hσ₁ : 0 ≤ σ₁) (hρ₂ : 0 ≤ ρ₂) (hσ₂ : 0 ≤ σ₂)
    (hQ₁ : (sandwichedQuasi α ρ₁ σ₁).re ≠ 0)
    (hQ₂ : (sandwichedQuasi α ρ₂ σ₂).re ≠ 0)
    (hT₁ : (Tr ρ₁).re ≠ 0) (hT₂ : (Tr ρ₂).re ≠ 0)
    (hQ₁im : (sandwichedQuasi α ρ₁ σ₁).im = 0)
    (hQ₂im : (sandwichedQuasi α ρ₂ σ₂).im = 0)
    (hT₁im : (Tr ρ₁).im = 0) (hT₂im : (Tr ρ₂).im = 0) :
    sandwichedRenyiDiv α (TensorProduct.map ρ₁ ρ₂ : L (ℋ₁ ⊗[ℂ] ℋ₂))
        (TensorProduct.map σ₁ σ₂) =
      sandwichedRenyiDiv α ρ₁ σ₁ + sandwichedRenyiDiv α ρ₂ σ₂ := by
  unfold sandwichedRenyiDiv
  rw [sandwichedQuasi_tensor α ρ₁ σ₁ ρ₂ σ₂ hρ₁ hσ₁ hρ₂ hσ₂,
    LinearMap.trace_tensorProduct' ρ₁ ρ₂]
  have hre_mul_Q : (sandwichedQuasi α ρ₁ σ₁ * sandwichedQuasi α ρ₂ σ₂).re =
      (sandwichedQuasi α ρ₁ σ₁).re * (sandwichedQuasi α ρ₂ σ₂).re := by
    simp [Complex.mul_re, hQ₁im, hQ₂im]
  have hre_mul_T : ((Tr ρ₁) * (Tr ρ₂)).re = (Tr ρ₁).re * (Tr ρ₂).re := by
    simp [Complex.mul_re, hT₁im, hT₂im]
  rw [hre_mul_Q, hre_mul_T, mul_div_mul_comm, Real.log_mul
    (div_ne_zero hQ₁ hT₁) (div_ne_zero hQ₂ hT₂), mul_add]

end TensorMultiplicativity

section Monotonicity

open MeasureTheory HaarUnitary QuantumChannel TensorProduct

universe u₅

variable {ℋ : Type u₅} [Qudit ℋ] [Nontrivial ℋ]

set_option linter.style.longLine false

omit [Nontrivial ℋ] in
/-- Pure-state Stinespring isometry from a Kraus family `A : κ → (ℋ →ₗ[ℂ] 𝒦)`
    (possibly different input/output spaces) satisfying `Σ_a A_a* A_a = I_ℋ`.
    The map `V ψ := Σ_a (A_a ψ) ⊗ e_a` is a linear isometry `ℋ → 𝒦 ⊗ ℂ^κ`
    realizing the channel `γ ↦ Σ_a A_a γ A_a*` as `TrRight(V γ V*)`. -/
private lemma kraus_to_pure_stinespring_isometry
    {𝒦 : Type u₅} [Qudit 𝒦]
    {κ : Type u₅} [Fintype κ] [DecidableEq κ]
    (A : κ → (ℋ →ₗ[ℂ] 𝒦))
    (hSumAA : (∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) = (1 : L ℋ)) :
    ∃ V : ℋ →ₗ[ℂ] 𝒦 ⊗[ℂ] EuclideanSpace ℂ κ,
      (LinearMap.adjoint V).comp V = (1 : L ℋ) ∧
      ∀ γ : L ℋ,
        (∑ a : κ, (A a).comp (γ.comp (LinearMap.adjoint (A a)))) =
          TrRight ((V.comp γ).comp (LinearMap.adjoint V)) := by
  classical
  -- The Stinespring isometry from QuantumChannel.lean.
  refine ⟨krausToStinespringOperator (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A, ?_, ?_⟩
  · -- `V* V = Σ_a A_a* A_a = 1` by `hSumAA`.
    set V := krausToStinespringOperator (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A with hV_def
    apply LinearMap.ext
    intro ψ
    -- Reduce to computing `(V* V) ψ` directly.
    have hVψ : V ψ = ∑ a : κ, (A a ψ) ⊗ₜ[ℂ] (EuclideanSpace.basisFun κ ℂ a) :=
      krausToStinespringOperator_apply (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A ψ
    have hcomp : (V.adjoint.comp V) ψ = V.adjoint (V ψ) := rfl
    rw [hcomp, hVψ, map_sum]
    have hpiece : ∀ a : κ,
        V.adjoint ((A a ψ) ⊗ₜ[ℂ] (EuclideanSpace.basisFun κ ℂ a)) =
          (LinearMap.adjoint (A a)) (A a ψ) := by
      intro a
      simpa [hV_def] using
        adjoint_krausToStinespringOperator_tmul_basisFun
          (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A (A a ψ) a
    -- Replace each summand and recognize `Σ_a A_a* A_a = 1`.
    simp_rw [hpiece]
    have hSumApp :
        (∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) ψ = (1 : L ℋ) ψ := by
      rw [hSumAA]
    -- LHS sum equals `(∑ a, A_a* ∘ A_a) ψ`.
    have hsum_eq :
        (∑ a : κ, (LinearMap.adjoint (A a)) (A a ψ)) =
          (∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) ψ := by
      simp [LinearMap.sum_apply]
    rw [hsum_eq, hSumApp]
  · -- Partial-trace identity: this is exactly `trRight_kraus`.
    intro γ
    have h := trRight_kraus (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A γ
    exact h.symm

/-- **Stinespring dilation theorem (Form A, isometric / pure-environment form).**

    Every quantum channel `E : CPTP ℋ 𝒦` (possibly different input/output
    spaces) admits an *isometric* Stinespring dilation: there exists a
    finite-dimensional environment Hilbert space
    `ℋ_env`, a linear map `V : ℋ →ₗ[ℂ] (𝒦 ⊗ ℋ_env)` satisfying
      `V*V = I_ℋ` (isometry),
    and
      `E(γ) = TrRight(V γ V*)` for every `γ : L ℋ`,
    where `TrRight` traces out the *second* (environment) factor.

    This is the form directly available from
    `QuantumChannel.cp_to_stinespring` strengthened by trace preservation,
    and matches **Watrous Cor. 2.27** in its pure-environment incarnation
    (also Frank–Lieb arXiv:1306.5358 with `τ` chosen pure).

    The previous unitary form
      `E(γ) = Tr₂(U (τ ⊗ γ) U*)`
    with positive-definite `τ` on the environment (Form B / Naimark) is
    strictly stronger and is **not** used downstream after the present
    refactor; the data-processing inequality is proved directly from this
    Form A statement following the Frank–Lieb scheme. -/
theorem CPTP.exists_stinespring_dilation {𝒦 : Type u₅} [Qudit 𝒦] (E : CPTP ℋ 𝒦) :
    ∃ (ℋ_env : Type u₅) (_ : Qudit ℋ_env) (_ : Nontrivial ℋ_env)
      (V : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env)),
        (LinearMap.adjoint V).comp V = (1 : L ℋ) ∧
        ∀ γ : L ℋ,
          E.toFun γ = TrRight ((V.comp γ).comp (LinearMap.adjoint V)) := by
  classical
  -- Extract a Kraus representation of E.
  have hE_cp : IsCompletelyPositive E.toLinearMap :=
    ⟨E.toCompletelyPositiveMap, rfl⟩
  let bℋ := Module.Free.chooseBasis ℂ ℋ
  have hKraus : HasKraus (E.toLinearMap) :=
    cp_to_kraus bℋ E.toLinearMap hE_cp
  obtain ⟨κ, hκ_dec, hκ_fin, A, hA_eq⟩ := hKraus
  letI : DecidableEq κ := hκ_dec
  letI : Fintype κ := hκ_fin
  -- Trace preservation gives Σ_a A_a* A_a = 1 (same derivation as before).
  set S : L ℋ := ∑ a : κ, (LinearMap.adjoint (A a)).comp (A a) with hS_def
  have hSρ_tr : ∀ ρ : L ℋ, Tr (S * ρ) = Tr ρ := by
    intro ρ
    have htr : Tr ρ = Tr (E.toLinearMap ρ) := E.trace_map ρ
    have hKr : E.toLinearMap ρ =
        ∑ a : κ, (A a).comp (ρ.comp (LinearMap.adjoint (A a))) := hA_eq ρ
    have hcycle : ∀ a : κ,
        Tr ((A a).comp (ρ.comp (LinearMap.adjoint (A a)))) =
          Tr (((LinearMap.adjoint (A a)).comp (A a)) * ρ) := by
      intro a
      -- Cyclicity across the mixed spaces `ℋ → 𝒦`:
      -- `Tr_𝒦 (Aₐ ∘ ρ ∘ Aₐ*) = Tr_ℋ ((ρ ∘ Aₐ*) ∘ Aₐ) = Tr_ℋ (ρ ∘ (Aₐ* ∘ Aₐ))`.
      rw [← LinearMap.trace_comp_comm' (A a) (ρ.comp (LinearMap.adjoint (A a))),
          LinearMap.comp_assoc, Module.End.mul_eq_comp]
      -- Now `Tr (ρ ∘ (Aₐ* ∘ Aₐ)) = Tr ((Aₐ* ∘ Aₐ) ∘ ρ)`, a cyclic swap within `L ℋ`.
      exact (LinearMap.trace_comp_comm' ρ ((LinearMap.adjoint (A a)).comp (A a))).symm
    calc Tr (S * ρ)
        = Tr ((∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) * ρ) := by rw [hS_def]
      _ = ∑ a : κ, Tr (((LinearMap.adjoint (A a)).comp (A a)) * ρ) := by
          rw [Finset.sum_mul]; exact map_sum Tr _ _
      _ = ∑ a : κ, Tr ((A a).comp (ρ.comp (LinearMap.adjoint (A a)))) := by
          refine Finset.sum_congr rfl ?_
          intro a _; rw [(hcycle a).symm]
      _ = Tr (∑ a : κ, (A a).comp (ρ.comp (LinearMap.adjoint (A a)))) := by
          rw [map_sum Tr]
      _ = Tr (E.toLinearMap ρ) := by rw [← hKr]
      _ = Tr ρ := htr.symm
  have hSumAA : S = (1 : L ℋ) := by
    apply LinearMap.ext
    intro v
    refine ext_inner_left ℂ ?_
    intro w
    have h_compOuter : ∀ M : L ℋ, M.comp (outer_product w v) = outer_product w (M v) := by
      intro M
      ext x
      simp [outer_product_eq_rankOne]
    have htrace_eq : Tr (S * (outer_product w v)) = Tr (outer_product w v) :=
      hSρ_tr (outer_product w v)
    have hLHS : Tr (S * (outer_product w v)) = inner ℂ w (S v) := by
      change Tr (S.comp (outer_product w v)) = inner ℂ w (S v)
      rw [h_compOuter S, trace_outer_product]
    have hRHS : Tr (outer_product w v) = inner ℂ w v := trace_outer_product w v
    have h1v : (1 : L ℋ) v = v := rfl
    rw [h1v]
    rw [← hLHS, htrace_eq, hRHS]
  -- The environment is `EuclideanSpace ℂ κ`. We need it `Nontrivial`, which is
  -- equivalent to `κ` being nonempty. The hypothesis `Σ A_a* A_a = 1 ≠ 0`
  -- (since `ℋ` is nontrivial, so `1 ≠ 0`) forces `κ` to be nonempty.
  have hκ_nonempty : Nonempty κ := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hS_zero : S = 0 := by
      simp [hS_def, Finset.sum_empty]
    have h1ne : (1 : L ℋ) ≠ 0 := one_ne_zero
    apply h1ne
    rw [← hSumAA, hS_zero]
  haveI : Nonempty κ := hκ_nonempty
  haveI : Nontrivial (EuclideanSpace ℂ κ) :=
    Module.nontrivial_of_finrank_pos
      (by
        rw [finrank_euclideanSpace]
        exact Fintype.card_pos)
  -- Pure-state Stinespring isometry from the Kraus family.
  obtain ⟨V, hV_iso, hV_eq⟩ :=
    kraus_to_pure_stinespring_isometry (ℋ := ℋ) A hSumAA
  refine ⟨EuclideanSpace ℂ κ, inferInstance, inferInstance, V, hV_iso, ?_⟩
  intro γ
  have hKraus_γ : E.toFun γ =
      ∑ a : κ, (A a).comp (γ.comp (LinearMap.adjoint (A a))) := hA_eq γ
  rw [hKraus_γ, hV_eq γ]

omit [Nontrivial ℋ] in
/-- For any positive-definite operator `τ` and any nonzero exponent `α`,
    `sandwichedQuasi α τ τ = Tr τ`. In particular, for a density operator
    (`Tr τ = 1`) this gives `Q_α(τ‖τ) = 1`. -/
lemma sandwichedQuasi_self_pdSetLM
    {α : ℝ} (hα_ne : α ≠ 0) {τ : L ℋ} (hτ : τ ∈ pdSetLM (ℋ := ℋ)) :
    sandwichedQuasi α τ τ = Tr τ := by
  unfold sandwichedQuasi
  have hτ_nn := nonneg_of_pdSetLM hτ
  have hτ_unit := isUnit_of_pdSetLM hτ
  have h2α_ne : (2 * α : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hα_ne
  set β : ℝ := (1 - α) / (2 * α) with hβ_def
  have hexp1 : β + 1 + β = 1 / α := by rw [hβ_def]; field_simp; ring
  -- τ^β · τ · τ^β = τ^(1/α)
  have h_middle : CFC.rpow τ β * τ * CFC.rpow τ β = CFC.rpow τ (1 / α) := by
    have h_τ1 : τ = CFC.rpow τ 1 := (CFC.rpow_one τ hτ_nn).symm
    calc CFC.rpow τ β * τ * CFC.rpow τ β
        = CFC.rpow τ β * CFC.rpow τ 1 * CFC.rpow τ β := by rw [← h_τ1]
      _ = CFC.rpow τ (β + 1) * CFC.rpow τ β := by
          simp only [CFC.rpow_eq_pow]
          rw [← CFC.rpow_add hτ_unit]
      _ = CFC.rpow τ (β + 1 + β) := by
          simp only [CFC.rpow_eq_pow]
          rw [← CFC.rpow_add hτ_unit]
      _ = CFC.rpow τ (1 / α) := by rw [hexp1]
  rw [h_middle]
  -- (τ^(1/α))^α = τ
  have h_outer : CFC.rpow (CFC.rpow τ (1 / α)) α = τ := by
    have h1α_ne : (1 / α : ℝ) ≠ 0 := one_div_ne_zero hα_ne
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow τ (1 / α) α hτ_unit h1α_ne]
    rw [show (1 / α) * α = 1 from by field_simp]
    exact CFC.rpow_one τ hτ_nn
  rw [h_outer]

/-- The maximally mixed state on a finite-dimensional Hilbert space is positive definite. -/
lemma maxmixed_pdSetLM (ℋ_env : Type u₅) [Qudit ℋ_env] [Nontrivial ℋ_env] :
    ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) ∈ pdSetLM (ℋ := ℋ_env) := by
  set d : ℕ := Module.finrank ℂ ℋ_env
  have hd_pos : 0 < d := Module.finrank_pos
  have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
  set c : ℂ := (d : ℂ)⁻¹
  have hc_ne : c ≠ 0 := inv_ne_zero hd_ne
  -- `0 ≤ c` in `ℂ` (using `ComplexOrder`): `c.re ≥ 0` and `c.im = 0`.
  have hc_nn : (0 : ℂ) ≤ c := by
    refine ⟨?_, ?_⟩
    · change 0 ≤ ((d : ℂ)⁻¹).re
      rw [Complex.inv_re]
      have hd_re : ((d : ℂ)).re = (d : ℝ) := Complex.natCast_re d
      have hd_im : ((d : ℂ)).im = 0 := Complex.natCast_im d
      rw [hd_re,
          show Complex.normSq (d : ℂ) = (d : ℝ)^2 from by
            rw [Complex.normSq_apply, hd_re, hd_im]; ring]
      positivity
    · symm
      change ((d : ℂ)⁻¹).im = 0
      rw [Complex.inv_im]
      simp [Complex.natCast_im]
  -- `(c • 1).IsPositive` via `LinearMap.isPositive_one.smul_of_nonneg`.
  have h_isPos : ((c • (1 : L ℋ_env)) : L ℋ_env).IsPositive :=
    LinearMap.isPositive_one.smul_of_nonneg hc_nn
  have h_nn : (0 : L ℋ_env) ≤ c • (1 : L ℋ_env) :=
    (LinearMap.nonneg_iff_isPositive _).mpr h_isPos
  -- `c • 1` is a unit (inverse is `c⁻¹ • 1`).
  have h_unit : IsUnit (c • (1 : L ℋ_env)) := by
    refine ⟨⟨c • 1, c⁻¹ • 1, ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul_comm, mul_inv_cancel₀ hc_ne, mul_one, one_smul]
    · rw [smul_mul_smul_comm, inv_mul_cancel₀ hc_ne, mul_one, one_smul]
  -- Push positivity and unit-ness through the CLM iso.
  have h_clm_nn : (0 : LownerHeinzTheorem.L ℋ_env) ≤
      (c • (1 : L ℋ_env)).toContinuousLinearMap :=
    map_nonneg (toCLMStarAlgHom (ℋ := ℋ_env)) h_nn
  have h_clm_unit : IsUnit (c • (1 : L ℋ_env)).toContinuousLinearMap :=
    (toCLMStarAlgHom (ℋ := ℋ_env)).toRingHom.isUnit_map h_unit
  have h_clm_sa : IsSelfAdjoint (c • (1 : L ℋ_env)).toContinuousLinearMap :=
    IsSelfAdjoint.of_nonneg h_clm_nn
  refine ⟨h_clm_sa, ?_⟩
  intro r hr
  have h_spec_nn : spectrum ℝ (c • (1 : L ℋ_env)).toContinuousLinearMap ⊆ Set.Ici 0 :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := h_clm_sa)).1 h_clm_nn
  rcases lt_or_eq_of_le (by simpa [Set.Ici] using h_spec_nn hr) with h | h
  · exact h
  · exfalso; rw [← h] at hr
    exact (spectrum.zero_notMem_iff (R := ℝ)).mpr h_clm_unit hr

/-- `TensorProduct.map` preserves `pdSetLM`: the tensor of two positive-definite
    operators is positive-definite. -/
lemma pdSetLM_tensorMap {ℋ₁ ℋ₂ : Type u₅} [Qudit ℋ₁] [Qudit ℋ₂]
    [Nontrivial ℋ₁] [Nontrivial ℋ₂]
    {A : L ℋ₁} {B : L ℋ₂} (hA : A ∈ pdSetLM (ℋ := ℋ₁)) (hB : B ∈ pdSetLM (ℋ := ℋ₂)) :
    (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) ∈ pdSetLM (ℋ := ℋ₁ ⊗[ℂ] ℋ₂) := by
  have hA_nn := nonneg_of_pdSetLM hA
  have hB_nn := nonneg_of_pdSetLM hB
  have hA_unit := isUnit_of_pdSetLM hA
  have hB_unit := isUnit_of_pdSetLM hB
  -- Build the tensor map as `star X * X` for `X = map (sqrt A) (sqrt B)`.
  set sA := CFC.sqrt A
  set sB := CFC.sqrt B
  have hsA_nn : (0 : L ℋ₁) ≤ sA := CFC.sqrt_nonneg A
  have hsB_nn : (0 : L ℋ₂) ≤ sB := CFC.sqrt_nonneg B
  have h_star_map : star (TensorProduct.map sA sB : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      TensorProduct.map sA sB := by
    rw [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map]
    rw [← LinearMap.star_eq_adjoint, ← LinearMap.star_eq_adjoint,
        (IsSelfAdjoint.of_nonneg hsA_nn).star_eq,
        (IsSelfAdjoint.of_nonneg hsB_nn).star_eq]
  have h_tensor_eq : (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      star (TensorProduct.map sA sB) * TensorProduct.map sA sB := by
    rw [h_star_map, ← TensorProduct.map_mul, CFC.sqrt_mul_sqrt_self A, CFC.sqrt_mul_sqrt_self B]
  -- Nonnegativity: `TensorProduct.map A B = star X * X ≥ 0`.
  have h_nn : (0 : L (ℋ₁ ⊗[ℂ] ℋ₂)) ≤ TensorProduct.map A B := by
    rw [h_tensor_eq]; exact star_mul_self_nonneg _
  -- Invertibility: inverse is `TensorProduct.map A⁻¹ B⁻¹` (using `TensorProduct.map_mul`).
  obtain ⟨uA, huA⟩ := hA_unit
  obtain ⟨uB, huB⟩ := hB_unit
  have h_unit : IsUnit (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
    refine ⟨⟨TensorProduct.map A B,
      TensorProduct.map (↑uA⁻¹ : L ℋ₁) (↑uB⁻¹ : L ℋ₂), ?_, ?_⟩, rfl⟩
    · rw [← TensorProduct.map_mul]
      rw [show A * (↑uA⁻¹ : L ℋ₁) = 1 from by
        rw [← huA, Units.mul_inv]]
      rw [show B * (↑uB⁻¹ : L ℋ₂) = 1 from by
        rw [← huB, Units.mul_inv]]
      exact TensorProduct.map_one
    · rw [← TensorProduct.map_mul]
      rw [show (↑uA⁻¹ : L ℋ₁) * A = 1 from by
        rw [← huA, Units.inv_mul]]
      rw [show (↑uB⁻¹ : L ℋ₂) * B = 1 from by
        rw [← huB, Units.inv_mul]]
      exact TensorProduct.map_one
  -- Push to CLM and apply the standard chain.
  have h_clm_nn : (0 : LownerHeinzTheorem.L (ℋ₁ ⊗[ℂ] ℋ₂)) ≤
      (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap :=
    map_nonneg (toCLMStarAlgHom (ℋ := ℋ₁ ⊗[ℂ] ℋ₂)) h_nn
  have h_clm_unit : IsUnit (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap :=
    (toCLMStarAlgHom (ℋ := ℋ₁ ⊗[ℂ] ℋ₂)).toRingHom.isUnit_map h_unit
  have h_clm_sa : IsSelfAdjoint
      (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap :=
    IsSelfAdjoint.of_nonneg h_clm_nn
  refine ⟨h_clm_sa, ?_⟩
  intro r hr
  have h_spec_nn : spectrum ℝ
      (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap ⊆ Set.Ici 0 :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := h_clm_sa)).1 h_clm_nn
  rcases lt_or_eq_of_le (by simpa [Set.Ici] using h_spec_nn hr) with h | h
  · exact h
  · exfalso; rw [← h] at hr
    exact (spectrum.zero_notMem_iff (R := ℝ)).mpr h_clm_unit hr

/-- For any positive-definite operator in `pdSetLM`, the trace is a real positive number.
    Proof: trace = sum of eigenvalues; each eigenvalue is ≥ 0 (from positivity) and ≠ 0
    (from invertibility), hence > 0. The sum over a nonempty index set of positives is positive. -/
lemma trace_re_pos_of_pdSetLM {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    0 < (Tr A).re := by
  have hA_nn := nonneg_of_pdSetLM hA
  have hA_pos : A.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hA_nn
  have hA_sym := hA_pos.isSymmetric
  have hA_unit := isUnit_of_pdSetLM hA
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hn_pos : 0 < n := Module.finrank_pos
  -- Re (Tr A) = ∑ eigenvalues.
  rw [show (Tr A).re = ∑ i, hA_sym.eigenvalues hn i from
        hA_sym.re_trace_eq_sum_eigenvalues hn]
  -- Each eigenvalue is positive; the sum over a nonempty index set is positive.
  have h_nonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn_pos⟩, Finset.mem_univ _⟩
  apply Finset.sum_pos _ h_nonempty
  intro i _
  -- eigenvalues are ≥ 0 from `IsPositive.nonneg_eigenvalues`.
  have hlam_nn : 0 ≤ hA_sym.eigenvalues hn i := hA_pos.nonneg_eigenvalues hn i
  -- eigenvalues are ≠ 0 because `A` is a unit (so `0 ∉ spectrum`).
  rcases lt_or_eq_of_le hlam_nn with hpos | hzero
  · exact hpos
  · exfalso
    have h_eig : Module.End.HasEigenvalue A ((hA_sym.eigenvalues hn i : ℂ)) :=
      hA_sym.hasEigenvalue_eigenvalues hn i
    rw [← hzero] at h_eig
    push_cast at h_eig
    obtain ⟨v, hv_mem, hv_ne⟩ := h_eig.exists_hasEigenvector
    have hAv : A v = 0 := by
      rw [Module.End.mem_eigenspace_iff] at hv_mem
      simpa using hv_mem
    obtain ⟨uA, huA⟩ := hA_unit
    have h_inv_mul : (↑uA⁻¹ : L ℋ) * A = 1 := by rw [← huA, Units.inv_mul]
    have hv_eq : v = ((↑uA⁻¹ : L ℋ) * A) v := by rw [h_inv_mul]; rfl
    rw [show ((↑uA⁻¹ : L ℋ) * A) v = (↑uA⁻¹ : L ℋ) (A v) from rfl, hAv, map_zero] at hv_eq
    exact hv_ne hv_eq

omit [Nontrivial ℋ] in
/-- Unitary conjugation preserves `pdSetLM`. -/
lemma pdSetLM_unitary_conj {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ))
    (V : unitary (L ℋ)) :
    (V : L ℋ) * A * star (V : L ℋ) ∈ pdSetLM (ℋ := ℋ) := by
  -- `pdSetLM_conj` gives `star B * A * B ∈ pdSetLM` when `B` is a unit. Apply with `B = star V`.
  have hV_unit : IsUnit (star (V : L ℋ)) := by
    refine ⟨⟨star (V : L ℋ), (V : L ℋ), ?_, ?_⟩, rfl⟩
    · exact (Unitary.mem_iff.mp V.property).1
    · exact (Unitary.mem_iff.mp V.property).2
  have h := pdSetLM_conj hA hV_unit
  rwa [star_star] at h

/-- The `ℝ≥0`-spectrum of any operator in `pdSetLM` lies in `Set.Ioi 0`. -/
private lemma pdSetLM_spectrum_nnreal_subset_Ioi
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux]
    {A : L ℋ_aux} (hA : A ∈ pdSetLM (ℋ := ℋ_aux)) :
    spectrum ℝ≥0 A ⊆ Set.Ioi 0 := by
  intro r hr
  have hA_unit : IsUnit A := isUnit_of_pdSetLM hA
  have h0_notMem : (0 : ℝ≥0) ∉ spectrum ℝ≥0 A :=
    (spectrum.zero_notMem_iff (R := ℝ≥0)).mpr hA_unit
  rcases lt_or_eq_of_le (zero_le r) with hr_pos | hr_zero
  · exact hr_pos
  · exact absurd (hr_zero ▸ hr) h0_notMem

/-- For each fixed real exponent `p`, the map `A ↦ CFC.rpow A p` is continuous on `pdSetLM`. -/
private lemma rpow_continuousOn_pdSetLM
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux] (p : ℝ) :
    ContinuousOn (fun A : L ℋ_aux => CFC.rpow A p) (pdSetLM (ℋ := ℋ_aux)) := by
  -- `CFC.rpow A p = cfc (· ^ p : ℝ≥0 → ℝ≥0) A`. Apply `ContinuousOn.cfc_nnreal_of_mem_nhdsSet`.
  have h_subset : (⋃ A ∈ pdSetLM (ℋ := ℋ_aux), spectrum ℝ≥0 A) ⊆ Set.Ioi 0 := by
    intro r hr
    rw [Set.mem_iUnion₂] at hr
    obtain ⟨A, hA, hrA⟩ := hr
    exact pdSetLM_spectrum_nnreal_subset_Ioi hA hrA
  have h_nhds : (Set.Ioi 0 : Set ℝ≥0) ∈ 𝓝ˢ (⋃ A ∈ pdSetLM (ℋ := ℋ_aux), spectrum ℝ≥0 A) :=
    isOpen_Ioi.mem_nhdsSet.mpr h_subset
  have h_id_cont : ContinuousOn (fun A : L ℋ_aux => A) (pdSetLM (ℋ := ℋ_aux)) := continuousOn_id
  have h_nn : ∀ A ∈ pdSetLM (ℋ := ℋ_aux), (0 : L ℋ_aux) ≤ A :=
    fun _ hA => nonneg_of_pdSetLM hA
  have h_f_cont : ContinuousOn (fun x : ℝ≥0 => x ^ p) (Set.Ioi 0) :=
    NNReal.continuousOn_rpow_const (.inl (by simp : (0 : ℝ≥0) ∉ Set.Ioi 0))
  exact h_id_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.Ioi 0) (f := (· ^ p))
    h_nhds (ha' := h_nn) (hf := h_f_cont)

/-- Continuity of `(ρ, σ) ↦ σ^β * ρ * σ^β` on `pdSetLM × pdSetLM`. -/
private lemma rpow_conj_continuousOn_pdSetLM
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux] (β : ℝ) :
    ContinuousOn
      (fun p : L ℋ_aux × L ℋ_aux => CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)
      (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) := by
  have h_rpow_snd : ContinuousOn (fun p : L ℋ_aux × L ℋ_aux => CFC.rpow p.2 β)
      (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) :=
    (rpow_continuousOn_pdSetLM (ℋ_aux := ℋ_aux) β).comp continuousOn_snd
      (fun _ hx => (Set.mem_prod.mp hx).2)
  have h_fst : ContinuousOn (fun p : L ℋ_aux × L ℋ_aux => p.1)
      (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) := continuousOn_fst
  exact (h_rpow_snd.mul h_fst).mul h_rpow_snd

/-- The conjugated operator `σ^β * ρ * σ^β` belongs to `pdSetLM` for `ρ, σ ∈ pdSetLM`. -/
private lemma rpow_conj_mem_pdSetLM
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux] (β : ℝ) {ρ σ : L ℋ_aux}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ_aux)) (hσ : σ ∈ pdSetLM (ℋ := ℋ_aux)) :
    (CFC.rpow σ β * ρ * CFC.rpow σ β) ∈ pdSetLM (ℋ := ℋ_aux) := by
  have hP_pd : CFC.rpow σ β ∈ pdSetLM (ℋ := ℋ_aux) := pdSetLM_rpow_ne hσ
  have hP_sa : IsSelfAdjoint (CFC.rpow σ β) :=
    IsSelfAdjoint.of_nonneg (nonneg_of_pdSetLM hP_pd)
  have hP_unit : IsUnit (CFC.rpow σ β) := isUnit_of_pdSetLM hP_pd
  have h_eq : CFC.rpow σ β * ρ * CFC.rpow σ β =
      star (CFC.rpow σ β) * ρ * CFC.rpow σ β := by rw [hP_sa.star_eq]
  rw [h_eq]; exact pdSetLM_conj hρ hP_unit

/-- The real part of `sandwichedQuasi` is jointly continuous on `pdSetLM × pdSetLM`.
    Built from continuity of `CFC.rpow` (via `ContinuousOn.cfc_nnreal_of_mem_nhdsSet`),
    continuity of multiplication, and continuity of `Tr`. -/
lemma sandwichedQuasi_re_continuousOn_pdSetLM
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux] (α : ℝ) :
    ContinuousOn (Function.uncurry (fun (ρ σ : L ℋ_aux) => (sandwichedQuasi α ρ σ).re))
      (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) := by
  set β : ℝ := (1 - α) / (2 * α)
  -- Step 1: `(ρ, σ) ↦ σ^β * ρ * σ^β` is continuous, and its image lies in `pdSetLM`.
  have h_inner_cont :
      ContinuousOn (fun p : L ℋ_aux × L ℋ_aux => CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)
        (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) :=
    rpow_conj_continuousOn_pdSetLM β
  have h_inner_mem : ∀ p ∈ pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux),
      CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β ∈ pdSetLM (ℋ := ℋ_aux) := by
    rintro ⟨ρ, σ⟩ ⟨hρ, hσ⟩
    exact rpow_conj_mem_pdSetLM β hρ hσ
  -- Step 2: `A ↦ A^α` is continuous on operators whose spectrum lies in `Set.Ioi 0`.
  have h_nhds :
      (Set.Ioi 0 : Set ℝ≥0) ∈
        𝓝ˢ (⋃ p ∈ pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux),
          spectrum ℝ≥0 (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)) := by
    apply isOpen_Ioi.mem_nhdsSet.mpr
    intro r hr
    rw [Set.mem_iUnion₂] at hr
    obtain ⟨p, hp, hpr⟩ := hr
    exact pdSetLM_spectrum_nnreal_subset_Ioi (h_inner_mem p hp) hpr
  have h_nn : ∀ p ∈ pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux),
      (0 : L ℋ_aux) ≤ CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β :=
    fun p hp => nonneg_of_pdSetLM (h_inner_mem p hp)
  have h_f_cont : ContinuousOn (fun x : ℝ≥0 => x ^ α) (Set.Ioi 0) :=
    NNReal.continuousOn_rpow_const (.inl (by simp : (0 : ℝ≥0) ∉ Set.Ioi 0))
  have h_pow_cont :
      ContinuousOn
        (fun p : L ℋ_aux × L ℋ_aux =>
          CFC.rpow (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) α)
        (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) :=
    h_inner_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.Ioi (0 : ℝ≥0)) (f := (· ^ α))
      h_nhds (ha' := h_nn) (hf := h_f_cont)
  -- Step 3: `Tr` and `Re` are continuous.
  have h_trace_cont : Continuous (fun A : L ℋ_aux => Tr A) :=
    LinearMap.continuous_of_finiteDimensional _
  have h_final :
      ContinuousOn
        (fun p : L ℋ_aux × L ℋ_aux =>
          (Tr (CFC.rpow (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) α)).re)
        (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) :=
    Complex.continuous_re.comp_continuousOn (h_trace_cont.comp_continuousOn h_pow_cont)
  exact h_final

end Monotonicity

end SandwichedRenyiRelativeEntropy
