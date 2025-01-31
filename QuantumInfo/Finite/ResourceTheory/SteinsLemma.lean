import QuantumInfo.Finite.ResourceTheory.FreeState

open ResourcePretheory
open FreeStateTheory
open NNReal
open ComplexOrder
open Topology

namespace SteinsLemma

section hypotesting

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The optimal hypothesis testing rate, for a tolerance ε: given a state ρ and a set of states S,
the optimum distinguishing rate that allows a probability ε of errors. -/
noncomputable def OptimalHypothesisRate (ρ : MState d) (ε : ℝ) (S : Set (MState d)) : Prob :=
  ⨅ T : { m : Matrix d d ℂ //
    ∃ h : m.PosSemidef ∧ m ≤ 1, MState.exp_val (Matrix.isHermitian_one.sub h.1.1) ρ ≤ ε},
  ⨆ σ ∈ S,
  ⟨MState.exp_val T.2.1.1.1 σ, MState.exp_val_prob T.2.1 σ⟩

scoped notation "β_" ε " (" ρ "‖" S ")" =>  OptimalHypothesisRate ρ ε S

theorem OptimalHypothesisRate_singleton {ρ σ : MState d} {ε : ℝ}  :
  β_ ε(ρ‖{σ}) =
    ⨅ T : { m : Matrix d d ℂ //
    ∃ h : m.PosSemidef ∧ m ≤ 1, MState.exp_val (Matrix.isHermitian_one.sub h.1.1) ρ ≤ ε},
    ⟨MState.exp_val T.2.1.1.1 σ, MState.exp_val_prob T.2.1 σ⟩
  := by
  simp only [OptimalHypothesisRate, iSup_singleton]

private theorem Lemma3 (ρ : MState d) (ε : ℝ) (S : Set (MState d)) :
    ⨆ σ ∈ S, β_ ε(ρ‖{σ}) = β_ ε(ρ‖S) := by
  sorry

/- This is from "Strong converse exponents for a quantum channel discrimination problem and
quantum-feedback-assisted communication", Lemma 5. It will likely require some kind of
special condition that α ≠ 1 to be completely true. -/
private theorem Ref81Lem5 (ρ σ : MState d) (ε α : ℝ) (hε : 0 ≤ ε ∧ ε < 1) (hα : 0 < α) :
    -Real.log β_ ε(ρ‖{σ}) ≤ (SandwichedRelRentropy α ρ σ : EReal) - Real.log (1 - ε) * α / (1 - α)
    := by
  sorry

end hypotesting

variable {ι : Type*} [FreeStateTheory ι]
variable {i : ι}

-- This theorem should follow from "Fekete's subadditive lemma", which can be found in
-- Lemma A.1 of Hayashi's book "Quantum Information Theory - Mathematical Foundation".
--
-- Also, the sequence of states S^(n) mentioned in the paper is implicitly defined here as
-- IsFree (i := i⊗^[n]). It has all the properties we need plus some more (e.g., for this
-- lemma, we don't need convexity).
/-- Lemma 5 -/
theorem limit_rel_entropy_exists (ρ : MState (H i)) :
  ∃ d : ℝ≥0,
    Filter.Tendsto (fun n ↦ (↑n)⁻¹ * ⨅ σ ∈ IsFree (i := i⊗^[n]), 𝐃(ρ⊗^[n]‖σ))
    .atTop (𝓝 d) := by
  sorry

variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- Lemma 6 from the paper -/
private theorem Lemma6 (m : ℕ) (hm : 0 < m) (ρ σf : MState d) (σₘ : MState (Fin m → d)) (hσf : σf.m.PosDef) (ε : ℝ)
    (hε : 0 < ε) :
    let σn (n : ℕ) : (MState (Fin n → d)) :=
      let l : ℕ := n / m
      let q : ℕ := n % m
      let σl := σₘ ⊗^ l
      let σr := σf ⊗^ q
      let eqv : (Fin n → d) ≃ (Fin l → Fin m → d) × (Fin q → d) :=
        Equiv.piCongrLeft (fun _ ↦ d) ((finCongr (Eq.symm (Nat.div_add_mod' n m))).trans (finSumFinEquiv.symm))
          |>.trans <|
           (Equiv.sumArrowEquivProdArrow ..)
          |>.trans <|
           (Equiv.prodCongr (Equiv.piCongrLeft (fun _ ↦ d) finProdFinEquiv).symm (Equiv.refl _))
          |>.trans <|
          (Equiv.prodCongr (Equiv.curry ..) (Equiv.refl _))
      (σl.prod σr).relabel eqv
    Filter.atTop.limsup (fun n ↦ -Real.log β_ ε(ρ ⊗^ n‖{σn n}) / n : ℕ → EReal) ≤
    𝐃(ρ⊗^m‖σₘ) / m
  := by
  sorry

/-- Theorem 4, which is _also_ called the Generalized Quantum Stein's Lemma in Hayashi & Yamasaki -/
theorem limit_hypotesting_eq_limit_rel_entropy (ρ : MState (H i)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    ∃ d : ℝ≥0,
      Filter.Tendsto (fun n ↦ -Real.log β_ ε(ρ⊗^[n] ‖ IsFree) / n)
      .atTop (𝓝 d)
      ∧
      Filter.Tendsto (fun n ↦ (↑n)⁻¹ * ⨅ σ ∈ IsFree, 𝐃(ρ⊗^[n]‖σ))
      .atTop (𝓝 d)
      := by
  sorry

section Lemma7

open MatrixMap
open Matrix

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]

-- This should be moved to the files about matrix maps as soon as a good definition of "dual channel" can be made.
theorem positive_dual_channel_exists (ℰ : CPTPMap dIn dOut) :
  ∃ ℰdual : CPTPMap dOut dIn, ∀ ρ : MState dIn, ∀ T : Matrix dOut dOut ℂ, T.PosSemidef →
  MState.exp_val hT.1 (ℰ ρ) = MState.exp_val (ℰdual.pos hT).1 ρ := by
  -- The proof below was valid for a previous wrong version of the theorem. Nevertheless
  -- it could still be useful for this version.
  --------------------------------------------------
  -- have hkraus := IsCompletelyPositive.exists_kraus ℰ.map ℰ.completely_pos
  -- obtain ⟨r, M, hkraus⟩ := hkraus
  -- let T' : Matrix dIn dIn ℂ := ∑ i : Fin r, (M i)ᴴ * T * (M i)
  -- -- Should come from something like Matrix.PosSemidef.sum
  -- have hT' : T'.PosSemidef := by
  --   constructor
  --   · unfold IsHermitian T'
  --     rw [conjTranspose_sum]
  --     simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  --     rw [hT.1]
  --   · intro x
  --     unfold T'
  --     -- rw [AddMonoidHom.finset_sum_apply (mulVec.addMonoidHomLeft : (dIn → ℂ) → (Matrix dIn dIn ℂ) →+ dIn → ℂ)]
  --     sorry
  -- use T', hT'
  -- simp [MState.exp_val, IsHermitian.rinner, CPTPMap.mat_coe_eq_apply_mat, hkraus, of_kraus,
  --   Finset.mul_sum, Finset.sum_mul, ←Matrix.mul_assoc, T']
  -- conv =>
  --   enter [1, 2, x]
  --   rw [trace_mul_cycle, ←Matrix.mul_assoc]
  sorry

set_option pp.proofs true in
/-- Lemma S1 -/
private theorem optimalHypothesisRate_antitone (ρ σ : MState dIn) (ℰ : CPTPMap dIn dOut) (ε3 : ℝ) (hε3 : ε3 ≥ 0) :
  β_ ε3(ρ‖{σ}) ≤ β_ ε3(ℰ ρ‖{ℰ σ}) := by
  repeat rw [OptimalHypothesisRate_singleton]
  obtain ⟨ℰdual, hℰdual⟩ := positive_dual_channel_exists ℰ
  let ℰdualSubtype : { m : Matrix dOut dOut ℂ //
    ∃ h : m.PosSemidef ∧ m ≤ 1, MState.exp_val (Matrix.isHermitian_one.sub h.1.1) (ℰ ρ) ≤ ε3} →
    { m : Matrix dIn dIn ℂ //
    ∃ h : m.PosSemidef ∧ m ≤ 1, MState.exp_val (Matrix.isHermitian_one.sub h.1.1) ρ ≤ ε3} := sorry
  have h : ∀ x, (ℰdualSubtype x).val = ℰdual.map x.val := sorry
  -- have h' : ∀ x, (h ▸ (ℰdualSubtype x).2.1.1) = ℰdual.pos x.2.1.1 := sorry
  convert le_iInf_comp _ ℰdualSubtype
  rename_i T'
  specialize h T'
  specialize hℰdual σ T' T'.2.1.1
  -- simp [h]
  -- conv =>
  --   enter [2, 1, 1]
  --   rw [h]
  sorry

/-- Lemma 7 from the paper -/
private theorem Lemma7 (ρ : MState (H i)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) (σ : (n : ℕ+) → IsFree (i := i⊗^[n])) :
  -- This is not exactly how R_{1, ε} is defined in Eq. (17), but it should be equal due to
  -- the monotonicity of log and Lemma 3.
  let R1 : ℝ :=
    Filter.liminf (fun n ↦ -Real.log β_ ε(ρ⊗^[n]‖IsFree) / n) Filter.atTop
  let R2 : EReal :=
    Filter.liminf (fun n ↦ 𝐃(ρ⊗^[n]‖σ n) / n) Filter.atTop
  (R2 ≥ R1) →
  ∀ ε' : ℝ, 0 < ε' ∧ ε' < ε → -- ε' is written as \tilde{ε} in the paper.
  ∃ σ' : (n : ℕ+) → IsFree (i := i⊗^[n]),
  let R2' : EReal :=
    Filter.liminf (fun n ↦ 𝐃(ρ⊗^[n]‖σ' n) / n) Filter.atTop
  R2' - R1 ≤ (1 - ε') * (R2 - R1)
  := by
  sorry

end Lemma7

theorem GeneralizedQSteinsLemma {i : ι} (ρ : MState (H i)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    Filter.Tendsto (fun n ↦
      -Real.log β_ ε(ρ⊗^[n]‖IsFree) / n
    ) .atTop (𝓝 (RegularizedRelativeEntResource ρ)) := by
  sorry
