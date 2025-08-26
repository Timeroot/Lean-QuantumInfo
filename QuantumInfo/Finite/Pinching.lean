import QuantumInfo.Finite.CPTPMap
import QuantumInfo.Finite.MState
import QuantumInfo.Finite.Entropy
import QuantumInfo.ForMathlib.HermitianMat.CFC

/-! # Pinching channels
A pinching channel decoheres in the eigenspaces of a given state.
More precisely, given a state ρ, the pinching channel with respect to ρ is defined as
  E(σ) = ∑ Pᵢ σ Pᵢ
where the P_i are the projectors onto the i-th eigenspaces of ρ = ∑ᵢ pᵢ Pᵢ, with i ≠ j → pᵢ ≠ pⱼ.
-/

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

def pinching_kraus (ρ : MState d) : spectrum ℝ ρ.m → HermitianMat d ℂ :=
  fun x ↦ ρ.M.cfc (fun y ↦ if y = x then 1 else 0)

instance finite_spectrum_inst (ρ : MState d) : Fintype (spectrum ℝ ρ.m) :=
  Fintype.ofFinite (spectrum ℝ ρ.m)

theorem pinching_sq_eq_self (ρ : MState d) : ∀ k, (pinching_kraus ρ k)^2 = (pinching_kraus ρ k) := fun k => by
  ext1
  push_cast
  rw [pow_two, pinching_kraus, HermitianMat.cfc, ←cfc_mul
  (hf := by simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology, implies_true])
  (hg := by simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology, implies_true])]
  simp only [← pow_two, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow]

theorem pinching_sum (ρ : MState d) : ∑ k, pinching_kraus ρ k = 1 := by
  ext i j
  simp [pinching_kraus, HermitianMat.cfc]
  have heq : Set.EqOn (fun x => ∑ i : spectrum ℝ ρ.m, if x = ↑i then (1 : ℝ) else 0) 1 (spectrum ℝ ρ.m) := by
    unfold Set.EqOn; intro x hx
    dsimp
    rw [Finset.sum_set_coe (f := fun i => if x = i then 1 else 0) (s := spectrum ℝ ρ.m), Finset.sum_ite_eq_of_mem]
    rw [Set.mem_toFinset]
    exact hx
  rw [←cfc_sum (hf := by simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology, implies_true]),
  Finset.sum_fn, cfc_congr heq, cfc_one (R := ℝ) (ha := _)]
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, ρ.Hermitian]

def pinching_map (ρ : MState d) : CPTPMap d d ℂ :=
  CPTPMap.of_kraus_CPTPMap (HermitianMat.toMat ∘ pinching_kraus ρ) (by
  conv =>
    enter [1, 2, k]
    rw [Function.comp_apply, (pinching_kraus ρ k).H, ←pow_two]
    norm_cast
    rw [pinching_sq_eq_self ρ k]
  norm_cast
  rw [pinching_sum]
  rfl
  )

/-- Exercise 2.8 of Hayashi's book. Used in (S59) -/
theorem pinching_pythagoras (ρ σ : MState d) :  𝐃(ρ‖σ) = 𝐃(ρ‖pinching_map σ ρ) + 𝐃(pinching_map σ ρ‖σ) :=
  sorry
