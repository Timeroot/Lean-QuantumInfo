import StatMech.ThermoQuantities

noncomputable section

--! Specializing to an ideal gas of distinguishable particles.

/-- The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2.
The per-particle mass is normalized to 1. -/
def IdealGas : NVEHamiltonian where
  --The dimension of the manifold is 6 times the number of particles: three for position, three for momentum.
  dim := fun (n,_) ↦ Fin n × (Fin 3 ⊕ Fin 3)
  --The energy is ∞ if any positions are outside the cube, otherwise it's the sum of the momenta squared over 2.
  H := fun {d} config ↦
    let (n,V) := d
    let R := V^(1/3:ℝ) / 2 --half-sidelength of a cubical box
    if ∀ (i : Fin n) (ax : Fin 3), |config (i,.inl ax)| <= R then
      ∑ (i : Fin n) (ax : Fin 3), config (i,.inr ax)^2 / (2 : ℝ)
    else
      ⊤

namespace IdealGas
open MicroHamiltonian
open NVEHamiltonian

variable (n : ℕ) {V β T : ℝ}

open MeasureTheory in
/-- The partition function Z for an ideal gas. -/
theorem PartitionZ_eq (hV : 0 < V) (hβ : 0 < β) :
    IdealGas.PartitionZ (n,V) β = V^n * (2 * Real.pi / β)^(3 * n / 2 : ℝ) := by
  rw [PartitionZ, IdealGas]
  simp only [Finset.univ_product_univ, one_div, ite_eq_right_iff, WithTop.sum_eq_top,
    Finset.mem_univ, WithTop.coe_ne_top, and_false, exists_false, imp_false, not_forall, not_le,
    neg_mul]
  have h₀ : ∀ (config:Fin n × (Fin 3 ⊕ Fin 3) → ℝ) proof,
      ((if ∀ (i : Fin n) (ax : Fin 3), |config (i, Sum.inl ax)| ≤ V ^ (3 : ℝ)⁻¹ / 2 then
                  ∑ x : Fin n × Fin 3, config (x.1, Sum.inr x.2) ^ 2 / (2 :ℝ)
                else ⊤) : WithTop ℝ).untop proof = ∑ x : Fin n × Fin 3, config (x.1, Sum.inr x.2) ^ 2 / (2 :ℝ) := by
    intro config proof
    rw [WithTop.untop_eq_iff]
    split_ifs with h
    · simp
    · simp [h] at proof
  simp only [h₀, dite_eq_ite]; clear h₀

  let eq_pm : MeasurableEquiv ((Fin n × Fin 3 → ℝ) × (Fin n × Fin 3 → ℝ)) (Fin n × (Fin 3 ⊕ Fin 3) → ℝ) :=
    let e1 := (MeasurableEquiv.sumPiEquivProdPi (α := fun (_ : (Fin n × Fin 3) ⊕ (Fin n × Fin 3)) ↦ ℝ))
    let e2 := (MeasurableEquiv.piCongrLeft _ (MeasurableEquiv.prodSumDistrib (Fin n) (Fin 3) (Fin 3))).symm
    e1.symm.trans e2

  have h_preserve : MeasurePreserving eq_pm := by
    unfold eq_pm
    -- fun_prop --this *should* be a fun_prop!
    rw [MeasurableEquiv.coe_trans]
    apply MeasureTheory.MeasurePreserving.comp (μb := by volume_tac)
    · apply MeasurePreserving.symm
      apply MeasureTheory.volume_measurePreserving_piCongrLeft
    · apply MeasurePreserving.symm
      apply measurePreserving_sumPiEquivProdPi
  rw [← MeasurePreserving.integral_comp h_preserve eq_pm.measurableEmbedding]; clear h_preserve

  rw [show volume = Measure.prod volume volume from rfl]
  rw [integral_prod]

  have h_eval_eq_pm : ∀ (x y i p_i), eq_pm (x, y) (i, Sum.inl p_i) = x (i, p_i) := by
    intros; rfl
  have h_eval_eq_pm' : ∀ (x y i m_i), eq_pm (x, y) (i, Sum.inr m_i) = y (i, m_i) := by
    intros; rfl
  simp_rw [h_eval_eq_pm, h_eval_eq_pm']
  clear h_eval_eq_pm h_eval_eq_pm'

  simp_rw [← ite_not _ _ (0:ℝ), ← boole_mul _ (Real.exp _)]
  simp_rw [MeasureTheory.integral_mul_left, MeasureTheory.integral_mul_right]
  congr 1
  · --Volume of the box
    have h_integrand_prod : ∀ (a : Fin n × Fin 3 → ℝ),
        (if ¬∃ x y, V ^ (3⁻¹ : ℝ) / 2 < |a (x, y)| then 1 else 0) =
        (∏ xy, if |a xy| ≤ V ^ (3⁻¹ : ℝ) / 2 then 1 else 0 : ℝ) := by
      intro a
      push_neg
      simp_rw [← Prod.forall (p := fun xy ↦ |a xy| ≤ V ^ (3⁻¹ : ℝ) / 2)]
      exact Fintype.prod_boole.symm
    simp_rw [h_integrand_prod]; clear h_integrand_prod
    rw [MeasureTheory.integral_fintype_prod_eq_prod (𝕜 := ℝ)
      (f := fun _ r ↦ if |r| ≤ V ^ (3⁻¹ : ℝ) / 2 then 1 else 0)]
    rw [Finset.prod_const]
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have h_integral_1d : (∫ (x : ℝ), if |x| ≤ V ^ (3⁻¹ : ℝ) / 2 then 1 else 0) = V ^ (3⁻¹ : ℝ) := by
      have h_indicator := integral_indicator (f := fun _ ↦ (1:ℝ)) (μ := by volume_tac)
        (measurableSet_Icc (a := -(V ^ (3⁻¹ : ℝ) / 2)) (b := (V ^ (3⁻¹ : ℝ) / 2)))
      simp_rw [Set.indicator] at h_indicator
      simp_rw [abs_le, ← Set.mem_Icc, h_indicator]
      simp
      positivity
    rw [h_integral_1d]; clear h_integral_1d
    rw [← Real.rpow_mul_natCast]
    field_simp
    exact hV.le
  · --Gaussian integral
    have h_gaussian :=
      GaussianFourier.integral_rexp_neg_mul_sq_norm (V := PiLp 2 (fun (_ : Fin n × Fin 3) ↦ ℝ)) (half_pos hβ)
    apply (Eq.trans ?_ h_gaussian).trans ?_
    · congr
      · simp [measureSpaceOfInnerProductSpace, MeasureSpace.pi, PiLp, WithLp]
        apply congrArg
        sorry --Some MeasureTheory mess
      · funext x
        simp_rw [div_eq_inv_mul, ← Finset.mul_sum, ← mul_assoc, neg_mul, mul_comm, PiLp.norm_sq_eq_of_L2]
        simp
    · field_simp
      ring_nf
  sorry --Show integrability?

/-- The Helmholtz Free Energy A for an ideal gas. -/
theorem HelmholtzA_eq (hV : 0 < V) (hT : 0 < T) : IdealGas.HelmholtzA (n,V) T =
    -n * T * (Real.log V + (3/2) * Real.log (2 * Real.pi * T)) := by
  rw [HelmholtzA, PartitionZT, PartitionZ_eq n hV (one_div_pos.mpr hT), Real.log_mul,
    Real.log_pow, Real.log_rpow, one_div, div_inv_eq_mul]
  ring_nf
  all_goals positivity

theorem ZIntegrable (hV : 0 < V) (hβ : 0 < β) : IdealGas.ZIntegrable (n,V) β := by
  have hZpos : 0 < PartitionZ IdealGas (n, V) β := by
    rw [PartitionZ_eq n hV hβ]
    positivity
  constructor
  · apply MeasureTheory.Integrable.of_integral_ne_zero
    rw [← PartitionZ]
    exact hZpos.ne'
  · exact hZpos.ne'

/-- The ideal gas law: PV = nRT. In our unitsless system, R = 1.-/
theorem IdealGasLaw (hV : 0 < V) (hT : 0 < T) :
    let P := IdealGas.Pressure (n,V) T;
    let R := 1;
    P * V = n * R * T := by
  dsimp [Pressure]
  rw [← derivWithin_of_isOpen (s := Set.Ioi 0) isOpen_Ioi hV]
  rw [derivWithin_congr (f := fun V' ↦ -n * T * (Real.log V' + (3/2) * Real.log (2 * Real.pi * T))) ?_ ?_]
  rw [derivWithin_of_isOpen (s := Set.Ioi 0) isOpen_Ioi hV]
  rw [deriv_mul (by fun_prop) (by fun_prop (disch := exact hV.ne'))]
  field_simp
  ring_nf
  · exact fun _ hV' ↦ HelmholtzA_eq n hV' hT
  · exact HelmholtzA_eq n hV hT

-- Now proving e.g. Boyle's Law ("for an ideal gas with a fixed particle number, P and V are inversely proportional")
-- is a trivial consequence of the ideal gas law.

end IdealGas
