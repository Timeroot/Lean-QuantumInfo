/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Exact closed-hypograph conic strong duality

This module adds a finite-dimensional continuous-linear-map conic program layer
whose dual variables live in the continuous dual `F →L[ℝ] ℝ`.  The theorem is
an exact closed-hypograph theorem: it assumes the primal hypograph is closed and
derives equality of the primal supremum and dual infimum.  It is proof
infrastructure for the source-backed cq min-entropy guessing route, not a
general Slater theorem.
-/

@[expose] public section

noncomputable section

open Set

namespace QIT.SDP

universe u v

/--
A finite-dimensional continuous conic linear program.

It represents the primal maximization problem
`maximize c x` subject to `A x = b` and `x ∈ K`.
-/
structure ContinuousConeProgram (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] where
  K : ProperCone ℝ E
  A : E →L[ℝ] F
  b : F
  c : E →L[ℝ] ℝ

namespace ContinuousConeProgram

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable (P : ContinuousConeProgram E F)

/-- Primal feasibility: `x ∈ K` and `A x = b`. -/
def IsPrimalFeasible (x : E) : Prop :=
  x ∈ P.K ∧ P.A x = P.b

/-- Primal objective value. -/
def primalValue (x : E) : ℝ :=
  P.c x

/-- Primal value set. -/
def primalValueSet : Set ℝ :=
  {v | ∃ x : E, P.IsPrimalFeasible x ∧ v = P.primalValue x}

/--
Closed-hypograph carrier for the exact strong-duality theorem.

The first coordinate records `A x`; the second records any objective lower than
the primal value at `x`.
-/
def primalHypograph : Set (F × ℝ) :=
  {zt | ∃ x : E, x ∈ P.K ∧ zt.1 = P.A x ∧ zt.2 ≤ P.primalValue x}

/-- Exactness assumption used by the strong-duality theorem. -/
def HasClosedPrimalHypograph : Prop :=
  IsClosed P.primalHypograph

/--
Dual feasibility for the primal maximization convention.

For every cone point, the dual functional upper-bounds the primal objective
after applying `A`; hence every primal feasible value is at most `y b`.
-/
def IsDualFeasible (y : F →L[ℝ] ℝ) : Prop :=
  ∀ x : E, x ∈ P.K → P.primalValue x ≤ y (P.A x)

/-- Dual objective value. -/
def dualValue (y : F →L[ℝ] ℝ) : ℝ :=
  y P.b

/-- Dual value set. -/
def dualValueSet : Set ℝ :=
  {v | ∃ y : F →L[ℝ] ℝ, P.IsDualFeasible y ∧ v = P.dualValue y}

/-- Pointwise weak duality. -/
theorem primalValue_le_dualValue {x : E} (hx : P.IsPrimalFeasible x)
    {y : F →L[ℝ] ℝ} (hy : P.IsDualFeasible y) :
    P.primalValue x ≤ P.dualValue y := by
  simpa [IsPrimalFeasible, IsDualFeasible, primalValue, dualValue, hx.2] using hy x hx.1

/-- A dual feasible point bounds the primal value set above. -/
theorem primalValueSet_bddAbove_of_dualFeasible
    {y : F →L[ℝ] ℝ} (hy : P.IsDualFeasible y) :
    BddAbove P.primalValueSet := by
  refine ⟨P.dualValue y, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  exact P.primalValue_le_dualValue hx hy

/-- A primal feasible point bounds the dual value set below. -/
theorem dualValueSet_bddBelow_of_primalFeasible
    {x : E} (hx : P.IsPrimalFeasible x) :
    BddBelow P.dualValueSet := by
  refine ⟨P.primalValue x, ?_⟩
  rintro w ⟨y, hy, rfl⟩
  exact P.primalValue_le_dualValue hx hy

/-- Every dual feasible value is above the primal supremum. -/
theorem sSup_primalValueSet_le_dualValue (hne : P.primalValueSet.Nonempty)
    {y : F →L[ℝ] ℝ} (hy : P.IsDualFeasible y) :
    sSup P.primalValueSet ≤ P.dualValue y := by
  have hbdd : BddAbove P.primalValueSet :=
    P.primalValueSet_bddAbove_of_dualFeasible hy
  exact csSup_le hne fun v hv => by
    rcases hv with ⟨x, hx, rfl⟩
    exact P.primalValue_le_dualValue hx hy

/--
Weak duality for value sets.  The proof explicitly derives the
conditional-completeness obligations from primal and dual witnesses.
-/
theorem sSup_primalValueSet_le_sInf_dualValueSet
    (hprimal : P.primalValueSet.Nonempty) (hdual : P.dualValueSet.Nonempty) :
    sSup P.primalValueSet ≤ sInf P.dualValueSet := by
  rcases hprimal with ⟨v, x, hx, rfl⟩
  rcases hdual with ⟨w, y0, hy0, rfl⟩
  have hdualBddBelow : BddBelow P.dualValueSet :=
    P.dualValueSet_bddBelow_of_primalFeasible hx
  have hprimalBddAbove : BddAbove P.primalValueSet :=
    P.primalValueSet_bddAbove_of_dualFeasible hy0
  refine le_csInf ⟨P.dualValue y0, ⟨y0, hy0, rfl⟩⟩ ?_
  rintro w ⟨y, hy, rfl⟩
  exact P.sSup_primalValueSet_le_dualValue ⟨P.primalValue x, ⟨x, hx, rfl⟩⟩ hy

/-- Nonemptiness of primal values gives a lower bound for all dual values. -/
theorem dualValueSet_bddBelow_of_primalValueSet_nonempty
    (hne : P.primalValueSet.Nonempty) :
    BddBelow P.dualValueSet := by
  rcases hne with ⟨v, x, hx, rfl⟩
  exact P.dualValueSet_bddBelow_of_primalFeasible hx

/-- The primal hypograph is convex. -/
theorem primalHypograph_convex : Convex ℝ P.primalHypograph := by
  rw [convex_iff_add_mem]
  rintro zt₁ ⟨x₁, hx₁K, hz₁, ht₁⟩ zt₂ ⟨x₂, hx₂K, hz₂, ht₂⟩ a b ha hb hab
  refine ⟨a • x₁ + b • x₂, ?_, ?_, ?_⟩
  · exact P.K.add_mem (P.K.smul_mem hx₁K ha) (P.K.smul_mem hx₂K hb)
  · simp [hz₁, hz₂, map_add, map_smul]
  · have h₁ : a * zt₁.2 ≤ a * P.primalValue x₁ :=
      mul_le_mul_of_nonneg_left ht₁ ha
    have h₂ : b * zt₂.2 ≤ b * P.primalValue x₂ :=
      mul_le_mul_of_nonneg_left ht₂ hb
    have hsum : a * zt₁.2 + b * zt₂.2 ≤
        a * P.primalValue x₁ + b * P.primalValue x₂ := add_le_add h₁ h₂
    simpa [primalValue, map_add, map_smul, smul_eq_mul] using hsum

/-- The origin belongs to every primal hypograph. -/
theorem zero_mem_primalHypograph :
    (0 : F × ℝ) ∈ P.primalHypograph := by
  refine ⟨0, ?_, ?_, ?_⟩
  · exact P.K.zero_mem
  · simp
  · simp [primalValue]

/-- The primal hypograph is closed under nonnegative scalar multiplication. -/
theorem smul_mem_primalHypograph {zt : F × ℝ} (hzt : zt ∈ P.primalHypograph)
    {a : ℝ} (ha : 0 ≤ a) :
    a • zt ∈ P.primalHypograph := by
  rcases hzt with ⟨x, hxK, hz, ht⟩
  refine ⟨a • x, P.K.smul_mem hxK ha, ?_, ?_⟩
  · simp [hz, map_smul]
  · have hmul : a * zt.2 ≤ a * P.primalValue x :=
      mul_le_mul_of_nonneg_left ht ha
    simpa [primalValue, map_smul, smul_eq_mul] using hmul

/-- The point `(b, sSup primalValueSet + ε)` is above the closed hypograph. -/
theorem target_not_mem_primalHypograph
    (hbdd : BddAbove P.primalValueSet) {ε : ℝ} (hε : 0 < ε) :
    (P.b, sSup P.primalValueSet + ε) ∉ P.primalHypograph := by
  rintro ⟨x, hxK, hxA, ht⟩
  have hx : P.IsPrimalFeasible x := ⟨hxK, hxA.symm⟩
  have hval : P.primalValue x ∈ P.primalValueSet := ⟨x, hx, rfl⟩
  have hleSup : P.primalValue x ≤ sSup P.primalValueSet := le_csSup hbdd hval
  linarith

/-- The separating threshold is positive because the hypograph contains zero. -/
theorem separator_threshold_pos {ell : (F × ℝ) →L[ℝ] ℝ} {τ : ℝ}
    (hsep : ∀ zt ∈ P.primalHypograph, ell zt < τ) :
    0 < τ := by
  simpa using hsep 0 (P.zero_mem_primalHypograph)

/--
For a strict separator of a conic hypograph from a point, the separating
functional is nonpositive on the whole hypograph.
-/
theorem separator_nonpos_on_primalHypograph {ell : (F × ℝ) →L[ℝ] ℝ} {τ : ℝ}
    (hsep : ∀ zt ∈ P.primalHypograph, ell zt < τ) :
    ∀ zt ∈ P.primalHypograph, ell zt ≤ 0 := by
  intro zt hzt
  by_contra hpos
  have hellpos : 0 < ell zt := lt_of_not_ge hpos
  have hτpos : 0 < τ := P.separator_threshold_pos hsep
  obtain ⟨n, hn⟩ := exists_nat_gt (τ / ell zt)
  have hτlt : τ < (n : ℝ) * ell zt := by
    have h := (div_lt_iff₀ hellpos).1 hn
    simpa [mul_comm] using h
  have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hscale : ((n : ℝ) • zt) ∈ P.primalHypograph :=
    P.smul_mem_primalHypograph hzt hnnonneg
  have hsepScale := hsep ((n : ℝ) • zt) hscale
  have hellScale : ell ((n : ℝ) • zt) = (n : ℝ) * ell zt := by
    simp [smul_eq_mul]
  linarith

omit [FiniteDimensional ℝ F] in
/-- Product-coordinate decomposition of a continuous linear separator. -/
theorem separator_apply_eq (ell : (F × ℝ) →L[ℝ] ℝ) (z : F) (t : ℝ) :
    ell (z, t) =
      (ell.comp (ContinuousLinearMap.inl ℝ F ℝ)) z + t * ell (0, 1) := by
  have hsplit :
      (z, t) =
        ContinuousLinearMap.inl ℝ F ℝ z +
          ContinuousLinearMap.inr ℝ F ℝ t := by
    ext <;> simp [ContinuousLinearMap.inl, ContinuousLinearMap.inr]
  rw [hsplit, map_add]
  have ht : ell (ContinuousLinearMap.inr ℝ F ℝ t) = t * ell (0, 1) := by
    have hpoint : ContinuousLinearMap.inr ℝ F ℝ t = t • ((0 : F), (1 : ℝ)) := by
      ext <;> simp [ContinuousLinearMap.inr]
    calc
      ell (ContinuousLinearMap.inr ℝ F ℝ t) = ell (t • ((0 : F), (1 : ℝ))) := by
        rw [hpoint]
      _ = t * ell (0, 1) := by
        rw [map_smul]
        simp [smul_eq_mul]
  simp only [ContinuousLinearMap.comp_apply]
  rw [ht]

/-- The objective-coordinate coefficient of a separator is nonnegative. -/
theorem separator_objectiveCoefficient_nonneg {ell : (F × ℝ) →L[ℝ] ℝ}
    (hnonpos : ∀ zt ∈ P.primalHypograph, ell zt ≤ 0) :
    0 ≤ ell (0, 1) := by
  have hdown : ((0 : F), (-1 : ℝ)) ∈ P.primalHypograph := by
    refine ⟨0, P.K.zero_mem, ?_, ?_⟩
    · simp
    · simp [primalValue]
  have h := hnonpos ((0 : F), (-1 : ℝ)) hdown
  have hell : ell ((0 : F), (-1 : ℝ)) = -ell ((0 : F), (1 : ℝ)) := by
    simpa using (map_neg ell ((0 : F), (1 : ℝ)))
  linarith

/-- The objective-coordinate coefficient is positive when the primal is feasible. -/
theorem separator_objectiveCoefficient_pos (hne : P.primalValueSet.Nonempty)
    {ell : (F × ℝ) →L[ℝ] ℝ} {τ ε : ℝ}
    (hsep : ∀ zt ∈ P.primalHypograph, ell zt < τ)
    (htarget : τ < ell (P.b, sSup P.primalValueSet + ε))
    (hnonpos : ∀ zt ∈ P.primalHypograph, ell zt ≤ 0)
    (hnonneg : 0 ≤ ell (0, 1)) :
    0 < ell (0, 1) := by
  have hne0 : ell ((0 : F), (1 : ℝ)) ≠ 0 := by
    intro hα
    rcases hne with ⟨v, x, hx, rfl⟩
    have hfeasHyp : (P.b, P.primalValue x) ∈ P.primalHypograph := by
      refine ⟨x, hx.1, ?_, le_rfl⟩
      exact hx.2.symm
    have hfeasNonpos := hnonpos (P.b, P.primalValue x) hfeasHyp
    have htargetEq :
        ell (P.b, sSup P.primalValueSet + ε) =
          (ell.comp (ContinuousLinearMap.inl ℝ F ℝ)) P.b := by
      rw [separator_apply_eq (F := F) ell P.b (sSup P.primalValueSet + ε)]
      simp [hα]
    have hfeasEq :
        ell (P.b, P.primalValue x) =
          (ell.comp (ContinuousLinearMap.inl ℝ F ℝ)) P.b := by
      rw [separator_apply_eq (F := F) ell P.b (P.primalValue x)]
      simp [hα]
    have htargetNonpos : ell (P.b, sSup P.primalValueSet + ε) ≤ 0 := by
      rw [htargetEq, ← hfeasEq]
      exact hfeasNonpos
    have hτpos : 0 < τ := P.separator_threshold_pos hsep
    linarith
  exact lt_of_le_of_ne hnonneg (Ne.symm hne0)

/--
Closed-hypograph separation gives an `ε`-optimal dual feasible point.

This is the core exact-closed-hypograph approximation theorem.  It separates
`(b, sSup primalValueSet + ε)` from the closed hypograph, proves the
objective-coordinate separator coefficient is positive, normalizes that
coefficient to one, and extracts a continuous dual feasible functional.
-/
theorem exists_dualValue_le_sSup_add
    (hne : P.primalValueSet.Nonempty)
    (hbdd : BddAbove P.primalValueSet)
    (hclosed : P.HasClosedPrimalHypograph)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y, P.IsDualFeasible y ∧
      P.dualValue y ≤ sSup P.primalValueSet + ε := by
  have hnotMem : (P.b, sSup P.primalValueSet + ε) ∉ P.primalHypograph :=
    P.target_not_mem_primalHypograph hbdd hε
  obtain ⟨ell, τ, hsep, htarget⟩ :=
    geometric_hahn_banach_closed_point P.primalHypograph_convex hclosed hnotMem
  let φ : F →L[ℝ] ℝ := ell.comp (ContinuousLinearMap.inl ℝ F ℝ)
  let α : ℝ := ell (0, 1)
  have hnonpos : ∀ zt ∈ P.primalHypograph, ell zt ≤ 0 :=
    P.separator_nonpos_on_primalHypograph hsep
  have hαnonneg : 0 ≤ α := by
    simpa [α] using P.separator_objectiveCoefficient_nonneg hnonpos
  have hαpos : 0 < α := by
    simpa [α] using
      P.separator_objectiveCoefficient_pos hne hsep htarget hnonpos hαnonneg
  let y : F →L[ℝ] ℝ := (-(α⁻¹)) • φ
  refine ⟨y, ?_, ?_⟩
  · intro x hxK
    have hhyp : (P.A x, P.primalValue x) ∈ P.primalHypograph :=
      ⟨x, hxK, rfl, le_rfl⟩
    have hle0 := hnonpos (P.A x, P.primalValue x) hhyp
    have hdecomp := separator_apply_eq (F := F) ell (P.A x) (P.primalValue x)
    have hdecomp' :
        ell (P.A x, P.primalValue x) = φ (P.A x) + P.primalValue x * α := by
      simpa [φ, α] using hdecomp
    have hineq : φ (P.A x) + P.primalValue x * α ≤ 0 := by
      linarith
    have hmul : P.primalValue x * α ≤ -φ (P.A x) := by
      linarith
    dsimp [IsDualFeasible, y]
    simp
    calc
      P.primalValue x = (P.primalValue x * α) * α⁻¹ := by
        field_simp [hαpos.ne']
      _ ≤ (-φ (P.A x)) * α⁻¹ :=
        mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr hαpos.le)
      _ = -(α⁻¹ * φ (P.A x)) := by ring
  · have hτpos : 0 < τ := P.separator_threshold_pos hsep
    have htargetPos : 0 < ell (P.b, sSup P.primalValueSet + ε) :=
      hτpos.trans htarget
    have hdecomp :=
      separator_apply_eq (F := F) ell P.b (sSup P.primalValueSet + ε)
    have hdecomp' :
        ell (P.b, sSup P.primalValueSet + ε) =
          φ P.b + (sSup P.primalValueSet + ε) * α := by
      simpa [φ, α] using hdecomp
    have hineq : 0 < φ P.b + (sSup P.primalValueSet + ε) * α := by
      linarith
    have hmul : -φ P.b < (sSup P.primalValueSet + ε) * α := by
      linarith
    dsimp [dualValue, y]
    simp
    exact le_of_lt (by
      calc
        -(α⁻¹ * φ P.b) = (-φ P.b) * α⁻¹ := by ring
        _ < ((sSup P.primalValueSet + ε) * α) * α⁻¹ :=
          mul_lt_mul_of_pos_right hmul (inv_pos.mpr hαpos)
        _ = sSup P.primalValueSet + ε := by
          field_simp [hαpos.ne']
      )

/-- Closed hypograph and bounded nonempty primal values give a dual feasible value. -/
theorem dualValueSet_nonempty_of_hasClosedPrimalHypograph
    (hclosed : P.HasClosedPrimalHypograph)
    (hne : P.primalValueSet.Nonempty)
    (hbdd : BddAbove P.primalValueSet) :
    P.dualValueSet.Nonempty := by
  obtain ⟨y, hy, _hybd⟩ :=
    P.exists_dualValue_le_sSup_add hne hbdd hclosed (ε := 1) zero_lt_one
  exact ⟨P.dualValue y, ⟨y, hy, rfl⟩⟩

/--
Exact closed-hypograph conic strong duality.

This proves equality of the primal supremum and dual infimum.  It does not
assert dual attainment and is not a Slater theorem.
-/
theorem sSup_primalValueSet_eq_sInf_dualValueSet_of_hasClosedPrimalHypograph
    (hclosed : P.HasClosedPrimalHypograph)
    (hne : P.primalValueSet.Nonempty)
    (hbdd : BddAbove P.primalValueSet) :
    sSup P.primalValueSet = sInf P.dualValueSet := by
  have hdualNonempty : P.dualValueSet.Nonempty :=
    P.dualValueSet_nonempty_of_hasClosedPrimalHypograph hclosed hne hbdd
  have hdualBddBelow : BddBelow P.dualValueSet :=
    P.dualValueSet_bddBelow_of_primalValueSet_nonempty hne
  refine le_antisymm (P.sSup_primalValueSet_le_sInf_dualValueSet hne hdualNonempty) ?_
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨y, hy, hybd⟩ :=
    P.exists_dualValue_le_sSup_add hne hbdd hclosed hε
  have hyMem : P.dualValue y ∈ P.dualValueSet := ⟨y, hy, rfl⟩
  have hInfLe : sInf P.dualValueSet ≤ P.dualValue y :=
    csInf_le hdualBddBelow hyMem
  linarith

end ContinuousConeProgram

end QIT.SDP
