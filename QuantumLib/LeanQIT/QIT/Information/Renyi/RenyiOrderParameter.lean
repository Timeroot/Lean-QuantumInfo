/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalSandwichedRenyiAdditivity
public import QIT.Information.Entropy.Entropy
public import QIT.OneShot.Smooth

/-!
# Extended Renyi order parameter for the closed interval [1/2, infinity]

This module provides the order carrier `RenyiOrder` spanning the full closed
sandwiched-Renyi data-processing range `alpha in [1/2, infinity]`, including
the boundary orders `alpha = 1/2`, `alpha = 1`, and `alpha = infinity`.

The carrier comes with:

* a region dispatch (`RenyiOrder.Region`, `RenyiOrder.region`) that partitions
  the closed interval into its five source-meaningful pieces;
* the reciprocal `RenyiOrder.recip` (with the convention `recip infinity = 0`);
* the source conjugate order map `alpha |-> beta = alpha / (2*alpha - 1)`,
  extended to the closed interval by the boundary pairs `(1/2, infinity)`,
  `(1, 1)`, `(infinity, 1/2)`; and
* the headline closure `recip_add_recip_conjugateOrder`, the identity
  `1/alpha + 1/beta = 2` over the full closed `[1/2, infinity]`.

The boundary values of the upward sandwiched conditional Renyi entropy are the
source-named entropies (conditional von Neumann entropy at `alpha = 1`,
conditional max-entropy at `alpha = 1/2`, conditional min-entropy at
`alpha = infinity`); the unified total surface
`State.conditionalSandwichedRenyiUpExtendedOrder` adds the `alpha = infinity`
boundary arm to the existing finite-order surface
`conditionalSandwichedRenyiUpFiniteOrder`, and is compatible with the existing
finite-real positive-definite-gated surface `conditionalSandwichedRenyi` on the
interior.

Source: Tomamichel2015FiniteResources, `renyi.tex` (the sandwiched Renyi
divergences are defined as limits at the boundary orders, so a definitional
boundary matching the source-named limit value is source-faithful), and
`cond.tex` (the boundary values of the upward conditional entropy and the
conjugate order map).

The real `alpha -> 1` and `alpha -> infinity` limit theorems for the upward
conditional entropy are out of scope here: the `alpha = infinity` limit has no
boxed source proof, and the `alpha = 1` conditional lift needs a
supremum-versus-limit exchange that is not yet available. Both are recorded as
named follow-up blockers; every theorem in this module is completely proved.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Topology

open Matrix Filter

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The closed sandwiched-Renyi order interval `[1/2, infinity]`.

The carrier is the subtype of `WithTop ℝ` bounded below by `1/2`; the top
element is the boundary order `alpha = infinity`. This is the parameter
universe needed by Tomamichel's entropy uncertainty relation, which is posed
over `alpha, beta in [1/2, infinity]` with `1/alpha + 1/beta = 2`. -/
def RenyiOrder : Type := {α : WithTop ℝ // ((1/2 : ℝ) : WithTop ℝ) ≤ α}

namespace RenyiOrder

/-- Construct a finite Renyi order from a real `r >= 1/2`. -/
def ofReal (r : ℝ) (h : ((1/2 : ℝ) : WithTop ℝ) ≤ ↑r) : RenyiOrder := ⟨↑r, h⟩

/-- The boundary order `alpha = infinity`. -/
def infinity : RenyiOrder := ⟨⊤, le_top⟩

instance : CoeOut RenyiOrder (WithTop ℝ) := ⟨Subtype.val⟩

/-- Safe partial projection of a Renyi order to a real parameter.

The top order `infinity` carries no finite real value and projects to `none`;
a finite order `ofReal r h` projects to `some r`. Unlike a total projection this
never silently assigns a real to the top order: the `Option` return type forces
every caller needing an unguarded `ℝ` to handle the top case. -/
def toReal? (α : RenyiOrder) : Option ℝ :=
  match α.val with
  | ⊤ => none
  | some r => some r

@[simp]
theorem toReal?_infinity : toReal? (infinity : RenyiOrder) = none := rfl

@[simp]
theorem toReal?_ofReal (r : ℝ) (h : ((1/2 : ℝ) : WithTop ℝ) ≤ ↑r) :
    toReal? (ofReal r h) = some r := rfl

example : toReal? (infinity : RenyiOrder) = none := rfl
example : toReal? (ofReal (1/2 : ℝ) (by norm_num)) = some (1/2 : ℝ) := rfl
example : toReal? (ofReal (1 : ℝ) (by norm_num)) = some (1 : ℝ) := rfl
example : toReal? (ofReal (2 : ℝ) (by exact_mod_cast (by norm_num : (1/2 : ℝ) ≤ 2))) =
    some (2 : ℝ) := rfl

@[simp]
theorem coe_ofReal (r : ℝ) (h : ((1/2 : ℝ) : WithTop ℝ) ≤ ↑r) :
    ((ofReal r h : RenyiOrder) : WithTop ℝ) = ↑r := rfl

@[simp]
theorem coe_infinity :
    ((infinity : RenyiOrder) : WithTop ℝ) = ⊤ := rfl

/-- A finite order coerced to `↑r` carries the real lower bound `1/2 <= r`. -/
theorem le_of_coe {r : ℝ} (α : RenyiOrder) (h : α.val = ↑r) : 1/2 ≤ r := by
  have hp := α.prop
  rw [h] at hp
  exact_mod_cast hp

@[simp]
theorem ofReal_inj {r s : ℝ}
    {hr : ((1/2 : ℝ) : WithTop ℝ) ≤ ↑r} {hs : ((1/2 : ℝ) : WithTop ℝ) ≤ ↑s} :
    (ofReal r hr : RenyiOrder) = ofReal s hs ↔ r = s :=
  ⟨fun h => WithTop.coe_injective (congrArg Subtype.val h),
   fun heq => by subst heq; exact Subtype.ext rfl⟩

theorem infinity_ne_ofReal (r : ℝ) (h : ((1/2 : ℝ) : WithTop ℝ) ≤ ↑r) :
    (infinity : RenyiOrder) ≠ ofReal r h := by
  intro heq
  have hcoe : (⊤ : WithTop ℝ) = (↑r : WithTop ℝ) := congrArg Subtype.val heq
  exact (WithTop.coe_ne_top (a := r)) hcoe.symm

/-- The source-meaningful region decomposition of the closed Renyi interval.

The five regions are the boundary orders (`half`, `one`, `infinity`) together
with the two interior pieces (`ltOne` for `1/2 < alpha < 1`, `gtOne` for
`1 < alpha`).  The interior arms carry the real parameter; the defining
inequality is invariant under the dispatch. -/
inductive Region where
  | half : Region
  | ltOne (r : ℝ) : Region
  | one : Region
  | gtOne (r : ℝ) : Region
  | infinity : Region

/-- The total region dispatch assigning each Renyi order to its unique region.

Each closed-interval order lies in exactly one of the five regions. -/
def region (α : RenyiOrder) : Region :=
  match α.val with
  | ⊤ => .infinity
  | some r =>
    if r = 1/2 then .half
    else if r = 1 then .one
    else if r < 1 then .ltOne r
    else .gtOne r

@[simp]
theorem region_infinity : (infinity : RenyiOrder).region = .infinity := rfl

/-- The reciprocal `1/alpha` of a Renyi order, in `WithTop ℝ`.

The convention is `recip infinity = 0`, matching the closed-interval identity
`1/alpha + 1/beta = 2` at the boundary pair `(infinity, 1/2)`. For finite
`alpha >= 1/2 > 0` the reciprocal is the ordinary real reciprocal. -/
def recip (α : RenyiOrder) : WithTop ℝ :=
  match α.val with
  | ⊤ => 0
  | some r => ↑(1/r)

@[simp]
theorem recip_infinity : (infinity : RenyiOrder).recip = 0 := rfl

@[simp]
theorem recip_ofReal (r : ℝ) (h : ((1/2 : ℝ) : WithTop ℝ) ≤ ↑r) :
    (ofReal r h).recip = ↑(1/r) := rfl

/-- The source conjugate order `beta = alpha / (2*alpha - 1)`, extended to the
closed interval by the boundary pairs `(1/2, infinity)`, `(1, 1)`,
`(infinity, 1/2)`.

The map is self-inverse on `[1/2, infinity]`; on the interior it is the
ordinary real formula, which is exactly the conjugate used in the upward
conditional Renyi additivity proof. -/
def conjugateOrder (α : RenyiOrder) : RenyiOrder :=
  match h : α.val with
  | ⊤ => ofReal (1/2) (by norm_num)
  | some r =>
    if hhalf : r = 1/2 then infinity
    else if hone : r = 1 then ofReal 1 (by norm_num)
    else
      have hle : 1/2 ≤ r := α.le_of_coe h
      have hβ : 1/2 < conditionalRenyiConjugateOrder r := by
        rcases lt_or_gt_of_ne hone with hlt | hgt
        · exact lt_trans (by norm_num)
            (conditionalRenyiConjugateOrder_gt_one_of_lt_one
              (lt_of_le_of_ne hle (Ne.symm hhalf)) hlt)
        · exact conditionalRenyiConjugateOrder_half_lt_of_one_lt hgt
      ofReal (conditionalRenyiConjugateOrder r) (by exact_mod_cast (le_of_lt hβ))

@[simp]
theorem conjugateOrder_infinity :
    (infinity : RenyiOrder).conjugateOrder = ofReal (1/2) (by norm_num) := rfl

/-- The closure of the conjugate boundary pairs: `1/alpha + 1/beta = 2` over
the full closed interval `[1/2, infinity]`.

At the interior this is the source identity
`1/alpha + 1/(alpha/(2*alpha-1)) = 2`; at the boundary pairs it follows from
the reciprocal convention (`recip infinity = 0`, `recip (1/2) = 2`,
`recip 1 = 1`). This is the closure needed by the entropy uncertainty
relation, which is posed over `alpha, beta in [1/2, infinity]`. -/
theorem recip_add_recip_conjugateOrder (α : RenyiOrder) :
    α.recip + α.conjugateOrder.recip = 2 := by
  obtain ⟨val, hprop⟩ := α
  cases val with
  | top =>
    simp only [recip, conjugateOrder]
    norm_num
  | coe r =>
    by_cases h0 : r = 1/2
    · subst h0
      simp only [recip, conjugateOrder]
      norm_num
    by_cases h1 : r = 1
    · subst h1
      simp only [recip, conjugateOrder]
      norm_num
    · have hle : 1/2 ≤ r := by exact_mod_cast hprop
      have hhalf : 1/2 < r := lt_of_le_of_ne hle (Ne.symm h0)
      have hconj : 1 / conditionalRenyiConjugateOrder r + 1 / r = 2 :=
        conditionalRenyiConjugateOrder_conjugate hhalf
      simp only [conjugateOrder, dif_neg h0, dif_neg h1]
      have h2 : 1/r + 1/conditionalRenyiConjugateOrder r = 2 := by linarith
      show (↑(1/r + 1/conditionalRenyiConjugateOrder r) : WithTop ℝ) = 2
      rw [h2]
      norm_num

/-- Core engine for the total upward sandwiched conditional Renyi entropy over
the full closed order interval `[1/2, infinity]`, dispatched on the order.

The finite-order arm reuses the existing unified surface
`conditionalSandwichedRenyiUpFiniteOrder` (which already handles the
`alpha = 1`, `alpha = 1/2`, and interior pieces); the extended surface adds
the `alpha = infinity` boundary arm (conditional min-entropy). The three
boundary values are the source-named entropies; the source defines the
boundary orders as limits of the sandwiched kernel, so a definitional
boundary matching the source-named limit value is source-faithful. The
state-scoped wrapper is `State.conditionalSandwichedRenyiUpExtendedOrder`. -/
def extendedSurfaceCore (ρ : State (Prod a b)) (α : RenyiOrder) : ℝ :=
  match α.val with
  | ⊤ => ρ.conditionalMinEntropy
  | some r => ρ.conditionalSandwichedRenyiUpFiniteOrder r

@[simp]
theorem extendedSurfaceCore_infinity (ρ : State (Prod a b)) :
    extendedSurfaceCore ρ infinity = ρ.conditionalMinEntropy := rfl

@[simp]
theorem extendedSurfaceCore_ofReal (ρ : State (Prod a b)) (r : ℝ)
    (h : ((1/2 : ℝ) : WithTop ℝ) ≤ ↑r) :
    extendedSurfaceCore ρ (ofReal r h) =
      ρ.conditionalSandwichedRenyiUpFiniteOrder r := rfl

end RenyiOrder

namespace State

/-- The total upward sandwiched conditional Renyi entropy over the full closed
order interval `[1/2, infinity]`, dispatched on `RenyiOrder`.

The surface returns:

* at `alpha = 1` the conditional von Neumann entropy;
* at `alpha = 1/2` the conditional max-entropy;
* at `alpha = infinity` the conditional min-entropy;
* on the interior (`1/2 < alpha < 1` or `1 < alpha`) the source-shaped upward
  sandwiched conditional Renyi entropy, which is support-aware and takes the
  input state at matrix positivity (no full-rank precondition).

The finite-order arms coincide definitionally with the existing
`conditionalSandwichedRenyiUpFiniteOrder`; the `alpha = infinity` arm is the
conditional min-entropy. The three boundary values are the source-named
entropies; the source defines the boundary orders as limits of the sandwiched
kernel, so a definitional boundary matching the source-named limit value is
source-faithful. -/
def conditionalSandwichedRenyiUpExtendedOrder
    (ρ : State (Prod a b)) (α : RenyiOrder) : ℝ :=
  RenyiOrder.extendedSurfaceCore ρ α

@[simp]
theorem conditionalSandwichedRenyiUpExtendedOrder_infinity
    (ρ : State (Prod a b)) :
    ρ.conditionalSandwichedRenyiUpExtendedOrder RenyiOrder.infinity =
      ρ.conditionalMinEntropy :=
  RenyiOrder.extendedSurfaceCore_infinity ρ

@[simp]
theorem conditionalSandwichedRenyiUpExtendedOrder_half (ρ : State (Prod a b)) :
    ρ.conditionalSandwichedRenyiUpExtendedOrder
      (RenyiOrder.ofReal (2 : ℝ)⁻¹ (by norm_num)) = ρ.conditionalMaxEntropy := by
  show RenyiOrder.extendedSurfaceCore ρ
      (RenyiOrder.ofReal (2 : ℝ)⁻¹ (by norm_num)) = ρ.conditionalMaxEntropy
  rw [RenyiOrder.extendedSurfaceCore_ofReal,
    conditionalSandwichedRenyiUpFiniteOrder_half]

@[simp]
theorem conditionalSandwichedRenyiUpExtendedOrder_one (ρ : State (Prod a b)) :
    ρ.conditionalSandwichedRenyiUpExtendedOrder
      (RenyiOrder.ofReal 1 (by norm_num)) = ρ.conditionalEntropy := by
  show RenyiOrder.extendedSurfaceCore ρ (RenyiOrder.ofReal 1 (by norm_num)) =
    ρ.conditionalEntropy
  rw [RenyiOrder.extendedSurfaceCore_ofReal,
    conditionalSandwichedRenyiUpFiniteOrder_one]

theorem conditionalSandwichedRenyiUpExtendedOrder_ltOne
    (ρ : State (Prod a b)) {r : ℝ} (h1 : 1/2 < r) (h2 : r < 1) :
    ρ.conditionalSandwichedRenyiUpExtendedOrder
      (RenyiOrder.ofReal r (by exact_mod_cast (le_of_lt h1))) =
      ρ.conditionalSandwichedRenyiUpSource r (lt_trans (by norm_num) h1)
        (ne_of_lt h2) := by
  have hpos : 0 < r := lt_trans (by norm_num) h1
  have hne : r ≠ 1 := ne_of_lt h2
  have hne_half : r ≠ (2 : ℝ)⁻¹ := by
    rw [show (2 : ℝ)⁻¹ = 1/2 from by norm_num]; exact ne_of_gt h1
  show RenyiOrder.extendedSurfaceCore ρ
      (RenyiOrder.ofReal r (by exact_mod_cast (le_of_lt h1))) =
    ρ.conditionalSandwichedRenyiUpSource r (lt_trans (by norm_num) h1) (ne_of_lt h2)
  rw [RenyiOrder.extendedSurfaceCore_ofReal,
    conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half ρ hpos hne hne_half]

theorem conditionalSandwichedRenyiUpExtendedOrder_gtOne
    (ρ : State (Prod a b)) {r : ℝ} (h : 1 < r) :
    ρ.conditionalSandwichedRenyiUpExtendedOrder
      (RenyiOrder.ofReal r
        (by exact_mod_cast (le_of_lt (lt_trans (by norm_num) h)))) =
      ρ.conditionalSandwichedRenyiUpSource r (lt_trans zero_lt_one h)
        (ne_of_gt h) := by
  have hpos : 0 < r := lt_trans zero_lt_one h
  have hne : r ≠ 1 := ne_of_gt h
  have hne_half : r ≠ (2 : ℝ)⁻¹ := by
    rw [show (2 : ℝ)⁻¹ = 1/2 from by norm_num]; exact ne_of_gt (lt_trans (by norm_num) h)
  show RenyiOrder.extendedSurfaceCore ρ
      (RenyiOrder.ofReal r
        (by exact_mod_cast (le_of_lt (lt_trans (by norm_num) h)))) =
    ρ.conditionalSandwichedRenyiUpSource r (lt_trans zero_lt_one h) (ne_of_gt h)
  rw [RenyiOrder.extendedSurfaceCore_ofReal,
    conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half ρ hpos hne hne_half]

/-- On positive-definite states, the extended interior surface agrees with the
existing finite-real positive-definite-gated `conditionalSandwichedRenyi`.

This is the strict-acceptance compatibility hinge: on the interior
`1/2 < alpha`, `alpha != 1`, the extended surface does not weaken the existing
finite-real surface. The boundary orders (`alpha = 1/2`, `1`, `infinity`) are
the source-named entropies and are handled by the corresponding simp lemmas. -/
theorem conditionalSandwichedRenyiUpExtendedOrder_ofReal
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    {r : ℝ} (hhalf : 1/2 < r) (hne : r ≠ 1) :
    ρ.conditionalSandwichedRenyiUpExtendedOrder
      (RenyiOrder.ofReal r (by exact_mod_cast (le_of_lt hhalf))) =
      ρ.conditionalSandwichedRenyi hρ r (le_of_lt hhalf) hne := by
  have hpos : 0 < r := lt_trans (by norm_num) hhalf
  have hne_half : r ≠ (2 : ℝ)⁻¹ := by
    rw [show (2 : ℝ)⁻¹ = 1/2 from by norm_num]; exact ne_of_gt hhalf
  show RenyiOrder.extendedSurfaceCore ρ
      (RenyiOrder.ofReal r (by exact_mod_cast (le_of_lt hhalf))) =
    ρ.conditionalSandwichedRenyi hρ r (le_of_lt hhalf) hne
  rw [RenyiOrder.extendedSurfaceCore_ofReal,
    conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half ρ hpos hne hne_half,
    conditionalSandwichedRenyiUpSource_eq_conditionalSandwichedRenyiUp
      ρ hρ r (le_of_lt hhalf) hne, conditionalSandwichedRenyiUp_eq]

/-- In-module smoke: the extended surface has the expected boundary at
`alpha = infinity`. -/
example (ρ : State (Prod a b)) :
    ρ.conditionalSandwichedRenyiUpExtendedOrder RenyiOrder.infinity =
      ρ.conditionalMinEntropy :=
  conditionalSandwichedRenyiUpExtendedOrder_infinity ρ

end State

end

end QIT
