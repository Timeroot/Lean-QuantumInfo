/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.POVMProbability
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Data.Fintype.BigOperators

/-!
# Bell-scenario behaviors

Finite Bell scenarios are represented by a nonnegative real probability table
`p(a,b|x,y)` normalized over the outcome pair for each settings pair
[Brunner2013BellNonlocality, ReviewALL.tex:204-209].
-/

@[expose] public section

open scoped NNReal

namespace QIT
namespace Bell

universe uX uY uA uB

noncomputable section

/-- Coordinate type for the real vector associated to a Bell behavior. -/
abbrev BellIndex (X : Type uX) (Y : Type uY) (A : Type uA) (B : Type uB) :=
  A × B × X × Y

/--
A finite Bell behavior `p(a,b|x,y)` as an `NNReal` table whose outcome pair
distribution is in the standard simplex for every settings pair
[Brunner2013BellNonlocality, ReviewALL.tex:204-209].
-/
structure Behavior (X : Type uX) (Y : Type uY) (A : Type uA) (B : Type uB)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  /-- Joint probability `p(a,b|x,y)`. -/
  prob : A → B → X → Y → ℝ≥0
  /-- For fixed settings, the outcome-pair table is a probability simplex. -/
  prob_mem_stdSimplex :
    ∀ x y, (fun ab : A × B => prob ab.1 ab.2 x y) ∈ stdSimplex ℝ≥0 (A × B)

namespace Behavior

variable {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- Outcome probabilities sum to one for every settings pair. -/
theorem sum_prob (p : Behavior X Y A B) (x : X) (y : Y) :
    ∑ a, ∑ b, p.prob a b x y = 1 := by
  have h := (p.prob_mem_stdSimplex x y).2
  simpa [Fintype.sum_prod_type] using h

/-- Real coordinate table used for convex-hull statements. -/
def realTable (p : Behavior X Y A B) : BellIndex X Y A B → ℝ
  | (a, b, x, y) => p.prob a b x y

end Behavior

/--
No-signaling says Alice's marginal is independent of Bob's setting and Bob's
marginal is independent of Alice's setting
[Brunner2013BellNonlocality, ReviewALL.tex:214-219].
-/
def IsNoSignaling {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (p : Behavior X Y A B) : Prop :=
  (∀ a x y y', ∑ b, p.prob a b x y = ∑ b, p.prob a b x y') ∧
    (∀ b y x x', ∑ a, p.prob a b x y = ∑ a, p.prob a b x' y)

/-- A deterministic local strategy chooses one output for each local setting. -/
abbrev DeterministicStrategy
    (X : Type uX) (Y : Type uY) (A : Type uA) (B : Type uB) :=
  (X → A) × (Y → B)

/--
The deterministic behavior associated to local output assignments
`a = A(x)` and `b = B(y)` [Brunner2013BellNonlocality,
ReviewALL.tex:304-327].
-/
def deterministicBehavior {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (strategy : DeterministicStrategy X Y A B) : Behavior X Y A B where
  prob a b x y := if strategy.1 x = a ∧ strategy.2 y = b then 1 else 0
  prob_mem_stdSimplex x y := by
    classical
    constructor
    · intro ab
      positivity
    · change
        ∑ ab : A × B,
            (if strategy.1 x = ab.1 ∧ strategy.2 y = ab.2 then 1 else 0 : ℝ≥0) = 1
      trans
        ∑ ab : A × B,
            (if ab = (strategy.1 x, strategy.2 y) then 1 else 0 : ℝ≥0)
      · refine Finset.sum_congr rfl ?_
        intro ab _
        by_cases h : ab = (strategy.1 x, strategy.2 y)
        · cases h
          simp
        · have hne : ¬(strategy.1 x = ab.1 ∧ strategy.2 y = ab.2) := by
            intro hab
            exact h (Prod.ext hab.1.symm hab.2.symm)
          simp [h, hne]
      · simp

/-- The set of deterministic local behavior tables. -/
def deterministicTables {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    Set (BellIndex X Y A B → ℝ) :=
  Set.range fun strategy : DeterministicStrategy X Y A B =>
    (deterministicBehavior strategy).realTable

/--
Local behaviors are finite convex mixtures of deterministic local behaviors
[Brunner2013BellNonlocality, ReviewALL.tex:244-248] and
[Brunner2013BellNonlocality, ReviewALL.tex:304-327].
-/
def IsLocal {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (p : Behavior X Y A B) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι),
    ∃ weights : ι → ℝ,
      ∃ strategies : ι → DeterministicStrategy X Y A B,
        (∀ i, 0 ≤ weights i) ∧
          (∑ i, weights i = 1) ∧
            p.realTable = ∑ i, weights i • (deterministicBehavior (strategies i)).realTable

/-- Every deterministic local behavior is local. -/
theorem deterministic_isLocal {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (strategy : DeterministicStrategy X Y A B) :
    IsLocal (deterministicBehavior strategy) := by
  refine ⟨PUnit, inferInstance, fun _ => 1, fun _ => strategy, ?_, ?_, ?_⟩
  · intro _
    norm_num
  · simp
  · ext idx
    rcases idx with ⟨a, b, x, y⟩
    simp [Behavior.realTable]

namespace IsLocal

/-- A local finite mixture belongs to the convex hull of deterministic tables. -/
theorem mem_convexHull {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {p : Behavior X Y A B} (hp : IsLocal p) :
    p.realTable ∈ convexHull ℝ (deterministicTables (X := X) (Y := Y) (A := A) (B := B)) := by
  rcases hp with ⟨ι, hι, weights, strategies, hnonneg, hsum, htable⟩
  letI : Fintype ι := hι
  refine mem_convexHull_of_exists_fintype weights
    (fun i => (deterministicBehavior (strategies i)).realTable) hnonneg hsum ?_ htable.symm
  intro i
  exact ⟨strategies i, rfl⟩

end IsLocal

/-- Convex-hull membership gives an explicit finite local mixture. -/
theorem isLocal_of_mem_convexHull
    {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {p : Behavior X Y A B}
    (hp : p.realTable ∈
      convexHull ℝ (deterministicTables (X := X) (Y := Y) (A := A) (B := B))) :
    IsLocal p := by
  classical
  rcases (mem_convexHull_iff_exists_fintype.mp hp) with
    ⟨ι, hι, weights, tables, hnonneg, hsum, htables, hcenter⟩
  letI : Fintype ι := hι
  choose strategies hstrategies using htables
  refine ⟨ι, hι, weights, strategies, hnonneg, hsum, ?_⟩
  rw [← hcenter]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← hstrategies i]

/-- `IsLocal` is equivalent to convex-hull membership of deterministic tables. -/
theorem isLocal_iff_mem_convexHull
    {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {p : Behavior X Y A B} :
    IsLocal p ↔
      p.realTable ∈
        convexHull ℝ (deterministicTables (X := X) (Y := Y) (A := A) (B := B)) := by
  constructor
  · exact IsLocal.mem_convexHull
  · exact isLocal_of_mem_convexHull

/--
A finite tensor-product quantum realization: a bipartite state, local POVMs,
and a joint POVM whose effects are `M_{a|x} ⊗ M_{b|y}`
[Brunner2013BellNonlocality, ReviewALL.tex:254-259].
-/
structure QuantumRealization
    (X : Type uX) (Y : Type uY) (A : Type uA) (B : Type uB)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] where
  HA : Type (max uX uY uA uB)
  HB : Type (max uX uY uA uB)
  [fintypeHA : Fintype HA]
  [decidableEqHA : DecidableEq HA]
  [fintypeHB : Fintype HB]
  [decidableEqHB : DecidableEq HB]
  /-- Bipartite state shared by Alice and Bob. -/
  rho : State (HA × HB)
  /-- Alice's POVM for each setting. -/
  alice : X → POVM A HA
  /-- Bob's POVM for each setting. -/
  bob : Y → POVM B HB
  /-- Joint measurement for each settings pair. -/
  joint : X → Y → POVM (A × B) (HA × HB)
  /-- The joint POVM has tensor-product effects. -/
  joint_effects : ∀ x y outcome,
    (joint x y).effects outcome =
      Matrix.kronecker ((alice x).effects outcome.1) ((bob y).effects outcome.2)

namespace QuantumRealization

variable {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Born-rule outcome probability of a tensor-product quantum realization. -/
def prob (realization : QuantumRealization X Y A B) (a : A) (b : B) (x : X) (y : Y) :
    ℝ≥0 :=
  letI : Fintype realization.HA := realization.fintypeHA
  letI : DecidableEq realization.HA := realization.decidableEqHA
  letI : Fintype realization.HB := realization.fintypeHB
  letI : DecidableEq realization.HB := realization.decidableEqHB
  (realization.joint x y).prob realization.rho (a, b)

end QuantumRealization

/-- Behaviors realized by a finite-dimensional tensor-product quantum model. -/
def IsQuantum {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (p : Behavior X Y A B) : Prop :=
  ∃ realization : QuantumRealization X Y A B,
    ∀ a b x y, p.prob a b x y = realization.prob a b x y

/-- The CHSH settings/outcomes behavior type. -/
abbrev CHSHBehavior :=
  Behavior (Fin 2) (Fin 2) Bool Bool

namespace CHSH

/--
The CHSH `Bool` outcome convention: `false` represents `+1`, and `true`
represents `-1` [Brunner2013BellNonlocality, ReviewALL.tex:142-152].
-/
def outcomeSign : Bool → ℝ
  | false => 1
  | true => -1

/-- CHSH coefficient for the four settings in `S = E₀₀ + E₀₁ + E₁₀ - E₁₁`. -/
def settingCoeff (x y : Fin 2) : ℝ :=
  if x = 0 ∧ y = 0 then 1
  else if x = 0 ∧ y = 1 then 1
  else if x = 1 ∧ y = 0 then 1
  else if x = 1 ∧ y = 1 then -1
  else 0

/-- Correlator of a real behavior table at one CHSH settings pair. -/
def tableCorrelator (table : BellIndex (Fin 2) (Fin 2) Bool Bool → ℝ) (x y : Fin 2) :
    ℝ :=
  ∑ ab : Bool × Bool, outcomeSign ab.1 * outcomeSign ab.2 * table (ab.1, ab.2, x, y)

/-- Correlator `⟨a_x b_y⟩ = ∑ a b, a b p(ab|xy)` for the CHSH convention. -/
def correlator (p : CHSHBehavior) (x y : Fin 2) : ℝ :=
  tableCorrelator p.realTable x y

/-- Linear CHSH functional on a real behavior table. -/
def tableValue (table : BellIndex (Fin 2) (Fin 2) Bool Bool → ℝ) : ℝ :=
  tableCorrelator table 0 0 + tableCorrelator table 0 1 +
    tableCorrelator table 1 0 - tableCorrelator table 1 1

/-- The CHSH value `S = E₀₀ + E₀₁ + E₁₀ - E₁₁`. -/
def value (p : CHSHBehavior) : ℝ :=
  tableValue p.realTable

theorem settingCoeff_zero_zero : settingCoeff 0 0 = 1 := by
  simp [settingCoeff]

theorem settingCoeff_zero_one : settingCoeff 0 1 = 1 := by
  simp [settingCoeff]

theorem settingCoeff_one_zero : settingCoeff 1 0 = 1 := by
  simp [settingCoeff]

theorem settingCoeff_one_one : settingCoeff 1 1 = -1 := by
  simp [settingCoeff]

/-- The linear-table definition unfolds to the usual four-correlator CHSH formula. -/
theorem value_eq_correlators (p : CHSHBehavior) :
    value p =
      correlator p 0 0 + correlator p 0 1 + correlator p 1 0 - correlator p 1 1 := by
  classical
  simp [value, tableValue, correlator]

/-- Deterministic strategies realize the product of the assigned outcome signs. -/
theorem correlator_deterministicBehavior
    (strategy : DeterministicStrategy (Fin 2) (Fin 2) Bool Bool) (x y : Fin 2) :
    correlator (deterministicBehavior strategy) x y =
      outcomeSign (strategy.1 x) * outcomeSign (strategy.2 y) := by
  classical
  cases hAlice : strategy.1 x <;> cases hBob : strategy.2 y <;>
    simp [correlator, tableCorrelator, deterministicBehavior, Behavior.realTable, hAlice, hBob,
      outcomeSign, Fintype.sum_prod_type]

/--
Every deterministic CHSH corner satisfies the classical CHSH upper bound.
This is the finite-corner case in the local polytope proof
[Brunner2013BellNonlocality, ReviewALL.tex:300-347].
-/
theorem value_deterministicBehavior_le_two
    (strategy : DeterministicStrategy (Fin 2) (Fin 2) Bool Bool) :
    value (deterministicBehavior strategy) ≤ 2 := by
  classical
  rw [value_eq_correlators]
  cases hA0 : strategy.1 0 <;> cases hA1 : strategy.1 1 <;>
    cases hB0 : strategy.2 0 <;> cases hB1 : strategy.2 1 <;>
      simp [correlator_deterministicBehavior, hA0, hA1, hB0, hB1, outcomeSign] <;>
      norm_num

theorem tableCorrelator_sum_smul {ι : Type} [Fintype ι] (weights : ι → ℝ)
    (tables : ι → BellIndex (Fin 2) (Fin 2) Bool Bool → ℝ) (x y : Fin 2) :
    tableCorrelator (∑ i, weights i • tables i) x y =
      ∑ i, weights i * tableCorrelator (tables i) x y := by
  classical
  unfold tableCorrelator
  simp [Pi.smul_apply, Finset.mul_sum, mul_assoc, mul_comm]
  rw [Finset.sum_comm]

theorem tableValue_sum_smul {ι : Type} [Fintype ι] (weights : ι → ℝ)
    (tables : ι → BellIndex (Fin 2) (Fin 2) Bool Bool → ℝ) :
    tableValue (∑ i, weights i • tables i) =
      ∑ i, weights i * tableValue (tables i) := by
  classical
  simp [tableValue, tableCorrelator_sum_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    mul_add, mul_sub]

/--
Local CHSH behaviors satisfy the classical bound `S ≤ 2`
[Brunner2013BellNonlocality, ReviewALL.tex:142-152].
-/
theorem value_le_two_of_isLocal (p : CHSHBehavior) (hp : IsLocal p) :
    value p ≤ 2 := by
  classical
  rcases hp with ⟨ι, hι, weights, strategies, hnonneg, hsum, htable⟩
  letI : Fintype ι := hι
  rw [value, htable, tableValue_sum_smul]
  calc
    ∑ i, weights i * tableValue (deterministicBehavior (strategies i)).realTable
        ≤ ∑ i, weights i * 2 := by
          refine Finset.sum_le_sum ?_
          intro i _
          simpa [value] using mul_le_mul_of_nonneg_left
            (value_deterministicBehavior_le_two (strategies i)) (hnonneg i)
    _ = 2 := by
      rw [← Finset.sum_mul, hsum]
      norm_num

/--
The PR-box winning condition in the CHSH Bool convention.  Since
`false = +1` and `true = -1`, unequal Bool outcomes give product `-1`.
Thus the PR box has equal outcomes except at the `(1,1)` settings pair.
-/
def prBoxCondition (a b : Bool) (x y : Fin 2) : Bool :=
  decide ((a ≠ b) ↔ (x = 1 ∧ y = 1))

/-- PR-box probability table: `1/2` on the two winning outcome pairs, else `0`. -/
def prBoxProb (a b : Bool) (x y : Fin 2) : ℝ≥0 :=
  if prBoxCondition a b x y then (1 / 2 : ℝ≥0) else 0

/--
The CHSH PR box, the no-signaling behavior with algebraic CHSH value `4`
[Brunner2013BellNonlocality, ReviewALL.tex:581-599].
-/
def prBox : CHSHBehavior where
  prob := prBoxProb
  prob_mem_stdSimplex x y := by
    classical
    constructor
    · intro ab
      simp [prBoxProb]
    · change ∑ ab : Bool × Bool, prBoxProb ab.1 ab.2 x y = 1
      fin_cases x <;> fin_cases y <;>
        simp [prBoxProb, prBoxCondition, Fintype.sum_prod_type]
      norm_num

theorem prBox_prob (a b : Bool) (x y : Fin 2) :
    prBox.prob a b x y = prBoxProb a b x y := rfl

theorem prBox_correlator_zero_zero : correlator prBox 0 0 = 1 := by
  simp [correlator, tableCorrelator, prBox, prBoxProb, prBoxCondition,
    Behavior.realTable, outcomeSign, Fintype.sum_prod_type]
  norm_num

theorem prBox_correlator_zero_one : correlator prBox 0 1 = 1 := by
  simp [correlator, tableCorrelator, prBox, prBoxProb, prBoxCondition,
    Behavior.realTable, outcomeSign, Fintype.sum_prod_type]
  norm_num

theorem prBox_correlator_one_zero : correlator prBox 1 0 = 1 := by
  simp [correlator, tableCorrelator, prBox, prBoxProb, prBoxCondition,
    Behavior.realTable, outcomeSign, Fintype.sum_prod_type]
  norm_num

theorem prBox_correlator_one_one : correlator prBox 1 1 = -1 := by
  simp [correlator, tableCorrelator, prBox, prBoxProb, prBoxCondition,
    Behavior.realTable, outcomeSign, Fintype.sum_prod_type]
  norm_num

/-- The PR box reaches the algebraic CHSH value `4`. -/
theorem value_prBox : value prBox = 4 := by
  rw [value_eq_correlators]
  rw [prBox_correlator_zero_zero, prBox_correlator_zero_one,
    prBox_correlator_one_zero, prBox_correlator_one_one]
  norm_num

/-- The PR box satisfies the no-signaling constraints. -/
theorem prBox_isNoSignaling : IsNoSignaling prBox := by
  classical
  constructor
  · intro a x y y'
    fin_cases x <;> fin_cases y <;> fin_cases y' <;> cases a <;>
      simp [prBox, prBoxProb, prBoxCondition]
  · intro b y x x'
    fin_cases y <;> fin_cases x <;> fin_cases x' <;> cases b <;>
      simp [prBox, prBoxProb, prBoxCondition]

/-- The PR box is not local, since it violates the local CHSH bound. -/
theorem prBox_not_isLocal : ¬ IsLocal prBox := by
  intro hlocal
  have hle : value prBox ≤ 2 := value_le_two_of_isLocal prBox hlocal
  rw [value_prBox] at hle
  norm_num at hle

/-- Witness form: some no-signaling behavior is not local. -/
theorem exists_noSignaling_not_isLocal :
    ∃ p : CHSHBehavior, IsNoSignaling p ∧ ¬ IsLocal p :=
  ⟨prBox, prBox_isNoSignaling, prBox_not_isLocal⟩

end CHSH

/-- There are 16 deterministic local strategies in the CHSH scenario. -/
theorem chsh_deterministicStrategy_card :
    Fintype.card (DeterministicStrategy (Fin 2) (Fin 2) Bool Bool) = 16 := by
  simp [DeterministicStrategy]

end

end Bell
end QIT
