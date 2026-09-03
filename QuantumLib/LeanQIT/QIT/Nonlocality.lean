/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Nonlocality.Bell
public import QIT.Nonlocality.Tsirelson
public import QIT.Nonlocality.TwoQubit
public import QIT.Nonlocality.SelfTesting
public import QIT.Nonlocality.ProjectiveRealization
public import QIT.Nonlocality.YangNavascues
public import QIT.Nonlocality.YangNavascues.BobLocal
public import QIT.Nonlocality.YangNavascues.RankOneSupport
public import QIT.Nonlocality.YangNavascues.BobSupport
public import QIT.Nonlocality.YangNavascues.Fourier
public import QIT.Nonlocality.YangNavascues.LocalIsometry
public import QIT.Nonlocality.YangNavascues.Coherence
public import QIT.Nonlocality.YangNavascues.Action
public import QIT.Nonlocality.YangNavascues.Extraction

/-!
# Nonlocality interfaces

Thin nonlocality-facing import surface for Bell/CHSH, Tsirelson, and
self-testing work.
-/

@[expose] public section

universe uX uY uA uB u v w z uGA uGB

namespace QIT
namespace Nonlocality

namespace SelfTestingDefinition

variable {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]
variable {TA : Type w} {TB : Type z}
variable [Fintype TA] [DecidableEq TA] [Fintype TB] [DecidableEq TB]

/--
Public nonlocality entrypoint for the junk-free special case of a full state
self-testing theorem. Use `main_with_aux` for the source-facing version with
auxiliary output.
-/
public theorem main {p : Bell.Behavior X Y A B} {target : State (TA × TB)}
    (hRealizes : Bell.RealizesTargetState p target)
    (hAll :
      ∀ R : Bell.QuantumRealization X Y A B,
        R.RealizesBehavior p →
          letI : Fintype R.HA := R.fintypeHA
          letI : DecidableEq R.HA := R.decidableEqHA
          letI : Fintype R.HB := R.fintypeHB
          letI : DecidableEq R.HB := R.decidableEqHB
          Bell.ExtractsBipartiteState R.rho target) :
    Bell.SelfTestsState p target :=
  SelfTesting.Definition.main hRealizes hAll

/--
Source-facing public nonlocality entrypoint for a full state self-testing
theorem with explicit auxiliary garbage in the local-isometry output.
-/
public theorem main_with_aux {p : Bell.Behavior X Y A B} {target : State (TA × TB)}
    (hRealizes :
      Bell.RealizesTargetStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target)
    (hAll :
      ∀ R : Bell.QuantumRealization X Y A B,
        R.RealizesBehavior p →
          ∃ (GA : Type uGA) (GB : Type uGB),
            ∃ (instGA : Fintype GA) (decGA : DecidableEq GA)
              (instGB : Fintype GB) (decGB : DecidableEq GB),
              letI : Fintype GA := instGA
              letI : DecidableEq GA := decGA
              letI : Fintype GB := instGB
              letI : DecidableEq GB := decGB
              ∃ garbage : State (GA × GB),
                letI : Fintype R.HA := R.fintypeHA
                letI : DecidableEq R.HA := R.decidableEqHA
                letI : Fintype R.HB := R.fintypeHB
                letI : DecidableEq R.HB := R.decidableEqHB
                Bell.ExtractsBipartiteStateWithAux R.rho garbage target) :
    Bell.SelfTestsStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target :=
  SelfTesting.Definition.main_with_aux hRealizes hAll

end SelfTestingDefinition

namespace SelfTestingManifest

variable {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]
variable {HA : Type u} {HB : Type v} {TA : Type w} {TB : Type z}
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
variable [Fintype TA] [DecidableEq TA] [Fintype TB] [DecidableEq TB]

/--
Public nonlocality entrypoint for the junk-free special case of the manifest
self-testing witness. Use `main_with_aux` for the source-facing version with
auxiliary output.
-/
public theorem main (R : Bell.QuantumRealization X Y A B)
    {p : Bell.Behavior X Y A B} {target : State (TA × TB)}
    (hR : R.RealizesBehavior p)
    (hExtract :
      letI : Fintype R.HA := R.fintypeHA
      letI : DecidableEq R.HA := R.decidableEqHA
      letI : Fintype R.HB := R.fintypeHB
      letI : DecidableEq R.HB := R.decidableEqHB
      Bell.ExtractsBipartiteState R.rho target) :
    Bell.RealizesTargetState p target :=
  SelfTesting.Manifest.main R hR hExtract

/-- Project the manifest realization witness from a full self-testing theorem. -/
public theorem of_selfTestsState {p : Bell.Behavior X Y A B}
    {target : State (TA × TB)}
    (h : Bell.SelfTestsState p target) :
    Bell.RealizesTargetState p target :=
  SelfTesting.Manifest.of_selfTestsState h

/--
Source-facing public nonlocality entrypoint for the manifest self-testing
witness with explicit auxiliary garbage in the local-isometry output.
-/
public theorem main_with_aux (R : Bell.QuantumRealization X Y A B)
    {p : Bell.Behavior X Y A B} {target : State (TA × TB)}
    {GA : Type uGA} {GB : Type uGB}
    [Fintype GA] [DecidableEq GA] [Fintype GB] [DecidableEq GB]
    (garbage : State (GA × GB))
    (hR : R.RealizesBehavior p)
    (hExtract :
      letI : Fintype R.HA := R.fintypeHA
      letI : DecidableEq R.HA := R.decidableEqHA
      letI : Fintype R.HB := R.fintypeHB
      letI : DecidableEq R.HB := R.decidableEqHB
      Bell.ExtractsBipartiteStateWithAux R.rho garbage target) :
    Bell.RealizesTargetStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target :=
  SelfTesting.Manifest.main_with_aux.{w, z, uX, uY, uA, uB, uGA, uGB}
    R garbage hR hExtract

/--
Project the auxiliary-garbage manifest realization witness from a full
source-strength self-testing theorem.
-/
public theorem of_selfTestsStateWithAux {p : Bell.Behavior X Y A B}
    {target : State (TA × TB)}
    (h : Bell.SelfTestsStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target) :
    Bell.RealizesTargetStateWithAux.{w, z, uX, uY, uA, uB, uGA, uGB} p target :=
  SelfTesting.Manifest.of_selfTestsStateWithAux h

end SelfTestingManifest

namespace ProjectiveRealization

variable {X : Type uX} {Y : Type uY} {A : Type uA} {B : Type uB}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B] [Inhabited A] [Inhabited B]

/-- Public nonlocality entrypoint for replacing finite POVM realizations by projective ones. -/
public theorem main (R : Bell.QuantumRealization X Y A B) :
    ∃ PR : Bell.ProjectiveQuantumRealization X Y A B,
      ∀ a b x y, PR.prob a b x y = R.prob a b x y :=
  SelfTesting.ProjectiveRealization.main R

end ProjectiveRealization

end Nonlocality
end QIT
