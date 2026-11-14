/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.LeanQIT.Nonlocality.Bell
public import QuantumLib.LeanQIT.Nonlocality.Tsirelson
public import QuantumLib.LeanQIT.Nonlocality.TwoQubit
public import QuantumLib.LeanQIT.Nonlocality.SelfTesting
public import QuantumLib.LeanQIT.Nonlocality.ProjectiveRealization
public import QuantumLib.LeanQIT.Nonlocality.YangNavascues
public import QuantumLib.LeanQIT.Nonlocality.YangNavascues.BobLocal
public import QuantumLib.LeanQIT.Nonlocality.YangNavascues.RankOneSupport
public import QuantumLib.LeanQIT.Nonlocality.YangNavascues.BobSupport
public import QuantumLib.LeanQIT.Nonlocality.YangNavascues.Fourier
public import QuantumLib.LeanQIT.Nonlocality.YangNavascues.LocalIsometry
public import QuantumLib.LeanQIT.Nonlocality.YangNavascues.Coherence
public import QuantumLib.LeanQIT.Nonlocality.YangNavascues.Action
public import QuantumLib.LeanQIT.Nonlocality.YangNavascues.Extraction

/-!
# Nonlocality interfaces

Thin nonlocality-facing import surface for Bell/CHSH, Tsirelson, and
self-testing work. The entry points are `QIT.SelfTesting.Definition.main`,
`QIT.SelfTesting.Manifest.main` and `QIT.SelfTesting.ProjectiveRealization.main`.
-/
