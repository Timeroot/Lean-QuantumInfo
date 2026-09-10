/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Nonlocality.Bell
public import QuantumLib.QIT.Nonlocality.Tsirelson
public import QuantumLib.QIT.Nonlocality.TwoQubit
public import QuantumLib.QIT.Nonlocality.SelfTesting
public import QuantumLib.QIT.Nonlocality.ProjectiveRealization
public import QuantumLib.QIT.Nonlocality.YangNavascues
public import QuantumLib.QIT.Nonlocality.YangNavascues.BobLocal
public import QuantumLib.QIT.Nonlocality.YangNavascues.RankOneSupport
public import QuantumLib.QIT.Nonlocality.YangNavascues.BobSupport
public import QuantumLib.QIT.Nonlocality.YangNavascues.Fourier
public import QuantumLib.QIT.Nonlocality.YangNavascues.LocalIsometry
public import QuantumLib.QIT.Nonlocality.YangNavascues.Coherence
public import QuantumLib.QIT.Nonlocality.YangNavascues.Action
public import QuantumLib.QIT.Nonlocality.YangNavascues.Extraction

/-!
# Nonlocality interfaces

Thin nonlocality-facing import surface for Bell/CHSH, Tsirelson, and
self-testing work. The entry points are `QIT.SelfTesting.Definition.main`,
`QIT.SelfTesting.Manifest.main` and `QIT.SelfTesting.ProjectiveRealization.main`.
-/
