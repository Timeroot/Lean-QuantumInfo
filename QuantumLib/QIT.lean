/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Init
public import QuantumLib.QIT.Util
public import QuantumLib.QIT.Core
public import QuantumLib.QIT.States
public import QuantumLib.QIT.Channels
public import QuantumLib.QIT.Measurements
public import QuantumLib.QIT.Classical
public import QuantumLib.QIT.Information
public import QuantumLib.QIT.OneShot
public import QuantumLib.QIT.HypothesisTesting
public import QuantumLib.QIT.Asymptotic
public import QuantumLib.QIT.Symmetry
public import QuantumLib.QIT.Coding
public import QuantumLib.QIT.Protocols
public import QuantumLib.QIT.Security
public import QuantumLib.QIT.Entanglement
public import QuantumLib.QIT.Nonlocality

/-!
# QIT

QuAIR's Lean-QIT: entropies and divergences, one-shot and asymptotic rates, coding theorems,
hypothesis testing, symmetry, nonlocality and protocols, built on the finite-dimensional matrix
model of `QIT.CMatrix`. `QuantumLib.QIT.Bridge` records how it lines up with the rest of
QuantumLib.
-/
