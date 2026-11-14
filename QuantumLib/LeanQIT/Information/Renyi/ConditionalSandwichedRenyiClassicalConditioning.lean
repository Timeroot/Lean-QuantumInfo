/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

import Mathlib.Algebra.Order.CompleteField
public import QuantumLib.LeanQIT.Information.Renyi.ConditionalRenyiClassical
public import QuantumLib.LeanQIT.Information.Renyi.SandwichedRenyiOptimizedUSC
public import QuantumLib.LeanQIT.Information.Renyi.ConditionalSandwichedRenyiDuality
public import QuantumLib.LeanQIT.Information.Renyi.ConditionalSandwichedRenyiAdditivity
public import QuantumLib.LeanQIT.Measurements.Projective
public import QuantumLib.LeanQIT.OneShot.CQGuessing
public import QuantumLib.LeanQIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.BlockAlgebra
public import QuantumLib.LeanQIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.LowAlphaQDecomposition
public import QuantumLib.LeanQIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.HighAlphaSupport
public import QuantumLib.LeanQIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.ScalarOptimizer
public import QuantumLib.LeanQIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.RegularizedSourceWrappers
public import QuantumLib.LeanQIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.ArbitraryReference

/-!
# Sandwiched conditional Renyi entropy under classical conditioning

Facade for the dependency-ordered responsibility-layer modules (cq/block
algebra, low-alpha Q decomposition, high-alpha support route, scalar
optimizer / component bridge, and the public source-shaped wrappers).
-/
