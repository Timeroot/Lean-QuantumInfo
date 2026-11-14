/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/
module

import Mathlib.Algebra.Order.CompleteField
public import QIT.Information.Renyi.ConditionalRenyiClassical
public import QIT.Information.Renyi.SandwichedRenyiOptimizedUSC
public import QIT.Information.Renyi.ConditionalSandwichedRenyiDuality
public import QIT.Information.Renyi.ConditionalSandwichedRenyiAdditivity
public import QIT.Measurements.Projective
public import QIT.OneShot.CQGuessing
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.BlockAlgebra
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.LowAlphaQDecomposition
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.HighAlphaSupport
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.ScalarOptimizer
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.RegularizedSourceWrappers
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning.ArbitraryReferenceWrappers

/-!
# Sandwiched conditional Renyi entropy under classical conditioning

Facade for the dependency-ordered responsibility-layer modules (cq/block
algebra, low-alpha Q decomposition, high-alpha support route, scalar
optimizer / component bridge, and the public source-shaped wrappers, split
in two for the 2500-line budget).  The public surface is unchanged from the
original monolithic module; this file re-exports it for downstream
compatibility.
-/

@[expose] public section

namespace QIT
namespace Information
namespace Renyi

end Renyi
end Information
end QIT
