/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.Entropy
public import QIT.States.Geometry.Fidelity

/-!
# Universal recovery map (Fawzi-Renner)

The Fawzi-Renner theorem and its recovery channel are reserved for the
information-recovery layer.

This module provides the import surface for recovery-map definitions. The
linear map construction (`embedRecoveryMap`) and the full inequality proof
will be added here once their mathematical prerequisites are available.
-/

@[expose] public section

namespace QIT

/- The recovery channel and the full Fawzi-Renner inequality are deferred until
   the required fidelity and conditional mutual information APIs are complete. -/

end QIT
