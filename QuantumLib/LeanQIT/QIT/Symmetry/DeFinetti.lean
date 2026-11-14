/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Symmetry.DeFinetti.ProfilesMixtures
public import QIT.Symmetry.DeFinetti.Domination
public import QIT.Symmetry.DeFinetti.Twirling
public import QIT.Symmetry.DeFinetti.RennerProjectors
public import QIT.Symmetry.DeFinetti.Postselection

/-!
# Quantum de Finetti representation

Permutation-invariant states are approximated by mixtures of i.i.d. states
(renner-2007-symmetry-independence, sub.tex:618 thm:main;
christandl-koenig-renner-2008-postselection, .tex:291 thm:main).

The full de Finetti/post-selection proof is intentionally not stated here.
This module currently exposes only the route surface that imports the symmetric
tensor-power support.
-/
