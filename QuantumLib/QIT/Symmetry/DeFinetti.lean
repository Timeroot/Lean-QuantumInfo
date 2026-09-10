/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Symmetry.DeFinetti.ProfilesMixtures
public import QuantumLib.QIT.Symmetry.DeFinetti.Domination
public import QuantumLib.QIT.Symmetry.DeFinetti.Twirling
public import QuantumLib.QIT.Symmetry.DeFinetti.RennerProjectors
public import QuantumLib.QIT.Symmetry.DeFinetti.Postselection

/-!
# Quantum de Finetti representation

Permutation-invariant states are approximated by mixtures of i.i.d. states
(renner-2007-symmetry-independence, sub.tex:618 thm:main;
christandl-koenig-renner-2008-postselection, .tex:291 thm:main).

The pieces live in the submodules: `DeFinetti.ProfilesMixtures` sets up the type
profiles and the finite i.i.d. mixtures the approximation is measured against,
`DeFinetti.Twirling` and `DeFinetti.RennerProjectors` supply the symmetry
averaging and the symmetric-subspace projectors, and `DeFinetti.Domination` and
`DeFinetti.Postselection` give the operator domination and post-selection
bounds.  This module only re-exports them.
-/
