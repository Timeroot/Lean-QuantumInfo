/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

module

public import QuantumLib.LeanQIT.Bridge.Entropy

/-!
# The bridge between Lean-QIT and the rest of QuantumLib

Lean-QIT arrived with a tower of quantum information objects of its own — states, kets, POVMs,
channels and the maps between matrix algebras — built on top of Mathlib alongside the one physlib
already had. The two towers are now one. States are `MState`, kets are `Ket`, measurements are
`POVM`, channels are `CPTPOp`, and `QIT.MatrixMap a b` is `MatrixMap a b ℂ`, so at the level of
objects there is nothing left to translate: Lean-QIT's theories of matrix maps, of states, of kets
and of POVMs are derived from physlib's in `QuantumLib.LeanQIT.Core.Map`, `QuantumLib.LeanQIT.Core.State`,
`QuantumLib.LeanQIT.Core.Pure` and `QuantumLib.LeanQIT.Core.Measurement`, and the operations agree on the
nose — taking products, tracing out a factor, relabelling, applying and composing channels, forming
the rank-one state of a ket, and measuring.

What is left is a convention. Lean-QIT counts entropy in bits and physlib in nats, so the two
disagree by a factor of `Real.log 2`; `QuantumLib.LeanQIT.Bridge.Entropy` records that factor for the
conditional entropy and the mutual information, and the von Neumann entropies themselves are
identified where `MState.vonNeumann` is defined.
-/
