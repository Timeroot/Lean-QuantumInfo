/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QIT.Bridge.Channel
import QuantumLib.QIT.Bridge.Entropy
import QuantumLib.QIT.Bridge.Map
import QuantumLib.QIT.Bridge.Measurement
import QuantumLib.QIT.Bridge.Pure
import QuantumLib.QIT.Bridge.State

/-!
# The bridge between Lean-QIT and the rest of QuantumLib

Lean-QIT builds its own tower of quantum information objects on top of Mathlib: `QIT.CMatrix`,
`QIT.MatrixMap`, `QIT.State`, `QIT.Channel`, `QIT.PureVector` and `QIT.POVM`. physlib builds a
parallel tower whose states and channels are operators rather than matrices: `MState`, `CPTPMap`,
`Ket` and `POVM`. The files gathered here identify the two.

At the level of maps there is nothing to identify: `QIT.MatrixMap a b` and `MatrixMap a b ℂ` are the
same type, and their trace-preservation predicates are the same predicate. Their Choi matrices
differ only in the order of the two index factors. Everything above that level is an equivalence of
structures carrying the same data:

* `QIT.State.equivMState : QIT.State a ≃ MState a`
* `QIT.Channel.equivCPTPMap : QIT.Channel a b ≃ CPTPMap a b`
* `QIT.PureVector.equivKet : QIT.PureVector a ≃ Ket a`
* `QIT.POVM.equivPOVM : QIT.POVM x a ≃ POVM x a`

The identifications are compatible with the operations each library defines on those types: taking
products, tracing out a factor, relabelling, applying a channel, composing channels, forming the
rank-one state of a pure vector, and measuring. Entropies agree once the change of log base is
accounted for, Lean-QIT counting in bits and physlib in nats.
-/
