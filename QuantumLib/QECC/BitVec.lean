/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm, Yi Lee, Runzhou Tao, Xiaodi Wu, Eashan Hatti
-/

import QuantumLib.QECC.BitVec.Bridge.Codes
import QuantumLib.QECC.BitVec.Bridge.Symplectic
import QuantumLib.QECC.BitVec.Classical.CodeSpace
import QuantumLib.QECC.BitVec.Examples.BB54
import QuantumLib.QECC.BitVec.Examples.BB72
import QuantumLib.QECC.BitVec.Examples.Planar
import QuantumLib.QECC.BitVec.Examples.Steane
import QuantumLib.QECC.BitVec.Examples.Toric
import QuantumLib.QECC.BitVec.LinearAlgebra.DistanceLB
import QuantumLib.QECC.BitVec.LinearAlgebra.RowspaceKernel
import QuantumLib.QECC.BitVec.SAT.Correctness
import QuantumLib.QECC.BitVec.SAT.Distance
import QuantumLib.QECC.BitVec.SAT.Encoding
import QuantumLib.QECC.BitVec.Stabilizer.Basic
import QuantumLib.QECC.BitVec.Stabilizer.BivariateBicycle
import QuantumLib.QECC.BitVec.Stabilizer.CSS

/-!
# Codes with SAT-checked distances

The `BitVec` development: a pipeline that states the distance of a concrete stabilizer code as a
propositional formula, refutes that formula with `bv_decide`, and hands the resulting bound back
to `QuantumLib.QECC`.

* `Classical.CodeSpace` is the classical linear-code background, and `LinearAlgebra` the linear
  algebra of row spaces and kernels together with the disjoint-cut lower bound on weights.
* `Stabilizer` reads a check matrix in the binary symplectic representation, assembles CSS codes
  out of pairs of classical codes, and builds the bivariate bicycle construction.
* `SAT` encodes "some error of weight below `dist` is undetectable" as a statement about
  `BitVec`s, proves that encoding faithful, and turns its refutation into a distance bound.
* `Examples` carries this out for the Steane, toric and planar codes and for the bivariate
  bicycle codes `⟦54, 8, ≥ 6⟧` and `⟦72, 12, ≥ 6⟧`.
* `Bridge` identifies the check matrices with `QuantumLib.PauliOp.StabGroup` and the codes with
  the error-correcting channels of `QuantumLib.QECC`.
-/
