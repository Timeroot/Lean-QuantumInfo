/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm, Yi Lee, Runzhou Tao, Xiaodi Wu, Eashan Hatti
-/

import QuantumLib.LeanQEC.Bridge.Codes
import QuantumLib.LeanQEC.Bridge.Symplectic
import QuantumLib.LeanQEC.Classical.CodeSpace
import QuantumLib.LeanQEC.Examples.BB54
import QuantumLib.LeanQEC.Examples.BB72
import QuantumLib.LeanQEC.Examples.Planar
import QuantumLib.LeanQEC.Examples.Steane
import QuantumLib.LeanQEC.Examples.Toric
import QuantumLib.Core.ForMathlib.DistanceLB
import QuantumLib.Core.ForMathlib.RowspaceKernel
import QuantumLib.LeanQEC.SAT.Correctness
import QuantumLib.LeanQEC.SAT.Distance
import QuantumLib.LeanQEC.SAT.Encoding
import QuantumLib.LeanQEC.Stabilizer.Basic
import QuantumLib.LeanQEC.Stabilizer.BivariateBicycle
import QuantumLib.LeanQEC.Stabilizer.CSS

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
