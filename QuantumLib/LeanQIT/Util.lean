/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.Core.ForMathlib.Matrix
public import QuantumLib.Core.ForMathlib.MatrixInstances
public import QuantumLib.Core.ForMathlib.Matrix.PosSqrt
public import QuantumLib.Core.ForMathlib.BlockMatrix
public import QuantumLib.Core.ForMathlib.RpowOperatorConvex
public import QuantumLib.Core.ForMathlib.Order.EReal
public import QuantumLib.LeanQIT.Util.TensorPower
public import QuantumLib.Core.ForMathlib.Wires
public import QuantumLib.Core.ForMathlib.CMatrixCLM

/-!
# QIT utilities

Quantum-free helper lemmas and notation support used by QIT core modules.
-/

@[expose] public section
