# Integration into QuantumLib

Source: <https://github.com/QuAIR/Lean-QIT> at `da54e3070298468dc884877726bc45a92c57e4b3`.

The branch preserves every ancestor of that commit, with original commit IDs,
authors, and messages. A separate relocation commit puts the entire original
repository in `QuantumLib/LeanQIT/`; a merge then joins it to Core.
The integration commit ports and deduplicates that snapshot using the saved
integration, keeping project-specific theory and examples in this directory.

Core never imports this project. This project imports Core where needed and
does not import the other project folders. Declaration namespaces are unchanged.
The adjacent README and license are the original upstream documents.

## Shared infrastructure

| Previous integrated path | Shared module |
| --- | --- |
| `QuantumLib/QIT/Util/BlockMatrix.lean` | `QuantumLib/Core/ForMathlib/BlockMatrix.lean` |
| `QuantumLib/QIT/Util/CMatrixCLM.lean` | `QuantumLib/Core/ForMathlib/CMatrixCLM.lean` |
| `QuantumLib/QIT/Util/CMatrixIntegral.lean` | `QuantumLib/Core/ForMathlib/CMatrixIntegral.lean` |
| `QuantumLib/QIT/Util/Matrix.lean` | `QuantumLib/Core/ForMathlib/Matrix.lean` |
| `QuantumLib/QIT/Util/Matrix/PosSqrt.lean` | `QuantumLib/Core/ForMathlib/Matrix/PosSqrt.lean` |
| `QuantumLib/QIT/Util/MatrixInstances.lean` | `QuantumLib/Core/ForMathlib/MatrixInstances.lean` |
| `QuantumLib/QIT/Util/Order/EReal.lean` | `QuantumLib/Core/ForMathlib/Order/EReal.lean` |
| `QuantumLib/QIT/Util/Order/Majorization.lean` | `QuantumLib/Core/ForMathlib/Order/Majorization.lean` |
| `QuantumLib/QIT/Util/RpowOperatorConvex.lean` | `QuantumLib/Core/ForMathlib/RpowOperatorConvex.lean` |
| `QuantumLib/QIT/Util/Wires.lean` | `QuantumLib/Core/ForMathlib/Wires.lean` |
