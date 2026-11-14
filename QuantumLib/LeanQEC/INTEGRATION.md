# Integration into QuantumLib

Source: <https://github.com/VerifiedQC/Lean-QEC> at `e0b90148694cf6b9c8482b21dbd911f2d8f13493`.

The branch preserves every ancestor of that commit, with original commit IDs,
authors, and messages. A separate relocation commit puts the entire original
repository in `QuantumLib/LeanQEC/`; a merge then joins it to Core.
The integration commit ports and deduplicates that snapshot using the saved
integration, keeping project-specific theory and examples in this directory.

Core never imports this project. This project imports Core where needed and
does not import the other project folders. Declaration namespaces are unchanged.
The adjacent README and license are the original upstream documents.

## Shared infrastructure

| Previous integrated path | Shared module |
| --- | --- |
| `QuantumLib/QECC/BitVec/LinearAlgebra/DistanceLB.lean` | `QuantumLib/Core/ForMathlib/DistanceLB.lean` |
| `QuantumLib/QECC/BitVec/LinearAlgebra/RowspaceKernel.lean` | `QuantumLib/Core/ForMathlib/RowspaceKernel.lean` |
