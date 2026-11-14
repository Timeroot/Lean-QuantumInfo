# Integration into QuantumLib

Source: <https://github.com/Hayata-Yamasaki-Group/lean-quantum> at `bf1c4f6aaec84948f1a1c76c0728432813404a0f`.

The branch preserves every ancestor of that commit, with original commit IDs,
authors, and messages. A separate relocation commit puts the entire original
repository in `QuantumLib/LeanQuantum/`; a merge then joins it to Core.
The integration commit ports and deduplicates that snapshot using the saved
integration, keeping project-specific theory and examples in this directory.

Core never imports this project. This project imports Core where needed and
does not import the other project folders. Declaration namespaces are unchanged.
The adjacent README and license are the original upstream documents.

## Shared infrastructure

| Previous integrated path | Shared module |
| --- | --- |
| `QuantumLib/Channels/Superoperator.lean` | `QuantumLib/Core/Channels/Superoperator.lean` |
| `QuantumLib/ForMathlib/CFCDeriv.lean` | `QuantumLib/Core/ForMathlib/CFCDeriv.lean` |
| `QuantumLib/ForMathlib/TensorCFC.lean` | `QuantumLib/Core/ForMathlib/TensorCFC.lean` |
| `QuantumLib/States/Qudit.lean` | `QuantumLib/Core/States/Qudit.lean` |
