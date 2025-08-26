--Mathlib imports
import QuantumInfo.ForMathlib

--Code
import QuantumInfo.Finite.Channel.DegradableOrder
import QuantumInfo.Finite.CPTPMap
import QuantumInfo.Finite.Distance
import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.Finite.ResourceTheory.FreeState
import QuantumInfo.Finite.ResourceTheory.ResourceTheory
import QuantumInfo.Finite.ResourceTheory.SteinsLemma
import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.Capacity
import QuantumInfo.Finite.Ensemble
import QuantumInfo.Finite.Entanglement
import QuantumInfo.Finite.Entropy
import QuantumInfo.Finite.MState
import QuantumInfo.Finite.POVM
import QuantumInfo.Finite.Unitary
import QuantumInfo.Finite.Pinching

--Documentation without code
import QuantumInfo.Finite.Capacity_doc

/-! # Quantum Information in Lean

What follows is a top-level index to the major top-level definitions in this repository, in roughly their dependency order:
 * `Bra` and `Ket` for pure quantum states
 * `MState` for mixed quantum states
 * `MState.«term𝐔[_]»`, a notation for unitary matrices, acting on quantum states
 * `MEnsemble` and `PEnsemble`: Ensemble of mixed and pure states, respectively
 * `(mixed_)convex_roof` : (Mixed) convex roof extension
 * `CPTPMap` for quantum channels
 * `Matrix.traceNorm`, the trace norm between matrices (mostly for `MState` distance)
 * `MState.fidelity`, the fidelity between quantum states
 * `Sᵥₙ`, `qConditionalEnt`, `qMutualInfo`, `coherentInfo`, etc. - different notions of entropy or information in quantum states
 * `DegradablePreorder` the degradable order on quantum channels (technically a preorder)
 * `CPTPMap.quantumCapacity`, the quantum capacity of a channel

And a pointer to the main theorems (many of which are unproved):
 * `MatrixMap.choi_PSD_iff_CP_map`, Choi's theorem on completely positive maps
 * `Sᵥₙ_strong_subadditivity`, the strong subadditivity of von Neumann entropy
 * `CPTPMap.coherentInfo_le_quantumCapacity`, the LSD theorem that the capacity of a channel is at least the coherent information

-/
