# Quantum Information and Quantum Computing in Lean

## Library layout

`QuantumLib/Core/` contains the shared library. Import `QuantumLib.Core` to use it
without loading the imported project developments.

The collaboration branches add `QuantumLib/LeanQEC/`, `QuantumLib/LeanQIT/`, and
`QuantumLib/LeanQuantum/` for the corresponding projects. Their theory and examples
stay in those folders; reusable infrastructure can move into Core. Each project
imports Core as needed, and Core does not import the project folders. Declaration
namespaces are kept independently of these module paths.
