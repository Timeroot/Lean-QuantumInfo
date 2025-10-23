import Lake
open System Lake DSL

package «quantumInfo»

require "mathlib" from git "https://github.com/leanprover-community/mathlib4.git"

require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib QuantumInfo

lean_lib ClassicalInfo

lean_lib StatMech
