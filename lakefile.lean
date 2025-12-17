import Lake
open System Lake DSL

package «quantumInfo»

require "mathlib" from git "https://github.com/leanprover-community/mathlib4.git" @ "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib QuantumInfo

lean_lib ClassicalInfo

lean_lib StatMech
