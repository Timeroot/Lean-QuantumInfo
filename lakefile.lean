import Lake
open System Lake DSL

package «quantumLib»

require "physlib" from git "https://github.com/leanprover-community/physlib.git" @ "v4.31.0"

require "cslib" from git "https://github.com/leanprover/cslib.git" @ "v4.31.0"

--require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib QuantumLib
