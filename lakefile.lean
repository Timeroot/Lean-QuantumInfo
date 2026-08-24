import Lake
open System Lake DSL

package «quantumLib»

require "physlib" from git "https://github.com/leanprover-community/physlib.git"
  @ "e3a45ba3fc1514e71919a00879ae634d5932c9f1"

@[default_target]
lean_lib QuantumLib
