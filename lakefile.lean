import Lake
open System Lake DSL

package «quantumLib»

require "physlib" from git "https://github.com/leanprover-community/physlib.git"
  @ "8b7337ff5c27379bed0f5cce35418e34645a5bb1"

@[default_target]
lean_lib QuantumLib
