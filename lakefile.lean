import Lake
open System Lake DSL

package «quantumLib»

require "physlib" from git "https://github.com/leanprover-community/physlib.git"
  @ "182189810e145ff21652b6fda3b9ec0b01ce2b6e"

@[default_target]
lean_lib QuantumLib
