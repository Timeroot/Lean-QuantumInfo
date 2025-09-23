import Lake
open System Lake DSL

package «quantumInfo»

@[default_target]
lean_lib QuantumInfo

require "mathlib" from git
  "https://github.com/leanprover-community/mathlib4.git"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

lean_lib ClassicalInfo
