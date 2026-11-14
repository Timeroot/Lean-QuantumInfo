import Lake
open System Lake DSL

package «LeanQEC»{
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc2"

@[default_target]
lean_lib LeanQEC
