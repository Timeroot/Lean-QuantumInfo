import Lake
open Lake DSL

package «quantumInfo» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"


lean_lib «ClassicalInfo» {
  -- add any library configuration options here
}

@[default_target]
lean_lib «QuantumInfo» {
  -- add any library configuration options here
}
