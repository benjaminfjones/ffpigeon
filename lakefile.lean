import Lake
open Lake DSL

package «ffpigeon» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Ffpigeon» {
  -- add any library configuration options here
}
