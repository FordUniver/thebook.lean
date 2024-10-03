import Lake
open Lake DSL

package «TheBook» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.10.0"

@[default_target]
lean_lib «TheBook» where
  -- add any library configuration options here
