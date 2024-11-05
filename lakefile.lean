import Lake
open Lake DSL

package «TheBook» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"76ffa613a406252a5f5bc4f5126d8dfed73ce8df"

@[default_target]
lean_lib «TheBook» where
  -- add any library configuration options here
