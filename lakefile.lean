import Lake
open Lake DSL

package taylor-expansions where
  -- add package configuration options here

@[default_target]
lean_lib TaylorExpansions where
  srcDir := "."


require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"
