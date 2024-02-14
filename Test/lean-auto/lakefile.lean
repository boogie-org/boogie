import Lake
open Lake DSL

package «test» {
  -- add any package configuration options here
}

require auto from git
  "https://github.com/leanprover-community/lean-auto"@"v0.0.6"

@[default_target]
lean_lib «ToBuild» {
  -- add any library configuration options here
}
