import Lake
open Lake DSL

package «prelude» {
  -- add any package configuration options here
}

require auto from git
  "https://github.com/leanprover-community/lean-auto"@"main"

@[default_target]
lean_lib «Prelude» {
  -- add any library configuration options here
}
