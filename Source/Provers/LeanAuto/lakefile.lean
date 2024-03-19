import Lake
open Lake DSL

package «prelude» {
  -- add any package configuration options here
}

require auto from git
  "https://github.com/leanprover-community/lean-auto"@"v0.0.6"

@[default_target]
lean_lib «Prelude» {
  -- add any library configuration options here
}
