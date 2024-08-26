import Lake
open Lake DSL

package «test» {
  -- add any package configuration options here
}

require auto from git
  "https://github.com/leanprover-community/lean-auto"@"0831a6eff8cbb456e90c616bd2f4db51aefea3d0"

@[default_target]
lean_lib «ToBuild» {
  -- add any library configuration options here
}
