import Lake
open Lake DSL

package «test» {
  -- add any package configuration options here
}

require auto from git
  "https://github.com/leanprover-community/lean-auto"@"60e546ca7a9d40d508e58847a9d0630406835178"

@[default_target]
lean_lib «ToBuild» {
  -- add any library configuration options here
}
