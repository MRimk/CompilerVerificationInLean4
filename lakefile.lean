import Lake
open Lake DSL

package «comp» {
  -- add package configuration options here
}

lean_lib «Comp» {
  -- add library configuration options here
}

@[default_target]
lean_exe «comp» {
  root := `Main
}
