import Lake
open Lake DSL

package myNat {
  -- add package configuration options here
}

lean_lib MyNat {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe myNat {
  root := `Main
}
