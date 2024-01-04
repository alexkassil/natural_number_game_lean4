import Lake
open Lake DSL

package myNat {
  -- add package configuration options here
}

lean_lib MyNat {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe myNat {
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
}
