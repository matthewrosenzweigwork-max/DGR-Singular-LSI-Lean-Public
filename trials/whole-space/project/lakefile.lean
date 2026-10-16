import Lake
open Lake DSL

package «tablet» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Tablet» where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

-- Independent audited statement and existing-proof implementation.
lean_lib «Challenge» where
  srcDir := "."

lean_lib «Solution» where
  srcDir := "."
