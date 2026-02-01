import Lake
open Lake DSL

package verifiedFilter

abbrev packageLinters : Array LeanOption := #[]

abbrev packageLeanOptions :=
  packageLinters

@[default_target]
lean_lib VerifiedFilter where
  leanOptions := packageLeanOptions
  moreServerOptions := packageLinters

-- dependencies std4, quote4 are obtained transitively through mathlib4
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.27.0"
