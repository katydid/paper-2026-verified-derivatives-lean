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
