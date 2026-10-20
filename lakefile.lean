import Lake
open Lake DSL

package «glamsterdam-proof-closure» where
  version := v!"0.1.0"

@[default_target]
lean_lib «Glamsterdam» where
  globs := #[.andSubmodules `Glamsterdam]

lean_lib «glamsterdam_spec_cabi» where
  roots := #[`Glamsterdam]
  defaultFacets := #[LeanLib.staticFacet]
