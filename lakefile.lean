import Lake
open Lake DSL

package groupoid_model where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  -- add any additional package configuration options here

require Poly from git
  "https://github.com/sinhp/Poly.git"

@[default_target]
lean_lib GroupoidModel where
  globs := #[.andSubmodules `GroupoidModel]
  -- add any library configuration options here
