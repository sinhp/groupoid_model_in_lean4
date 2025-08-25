import Lake
open Lake DSL

package groupoid_model where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`grind.warning, false⟩
  ]
  -- add any additional package configuration options here

require Poly from git "https://github.com/sinhp/Poly" @ "master"


@[default_target]
lean_lib GroupoidModel where
  globs := #[`GroupoidModel]
  -- add any library configuration options here

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.22.0-rc3"

@[test_driver]
lean_lib Test.Typechecker where
  srcDir := "test"
  roots := #[`typechecker]
