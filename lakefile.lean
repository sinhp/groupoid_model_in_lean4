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

require "chasenorman" / "Canonical"

/-- We must ensure the theory prelude gets built
so that theory environments can be created from its `.olean`.
But we should not import the theory prelude into any Lean environment.
So it is built manually. -/
lean_lib Prelude where
  roots := #[`GroupoidModel.Syntax.Frontend.Prelude]

@[default_target]
lean_lib GroupoidModel where
  needs := #[Prelude]

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.22.0-rc3"

@[test_driver]
lean_lib test where

lean_lib Bench where
  srcDir := "test"
  roots := #[`bench]
