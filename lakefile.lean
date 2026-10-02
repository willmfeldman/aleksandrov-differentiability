import Lake
open Lake DSL

package "AleksandrovDifferentiability" where
  version := v!"0.4.0"
  -- Projects that require a release tag download the prebuilt build archive attached to the
  -- GitHub release (see .github/workflows/release-build-archive.yml) instead of building.
  preferReleaseBuild := true
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`linter.style.header, false⟩,
  ]

require "leanprover-community" / "mathlib" @ git "v4.35.0-rc3"

@[default_target]
lean_lib «AleksandrovDifferentiability» where
  -- add any library configuration options here

@[default_target]
lean_lib «AleksandrovDifferentiabilityComparator» where
  roots := #[`AleksandrovDifferentiability.Comparator]
