import Lake
open Lake DSL

package "AleksandrovDifferentiability" where
  version := v!"0.2.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`linter.style.header, false⟩,
  ]

require "leanprover-community" / "mathlib" @ git "v4.30.0"

@[default_target]
lean_lib «AleksandrovDifferentiability» where
  -- add any library configuration options here

@[default_target]
lean_lib «AleksandrovDifferentiabilityComparator» where
  roots := #[`AleksandrovDifferentiability.Comparator]
