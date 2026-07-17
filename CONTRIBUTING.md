# Contributing

Issues and small pull requests are welcome, but larger changes should be discussed before substantial work is
started.

## Checks

Before proposing a Lean change, run:

```bash
lake build
```

For a smaller local check while editing one file, run:

```bash
lake env lean path/to/file.lean
```

## Style

- Prefer existing local naming and module-organization patterns.
- Keep public theorem names consistent with Mathlib naming conventions.
- Add docstrings for declarations intended as public API.
- Do not add local reference scans, agent notes, prompt logs, or internal planning material.
- Keep source files under the Apache License 2.0 unless the project deliberately chooses otherwise.

## Scope

The main public theorem is `AleksandrovDifferentiability.convexAleksandrovAE`. Changes that affect
its statement, imports, or proof route should include a short explanation of the mathematical
effect and should be checked with a full `lake build`.
