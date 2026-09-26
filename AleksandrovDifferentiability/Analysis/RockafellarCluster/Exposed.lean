module

public import AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed.Face
public import AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed.Thickening
public import AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed.Directional
public import AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed.Point
public import AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed.Mathlib

/-!
# Exposed faces and exposed points for the Rockafellar cluster argument

This compatibility module re-exports the exposed-face and exposed-point pieces used in the
Rockafellar cluster-density formalization:

* `RockafellarCluster.Exposed.Face` defines exposed faces and proves their basic geometric
  properties.
* `RockafellarCluster.Exposed.Thickening` contains norm-thickening and cluster-point tools.
* `RockafellarCluster.Exposed.Directional` contains the directional exposed-face
  outer-semicontinuity wrappers.
* `RockafellarCluster.Exposed.Point` contains exposed-point normalization and singleton-face
  lemmas.
* `RockafellarCluster.Exposed.Mathlib` bridges the project-local exposed-point carrier with
  Mathlib's `Set.exposedPoints`.
-/
