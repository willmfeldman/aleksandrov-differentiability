import AleksandrovDifferentiability.Analysis.RockafellarCluster.ExposedCluster.Pointwise
import AleksandrovDifferentiability.Analysis.RockafellarCluster.ExposedCluster.Compact
import AleksandrovDifferentiability.Analysis.RockafellarCluster.ExposedCluster.Local

/-!
# Exposed subgradients as gradient cluster limits

This compatibility module re-exports the conceptual pieces of the exposed-cluster part of the
Rockafellar formalization:

* `RockafellarCluster.ExposedCluster.Pointwise` contains the pointwise exposed-subgradient
  cluster bridges.
* `RockafellarCluster.ExposedCluster.Compact` contains compact and bounded Straszewicz
  reductions for subdifferentials.
* `RockafellarCluster.ExposedCluster.Local` contains the final local cluster-density assembly
  wrappers.
-/
