import AleksandrovDifferentiability.Analysis.LineRestriction
import AleksandrovDifferentiability.Statements.OneDimensional.RealLine
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Aleksandrov theorem on affine-line restrictions

This file packages the real-line convex Aleksandrov theorem for restrictions of an ambient convex
function to affine lines.  It is intended as a slicing-facing interface for later finite-dimensional
assembly.
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On every affine line through an open convex domain, the restricted one-dimensional convex
function is twice differentiable a.e. in the line parameter. -/
theorem ConvexOn.secondOrderDifferentiableAEOn_lineRestriction
    {Ω : Set E} {u : E → ℝ} {x v : E}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    SecondOrderDifferentiableAEOn volume (lineDomain Ω x v)
      (AleksandrovDifferentiability.lineRestriction u x v) := by
  exact convexAleksandrovAEStatement_real
    (lineDomain Ω x v) (AleksandrovDifferentiability.lineRestriction u x v)
    (isOpen_lineDomain (s := Ω) (x := x) (v := v) hΩ)
    (ConvexOn.lineRestriction (x := x) (v := v) hu)

/-- Null-bad-set form of `ConvexOn.secondOrderDifferentiableAEOn_lineRestriction`. -/
theorem ConvexOn.measure_secondOrderBadSetOn_lineRestriction_eq_zero
    {Ω : Set E} {u : E → ℝ} {x v : E}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (secondOrderBadSetOn (lineDomain Ω x v)
      (AleksandrovDifferentiability.lineRestriction u x v)) = 0 := by
  exact convexAleksandrovNullBadSetOnStatement_real
    (lineDomain Ω x v) (AleksandrovDifferentiability.lineRestriction u x v)
    (isOpen_lineDomain (s := Ω) (x := x) (v := v) hΩ)
    (ConvexOn.lineRestriction (x := x) (v := v) hu)

/-- Restricted-measure null-bad-set form of
`ConvexOn.secondOrderDifferentiableAEOn_lineRestriction`. -/
theorem ConvexOn.measure_restrict_secondOrderBadSet_lineRestriction_eq_zero
    {Ω : Set E} {u : E → ℝ} {x v : E}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume.restrict (lineDomain Ω x v)
      (secondOrderBadSet (AleksandrovDifferentiability.lineRestriction u x v)) = 0 := by
  exact convexAleksandrovNullBadSetStatement_real
    (lineDomain Ω x v) (AleksandrovDifferentiability.lineRestriction u x v)
    (isOpen_lineDomain (s := Ω) (x := x) (v := v) hΩ)
    (ConvexOn.lineRestriction (x := x) (v := v) hu)

/-- Scalar-estimate full-measure form of the one-dimensional theorem on affine-line
restrictions. -/
theorem ConvexOn.measure_lineDomain_diff_realScalarQuadraticEstimateSet_lineRestriction_eq_zero
    {Ω : Set E} {u : E → ℝ} {x v : E}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (lineDomain Ω x v \
      realScalarQuadraticEstimateSet (AleksandrovDifferentiability.lineRestriction u x v)) =
        0 := by
  exact convexOneDimensionalScalarEstimateStatement
    (lineDomain Ω x v) (AleksandrovDifferentiability.lineRestriction u x v)
    (isOpen_lineDomain (s := Ω) (x := x) (v := v) hΩ)
    (ConvexOn.lineRestriction (x := x) (v := v) hu)

/-- Scalar-estimate a.e. form of the one-dimensional theorem on affine-line restrictions. -/
theorem ConvexOn.ae_lineRestriction_mem_realScalarQuadraticEstimateSet
    {Ω : Set E} {u : E → ℝ} {x v : E}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ∀ᵐ t ∂volume.restrict (lineDomain Ω x v),
      t ∈ realScalarQuadraticEstimateSet
        (AleksandrovDifferentiability.lineRestriction u x v) := by
  exact ae_restrict_mem_of_measure_diff_eq_zero
    (μ := volume) (s := lineDomain Ω x v)
    (G := realScalarQuadraticEstimateSet
      (AleksandrovDifferentiability.lineRestriction u x v))
    (isOpen_lineDomain (s := Ω) (x := x) (v := v) hΩ).measurableSet
    (ConvexOn.measure_lineDomain_diff_realScalarQuadraticEstimateSet_lineRestriction_eq_zero
      hΩ hu)

/-- Slicewise form of the fixed-direction scalar estimate target: for almost every line
parameter, the corresponding ambient base point has scalar quadratic estimate data in the line
direction. -/
theorem ConvexOn.ae_lineParam_mem_directionalLineScalarEstimateSet
    {Ω : Set E} {u : E → ℝ} {x v : E}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ∀ᵐ t ∂volume.restrict (lineDomain Ω x v),
      x + t • v ∈ directionalLineScalarEstimateSet v u := by
  filter_upwards [ConvexOn.ae_lineRestriction_mem_realScalarQuadraticEstimateSet
    (x := x) (v := v) hΩ hu] with t ht
  exact RealScalarQuadraticEstimateAt.lineRestriction_rebase
    (u := u) (x := x) (v := v) (t := t) ht

/-- Null-complement version of
`ConvexOn.ae_lineParam_mem_directionalLineScalarEstimateSet`. -/
theorem ConvexOn.measure_lineDomain_diff_lineParamScalarEstimateSet_eq_zero
    {Ω : Set E} {u : E → ℝ} {x v : E}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (lineDomain Ω x v \
      {t : ℝ | x + t • v ∈ directionalLineScalarEstimateSet v u}) = 0 :=
  measure_diff_eq_zero_of_ae_restrict_mem
    (isOpen_lineDomain (s := Ω) (x := x) (v := v) hΩ).measurableSet
    (ConvexOn.ae_lineParam_mem_directionalLineScalarEstimateSet
      (x := x) (v := v) hΩ hu)

/-- Scalar quotient-estimate full-measure form of the one-dimensional theorem on affine-line
restrictions. -/
theorem ConvexOn.measure_lineDomain_diff_realScalarQuadraticQuotientSet_lineRestriction_eq_zero
    {Ω : Set E} {u : E → ℝ} {x v : E}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (lineDomain Ω x v \
      realScalarQuadraticQuotientEstimateSet
        (AleksandrovDifferentiability.lineRestriction u x v)) = 0 := by
  exact convexOneDimensionalScalarQuotientEstimateStatement
    (lineDomain Ω x v) (AleksandrovDifferentiability.lineRestriction u x v)
    (isOpen_lineDomain (s := Ω) (x := x) (v := v) hΩ)
    (ConvexOn.lineRestriction (x := x) (v := v) hu)

/-- Scalar quotient-estimate a.e. form of the one-dimensional theorem on affine-line
restrictions. -/
theorem ConvexOn.ae_lineRestriction_mem_realScalarQuadraticQuotientEstimateSet
    {Ω : Set E} {u : E → ℝ} {x v : E}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ∀ᵐ t ∂volume.restrict (lineDomain Ω x v),
      t ∈ realScalarQuadraticQuotientEstimateSet
        (AleksandrovDifferentiability.lineRestriction u x v) := by
  exact ae_restrict_mem_of_measure_diff_eq_zero
    (μ := volume) (s := lineDomain Ω x v)
    (G := realScalarQuadraticQuotientEstimateSet
      (AleksandrovDifferentiability.lineRestriction u x v))
    (isOpen_lineDomain (s := Ω) (x := x) (v := v) hΩ).measurableSet
    (ConvexOn.measure_lineDomain_diff_realScalarQuadraticQuotientSet_lineRestriction_eq_zero
      hΩ hu)

/-- Quotient-estimate version of
`ConvexOn.ae_lineParam_mem_directionalLineScalarEstimateSet`. -/
theorem ConvexOn.ae_lineParam_mem_directionalLineScalarQuotientEstimateSet
    {Ω : Set E} {u : E → ℝ} {x v : E}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ∀ᵐ t ∂volume.restrict (lineDomain Ω x v),
      x + t • v ∈ directionalLineScalarQuotientEstimateSet v u := by
  filter_upwards [ConvexOn.ae_lineRestriction_mem_realScalarQuadraticQuotientEstimateSet
    (x := x) (v := v) hΩ hu] with t ht
  exact RealScalarQuadraticQuotientEstimateAt.lineRestriction_rebase
    (u := u) (x := x) (v := v) (t := t) ht

/-- Null-complement quotient-estimate version of
`ConvexOn.measure_lineDomain_diff_lineParamScalarEstimateSet_eq_zero`. -/
theorem ConvexOn.measure_lineDomain_diff_lineParamScalarQuotientSet_eq_zero
    {Ω : Set E} {u : E → ℝ} {x v : E}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (lineDomain Ω x v \
      {t : ℝ | x + t • v ∈ directionalLineScalarQuotientEstimateSet v u}) = 0 :=
  measure_diff_eq_zero_of_ae_restrict_mem
    (isOpen_lineDomain (s := Ω) (x := x) (v := v) hΩ).measurableSet
    (ConvexOn.ae_lineParam_mem_directionalLineScalarQuotientEstimateSet
      (x := x) (v := v) hΩ hu)

end AleksandrovDifferentiability
