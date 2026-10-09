module

public import AleksandrovDifferentiability.Analysis.LineRestriction
public import AleksandrovDifferentiability.Statements.OneDimensional.RealLine
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Aleksandrov theorem on affine-line restrictions

This file packages the real-line convex Aleksandrov theorem for restrictions of an ambient convex
function to affine lines.  It is intended as a slicing-facing interface for later finite-dimensional
assembly.
-/

@[expose] public noncomputable section

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

end AleksandrovDifferentiability
