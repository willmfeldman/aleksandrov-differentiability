module

public import AleksandrovDifferentiability.Statements.Aleksandrov.Localization

/-!
# Final convex Aleksandrov theorem

This module provides the public theorem endpoint for the convex Aleksandrov second-order
differentiability theorem in finite-dimensional real inner product spaces.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Convex Aleksandrov second-order differentiability theorem, statement-predicate form. -/
theorem convexAleksandrovAEStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_finiteDimensional E Ω u

/-- Convex Aleksandrov second-order differentiability theorem.

If `u` is convex on an open subset `Ω` of a finite-dimensional real inner product space, then
`u` is second-order differentiable at Lebesgue-a.e. point of `Ω`. -/
theorem convexAleksandrovAE
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ∀ᵐ x ∂((volume : Measure E).restrict Ω), SecondOrderDifferentiableAt u x :=
  convexAleksandrovAEStatement E Ω u hΩ hu

end AleksandrovDifferentiability
