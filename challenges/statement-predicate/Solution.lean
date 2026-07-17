import AleksandrovDifferentiability

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

theorem challenge_statement_predicate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement E Ω u

end AleksandrovDifferentiability
