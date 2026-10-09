module

public import AleksandrovDifferentiability.Statements.Aleksandrov.Reconstruction

/-!
# Equivalent Aleksandrov statement forms
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

theorem convexAleksandrovAEStatement_iff_nullBadSetStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovAEStatement E Ω u ↔
      ConvexAleksandrovNullBadSetStatement E Ω u := by
  unfold ConvexAleksandrovAEStatement ConvexAleksandrovNullBadSetStatement
  constructor
  · intro h hΩ hu
    exact secondOrderDifferentiableAE_iff_measure_secondOrderBadSet_eq_zero.mp (h hΩ hu)
  · intro h hΩ hu
    exact secondOrderDifferentiableAE_iff_measure_secondOrderBadSet_eq_zero.mpr (h hΩ hu)

theorem convexAleksandrovAEStatement_iff_nullBadSetOnStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovAEStatement E Ω u ↔
      ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  unfold ConvexAleksandrovAEStatement ConvexAleksandrovNullBadSetOnStatement
  constructor
  · intro h hΩ hu
    exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
      (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp (h hΩ hu)
  · intro h hΩ hu
    exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
      (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mpr (h hΩ hu)

/-- The restricted-measure and domain-intersected null-exceptional-set formulations are
equivalent for open domains. -/
theorem convexAleksandrovNullBadSetStatement_iff_nullBadSetOnStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) :
    ConvexAleksandrovNullBadSetStatement E Ω u ↔
      ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  rw [← convexAleksandrovAEStatement_iff_nullBadSetStatement E Ω u]
  exact convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u

/-- Convert the domain-intersected null-exceptional-set formulation into the
restricted-measure formulation. -/
theorem ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : Set E} {u : E → ℝ}
    (h : ConvexAleksandrovNullBadSetOnStatement E Ω u) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  (convexAleksandrovNullBadSetStatement_iff_nullBadSetOnStatement E Ω u).mpr h

end AleksandrovDifferentiability
