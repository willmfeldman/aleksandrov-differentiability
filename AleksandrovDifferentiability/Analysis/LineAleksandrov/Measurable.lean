module

public import AleksandrovDifferentiability.Analysis.LineAleksandrov.Geometry
public import AleksandrovDifferentiability.Statements.Aleksandrov.Transport

/-!
# Measurability interfaces for unit-direction good sets
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Measurability side condition for the canonical unit-direction scalar Fubini bridge. -/
def DirectionalLineScalarUnitBadSetMeasurableStatement
    (Ω : Set E) (u : E → ℝ) : Prop :=
  ∀ (ξ : E) (hξ : ‖ξ‖ = 1),
    MeasurableSet
      ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω \
        directionalLineScalarEstimateSet
          (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
          (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm))

/-- Quotient-estimate measurability side condition for the canonical unit-direction Fubini
bridge. -/
def DirectionalLineScalarQuotientUnitBadSetMeasurableStatement
    (Ω : Set E) (u : E → ℝ) : Prop :=
  ∀ (ξ : E) (hξ : ‖ξ‖ = 1),
    MeasurableSet
      ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω \
        directionalLineScalarQuotientEstimateSet
          (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
          (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm))

/-- Null-measurability side condition for the canonical unit-direction scalar Fubini bridge. -/
def DirectionalLineScalarUnitBadSetNullMeasurableStatement
    (Ω : Set E) (u : E → ℝ) : Prop :=
  ∀ (ξ : E) (hξ : ‖ξ‖ = 1),
    NullMeasurableSet
      ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω \
        directionalLineScalarEstimateSet
          (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
          (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm)) volume

/-- Quotient-estimate null-measurability side condition for the canonical unit-direction Fubini
bridge. -/
def DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement
    (Ω : Set E) (u : E → ℝ) : Prop :=
  ∀ (ξ : E) (hξ : ‖ξ‖ = 1),
    NullMeasurableSet
      ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω \
        directionalLineScalarQuotientEstimateSet
          (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
          (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm)) volume

namespace DirectionalLineScalarUnitBadSetMeasurableStatement

/-- Measurable unit-direction bad sets are null-measurable. -/
theorem nullMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u := by
  intro ξ hξ
  exact (hmeas ξ hξ).nullMeasurableSet

end DirectionalLineScalarUnitBadSetMeasurableStatement

namespace DirectionalLineScalarQuotientUnitBadSetMeasurableStatement

/-- Measurable quotient unit-direction bad sets are null-measurable. -/
theorem nullMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u := by
  intro ξ hξ
  exact (hmeas ξ hξ).nullMeasurableSet

end DirectionalLineScalarQuotientUnitBadSetMeasurableStatement

end AleksandrovDifferentiability
