import AleksandrovDifferentiability.Analysis.LineAleksandrov.Slicewise

/-!
# Measurability interfaces for unit-direction good sets
-/

noncomputable section

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

/-- Measurability side condition for the transformed good sets in the canonical unit-direction
scalar Fubini bridge.  For open domains this implies
`DirectionalLineScalarUnitBadSetMeasurableStatement`, because the transformed bad set is the
difference of the transformed open domain and this good set. -/
def DirectionalLineScalarUnitGoodSetMeasurableStatement
    (_Ω : Set E) (u : E → ℝ) : Prop :=
  ∀ (ξ : E) (hξ : ‖ξ‖ = 1),
    MeasurableSet
      (directionalLineScalarEstimateSet
        (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
        (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm))

/-- Quotient-estimate version of
`DirectionalLineScalarUnitGoodSetMeasurableStatement`. -/
def DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement
    (_Ω : Set E) (u : E → ℝ) : Prop :=
  ∀ (ξ : E) (hξ : ‖ξ‖ = 1),
    MeasurableSet
      (directionalLineScalarQuotientEstimateSet
        (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
        (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm))

namespace DirectionalLineScalarUnitGoodSetMeasurableStatement

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Affine functions satisfy the canonical scalar unit-direction good-set measurability
condition: after verticalizing any unit direction, the transformed directional good set is all of
the coordinate model. -/
theorem inner_add_const (Ω : Set E) (p : E) (c : ℝ) :
    DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω
      (fun y : E => inner ℝ p y + c) := by
  intro ξ hξ
  let e := verticalizingLinearIsometryEquiv ξ hξ
  let η := WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ)
  have hfun :
      ((fun y : E => inner ℝ p y + c) ∘ e.symm) =
        (fun y : WithLp 2 (((ℝ ∙ ξ)ᗮ) × ℝ) => inner ℝ (e p) y + c) := by
    funext y
    change inner ℝ p (e.symm y) + c = inner ℝ (e p) y + c
    rw [← e.inner_map_eq_flip p y]
  rw [hfun, directionalLineScalarEstimateSet_inner_add_const (e p) η c]
  exact MeasurableSet.univ

end DirectionalLineScalarUnitGoodSetMeasurableStatement

namespace DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Quotient-estimate version of
`DirectionalLineScalarUnitGoodSetMeasurableStatement.inner_add_const`. -/
theorem inner_add_const (Ω : Set E) (p : E) (c : ℝ) :
    DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω
      (fun y : E => inner ℝ p y + c) := by
  intro ξ hξ
  let e := verticalizingLinearIsometryEquiv ξ hξ
  let η := WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ)
  have hfun :
      ((fun y : E => inner ℝ p y + c) ∘ e.symm) =
        (fun y : WithLp 2 (((ℝ ∙ ξ)ᗮ) × ℝ) => inner ℝ (e p) y + c) := by
    funext y
    change inner ℝ p (e.symm y) + c = inner ℝ (e p) y + c
    rw [← e.inner_map_eq_flip p y]
  rw [hfun, directionalLineScalarQuotientEstimateSet_inner_add_const (e p) η c]
  exact MeasurableSet.univ

end DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement

namespace DirectionalLineScalarUnitBadSetMeasurableStatement

-- For open domains, transformed good-set measurability implies transformed bad-set
-- measurability in the canonical unit-direction scalar bridge.
omit [FiniteDimensional ℝ E] in
theorem of_goodSetMeasurable
    {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u := by
  intro ξ hξ
  have hΩimage :
      MeasurableSet ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω) :=
    (isOpen_image_linearIsometryEquiv (verticalizingLinearIsometryEquiv ξ hξ) hΩ).measurableSet
  exact hΩimage.diff (hgood ξ hξ)

end DirectionalLineScalarUnitBadSetMeasurableStatement

namespace DirectionalLineScalarUnitBadSetNullMeasurableStatement

-- For open domains, transformed good-set measurability implies transformed bad-set
-- null-measurability in the canonical unit-direction scalar bridge.
theorem of_goodSetMeasurable
    {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω)
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u := by
  intro ξ hξ
  have hbad :=
    DirectionalLineScalarUnitBadSetMeasurableStatement.of_goodSetMeasurable hΩ hgood ξ hξ
  exact hbad.nullMeasurableSet

end DirectionalLineScalarUnitBadSetNullMeasurableStatement

namespace DirectionalLineScalarQuotientUnitBadSetMeasurableStatement

-- Quotient-estimate version of
-- `DirectionalLineScalarUnitBadSetMeasurableStatement.of_goodSetMeasurable`.
omit [FiniteDimensional ℝ E] in
theorem of_goodSetMeasurable
    {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u := by
  intro ξ hξ
  have hΩimage :
      MeasurableSet ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω) :=
    (isOpen_image_linearIsometryEquiv (verticalizingLinearIsometryEquiv ξ hξ) hΩ).measurableSet
  exact hΩimage.diff (hgood ξ hξ)

end DirectionalLineScalarQuotientUnitBadSetMeasurableStatement

namespace DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement

-- Quotient-estimate version of
-- `DirectionalLineScalarUnitBadSetNullMeasurableStatement.of_goodSetMeasurable`.
theorem of_goodSetMeasurable
    {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω)
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u := by
  intro ξ hξ
  have hbad :=
    DirectionalLineScalarQuotientUnitBadSetMeasurableStatement.of_goodSetMeasurable hΩ hgood
      ξ hξ
  exact hbad.nullMeasurableSet

end DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement

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
