import AleksandrovDifferentiability.Analysis.LineAleksandrov.Measurable

/-!
# Fubini and finite-slice transfer from line estimates
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The canonical verticalizing coordinate model proves the scalar unit-direction
slicewise-to-Fubini transfer once the transformed bad sets are measurable. -/
theorem directionalLineScalarUnitSlicewiseToFubini_of_unitBadSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u := by
  intro hslice hΩ hu ξ hξ
  exact measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection_of_slicewise
    hξ (hmeas ξ hξ) hslice hΩ hu

/-- Quotient-estimate version of
`directionalLineScalarUnitSlicewiseToFubini_of_unitBadSetMeasurable`. -/
theorem directionalLineScalarQuotientUnitSlicewiseToFubini_of_unitBadSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u := by
  intro hslice hΩ hu ξ hξ
  exact measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_unitDirection_of_slicewise
    hξ (hmeas ξ hξ) hslice hΩ hu

/-- The canonical verticalizing coordinate model proves the scalar unit-direction
slicewise-to-Fubini transfer once the transformed bad sets are null-measurable. -/
theorem directionalLineScalarUnitSlicewiseToFubini_of_unitBadSetNullMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u := by
  intro hslice hΩ hu ξ hξ
  exact measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection_of_slicewise₀
    hξ (hmeas ξ hξ) hslice hΩ hu

/-- Quotient-estimate version of
`directionalLineScalarUnitSlicewiseToFubini_of_unitBadSetNullMeasurable`. -/
theorem directionalLineScalarQuotientUnitSlicewiseToFubini_of_unitBadSetNullMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u := by
  intro hslice hΩ hu ξ hξ
  exact measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_unitDirection_of_slicewise₀
    hξ (hmeas ξ hξ) hslice hΩ hu

/-- The canonical verticalizing coordinate model proves the scalar unit-direction
slicewise-to-Fubini transfer once the transformed good sets are measurable. -/
theorem directionalLineScalarUnitSlicewiseToFubini_of_unitGoodSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u := by
  intro hslice hΩ hu ξ hξ
  exact measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection_of_slicewise
    hξ
    (DirectionalLineScalarUnitBadSetMeasurableStatement.of_goodSetMeasurable hΩ hgood ξ hξ)
    hslice hΩ hu

/-- Quotient-estimate version of
`directionalLineScalarUnitSlicewiseToFubini_of_unitGoodSetMeasurable`. -/
theorem directionalLineScalarQuotientUnitSlicewiseToFubini_of_unitGoodSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u := by
  intro hslice hΩ hu ξ hξ
  exact measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_unitDirection_of_slicewise
    hξ
    (DirectionalLineScalarQuotientUnitBadSetMeasurableStatement.of_goodSetMeasurable hΩ hgood ξ hξ)
    hslice hΩ hu

/-- The proved slicewise scalar estimate statement plus a finite-dimensional slicewise-to-Fubini
transfer gives the global directional-line Fubini target. -/
theorem directionalLineScalarFubiniStatement_of_slicewiseToFubini
    {Ω : Set E} {u : E → ℝ}
    (htransfer : DirectionalLineScalarSlicewiseToFubiniStatement E Ω u) :
    DirectionalLineScalarEstimateFubiniStatement E Ω u :=
  htransfer (directionalLineScalarEstimateSlicewiseStatement (E := E) Ω u)

/-- Quotient-estimate version of
`directionalLineScalarFubiniStatement_of_slicewiseToFubini`. -/
theorem directionalLineScalarQuotientFubiniStatement_of_slicewiseToFubini
    {Ω : Set E} {u : E → ℝ}
    (htransfer : DirectionalLineScalarQuotientSlicewiseToFubiniStatement E Ω u) :
    DirectionalLineScalarQuotientFubiniStatement E Ω u :=
  htransfer (directionalLineScalarQuotientSlicewiseStatement (E := E) Ω u)

/-- Mixed-strength wrapper: a scalar slicewise-to-Fubini transfer, applied to the proved scalar
slicewise theorem, also supplies the quotient directional-line Fubini target. -/
theorem directionalLineScalarQuotientFubiniStatement_of_scalarSlicewiseToFubini
    {Ω : Set E} {u : E → ℝ}
    (htransfer : DirectionalLineScalarSlicewiseToFubiniStatement E Ω u) :
    DirectionalLineScalarQuotientFubiniStatement E Ω u :=
  DirectionalLineScalarEstimateFubiniStatement.quotient E
    (directionalLineScalarFubiniStatement_of_slicewiseToFubini htransfer)

/-- The proved slicewise scalar estimate statement plus a unit-direction slicewise-to-Fubini
transfer gives the unit-direction directional-line Fubini target. -/
theorem directionalLineScalarUnitFubiniStatement_of_unitSlicewiseToFubini
    {Ω : Set E} {u : E → ℝ}
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u) :
    DirectionalLineScalarUnitFubiniStatement E Ω u :=
  htransfer (directionalLineScalarEstimateSlicewiseStatement (E := E) Ω u)

/-- Quotient-estimate version of
`directionalLineScalarUnitFubiniStatement_of_unitSlicewiseToFubini`. -/
theorem directionalLineScalarQuotientUnitFubiniStatement_of_unitSlicewiseToFubini
    {Ω : Set E} {u : E → ℝ}
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u) :
    DirectionalLineScalarQuotientUnitFubiniStatement E Ω u :=
  htransfer (directionalLineScalarQuotientSlicewiseStatement (E := E) Ω u)

/-- Mixed-strength unit-direction wrapper: a scalar unit-direction slicewise-to-Fubini transfer
also supplies the quotient unit-direction Fubini target. -/
theorem directionalLineScalarQuotientUnitFubiniStatement_of_scalarUnitSlicewiseToFubini
    {Ω : Set E} {u : E → ℝ}
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u) :
    DirectionalLineScalarQuotientUnitFubiniStatement E Ω u :=
  DirectionalLineScalarUnitFubiniStatement.quotient E
    (directionalLineScalarUnitFubiniStatement_of_unitSlicewiseToFubini htransfer)

/-- A unit-direction slicewise-to-Fubini transfer also gives the all-directions Fubini target. -/
theorem directionalLineScalarFubiniStatement_of_unitSlicewiseToFubini
    {Ω : Set E} {u : E → ℝ}
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u) :
    DirectionalLineScalarEstimateFubiniStatement E Ω u :=
  DirectionalLineScalarUnitFubiniStatement.fubiniStatement E
    (directionalLineScalarUnitFubiniStatement_of_unitSlicewiseToFubini htransfer)

/-- Quotient-estimate version of
`directionalLineScalarFubiniStatement_of_unitSlicewiseToFubini`. -/
theorem directionalLineScalarQuotientFubiniStatement_of_unitSlicewiseToFubini
    {Ω : Set E} {u : E → ℝ}
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u) :
    DirectionalLineScalarQuotientFubiniStatement E Ω u :=
  DirectionalLineScalarQuotientUnitFubiniStatement.fubiniStatement E
    (directionalLineScalarQuotientUnitFubiniStatement_of_unitSlicewiseToFubini htransfer)

/-- Mixed-strength all-directions wrapper from a scalar unit-direction slicewise-to-Fubini
transfer to the quotient directional-line Fubini target. -/
theorem directionalLineScalarQuotientFubiniStatement_of_scalarUnitSlicewiseToFubini
    {Ω : Set E} {u : E → ℝ}
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u) :
    DirectionalLineScalarQuotientFubiniStatement E Ω u :=
  DirectionalLineScalarQuotientUnitFubiniStatement.fubiniStatement E
    (directionalLineScalarQuotientUnitFubiniStatement_of_scalarUnitSlicewiseToFubini htransfer)

/-- The canonical scalar unit-direction good-set measurability obligation gives the
unit-direction Fubini target after applying the proved slicewise theorem. -/
theorem directionalLineScalarUnitFubiniStatement_of_unitGoodSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarUnitFubiniStatement E Ω u :=
  directionalLineScalarUnitFubiniStatement_of_unitSlicewiseToFubini
    (directionalLineScalarUnitSlicewiseToFubini_of_unitGoodSetMeasurable hgood)

/-- Quotient-estimate version of
`directionalLineScalarUnitFubiniStatement_of_unitGoodSetMeasurable`. -/
theorem directionalLineScalarQuotientUnitFubiniStatement_of_unitGoodSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitFubiniStatement E Ω u :=
  directionalLineScalarQuotientUnitFubiniStatement_of_unitSlicewiseToFubini
    (directionalLineScalarQuotientUnitSlicewiseToFubini_of_unitGoodSetMeasurable hgood)

/-- Mixed-strength unit-direction Fubini wrapper: scalar canonical good-set measurability also
supplies the quotient unit-direction Fubini target. -/
theorem directionalLineScalarQuotientUnitFubiniStatement_of_scalarUnitGoodSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitFubiniStatement E Ω u :=
  DirectionalLineScalarUnitFubiniStatement.quotient E
    (directionalLineScalarUnitFubiniStatement_of_unitGoodSetMeasurable hgood)

/-- Mixed-strength unit-direction transfer wrapper: scalar canonical good-set measurability also
supplies the quotient unit-direction slicewise-to-Fubini target. -/
theorem directionalLineScalarQuotientUnitSlicewiseToFubini_of_scalarUnitGoodSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u := by
  intro _hslice
  exact directionalLineScalarQuotientUnitFubiniStatement_of_scalarUnitGoodSetMeasurable hgood

/-- The canonical scalar unit-direction good-set measurability obligation gives the
all-directions Fubini target after applying the proved slicewise theorem. -/
theorem directionalLineScalarFubiniStatement_of_unitGoodSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarEstimateFubiniStatement E Ω u :=
  DirectionalLineScalarUnitFubiniStatement.fubiniStatement E
    (directionalLineScalarUnitFubiniStatement_of_unitGoodSetMeasurable hgood)

/-- Quotient-estimate version of
`directionalLineScalarFubiniStatement_of_unitGoodSetMeasurable`. -/
theorem directionalLineScalarQuotientFubiniStatement_of_unitGoodSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientFubiniStatement E Ω u :=
  DirectionalLineScalarQuotientUnitFubiniStatement.fubiniStatement E
    (directionalLineScalarQuotientUnitFubiniStatement_of_unitGoodSetMeasurable hgood)

/-- Mixed-strength all-directions Fubini wrapper: scalar canonical good-set measurability also
supplies the quotient directional-line Fubini target. -/
theorem directionalLineScalarQuotientFubiniStatement_of_scalarUnitGoodSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientFubiniStatement E Ω u :=
  DirectionalLineScalarQuotientUnitFubiniStatement.fubiniStatement E
    (directionalLineScalarQuotientUnitFubiniStatement_of_scalarUnitGoodSetMeasurable hgood)

/-- The canonical scalar unit-direction bad-set measurability obligation gives the
unit-direction Fubini target after applying the proved slicewise theorem. -/
theorem directionalLineScalarUnitFubiniStatement_of_unitBadSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarUnitFubiniStatement E Ω u :=
  directionalLineScalarUnitFubiniStatement_of_unitSlicewiseToFubini
    (directionalLineScalarUnitSlicewiseToFubini_of_unitBadSetMeasurable hmeas)

/-- The canonical scalar unit-direction bad-set null-measurability obligation gives the
unit-direction Fubini target after applying the proved slicewise theorem. -/
theorem directionalLineScalarUnitFubiniStatement_of_unitBadSetNullMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarUnitFubiniStatement E Ω u :=
  directionalLineScalarUnitFubiniStatement_of_unitSlicewiseToFubini
    (directionalLineScalarUnitSlicewiseToFubini_of_unitBadSetNullMeasurable hmeas)

/-- Quotient-estimate version of
`directionalLineScalarUnitFubiniStatement_of_unitBadSetMeasurable`. -/
theorem directionalLineScalarQuotientUnitFubiniStatement_of_unitBadSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitFubiniStatement E Ω u :=
  directionalLineScalarQuotientUnitFubiniStatement_of_unitSlicewiseToFubini
    (directionalLineScalarQuotientUnitSlicewiseToFubini_of_unitBadSetMeasurable hmeas)

/-- Quotient-estimate version of
`directionalLineScalarUnitFubiniStatement_of_unitBadSetNullMeasurable`. -/
theorem directionalLineScalarQuotientUnitFubiniStatement_of_unitBadSetNullMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitFubiniStatement E Ω u :=
  directionalLineScalarQuotientUnitFubiniStatement_of_unitSlicewiseToFubini
    (directionalLineScalarQuotientUnitSlicewiseToFubini_of_unitBadSetNullMeasurable hmeas)

/-- Mixed-strength unit-direction Fubini wrapper: scalar canonical bad-set measurability also
supplies the quotient unit-direction Fubini target. -/
theorem directionalLineScalarQuotientUnitFubiniStatement_of_scalarUnitBadSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitFubiniStatement E Ω u :=
  DirectionalLineScalarUnitFubiniStatement.quotient E
    (directionalLineScalarUnitFubiniStatement_of_unitBadSetMeasurable hmeas)

/-- Mixed-strength unit-direction Fubini wrapper: scalar canonical bad-set null-measurability also
supplies the quotient unit-direction Fubini target. -/
theorem directionalLineScalarQuotientUnitFubiniStatement_of_scalarUnitBadSetNullMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitFubiniStatement E Ω u :=
  DirectionalLineScalarUnitFubiniStatement.quotient E
    (directionalLineScalarUnitFubiniStatement_of_unitBadSetNullMeasurable hmeas)

/-- Mixed-strength unit-direction transfer wrapper: scalar canonical bad-set measurability also
supplies the quotient unit-direction slicewise-to-Fubini target. -/
theorem directionalLineScalarQuotientUnitSlicewiseToFubini_of_scalarUnitBadSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u := by
  intro _hslice
  exact directionalLineScalarQuotientUnitFubiniStatement_of_scalarUnitBadSetMeasurable hmeas

/-- Mixed-strength unit-direction transfer wrapper: scalar canonical bad-set null-measurability
also supplies the quotient unit-direction slicewise-to-Fubini target. -/
theorem directionalLineScalarQuotientUnitSlicewiseToFubini_of_scalarUnitBadSetNullMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u := by
  intro _hslice
  exact directionalLineScalarQuotientUnitFubiniStatement_of_scalarUnitBadSetNullMeasurable hmeas

/-- The canonical scalar unit-direction bad-set measurability obligation gives the
all-directions Fubini target after applying the proved slicewise theorem. -/
theorem directionalLineScalarFubiniStatement_of_unitBadSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarEstimateFubiniStatement E Ω u :=
  DirectionalLineScalarUnitFubiniStatement.fubiniStatement E
    (directionalLineScalarUnitFubiniStatement_of_unitBadSetMeasurable hmeas)

/-- The canonical scalar unit-direction bad-set null-measurability obligation gives the
all-directions Fubini target after applying the proved slicewise theorem. -/
theorem directionalLineScalarFubiniStatement_of_unitBadSetNullMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarEstimateFubiniStatement E Ω u :=
  DirectionalLineScalarUnitFubiniStatement.fubiniStatement E
    (directionalLineScalarUnitFubiniStatement_of_unitBadSetNullMeasurable hmeas)

/-- Quotient-estimate version of
`directionalLineScalarFubiniStatement_of_unitBadSetMeasurable`. -/
theorem directionalLineScalarQuotientFubiniStatement_of_unitBadSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientFubiniStatement E Ω u :=
  DirectionalLineScalarQuotientUnitFubiniStatement.fubiniStatement E
    (directionalLineScalarQuotientUnitFubiniStatement_of_unitBadSetMeasurable hmeas)

/-- Quotient-estimate version of
`directionalLineScalarFubiniStatement_of_unitBadSetNullMeasurable`. -/
theorem directionalLineScalarQuotientFubiniStatement_of_unitBadSetNullMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientFubiniStatement E Ω u :=
  DirectionalLineScalarQuotientUnitFubiniStatement.fubiniStatement E
    (directionalLineScalarQuotientUnitFubiniStatement_of_unitBadSetNullMeasurable hmeas)

/-- Mixed-strength all-directions Fubini wrapper: scalar canonical bad-set measurability also
supplies the quotient directional-line Fubini target. -/
theorem directionalLineScalarQuotientFubiniStatement_of_scalarUnitBadSetMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientFubiniStatement E Ω u :=
  DirectionalLineScalarQuotientUnitFubiniStatement.fubiniStatement E
    (directionalLineScalarQuotientUnitFubiniStatement_of_scalarUnitBadSetMeasurable hmeas)

/-- Mixed-strength all-directions Fubini wrapper: scalar canonical bad-set null-measurability
also supplies the quotient directional-line Fubini target. -/
theorem directionalLineScalarQuotientFubiniStatement_of_scalarUnitBadSetNullMeasurable
    {Ω : Set E} {u : E → ℝ}
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u) :
    DirectionalLineScalarQuotientFubiniStatement E Ω u :=
  DirectionalLineScalarQuotientUnitFubiniStatement.fubiniStatement E
    (directionalLineScalarQuotientUnitFubiniStatement_of_scalarUnitBadSetNullMeasurable hmeas)

/-- A global slicewise-to-Fubini transfer implies the finite-family off-diagonal transfer for
any selected finite direction family. -/
theorem finiteDirectionalLineScalarSlicewiseToFullMeasure_of_slicewiseToFubini
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : DirectionalLineScalarSlicewiseToFubiniStatement E Ω u) :
    FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v := by
  intro hslice hΩ hu
  have hfubini : DirectionalLineScalarEstimateFubiniStatement E Ω u :=
    htransfer hslice
  exact
    ⟨(fun i _hi => hfubini hΩ hu (v i)),
      (fun i _hi j _hj _hij => hfubini hΩ hu (v i + v j))⟩

/-- Quotient-estimate version of
`finiteDirectionalLineScalarSlicewiseToFullMeasure_of_slicewiseToFubini`. -/
theorem finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_slicewiseToFubini
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : DirectionalLineScalarQuotientSlicewiseToFubiniStatement E Ω u) :
    FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v := by
  intro hslice hΩ hu
  have hfubini : DirectionalLineScalarQuotientFubiniStatement E Ω u :=
    htransfer hslice
  exact
    ⟨(fun i _hi => hfubini hΩ hu (v i)),
      (fun i _hi j _hj _hij => hfubini hΩ hu (v i + v j))⟩

/-- Applying a scalar finite slicewise transfer to the proved slicewise theorem also supplies the
quotient full-measure line inputs needed by quotient reconstruction. -/
theorem finiteDirectionalLineScalarQuotientFullMeasure_of_finiteSlicewiseTransfer
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    (∀ ⦃i : ι⦄, i ∈ D →
      volume (Ω \ directionalLineScalarQuotientEstimateSet (v i) u) = 0) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      volume (Ω \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0) := by
  have hscalar :=
    htransfer (directionalLineScalarEstimateSlicewiseStatement (E := E) Ω u) hΩ hu
  exact
    ⟨(fun {_i} hi =>
      measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_estimateSet
        (hscalar.1 hi)),
      (fun {_i} hi {_j} hj hij =>
        measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_estimateSet
          (hscalar.2 hi hj hij))⟩

/-- Applying a scalar finite slicewise transfer to the proved slicewise theorem supplies the
scalar full-measure line inputs needed by polarized reconstruction. -/
theorem finiteDirectionalLineScalarFullMeasure_of_finiteSlicewiseTransfer
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    (∀ ⦃i : ι⦄, i ∈ D →
      volume (Ω \ directionalLineScalarEstimateSet (v i) u) = 0) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      volume (Ω \ directionalLineScalarEstimateSet (v i + v j) u) = 0) :=
  htransfer (directionalLineScalarEstimateSlicewiseStatement (E := E) Ω u) hΩ hu

/-- Finite scalar transfer may ignore zero directions: the corresponding directional-line good
set is all of the ambient space. -/
theorem finiteDirectionalLineScalarSlicewiseToFullMeasure_of_nonzero_fullMeasure
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : DirectionalLineScalarEstimateSlicewiseStatement E Ω u →
      IsOpen Ω → ConvexOn ℝ Ω u →
        (∀ ⦃i : ι⦄, i ∈ D → v i ≠ 0 →
          volume (Ω \ directionalLineScalarEstimateSet (v i) u) = 0) ∧
        (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
          v i + v j ≠ 0 →
            volume (Ω \ directionalLineScalarEstimateSet (v i + v j) u) = 0)) :
    FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v := by
  intro hslice hΩ hu
  rcases htransfer hslice hΩ hu with ⟨hpure, hpair⟩
  constructor
  · intro i hi
    by_cases hzero : v i = 0
    · simp [hzero]
    · exact hpure hi hzero
  · intro i hi j hj hij
    by_cases hzero : v i + v j = 0
    · simp [hzero]
    · exact hpair hi hj hij hzero

/-- Quotient-estimate version of
`finiteDirectionalLineScalarSlicewiseToFullMeasure_of_nonzero_fullMeasure`. -/
theorem finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_nonzero_fullMeasure
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : DirectionalLineScalarQuotientSlicewiseStatement E Ω u →
      IsOpen Ω → ConvexOn ℝ Ω u →
        (∀ ⦃i : ι⦄, i ∈ D → v i ≠ 0 →
          volume (Ω \ directionalLineScalarQuotientEstimateSet (v i) u) = 0) ∧
        (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
          v i + v j ≠ 0 →
            volume (Ω \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0)) :
    FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v := by
  intro hslice hΩ hu
  rcases htransfer hslice hΩ hu with ⟨hpure, hpair⟩
  constructor
  · intro i hi
    by_cases hzero : v i = 0
    · simp [hzero]
    · exact hpure hi hzero
  · intro i hi j hj hij
    by_cases hzero : v i + v j = 0
    · simp [hzero]
    · exact hpair hi hj hij hzero

/-- Finite scalar transfer can be proved after normalizing every nonzero direction to unit
length. Scalar-rescaling invariance then returns the required full-measure statements for the
original directions. -/
theorem finiteDirectionalLineScalarSlicewiseToFullMeasure_of_normalized_nonzero
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : DirectionalLineScalarEstimateSlicewiseStatement E Ω u →
      IsOpen Ω → ConvexOn ℝ Ω u →
        (∀ ⦃i : ι⦄, i ∈ D → v i ≠ 0 →
          volume (Ω \ directionalLineScalarEstimateSet (‖v i‖⁻¹ • v i) u) = 0) ∧
        (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
          v i + v j ≠ 0 →
            volume
              (Ω \ directionalLineScalarEstimateSet (‖v i + v j‖⁻¹ • (v i + v j)) u) =
                0)) :
    FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v := by
  refine finiteDirectionalLineScalarSlicewiseToFullMeasure_of_nonzero_fullMeasure ?_
  intro hslice hΩ hu
  rcases htransfer hslice hΩ hu with ⟨hpure, hpair⟩
  constructor
  · intro i hi hvi
    have hc : ‖v i‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hvi)
    rw [← measure_diff_directionalLineScalarEstimateSet_smul_eq
      (μ := volume) Ω (v := v i) (c := ‖v i‖⁻¹) hc u]
    exact hpure hi hvi
  · intro i hi j hj hij hvij
    have hc : ‖v i + v j‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hvij)
    rw [← measure_diff_directionalLineScalarEstimateSet_smul_eq
      (μ := volume) Ω (v := v i + v j) (c := ‖v i + v j‖⁻¹) hc u]
    exact hpair hi hj hij hvij

/-- Quotient-estimate version of
`finiteDirectionalLineScalarSlicewiseToFullMeasure_of_normalized_nonzero`. -/
theorem finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_normalized_nonzero
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : DirectionalLineScalarQuotientSlicewiseStatement E Ω u →
      IsOpen Ω → ConvexOn ℝ Ω u →
        (∀ ⦃i : ι⦄, i ∈ D → v i ≠ 0 →
          volume (Ω \ directionalLineScalarQuotientEstimateSet (‖v i‖⁻¹ • v i) u) = 0) ∧
        (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
          v i + v j ≠ 0 →
            volume
              (Ω \ directionalLineScalarQuotientEstimateSet
                (‖v i + v j‖⁻¹ • (v i + v j)) u) = 0)) :
    FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v := by
  refine finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_nonzero_fullMeasure ?_
  intro hslice hΩ hu
  rcases htransfer hslice hΩ hu with ⟨hpure, hpair⟩
  constructor
  · intro i hi hvi
    have hc : ‖v i‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hvi)
    rw [← measure_diff_directionalLineScalarQuotientEstimateSet_smul_eq
      (μ := volume) Ω (v := v i) (c := ‖v i‖⁻¹) hc u]
    exact hpure hi hvi
  · intro i hi j hj hij hvij
    have hc : ‖v i + v j‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hvij)
    rw [← measure_diff_directionalLineScalarQuotientEstimateSet_smul_eq
      (μ := volume) Ω (v := v i + v j) (c := ‖v i + v j‖⁻¹) hc u]
    exact hpair hi hj hij hvij

/-- A unit-direction finite scalar transfer implies the finite transfer for arbitrary directions:
zero directions are automatic and nonzero directions are normalized. -/
theorem finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unit_fullMeasure
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : DirectionalLineScalarEstimateSlicewiseStatement E Ω u →
      IsOpen Ω → ConvexOn ℝ Ω u →
        ∀ ξ : E, ‖ξ‖ = 1 →
          volume (Ω \ directionalLineScalarEstimateSet ξ u) = 0) :
    FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v := by
  refine finiteDirectionalLineScalarSlicewiseToFullMeasure_of_normalized_nonzero ?_
  intro hslice hΩ hu
  constructor
  · intro i _hi hvi
    exact htransfer hslice hΩ hu (‖v i‖⁻¹ • v i) (norm_inv_norm_smul_eq_one hvi)
  · intro i _hi j _hj _hij hvij
    exact htransfer hslice hΩ hu (‖v i + v j‖⁻¹ • (v i + v j))
      (norm_inv_norm_smul_eq_one hvij)

/-- Quotient-estimate version of
`finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unit_fullMeasure`. -/
theorem finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unit_fullMeasure
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : DirectionalLineScalarQuotientSlicewiseStatement E Ω u →
      IsOpen Ω → ConvexOn ℝ Ω u →
        ∀ ξ : E, ‖ξ‖ = 1 →
          volume (Ω \ directionalLineScalarQuotientEstimateSet ξ u) = 0) :
    FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v := by
  refine finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_normalized_nonzero ?_
  intro hslice hΩ hu
  constructor
  · intro i _hi hvi
    exact htransfer hslice hΩ hu (‖v i‖⁻¹ • v i) (norm_inv_norm_smul_eq_one hvi)
  · intro i _hi j _hj _hij hvij
    exact htransfer hslice hΩ hu (‖v i + v j‖⁻¹ • (v i + v j))
      (norm_inv_norm_smul_eq_one hvij)

/-- A unit-direction slicewise-to-Fubini transfer implies the finite-family off-diagonal transfer
for arbitrary selected directions. -/
theorem finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitSlicewiseToFubini
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u) :
    FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v :=
  finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unit_fullMeasure
    (fun hslice hΩ hu ξ hξ => htransfer hslice hΩ hu ξ hξ)

/-- Quotient-estimate version of
`finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitSlicewiseToFubini`. -/
theorem finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitSlicewiseToFubini
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : DirectionalLineScalarQuotientUnitSlicewiseToFubiniStatement E Ω u) :
    FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v :=
  finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unit_fullMeasure
    (fun hslice hΩ hu ξ hξ => htransfer hslice hΩ hu ξ hξ)

/-- A scalar unit-direction slicewise-to-Fubini transfer also supplies the finite quotient
full-measure inputs needed by quotient reconstruction. -/
theorem finiteDirectionalLineScalarQuotientFullMeasure_of_unitSlicewiseToFubini
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    (∀ ⦃i : ι⦄, i ∈ D →
      volume (Ω \ directionalLineScalarQuotientEstimateSet (v i) u) = 0) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      volume (Ω \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0) :=
  finiteDirectionalLineScalarQuotientFullMeasure_of_finiteSlicewiseTransfer
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitSlicewiseToFubini
      (D := D) (v := v) htransfer)
    hΩ hu

/-- A scalar unit-direction slicewise-to-Fubini transfer also supplies the finite scalar
full-measure inputs needed by polarized reconstruction. -/
theorem finiteDirectionalLineScalarFullMeasure_of_unitSlicewiseToFubini
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (htransfer : DirectionalLineScalarUnitSlicewiseToFubiniStatement E Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    (∀ ⦃i : ι⦄, i ∈ D →
      volume (Ω \ directionalLineScalarEstimateSet (v i) u) = 0) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      volume (Ω \ directionalLineScalarEstimateSet (v i + v j) u) = 0) :=
  finiteDirectionalLineScalarFullMeasure_of_finiteSlicewiseTransfer
    (finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitSlicewiseToFubini
      (D := D) (v := v) htransfer)
    hΩ hu

/-- The canonical scalar unit-direction good-set measurability obligation supplies the
finite-family off-diagonal transfer for arbitrary selected directions. -/
theorem finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitGoodSetMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u) :
    FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v :=
  finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitSlicewiseToFubini
    (directionalLineScalarUnitSlicewiseToFubini_of_unitGoodSetMeasurable hgood)

/-- Quotient-estimate version of
`finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitGoodSetMeasurable`. -/
theorem finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitGoodSetMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hgood : DirectionalLineScalarQuotientUnitGoodSetMeasurableStatement (E := E) Ω u) :
    FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v :=
  finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitSlicewiseToFubini
    (directionalLineScalarQuotientUnitSlicewiseToFubini_of_unitGoodSetMeasurable hgood)

/-- Scalar canonical good-set measurability also supplies the finite quotient full-measure inputs
after applying the proved scalar slicewise theorem. -/
theorem finiteDirectionalLineScalarQuotientFullMeasure_of_unitGoodSetMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    (∀ ⦃i : ι⦄, i ∈ D →
      volume (Ω \ directionalLineScalarQuotientEstimateSet (v i) u) = 0) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      volume (Ω \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0) :=
  finiteDirectionalLineScalarQuotientFullMeasure_of_unitSlicewiseToFubini
    (D := D) (v := v)
    (directionalLineScalarUnitSlicewiseToFubini_of_unitGoodSetMeasurable hgood)
    hΩ hu

/-- Scalar canonical good-set measurability also supplies the finite scalar full-measure inputs
after applying the proved scalar slicewise theorem. -/
theorem finiteDirectionalLineScalarFullMeasure_of_unitGoodSetMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    (∀ ⦃i : ι⦄, i ∈ D →
      volume (Ω \ directionalLineScalarEstimateSet (v i) u) = 0) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      volume (Ω \ directionalLineScalarEstimateSet (v i + v j) u) = 0) :=
  finiteDirectionalLineScalarFullMeasure_of_unitSlicewiseToFubini
    (D := D) (v := v)
    (directionalLineScalarUnitSlicewiseToFubini_of_unitGoodSetMeasurable hgood)
    hΩ hu

/-- Scalar canonical good-set measurability also supplies the quotient finite-family transfer
statement itself. -/
theorem finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_scalarUnitGoodSetMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hgood : DirectionalLineScalarUnitGoodSetMeasurableStatement (E := E) Ω u) :
    FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v := by
  intro _hslice hΩ hu
  exact finiteDirectionalLineScalarQuotientFullMeasure_of_unitGoodSetMeasurable
    (D := D) (v := v) hgood hΩ hu

/-- The canonical scalar unit-direction bad-set measurability obligation supplies the
finite-family off-diagonal transfer for arbitrary selected directions. -/
theorem finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitBadSetMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u) :
    FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v :=
  finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitSlicewiseToFubini
    (directionalLineScalarUnitSlicewiseToFubini_of_unitBadSetMeasurable hmeas)

/-- Quotient-estimate version of
`finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitBadSetMeasurable`. -/
theorem finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitBadSetMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hmeas : DirectionalLineScalarQuotientUnitBadSetMeasurableStatement (E := E) Ω u) :
    FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v :=
  finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitSlicewiseToFubini
    (directionalLineScalarQuotientUnitSlicewiseToFubini_of_unitBadSetMeasurable hmeas)

/-- Scalar canonical bad-set measurability also supplies the finite quotient full-measure inputs
after applying the proved scalar slicewise theorem. -/
theorem finiteDirectionalLineScalarQuotientFullMeasure_of_unitBadSetMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    (∀ ⦃i : ι⦄, i ∈ D →
      volume (Ω \ directionalLineScalarQuotientEstimateSet (v i) u) = 0) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      volume (Ω \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0) :=
  finiteDirectionalLineScalarQuotientFullMeasure_of_unitSlicewiseToFubini
    (D := D) (v := v)
    (directionalLineScalarUnitSlicewiseToFubini_of_unitBadSetMeasurable hmeas)
    hΩ hu

/-- Scalar canonical bad-set measurability also supplies the finite scalar full-measure inputs
after applying the proved scalar slicewise theorem. -/
theorem finiteDirectionalLineScalarFullMeasure_of_unitBadSetMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    (∀ ⦃i : ι⦄, i ∈ D →
      volume (Ω \ directionalLineScalarEstimateSet (v i) u) = 0) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      volume (Ω \ directionalLineScalarEstimateSet (v i + v j) u) = 0) :=
  finiteDirectionalLineScalarFullMeasure_of_unitSlicewiseToFubini
    (D := D) (v := v)
    (directionalLineScalarUnitSlicewiseToFubini_of_unitBadSetMeasurable hmeas)
    hΩ hu

/-- Scalar canonical bad-set measurability also supplies the quotient finite-family transfer
statement itself. -/
theorem finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_scalarUnitBadSetMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hmeas : DirectionalLineScalarUnitBadSetMeasurableStatement (E := E) Ω u) :
    FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v := by
  intro _hslice hΩ hu
  exact finiteDirectionalLineScalarQuotientFullMeasure_of_unitBadSetMeasurable
    (D := D) (v := v) hmeas hΩ hu

/-- The canonical scalar unit-direction bad-set null-measurability obligation supplies the
finite-family off-diagonal transfer for arbitrary selected directions. -/
theorem finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitBadSetNullMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u) :
    FiniteDirectionalLineScalarSlicewiseToFullMeasureStatement D E Ω u v :=
  finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitSlicewiseToFubini
    (directionalLineScalarUnitSlicewiseToFubini_of_unitBadSetNullMeasurable hmeas)

/-- Quotient-estimate version of
`finiteDirectionalLineScalarSlicewiseToFullMeasure_of_unitBadSetNullMeasurable`. -/
theorem finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitBadSetNullMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hmeas : DirectionalLineScalarQuotientUnitBadSetNullMeasurableStatement (E := E) Ω u) :
    FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v :=
  finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_unitSlicewiseToFubini
    (directionalLineScalarQuotientUnitSlicewiseToFubini_of_unitBadSetNullMeasurable hmeas)

/-- Scalar canonical bad-set null-measurability also supplies the finite quotient full-measure
inputs after applying the proved scalar slicewise theorem. -/
theorem finiteDirectionalLineScalarQuotientFullMeasure_of_unitBadSetNullMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    (∀ ⦃i : ι⦄, i ∈ D →
      volume (Ω \ directionalLineScalarQuotientEstimateSet (v i) u) = 0) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      volume (Ω \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0) :=
  finiteDirectionalLineScalarQuotientFullMeasure_of_unitSlicewiseToFubini
    (D := D) (v := v)
    (directionalLineScalarUnitSlicewiseToFubini_of_unitBadSetNullMeasurable hmeas)
    hΩ hu

/-- Scalar canonical bad-set null-measurability also supplies the finite scalar full-measure
inputs after applying the proved scalar slicewise theorem. -/
theorem finiteDirectionalLineScalarFullMeasure_of_unitBadSetNullMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    (∀ ⦃i : ι⦄, i ∈ D →
      volume (Ω \ directionalLineScalarEstimateSet (v i) u) = 0) ∧
    (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      volume (Ω \ directionalLineScalarEstimateSet (v i + v j) u) = 0) :=
  finiteDirectionalLineScalarFullMeasure_of_unitSlicewiseToFubini
    (D := D) (v := v)
    (directionalLineScalarUnitSlicewiseToFubini_of_unitBadSetNullMeasurable hmeas)
    hΩ hu

/-- Scalar canonical bad-set null-measurability also supplies the quotient finite-family transfer
statement itself. -/
theorem finiteDirectionalLineScalarQuotientSlicewiseToFullMeasure_of_scalarUnitBadSetNullMeasurable
    {ι : Type*} {D : Finset ι} {Ω : Set E} {u : E → ℝ} {v : ι → E}
    (hmeas : DirectionalLineScalarUnitBadSetNullMeasurableStatement (E := E) Ω u) :
    FiniteDirectionalLineScalarQuotientSlicewiseToFullMeasureStatement D E Ω u v := by
  intro _hslice hΩ hu
  exact finiteDirectionalLineScalarQuotientFullMeasure_of_unitBadSetNullMeasurable
    (D := D) (v := v) hmeas hΩ hu

end AleksandrovDifferentiability
