import AleksandrovDifferentiability.Analysis.LineAleksandrov.Geometry
import AleksandrovDifferentiability.Statements.Aleksandrov.Transport

/-!
# Slicewise Fubini reductions for line estimates
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The one-dimensional convex theorem proves the slicewise fixed-direction scalar estimate
statement. The remaining Fubini task is to integrate this along transverse parameters. -/
theorem directionalLineScalarEstimateSlicewiseStatement
    (Ω : Set E) (u : E → ℝ) :
    DirectionalLineScalarEstimateSlicewiseStatement E Ω u := by
  intro hΩ hu x ξ
  exact ConvexOn.ae_lineParam_mem_directionalLineScalarEstimateSet
    (x := x) (v := ξ) hΩ hu

/-- Quotient-estimate version of `directionalLineScalarEstimateSlicewiseStatement`. -/
theorem directionalLineScalarQuotientSlicewiseStatement
    (Ω : Set E) (u : E → ℝ) :
    DirectionalLineScalarQuotientSlicewiseStatement E Ω u := by
  intro hΩ hu x ξ
  exact ConvexOn.ae_lineParam_mem_directionalLineScalarQuotientEstimateSet
    (x := x) (v := ξ) hΩ hu

/-- Coordinate-model vertical Fubini step for scalar directional-line estimates.

In the `WithLp 2 (F × ℝ)` product coordinate model, slicewise goodness in the vertical direction
gives nullity of the preimage of the vertical bad set for the ordinary product measure on
`F × ℝ`. The remaining geometric Fubini work is to identify this preimage/product-measure
statement with the ambient volume statement after a coordinate change. -/
theorem prod_volume_preimage_diff_vertical_directionalLineScalarEstimateSet_eq_zero_of_slicewise
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    {Ω : Set (WithLp 2 (F × ℝ))} {u : WithLp 2 (F × ℝ) → ℝ}
    (hΩpre : MeasurableSet ((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω))
    (hbad : MeasurableSet
      (((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω) \
        ((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹'
          directionalLineScalarEstimateSet
            (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u)))
    (hslice : DirectionalLineScalarEstimateSlicewiseStatement (WithLp 2 (F × ℝ)) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ((volume : Measure F).prod (volume : Measure ℝ))
      (((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω) \
        ((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹'
          directionalLineScalarEstimateSet
            (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u)) = 0 := by
  refine prod_measure_diff_eq_zero_of_forall_ae_restrict_section
    (μ := (volume : Measure F)) (ν := (volume : Measure ℝ))
    (s := (WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω)
    (G := (WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹'
      directionalLineScalarEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u)
    hΩpre hbad ?_
  intro y
  have hy :=
    hslice hΩ hu (WithLp.toLp 2 ((y, (0 : ℝ)) : F × ℝ))
      (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ))
  have hline : ∀ t : ℝ,
      WithLp.toLp 2 ((y, (0 : ℝ)) : F × ℝ) +
          t • WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ) =
        WithLp.toLp 2 ((y, t) : F × ℝ) := by
    intro t
    apply WithLp.ofLp_injective 2
    simp
  simpa [lineDomain, hline] using hy

/-- Null-measurable version of
`prod_volume_preimage_diff_vertical_directionalLineScalarEstimateSet_eq_zero_of_slicewise`. -/
theorem
    prod_volume_preimage_diff_vertical_directionalLineScalarEstimateSet_eq_zero_of_slicewise₀
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    {Ω : Set (WithLp 2 (F × ℝ))} {u : WithLp 2 (F × ℝ) → ℝ}
    (hΩpre : MeasurableSet ((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω))
    (hbad : NullMeasurableSet
      ((((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω) \
        ((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹'
          directionalLineScalarEstimateSet
            (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u)))
      ((volume : Measure F).prod (volume : Measure ℝ)))
    (hslice : DirectionalLineScalarEstimateSlicewiseStatement (WithLp 2 (F × ℝ)) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ((volume : Measure F).prod (volume : Measure ℝ))
      (((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω) \
        ((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹'
          directionalLineScalarEstimateSet
            (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u)) = 0 := by
  refine prod_measure_diff_eq_zero_of_forall_ae_restrict_section₀
    (μ := (volume : Measure F)) (ν := (volume : Measure ℝ))
    (s := (WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω)
    (G := (WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹'
      directionalLineScalarEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u)
    hΩpre hbad ?_
  intro y
  have hy :=
    hslice hΩ hu (WithLp.toLp 2 ((y, (0 : ℝ)) : F × ℝ))
      (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ))
  have hline : ∀ t : ℝ,
      WithLp.toLp 2 ((y, (0 : ℝ)) : F × ℝ) +
          t • WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ) =
        WithLp.toLp 2 ((y, t) : F × ℝ) := by
    intro t
    apply WithLp.ofLp_injective 2
    simp
  simpa [lineDomain, hline] using hy

/-- Coordinate-model vertical Fubini step for quotient directional-line estimates. -/
theorem
    prod_volume_preimage_diff_vertical_scalarQuotientEstimateSet_eq_zero_of_slicewise
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    {Ω : Set (WithLp 2 (F × ℝ))} {u : WithLp 2 (F × ℝ) → ℝ}
    (hΩpre : MeasurableSet ((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω))
    (hbad : MeasurableSet
      (((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω) \
        ((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹'
          directionalLineScalarQuotientEstimateSet
            (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u)))
    (hslice : DirectionalLineScalarQuotientSlicewiseStatement (WithLp 2 (F × ℝ)) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ((volume : Measure F).prod (volume : Measure ℝ))
      (((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω) \
        ((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹'
          directionalLineScalarQuotientEstimateSet
            (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u)) = 0 := by
  refine prod_measure_diff_eq_zero_of_forall_ae_restrict_section
    (μ := (volume : Measure F)) (ν := (volume : Measure ℝ))
    (s := (WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω)
    (G := (WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹'
      directionalLineScalarQuotientEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u)
    hΩpre hbad ?_
  intro y
  have hy :=
    hslice hΩ hu (WithLp.toLp 2 ((y, (0 : ℝ)) : F × ℝ))
      (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ))
  have hline : ∀ t : ℝ,
      WithLp.toLp 2 ((y, (0 : ℝ)) : F × ℝ) +
          t • WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ) =
        WithLp.toLp 2 ((y, t) : F × ℝ) := by
    intro t
    apply WithLp.ofLp_injective 2
    simp
  simpa [lineDomain, hline] using hy

/-- Null-measurable version of
`prod_volume_preimage_diff_vertical_scalarQuotientEstimateSet_eq_zero_of_slicewise`. -/
theorem
    prod_volume_preimage_diff_vertical_scalarQuotientEstimateSet_eq_zero_of_slicewise₀
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    {Ω : Set (WithLp 2 (F × ℝ))} {u : WithLp 2 (F × ℝ) → ℝ}
    (hΩpre : MeasurableSet ((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω))
    (hbad : NullMeasurableSet
      ((((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω) \
        ((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹'
          directionalLineScalarQuotientEstimateSet
            (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u)))
      ((volume : Measure F).prod (volume : Measure ℝ)))
    (hslice : DirectionalLineScalarQuotientSlicewiseStatement (WithLp 2 (F × ℝ)) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ((volume : Measure F).prod (volume : Measure ℝ))
      (((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω) \
        ((WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹'
          directionalLineScalarQuotientEstimateSet
            (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u)) = 0 := by
  refine prod_measure_diff_eq_zero_of_forall_ae_restrict_section₀
    (μ := (volume : Measure F)) (ν := (volume : Measure ℝ))
    (s := (WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹' Ω)
    (G := (WithLp.toLp 2 : F × ℝ → WithLp 2 (F × ℝ)) ⁻¹'
      directionalLineScalarQuotientEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u)
    hΩpre hbad ?_
  intro y
  have hy :=
    hslice hΩ hu (WithLp.toLp 2 ((y, (0 : ℝ)) : F × ℝ))
      (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ))
  have hline : ∀ t : ℝ,
      WithLp.toLp 2 ((y, (0 : ℝ)) : F × ℝ) +
          t • WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ) =
        WithLp.toLp 2 ((y, t) : F × ℝ) := by
    intro t
    apply WithLp.ofLp_injective 2
    simp
  simpa [lineDomain, hline] using hy

/-- Coordinate-model vertical Fubini step for scalar estimates, stated directly for ambient
volume on `WithLp 2 (F × ℝ)`. -/
theorem volume_diff_vertical_directionalLineScalarEstimateSet_eq_zero_of_slicewise
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    {Ω : Set (WithLp 2 (F × ℝ))} {u : WithLp 2 (F × ℝ) → ℝ}
    (hbad : MeasurableSet
      (Ω \ directionalLineScalarEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u))
    (hslice : DirectionalLineScalarEstimateSlicewiseStatement (WithLp 2 (F × ℝ)) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume
      (Ω \ directionalLineScalarEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u) = 0 := by
  let T : F × ℝ → WithLp 2 (F × ℝ) := WithLp.toLp 2
  let G : Set (WithLp 2 (F × ℝ)) :=
    directionalLineScalarEstimateSet (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u
  have hΩpre : MeasurableSet (T ⁻¹' Ω) :=
    hΩ.measurableSet.preimage (WithLp.measurable_toLp 2 (F × ℝ))
  have hprebad : MeasurableSet (T ⁻¹' Ω \ T ⁻¹' G) := by
    have h := hbad.preimage (WithLp.measurable_toLp 2 (F × ℝ))
    simpa [T, G, Set.preimage_diff] using h
  have hprod :
      ((volume : Measure F).prod (volume : Measure ℝ)) (T ⁻¹' Ω \ T ⁻¹' G) = 0 := by
    simpa [T, G] using
      prod_volume_preimage_diff_vertical_directionalLineScalarEstimateSet_eq_zero_of_slicewise
        (F := F) (Ω := Ω) (u := u) hΩpre hprebad hslice hΩ hu
  have hplain : (volume : Measure (F × ℝ)) (T ⁻¹' (Ω \ G)) = 0 := by
    rw [Measure.volume_eq_prod]
    simpa [T, G, Set.preimage_diff] using hprod
  have hmp : MeasurePreserving T := WithLp.volume_preserving_toLp F ℝ
  rw [← hmp.map_eq, Measure.map_apply (WithLp.measurable_toLp 2 (F × ℝ)) hbad]
  simpa [T, G] using hplain

/-- Coordinate-model vertical Fubini step for quotient estimates, stated directly for ambient
volume on `WithLp 2 (F × ℝ)`. -/
theorem volume_diff_vertical_directionalLineScalarQuotientEstimateSet_eq_zero_of_slicewise
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    {Ω : Set (WithLp 2 (F × ℝ))} {u : WithLp 2 (F × ℝ) → ℝ}
    (hbad : MeasurableSet
      (Ω \ directionalLineScalarQuotientEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u))
    (hslice : DirectionalLineScalarQuotientSlicewiseStatement (WithLp 2 (F × ℝ)) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume
      (Ω \ directionalLineScalarQuotientEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u) = 0 := by
  let T : F × ℝ → WithLp 2 (F × ℝ) := WithLp.toLp 2
  let G : Set (WithLp 2 (F × ℝ)) :=
    directionalLineScalarQuotientEstimateSet
      (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u
  have hΩpre : MeasurableSet (T ⁻¹' Ω) :=
    hΩ.measurableSet.preimage (WithLp.measurable_toLp 2 (F × ℝ))
  have hprebad : MeasurableSet (T ⁻¹' Ω \ T ⁻¹' G) := by
    have h := hbad.preimage (WithLp.measurable_toLp 2 (F × ℝ))
    simpa [T, G, Set.preimage_diff] using h
  have hprod :
      ((volume : Measure F).prod (volume : Measure ℝ)) (T ⁻¹' Ω \ T ⁻¹' G) = 0 := by
    simpa [T, G] using
      prod_volume_preimage_diff_vertical_scalarQuotientEstimateSet_eq_zero_of_slicewise
        (F := F) (Ω := Ω) (u := u) hΩpre hprebad hslice hΩ hu
  have hplain : (volume : Measure (F × ℝ)) (T ⁻¹' (Ω \ G)) = 0 := by
    rw [Measure.volume_eq_prod]
    simpa [T, G, Set.preimage_diff] using hprod
  have hmp : MeasurePreserving T := WithLp.volume_preserving_toLp F ℝ
  rw [← hmp.map_eq, Measure.map_apply (WithLp.measurable_toLp 2 (F × ℝ)) hbad]
  simpa [T, G] using hplain

/-- Null-measurable version of
`volume_diff_vertical_directionalLineScalarEstimateSet_eq_zero_of_slicewise`. -/
theorem volume_diff_vertical_directionalLineScalarEstimateSet_eq_zero_of_slicewise₀
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    {Ω : Set (WithLp 2 (F × ℝ))} {u : WithLp 2 (F × ℝ) → ℝ}
    (hbad : NullMeasurableSet
      (Ω \ directionalLineScalarEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u) volume)
    (hslice : DirectionalLineScalarEstimateSlicewiseStatement (WithLp 2 (F × ℝ)) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume
      (Ω \ directionalLineScalarEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u) = 0 := by
  let T : F × ℝ → WithLp 2 (F × ℝ) := WithLp.toLp 2
  let G : Set (WithLp 2 (F × ℝ)) :=
    directionalLineScalarEstimateSet (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u
  have hΩpre : MeasurableSet (T ⁻¹' Ω) :=
    hΩ.measurableSet.preimage (WithLp.measurable_toLp 2 (F × ℝ))
  have hmp : MeasurePreserving T := WithLp.volume_preserving_toLp F ℝ
  have hprebadPlain :
      NullMeasurableSet (T ⁻¹' (Ω \ G)) (volume : Measure (F × ℝ)) := by
    exact hbad.preimage hmp.quasiMeasurePreserving
  have hprebad :
      NullMeasurableSet (T ⁻¹' Ω \ T ⁻¹' G)
        ((volume : Measure F).prod (volume : Measure ℝ)) := by
    have hprebadProd :
        NullMeasurableSet (T ⁻¹' (Ω \ G))
          ((volume : Measure F).prod (volume : Measure ℝ)) := by
      simpa [Measure.volume_eq_prod] using hprebadPlain
    simpa [Set.preimage_diff] using hprebadProd
  have hprod :
      ((volume : Measure F).prod (volume : Measure ℝ)) (T ⁻¹' Ω \ T ⁻¹' G) = 0 := by
    simpa [T, G] using
      prod_volume_preimage_diff_vertical_directionalLineScalarEstimateSet_eq_zero_of_slicewise₀
        (F := F) (Ω := Ω) (u := u) hΩpre hprebad hslice hΩ hu
  have hplain : (volume : Measure (F × ℝ)) (T ⁻¹' (Ω \ G)) = 0 := by
    rw [Measure.volume_eq_prod]
    simpa [T, G, Set.preimage_diff] using hprod
  exact (hmp.measure_preimage hbad).symm.trans hplain

/-- Null-measurable version of
`volume_diff_vertical_directionalLineScalarQuotientEstimateSet_eq_zero_of_slicewise`. -/
theorem volume_diff_vertical_directionalLineScalarQuotientEstimateSet_eq_zero_of_slicewise₀
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    {Ω : Set (WithLp 2 (F × ℝ))} {u : WithLp 2 (F × ℝ) → ℝ}
    (hbad : NullMeasurableSet
      (Ω \ directionalLineScalarQuotientEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u) volume)
    (hslice : DirectionalLineScalarQuotientSlicewiseStatement (WithLp 2 (F × ℝ)) Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume
      (Ω \ directionalLineScalarQuotientEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u) = 0 := by
  let T : F × ℝ → WithLp 2 (F × ℝ) := WithLp.toLp 2
  let G : Set (WithLp 2 (F × ℝ)) :=
    directionalLineScalarQuotientEstimateSet
      (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) u
  have hΩpre : MeasurableSet (T ⁻¹' Ω) :=
    hΩ.measurableSet.preimage (WithLp.measurable_toLp 2 (F × ℝ))
  have hmp : MeasurePreserving T := WithLp.volume_preserving_toLp F ℝ
  have hprebadPlain :
      NullMeasurableSet (T ⁻¹' (Ω \ G)) (volume : Measure (F × ℝ)) := by
    exact hbad.preimage hmp.quasiMeasurePreserving
  have hprebad :
      NullMeasurableSet (T ⁻¹' Ω \ T ⁻¹' G)
        ((volume : Measure F).prod (volume : Measure ℝ)) := by
    have hprebadProd :
        NullMeasurableSet (T ⁻¹' (Ω \ G))
          ((volume : Measure F).prod (volume : Measure ℝ)) := by
      simpa [Measure.volume_eq_prod] using hprebadPlain
    simpa [Set.preimage_diff] using hprebadProd
  have hprod :
      ((volume : Measure F).prod (volume : Measure ℝ)) (T ⁻¹' Ω \ T ⁻¹' G) = 0 := by
    simpa [T, G] using
      prod_volume_preimage_diff_vertical_scalarQuotientEstimateSet_eq_zero_of_slicewise₀
        (F := F) (Ω := Ω) (u := u) hΩpre hprebad hslice hΩ hu
  have hplain : (volume : Measure (F × ℝ)) (T ⁻¹' (Ω \ G)) = 0 := by
    rw [Measure.volume_eq_prod]
    simpa [T, G, Set.preimage_diff] using hprod
  exact (hmp.measure_preimage hbad).symm.trans hplain

/-- Coordinate-model Fubini bridge for scalar directional-line estimates.

If a linear isometry equivalence sends an ambient direction `ξ` to the vertical direction in a
`WithLp 2 (F × ℝ)` product model, then the vertical product-coordinate Fubini theorem gives full
measure of the original directional-line scalar good set. -/
theorem measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] WithLp 2 (F × ℝ)) {Ω : Set E} {u : E → ℝ} {ξ : E}
    (hξ : e ξ = WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ))
    (hbad : MeasurableSet
      (e '' Ω \ directionalLineScalarEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) (u ∘ e.symm)))
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarEstimateSet ξ u) = 0 := by
  have hΩF : IsOpen (e '' Ω) := isOpen_image_linearIsometryEquiv e hΩ
  have huF : ConvexOn ℝ (e '' Ω) (u ∘ e.symm) :=
    ConvexOn.image_linearIsometryEquiv e hu
  have hslice :
      DirectionalLineScalarEstimateSlicewiseStatement (WithLp 2 (F × ℝ)) (e '' Ω)
        (u ∘ e.symm) :=
    directionalLineScalarEstimateSlicewiseStatement
      (E := WithLp 2 (F × ℝ)) (e '' Ω) (u ∘ e.symm)
  have hnullVertical :
      volume (e '' Ω \ directionalLineScalarEstimateSet (e ξ) (u ∘ e.symm)) = 0 := by
    rw [hξ]
    exact volume_diff_vertical_directionalLineScalarEstimateSet_eq_zero_of_slicewise
      (F := F) (Ω := e '' Ω) (u := u ∘ e.symm) hbad hslice hΩF huF
  exact measure_diff_directionalLineScalarEstimateSet_image_linearIsometryEquiv_eq_zero
    (e := e) hnullVertical

/-- Quotient-estimate version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel`. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_verticalModel
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] WithLp 2 (F × ℝ)) {Ω : Set E} {u : E → ℝ} {ξ : E}
    (hξ : e ξ = WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ))
    (hbad : MeasurableSet
      (e '' Ω \ directionalLineScalarQuotientEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) (u ∘ e.symm)))
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarQuotientEstimateSet ξ u) = 0 := by
  have hΩF : IsOpen (e '' Ω) := isOpen_image_linearIsometryEquiv e hΩ
  have huF : ConvexOn ℝ (e '' Ω) (u ∘ e.symm) :=
    ConvexOn.image_linearIsometryEquiv e hu
  have hslice :
      DirectionalLineScalarQuotientSlicewiseStatement (WithLp 2 (F × ℝ)) (e '' Ω)
        (u ∘ e.symm) :=
    directionalLineScalarQuotientSlicewiseStatement
      (E := WithLp 2 (F × ℝ)) (e '' Ω) (u ∘ e.symm)
  have hnullVertical :
      volume (e '' Ω \ directionalLineScalarQuotientEstimateSet (e ξ) (u ∘ e.symm)) = 0 := by
    rw [hξ]
    exact volume_diff_vertical_directionalLineScalarQuotientEstimateSet_eq_zero_of_slicewise
      (F := F) (Ω := e '' Ω) (u := u ∘ e.symm) hbad hslice hΩF huF
  exact measure_diff_directionalLineScalarQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
    (e := e) hnullVertical

/-- Slicewise-input version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel`.

This is the form needed to package the geometric Fubini transfer independently of the already
proved convex line theorem. -/
theorem measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel_of_slicewise
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] WithLp 2 (F × ℝ)) {Ω : Set E} {u : E → ℝ} {ξ : E}
    (hξ : e ξ = WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ))
    (hbad : MeasurableSet
      (e '' Ω \ directionalLineScalarEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) (u ∘ e.symm)))
    (hslice : DirectionalLineScalarEstimateSlicewiseStatement E Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarEstimateSet ξ u) = 0 := by
  have hΩF : IsOpen (e '' Ω) := isOpen_image_linearIsometryEquiv e hΩ
  have huF : ConvexOn ℝ (e '' Ω) (u ∘ e.symm) :=
    ConvexOn.image_linearIsometryEquiv e hu
  have hsliceF :
      DirectionalLineScalarEstimateSlicewiseStatement (WithLp 2 (F × ℝ)) (e '' Ω)
        (u ∘ e.symm) :=
    hslice.image_linearIsometryEquiv e
  have hnullVertical :
      volume (e '' Ω \ directionalLineScalarEstimateSet (e ξ) (u ∘ e.symm)) = 0 := by
    rw [hξ]
    exact volume_diff_vertical_directionalLineScalarEstimateSet_eq_zero_of_slicewise
      (F := F) (Ω := e '' Ω) (u := u ∘ e.symm) hbad hsliceF hΩF huF
  exact measure_diff_directionalLineScalarEstimateSet_image_linearIsometryEquiv_eq_zero
    (e := e) hnullVertical

/-- Quotient-estimate version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel_of_slicewise`. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_verticalModel_of_slicewise
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] WithLp 2 (F × ℝ)) {Ω : Set E} {u : E → ℝ} {ξ : E}
    (hξ : e ξ = WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ))
    (hbad : MeasurableSet
      (e '' Ω \ directionalLineScalarQuotientEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) (u ∘ e.symm)))
    (hslice : DirectionalLineScalarQuotientSlicewiseStatement E Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarQuotientEstimateSet ξ u) = 0 := by
  have hΩF : IsOpen (e '' Ω) := isOpen_image_linearIsometryEquiv e hΩ
  have huF : ConvexOn ℝ (e '' Ω) (u ∘ e.symm) :=
    ConvexOn.image_linearIsometryEquiv e hu
  have hsliceF :
      DirectionalLineScalarQuotientSlicewiseStatement (WithLp 2 (F × ℝ)) (e '' Ω)
        (u ∘ e.symm) :=
    hslice.image_linearIsometryEquiv e
  have hnullVertical :
      volume (e '' Ω \ directionalLineScalarQuotientEstimateSet (e ξ) (u ∘ e.symm)) = 0 := by
    rw [hξ]
    exact volume_diff_vertical_directionalLineScalarQuotientEstimateSet_eq_zero_of_slicewise
      (F := F) (Ω := e '' Ω) (u := u ∘ e.symm) hbad hsliceF hΩF huF
  exact measure_diff_directionalLineScalarQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
    (e := e) hnullVertical

/-- Null-measurable version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel`. -/
theorem measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel₀
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] WithLp 2 (F × ℝ)) {Ω : Set E} {u : E → ℝ} {ξ : E}
    (hξ : e ξ = WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ))
    (hbad : NullMeasurableSet
      (e '' Ω \ directionalLineScalarEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) (u ∘ e.symm)) volume)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarEstimateSet ξ u) = 0 := by
  have hΩF : IsOpen (e '' Ω) := isOpen_image_linearIsometryEquiv e hΩ
  have huF : ConvexOn ℝ (e '' Ω) (u ∘ e.symm) :=
    ConvexOn.image_linearIsometryEquiv e hu
  have hslice :
      DirectionalLineScalarEstimateSlicewiseStatement (WithLp 2 (F × ℝ)) (e '' Ω)
        (u ∘ e.symm) :=
    directionalLineScalarEstimateSlicewiseStatement
      (E := WithLp 2 (F × ℝ)) (e '' Ω) (u ∘ e.symm)
  have hnullVertical :
      volume (e '' Ω \ directionalLineScalarEstimateSet (e ξ) (u ∘ e.symm)) = 0 := by
    rw [hξ]
    exact volume_diff_vertical_directionalLineScalarEstimateSet_eq_zero_of_slicewise₀
      (F := F) (Ω := e '' Ω) (u := u ∘ e.symm) hbad hslice hΩF huF
  exact measure_diff_directionalLineScalarEstimateSet_image_linearIsometryEquiv_eq_zero
    (e := e) hnullVertical

/-- Quotient-estimate version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel₀`. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_verticalModel₀
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] WithLp 2 (F × ℝ)) {Ω : Set E} {u : E → ℝ} {ξ : E}
    (hξ : e ξ = WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ))
    (hbad : NullMeasurableSet
      (e '' Ω \ directionalLineScalarQuotientEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) (u ∘ e.symm)) volume)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarQuotientEstimateSet ξ u) = 0 := by
  have hΩF : IsOpen (e '' Ω) := isOpen_image_linearIsometryEquiv e hΩ
  have huF : ConvexOn ℝ (e '' Ω) (u ∘ e.symm) :=
    ConvexOn.image_linearIsometryEquiv e hu
  have hslice :
      DirectionalLineScalarQuotientSlicewiseStatement (WithLp 2 (F × ℝ)) (e '' Ω)
        (u ∘ e.symm) :=
    directionalLineScalarQuotientSlicewiseStatement
      (E := WithLp 2 (F × ℝ)) (e '' Ω) (u ∘ e.symm)
  have hnullVertical :
      volume (e '' Ω \ directionalLineScalarQuotientEstimateSet (e ξ) (u ∘ e.symm)) = 0 := by
    rw [hξ]
    exact volume_diff_vertical_directionalLineScalarQuotientEstimateSet_eq_zero_of_slicewise₀
      (F := F) (Ω := e '' Ω) (u := u ∘ e.symm) hbad hslice hΩF huF
  exact measure_diff_directionalLineScalarQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
    (e := e) hnullVertical

/-- Slicewise-input version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel₀`. -/
theorem measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel_of_slicewise₀
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] WithLp 2 (F × ℝ)) {Ω : Set E} {u : E → ℝ} {ξ : E}
    (hξ : e ξ = WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ))
    (hbad : NullMeasurableSet
      (e '' Ω \ directionalLineScalarEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) (u ∘ e.symm)) volume)
    (hslice : DirectionalLineScalarEstimateSlicewiseStatement E Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarEstimateSet ξ u) = 0 := by
  have hΩF : IsOpen (e '' Ω) := isOpen_image_linearIsometryEquiv e hΩ
  have huF : ConvexOn ℝ (e '' Ω) (u ∘ e.symm) :=
    ConvexOn.image_linearIsometryEquiv e hu
  have hsliceF :
      DirectionalLineScalarEstimateSlicewiseStatement (WithLp 2 (F × ℝ)) (e '' Ω)
        (u ∘ e.symm) :=
    hslice.image_linearIsometryEquiv e
  have hnullVertical :
      volume (e '' Ω \ directionalLineScalarEstimateSet (e ξ) (u ∘ e.symm)) = 0 := by
    rw [hξ]
    exact volume_diff_vertical_directionalLineScalarEstimateSet_eq_zero_of_slicewise₀
      (F := F) (Ω := e '' Ω) (u := u ∘ e.symm) hbad hsliceF hΩF huF
  exact measure_diff_directionalLineScalarEstimateSet_image_linearIsometryEquiv_eq_zero
    (e := e) hnullVertical

/-- Quotient-estimate version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel_of_slicewise₀`. -/
theorem
    measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_verticalModel_of_slicewise₀
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] WithLp 2 (F × ℝ)) {Ω : Set E} {u : E → ℝ} {ξ : E}
    (hξ : e ξ = WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ))
    (hbad : NullMeasurableSet
      (e '' Ω \ directionalLineScalarQuotientEstimateSet
        (WithLp.toLp 2 (((0 : F), (1 : ℝ)) : F × ℝ)) (u ∘ e.symm)) volume)
    (hslice : DirectionalLineScalarQuotientSlicewiseStatement E Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarQuotientEstimateSet ξ u) = 0 := by
  have hΩF : IsOpen (e '' Ω) := isOpen_image_linearIsometryEquiv e hΩ
  have huF : ConvexOn ℝ (e '' Ω) (u ∘ e.symm) :=
    ConvexOn.image_linearIsometryEquiv e hu
  have hsliceF :
      DirectionalLineScalarQuotientSlicewiseStatement (WithLp 2 (F × ℝ)) (e '' Ω)
        (u ∘ e.symm) :=
    hslice.image_linearIsometryEquiv e
  have hnullVertical :
      volume (e '' Ω \ directionalLineScalarQuotientEstimateSet (e ξ) (u ∘ e.symm)) = 0 := by
    rw [hξ]
    exact volume_diff_vertical_directionalLineScalarQuotientEstimateSet_eq_zero_of_slicewise₀
      (F := F) (Ω := e '' Ω) (u := u ∘ e.symm) hbad hsliceF hΩF huF
  exact measure_diff_directionalLineScalarQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
    (e := e) hnullVertical

/-- Canonical unit-direction Fubini bridge for scalar estimates.

After applying `verticalizingLinearIsometryEquiv`, the existing vertical-model theorem gives the
full-measure directional good set for the original unit direction. The only remaining extra
hypothesis is measurability of the bad set in the image coordinate model. -/
theorem measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection
    {Ω : Set E} {u : E → ℝ} {ξ : E} (hξ : ‖ξ‖ = 1)
    (hbad : MeasurableSet
      ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω \
        directionalLineScalarEstimateSet
          (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
          (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm)))
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarEstimateSet ξ u) = 0 :=
  measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel
    (F := (ℝ ∙ ξ)ᗮ) (e := verticalizingLinearIsometryEquiv ξ hξ)
    (verticalizingLinearIsometryEquiv_apply_self ξ hξ) hbad hΩ hu

/-- Quotient-estimate version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection`. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_unitDirection
    {Ω : Set E} {u : E → ℝ} {ξ : E} (hξ : ‖ξ‖ = 1)
    (hbad : MeasurableSet
      ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω \
        directionalLineScalarQuotientEstimateSet
          (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
          (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm)))
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarQuotientEstimateSet ξ u) = 0 :=
  measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_verticalModel
    (F := (ℝ ∙ ξ)ᗮ) (e := verticalizingLinearIsometryEquiv ξ hξ)
    (verticalizingLinearIsometryEquiv_apply_self ξ hξ) hbad hΩ hu

/-- Slicewise-input version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection`. -/
theorem measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection_of_slicewise
    {Ω : Set E} {u : E → ℝ} {ξ : E} (hξ : ‖ξ‖ = 1)
    (hbad : MeasurableSet
      ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω \
        directionalLineScalarEstimateSet
          (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
          (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm)))
    (hslice : DirectionalLineScalarEstimateSlicewiseStatement E Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarEstimateSet ξ u) = 0 :=
  measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel_of_slicewise
    (F := (ℝ ∙ ξ)ᗮ) (e := verticalizingLinearIsometryEquiv ξ hξ)
    (verticalizingLinearIsometryEquiv_apply_self ξ hξ) hbad hslice hΩ hu

/-- Quotient-estimate version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection_of_slicewise`. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_unitDirection_of_slicewise
    {Ω : Set E} {u : E → ℝ} {ξ : E} (hξ : ‖ξ‖ = 1)
    (hbad : MeasurableSet
      ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω \
        directionalLineScalarQuotientEstimateSet
          (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
          (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm)))
    (hslice : DirectionalLineScalarQuotientSlicewiseStatement E Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarQuotientEstimateSet ξ u) = 0 :=
  measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_verticalModel_of_slicewise
    (F := (ℝ ∙ ξ)ᗮ) (e := verticalizingLinearIsometryEquiv ξ hξ)
    (verticalizingLinearIsometryEquiv_apply_self ξ hξ) hbad hslice hΩ hu

/-- Null-measurable version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection`. -/
theorem measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection₀
    {Ω : Set E} {u : E → ℝ} {ξ : E} (hξ : ‖ξ‖ = 1)
    (hbad : NullMeasurableSet
      ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω \
        directionalLineScalarEstimateSet
          (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
          (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm)) volume)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarEstimateSet ξ u) = 0 :=
  measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel₀
    (F := (ℝ ∙ ξ)ᗮ) (e := verticalizingLinearIsometryEquiv ξ hξ)
    (verticalizingLinearIsometryEquiv_apply_self ξ hξ) hbad hΩ hu

/-- Quotient-estimate version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection₀`. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_unitDirection₀
    {Ω : Set E} {u : E → ℝ} {ξ : E} (hξ : ‖ξ‖ = 1)
    (hbad : NullMeasurableSet
      ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω \
        directionalLineScalarQuotientEstimateSet
          (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
          (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm)) volume)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarQuotientEstimateSet ξ u) = 0 :=
  measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_verticalModel₀
    (F := (ℝ ∙ ξ)ᗮ) (e := verticalizingLinearIsometryEquiv ξ hξ)
    (verticalizingLinearIsometryEquiv_apply_self ξ hξ) hbad hΩ hu

/-- Slicewise-input version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection₀`. -/
theorem measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection_of_slicewise₀
    {Ω : Set E} {u : E → ℝ} {ξ : E} (hξ : ‖ξ‖ = 1)
    (hbad : NullMeasurableSet
      ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω \
        directionalLineScalarEstimateSet
          (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
          (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm)) volume)
    (hslice : DirectionalLineScalarEstimateSlicewiseStatement E Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarEstimateSet ξ u) = 0 :=
  measure_diff_directionalLineScalarEstimateSet_eq_zero_of_verticalModel_of_slicewise₀
    (F := (ℝ ∙ ξ)ᗮ) (e := verticalizingLinearIsometryEquiv ξ hξ)
    (verticalizingLinearIsometryEquiv_apply_self ξ hξ) hbad hslice hΩ hu

/-- Quotient-estimate version of
`measure_diff_directionalLineScalarEstimateSet_eq_zero_of_unitDirection_of_slicewise₀`. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_unitDirection_of_slicewise₀
    {Ω : Set E} {u : E → ℝ} {ξ : E} (hξ : ‖ξ‖ = 1)
    (hbad : NullMeasurableSet
      ((verticalizingLinearIsometryEquiv ξ hξ) '' Ω \
        directionalLineScalarQuotientEstimateSet
          (WithLp.toLp 2 (((0 : (ℝ ∙ ξ)ᗮ), (1 : ℝ)) : ((ℝ ∙ ξ)ᗮ) × ℝ))
          (u ∘ (verticalizingLinearIsometryEquiv ξ hξ).symm)) volume)
    (hslice : DirectionalLineScalarQuotientSlicewiseStatement E Ω u)
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    volume (Ω \ directionalLineScalarQuotientEstimateSet ξ u) = 0 :=
  measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_verticalModel_of_slicewise₀
    (F := (ℝ ∙ ξ)ᗮ) (e := verticalizingLinearIsometryEquiv ξ hξ)
    (verticalizingLinearIsometryEquiv_apply_self ξ hξ) hbad hslice hΩ hu

end AleksandrovDifferentiability
