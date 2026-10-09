module

public import AleksandrovDifferentiability.Analysis.Directional.Reconstruction
public import AleksandrovDifferentiability.Analysis.Directional.LineScalar

/-!
# Full-measure directional estimate assembly

This file turns directional scalar estimate sets and mixed-directional quadratic reconstruction
data into full-measure second-order differentiability statements.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [MeasurableSpace E]

/-- Nonzero scalar rescaling of the direction preserves the null complement of the scalar
directional-line good set. -/
theorem measure_diff_directionalLineScalarEstimateSet_smul_eq
    {μ : Measure E} (s : Set E) {v : E} {c : ℝ} (hc : c ≠ 0) (u : E → ℝ) :
    μ (s \ directionalLineScalarEstimateSet (c • v) u) =
      μ (s \ directionalLineScalarEstimateSet v u) := by
  rw [directionalLineScalarEstimateSet_smul_eq (v := v) (c := c) hc u]

/-- Quotient-estimate version of
`measure_diff_directionalLineScalarEstimateSet_smul_eq`. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_smul_eq
    {μ : Measure E} (s : Set E) {v : E} {c : ℝ} (hc : c ≠ 0) (u : E → ℝ) :
    μ (s \ directionalLineScalarQuotientEstimateSet (c • v) u) =
      μ (s \ directionalLineScalarQuotientEstimateSet v u) := by
  rw [directionalLineScalarQuotientEstimateSet_smul_eq (v := v) (c := c) hc u]

/-- Full measure of the fixed-direction scalar estimate good set implies full measure of the
corresponding punctured normalized quotient good set. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_eq_zero_of_estimateSet
    {μ : Measure E} {s : Set E} {v : E} {u : E → ℝ}
    (hnull : μ (s \ directionalLineScalarEstimateSet v u) = 0) :
    μ (s \ directionalLineScalarQuotientEstimateSet v u) = 0 :=
  measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    directionalLineScalarEstimateSet_subset_directionalLineScalarQuotientEstimateSet hnull

/-- Finite bookkeeping for directional slices: if each selected pure direction and each selected
pairwise-sum direction has scalar estimate data on a full-measure subset of `s`, then the bundled
finite directional slice target holds a.e. on `s`. -/
theorem ae_mem_directionalSliceEstimateSet_of_directionalLine_fullMeasure
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i + v j) u) = 0) :
    ∀ᵐ x ∂μ.restrict s, x ∈ directionalSliceEstimateSet D v u := by
  have hpureAE :
      ∀ᵐ x ∂μ.restrict s,
        ∀ i ∈ D, x ∈ directionalLineScalarEstimateSet (v i) u := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact ae_restrict_mem_of_measure_diff_eq_zero (μ := μ) hs (hpure hi)
  have hpairAE :
      ∀ᵐ x ∂μ.restrict s,
        ∀ i ∈ D, ∀ j ∈ D, x ∈ directionalLineScalarEstimateSet (v i + v j) u := by
    rw [Filter.eventually_all_finset]
    intro i hi
    rw [Filter.eventually_all_finset]
    intro j hj
    exact ae_restrict_mem_of_measure_diff_eq_zero (μ := μ) hs (hpair hi hj)
  filter_upwards [hpureAE, hpairAE] with x hpurex hpairx
  exact ⟨(fun i hi => hpurex i hi), (fun i hi j hj => hpairx i hi j hj)⟩

/-- Null-complement form of
`ae_mem_directionalSliceEstimateSet_of_directionalLine_fullMeasure`. -/
theorem measure_diff_directionalSliceEstimateSet_eq_zero_of_directionalLine_fullMeasure
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i + v j) u) = 0) :
    μ (s \ directionalSliceEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_ae_restrict_mem hs
    (ae_mem_directionalSliceEstimateSet_of_directionalLine_fullMeasure hs D v hpure hpair)

/-- Quotient-estimate version of
`ae_mem_directionalSliceEstimateSet_of_directionalLine_fullMeasure`. -/
theorem ae_mem_directionalSliceQuotientSet_of_directionalLine_fullMeasure
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0) :
    ∀ᵐ x ∂μ.restrict s, x ∈ directionalSliceQuotientEstimateSet D v u := by
  have hpureAE :
      ∀ᵐ x ∂μ.restrict s,
        ∀ i ∈ D, x ∈ directionalLineScalarQuotientEstimateSet (v i) u := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact ae_restrict_mem_of_measure_diff_eq_zero (μ := μ) hs (hpure hi)
  have hpairAE :
      ∀ᵐ x ∂μ.restrict s,
        ∀ i ∈ D, ∀ j ∈ D, x ∈ directionalLineScalarQuotientEstimateSet (v i + v j) u := by
    rw [Filter.eventually_all_finset]
    intro i hi
    rw [Filter.eventually_all_finset]
    intro j hj
    exact ae_restrict_mem_of_measure_diff_eq_zero (μ := μ) hs (hpair hi hj)
  filter_upwards [hpureAE, hpairAE] with x hpurex hpairx
  exact ⟨(fun i hi => hpurex i hi), (fun i hi j hj => hpairx i hi j hj)⟩

/-- Null-complement form of
`ae_mem_directionalSliceQuotientSet_of_directionalLine_fullMeasure`. -/
theorem measure_diff_directionalSliceQuotientSet_eq_zero_of_directionalLine_fullMeasure
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0) :
    μ (s \ directionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_ae_restrict_mem hs
    (ae_mem_directionalSliceQuotientSet_of_directionalLine_fullMeasure hs D v hpure hpair)

/-- Full measure of the compatible finite slice target implies full measure of the compatible
finite quotient-slice target. -/
theorem measure_diff_compatibleDirectionalSliceQuotientSet_eq_zero_of_compatibleSliceSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceEstimateSet D v u) = 0) :
    μ (s \ compatibleDirectionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    compatibleDirectionalSliceEstimateSet_subset_compatibleDirectionalSliceQuotientEstimateSet
    hnull

/-- Full measure of the compatible finite slice target implies full measure of the symmetric
compatible finite slice target. -/
theorem measure_diff_symmetricCompatibleSliceSet_eq_zero_of_compatibleSliceSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceEstimateSet D v u) = 0) :
    μ (s \ symmetricCompatibleDirectionalSliceEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    compatibleDirectionalSliceEstimateSet_subset_symmetricCompatibleDirectionalSliceEstimateSet
    hnull

/-- Full measure of the compatible finite quotient-slice target implies full measure of the
symmetric compatible finite quotient-slice target. -/
theorem measure_diff_symmetricCompatibleSliceQuotientSet_eq_zero_of_compatibleSliceQuotientSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceQuotientEstimateSet D v u) = 0) :
    μ (s \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    compatibleDirectionalSliceQuotientSet_subset_symmetricCompatibleDirectionalSliceQuotientSet
    hnull

/-- Full measure of the compatible finite slice target implies full measure of the symmetric
compatible finite quotient-slice target. -/
theorem measure_diff_symmetricCompatibleSliceQuotientSet_eq_zero_of_compatibleSliceSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceEstimateSet D v u) = 0) :
    μ (s \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_symmetricCompatibleSliceQuotientSet_eq_zero_of_compatibleSliceQuotientSet
    D v
    (measure_diff_compatibleDirectionalSliceQuotientSet_eq_zero_of_compatibleSliceSet
      D v hnull)

/-- Full measure of the symmetric compatible finite slice target implies full measure of the
symmetric compatible finite quotient-slice target. -/
theorem measure_diff_symmetricCompatibleSliceQuotientSet_eq_zero_of_symmetricSliceSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ symmetricCompatibleDirectionalSliceEstimateSet D v u) = 0) :
    μ (s \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u) = 0 :=
  measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    symmetricCompatibleDirectionalSliceEstimateSet_subset_symmetricCompatibleQuotientSet
    hnull

end AleksandrovDifferentiability
