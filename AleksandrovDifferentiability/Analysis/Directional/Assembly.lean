import AleksandrovDifferentiability.Analysis.Directional.FullMeasure
import AleksandrovDifferentiability.Analysis.EstimateAssembly

/-!
# Directional full-measure assembly

This file assembles full-measure hypotheses for finite directional quadratic data into
almost-everywhere second-order differentiability conclusions.
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- Full-measure assembly from estimates whose quadratic model is a finite mixed-directional
coefficient matrix. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticEstimateData
    {ι : Type*} {μ : Measure E} {s G : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ a : ι → ι → ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhds 0,
            ‖affineRemainder u x p (x + z) -
                (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ ≤
              ε * ‖z‖ ^ 2) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateData hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, a, hest⟩
    exact ⟨p, mixedDirectionalQuadraticSum D v a,
      isSymmetricOperator_mixedDirectionalQuadraticSum D v a, hest⟩)

/-- Punctured normalized quotient version of
`secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticEstimateData`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticQuotientData
    {ι : Type*} {μ : Measure E} {s G : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ a : ι → ι → ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
            ‖affineRemainder u x p (x + z) -
                (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ /
                ‖z‖ ^ 2 ≤ ε) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_quadraticQuotientEstimateData hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, a, hest⟩
    exact ⟨p, mixedDirectionalQuadraticSum D v a,
      isSymmetricOperator_mixedDirectionalQuadraticSum D v a, hest⟩)

/-- Full-measure assembly from estimates whose quadratic model is assembled from polarized
pure and pairwise-sum directional coefficients. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuadraticEstimateData
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s G : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhds 0,
            ‖affineRemainder u x p (x + z) -
                (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ ≤
              ε * ‖z‖ ^ 2) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateData hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, q, r, hest⟩
    exact ⟨p, polarizedMixedQuadraticSum D v q r,
      isSymmetricOperator_polarizedMixedQuadraticSum D v q r, hest⟩)

/-- Punctured normalized quotient version of
`secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuadraticEstimateData`. -/
theorem
    secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuadraticQuotientData
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s G : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
            ‖affineRemainder u x p (x + z) -
                (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ /
                ‖z‖ ^ 2 ≤ ε) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_quadraticQuotientEstimateData hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, q, r, hest⟩
    exact ⟨p, polarizedMixedQuadraticSum D v q r,
      isSymmetricOperator_polarizedMixedQuadraticSum D v q r, hest⟩)

/-- Full-measure assembly from arbitrary symmetric ambient quadratic estimate data whose pure
and off-diagonal pairwise-sum coefficients match a finite orthonormal spanning frame.  The
ambient Hessian candidate is canonicalized to the polarized mixed-directional model by the
finite-frame uniqueness theorem. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateData_coefficients
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s G : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hv : FiniteOrthonormalSpanningOn D v) (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ B : E →L[ℝ] E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
        IsSymmetricOperator B ∧
          (∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhds 0,
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
                ε * ‖z‖ ^ 2) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
          (∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
            inner ℝ (v i + v j) (B (v i + v j)) = r i j)) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuadraticEstimateData
    hs D v hnull (by
      intro x hxs hxG
      rcases hG hxs hxG with ⟨p, B, q, r, hB, hest, hr, hpure, hpair⟩
      exact polarizedMixedDirectionalQuadraticEstimateAt_of_quadraticEstimateData_coefficients
        hv hB hest hr hpure hpair)

/-- Punctured normalized quotient version of
`secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateData_coefficients`. -/
theorem
    secondOrderDifferentiableAEOn_of_fullMeasure_quadraticQuotientData_coefficients
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s G : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hv : FiniteOrthonormalSpanningOn D v) (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ B : E →L[ℝ] E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
        IsSymmetricOperator B ∧
          (∀ ε : ℝ, 0 < ε →
            ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
              ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                  ‖z‖ ^ 2 ≤ ε) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
          (∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i) ∧
          (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
            inner ℝ (v i + v j) (B (v i + v j)) = r i j)) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuadraticQuotientData
    hs D v hnull (by
      intro x hxs hxG
      rcases hG hxs hxG with ⟨p, B, q, r, hB, hest, hr, hpure, hpair⟩
      exact
        polarizedMixedDirectionalQuadraticQuotientEstimateAt_of_quadraticQuotientData_coefficients
          hv hB hest hr hpure hpair)

/-- If the named mixed-directional estimate set has full measure in `s`, then `u` is
second-order differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticEstimateSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ mixedDirectionalQuadraticEstimateSet D v u) = 0) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact mixedDirectionalQuadraticEstimateSet_subset_secondOrderDifferentiabilitySet hx.2)

/-- If the named mixed-directional quotient-estimate set has full measure in `s`, then `u` is
second-order differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticQuotientSet
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ mixedDirectionalQuadraticQuotientEstimateSet D v u) = 0) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact mixedDirectionalQuadraticQuotientEstimateSet_subset_secondOrderDifferentiabilitySet hx.2)

/-- If the named polarized mixed-directional estimate set has full measure in `s`, then `u` is
second-order differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuadraticSet
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ polarizedMixedDirectionalQuadraticEstimateSet D v u) = 0) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact polarizedMixedDirectionalQuadraticEstimateSet_subset_secondOrderDifferentiabilitySet
      hx.2)

/-- If the named polarized mixed-directional quotient-estimate set has full measure in `s`, then
`u` is second-order differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuotientSet
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u) = 0) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact hx.2.secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure finite slice-estimate set: once a pointwise
reconstruction theorem turns the finite slice target into mixed-directional ambient estimates, the
project second-order differentiability conclusion follows almost everywhere. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_directionalSliceEstimateSet_of_reconstruction
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ directionalSliceEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceEstimateAt D v u x → MixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure finite slice quotient-estimate set: once a
pointwise reconstruction theorem turns the finite slice quotient target into mixed-directional
ambient quotient estimates, the project second-order differentiability conclusion follows almost
everywhere. -/
theorem
    secondOrderDifferentiableAEOn_of_fullMeasure_directionalSliceQuotientSet_of_reconstruction
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ directionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceQuotientEstimateAt D v u x →
        MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure compatible finite slice-estimate set: once a
pointwise reconstruction theorem turns compatible finite line data into mixed-directional ambient
estimates, the project second-order differentiability conclusion follows almost everywhere. -/
theorem
    secondOrderDifferentiableAEOn_of_fullMeasure_compatibleSliceSet_of_reconstruction
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      CompatibleDirectionalSliceEstimateAt D v u x →
        MixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- Quotient-estimate version of the compatible-slice reconstruction assembly lemma. -/
theorem
    secondOrderDifferentiableAEOn_of_fullMeasure_compatibleSliceQuotientSet_of_reconstruction
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      CompatibleDirectionalSliceQuotientEstimateAt D v u x →
        MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- A.e.-membership version of
`secondOrderDifferentiableAEOn_of_fullMeasure_directionalSliceEstimateSet_of_reconstruction`. -/
theorem secondOrderDifferentiableAEOn_of_ae_directionalSliceSet_of_reconstruction
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hmem : ∀ᵐ x ∂μ.restrict s, x ∈ directionalSliceEstimateSet D v u)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceEstimateAt D v u x → MixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_ae_goodSet hs hmem (by
    intro x hxs hxG
    exact (hrecon hxs hxG).secondOrderDifferentiableAt)

/-- A.e.-membership version of
`secondOrderDifferentiableAEOn_of_fullMeasure_directionalSliceQuotientSet_of_reconstruction`. -/
theorem secondOrderDifferentiableAEOn_of_ae_directionalSliceQuotientSet_of_reconstruction
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hmem : ∀ᵐ x ∂μ.restrict s, x ∈ directionalSliceQuotientEstimateSet D v u)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceQuotientEstimateAt D v u x →
        MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_ae_goodSet hs hmem (by
    intro x hxs hxG
    exact (hrecon hxs hxG).secondOrderDifferentiableAt)

/-- A.e.-membership version of
`secondOrderDifferentiableAEOn_of_fullMeasure_compatibleSliceSet_of_reconstruction`. -/
theorem secondOrderDifferentiableAEOn_of_ae_compatibleSliceSet_of_reconstruction
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hmem : ∀ᵐ x ∂μ.restrict s, x ∈ compatibleDirectionalSliceEstimateSet D v u)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      CompatibleDirectionalSliceEstimateAt D v u x →
        MixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_ae_goodSet hs hmem (by
    intro x hxs hxG
    exact (hrecon hxs hxG).secondOrderDifferentiableAt)

/-- A.e.-membership version of
`secondOrderDifferentiableAEOn_of_fullMeasure_compatibleSliceQuotientSet_of_reconstruction`. -/
theorem secondOrderDifferentiableAEOn_of_ae_compatibleSliceQuotientSet_of_reconstruction
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (D : Finset ι) (v : ι → E)
    (hmem : ∀ᵐ x ∂μ.restrict s, x ∈ compatibleDirectionalSliceQuotientEstimateSet D v u)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      CompatibleDirectionalSliceQuotientEstimateAt D v u x →
        MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_ae_goodSet hs hmem (by
    intro x hxs hxG
    exact (hrecon hxs hxG).secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure finite slice-estimate set when pointwise
reconstruction produces polarized mixed-directional ambient estimates. -/
theorem
    secondOrderDifferentiableAEOn_of_sliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ directionalSliceEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- A.e.-membership version of
`secondOrderDifferentiableAEOn_of_sliceSet_polarized_reconstruction`. -/
theorem secondOrderDifferentiableAEOn_of_ae_sliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hmem : ∀ᵐ x ∂μ.restrict s, x ∈ directionalSliceEstimateSet D v u)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_ae_goodSet hs hmem (by
    intro x hxs hxG
    exact (hrecon hxs hxG).secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure compatible finite slice-estimate set when pointwise
reconstruction produces polarized mixed-directional ambient estimates. -/
theorem
    secondOrderDifferentiableAEOn_of_compatibleSliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      CompatibleDirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- A.e.-membership version of
`secondOrderDifferentiableAEOn_of_compatibleSliceSet_polarized_reconstruction`. -/
theorem secondOrderDifferentiableAEOn_of_ae_compatibleSliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hmem : ∀ᵐ x ∂μ.restrict s, x ∈ compatibleDirectionalSliceEstimateSet D v u)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      CompatibleDirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_ae_goodSet hs hmem (by
    intro x hxs hxG
    exact (hrecon hxs hxG).secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure symmetric-compatible finite slice-estimate set when
pointwise reconstruction produces polarized mixed-directional ambient estimates. -/
theorem
    secondOrderDifferentiableAEOn_of_symmetricCompatibleSliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ symmetricCompatibleDirectionalSliceEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      SymmetricCompatibleDirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- A.e.-membership version of
`secondOrderDifferentiableAEOn_of_symmetricCompatibleSliceSet_polarized_reconstruction`. -/
theorem secondOrderDifferentiableAEOn_of_ae_symmetricCompatibleSliceSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hmem : ∀ᵐ x ∂μ.restrict s,
      x ∈ symmetricCompatibleDirectionalSliceEstimateSet D v u)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      SymmetricCompatibleDirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_ae_goodSet hs hmem (by
    intro x hxs hxG
    exact (hrecon hxs hxG).secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure compatible finite quotient-slice set when pointwise
reconstruction produces polarized mixed-directional ambient quotient estimates. -/
theorem
    secondOrderDifferentiableAEOn_of_compatibleSliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ compatibleDirectionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      CompatibleDirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- A.e.-membership version of
`secondOrderDifferentiableAEOn_of_compatibleSliceQuotientSet_polarized_reconstruction`. -/
theorem secondOrderDifferentiableAEOn_of_ae_compatibleSliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hmem : ∀ᵐ x ∂μ.restrict s,
      x ∈ compatibleDirectionalSliceQuotientEstimateSet D v u)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      CompatibleDirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_ae_goodSet hs hmem (by
    intro x hxs hxG
    exact (hrecon hxs hxG).secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure symmetric-compatible finite quotient-slice set when
pointwise reconstruction produces polarized mixed-directional ambient quotient estimates. -/
theorem
    secondOrderDifferentiableAEOn_of_symmetricCompatibleSliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- A.e.-membership version of
`secondOrderDifferentiableAEOn_of_symmetricCompatibleSliceQuotientSet_polarized_reconstruction`. -/
theorem
    secondOrderDifferentiableAEOn_of_ae_symmetricCompatibleSliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hmem : ∀ᵐ x ∂μ.restrict s,
      x ∈ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_ae_goodSet hs hmem (by
    intro x hxs hxG
    exact (hrecon hxs hxG).secondOrderDifferentiableAt)

/-- Conditional assembly from a full-measure finite slice quotient-estimate set when pointwise
reconstruction produces polarized mixed-directional ambient quotient estimates. -/
theorem
    secondOrderDifferentiableAEOn_of_sliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hnull : μ (s \ directionalSliceQuotientEstimateSet D v u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact (hrecon hx.1 hx.2).secondOrderDifferentiableAt)

/-- A.e.-membership version of
`secondOrderDifferentiableAEOn_of_sliceQuotientSet_polarized_reconstruction`. -/
theorem secondOrderDifferentiableAEOn_of_ae_sliceQuotientSet_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hmem : ∀ᵐ x ∂μ.restrict s, x ∈ directionalSliceQuotientEstimateSet D v u)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_ae_goodSet hs hmem (by
    intro x hxs hxG
    exact (hrecon hxs hxG).secondOrderDifferentiableAt)

/-- Conditional assembly from full-measure scalar estimate sets for each selected direction and
pairwise-sum direction.  The only remaining pointwise input is reconstruction from the bundled
finite slice target into an ambient mixed-directional estimate. -/
theorem secondOrderDifferentiableAEOn_of_directionalLineScalarSets_reconstruction
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i + v j) u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceEstimateAt D v u x → MixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_directionalSliceEstimateSet_of_reconstruction
    hs D v
    (measure_diff_directionalSliceEstimateSet_eq_zero_of_directionalLine_fullMeasure
      hs D v hpure hpair)
    hrecon

/-- Quotient-estimate version of
`secondOrderDifferentiableAEOn_of_directionalLineScalarSets_reconstruction`. -/
theorem secondOrderDifferentiableAEOn_of_directionalLineScalarQuotientSets_reconstruction
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceQuotientEstimateAt D v u x →
        MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_directionalSliceQuotientSet_of_reconstruction
    hs D v
    (measure_diff_directionalSliceQuotientSet_eq_zero_of_directionalLine_fullMeasure
      hs D v hpure hpair)
    hrecon

/-- Off-diagonal version of
`secondOrderDifferentiableAEOn_of_directionalLineScalarSets_reconstruction`: the diagonal
pairwise-sum line estimates are supplied by rescaling the pure line estimates. -/
theorem secondOrderDifferentiableAEOn_of_directionalLineScalarSets_reconstruction_offDiagonal
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      μ (s \ directionalLineScalarEstimateSet (v i + v j) u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceEstimateAt D v u x → MixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_directionalSliceEstimateSet_of_reconstruction
    hs D v
    (measure_diff_directionalSliceSet_eq_zero_of_directionalLine_fullMeasure_offDiagonal
      hs D v hpure hpair)
    hrecon

/-- Quotient-estimate off-diagonal version of
`secondOrderDifferentiableAEOn_of_directionalLineScalarQuotientSets_reconstruction`. -/
theorem
    secondOrderDifferentiableAEOn_of_directionalLineScalarQuotientSets_reconstruction_offDiagonal
    {ι : Type*} {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceQuotientEstimateAt D v u x →
        MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_directionalSliceQuotientSet_of_reconstruction
    hs D v
    (measure_diff_directionalSliceQuotientSet_eq_zero_of_directionalLine_fullMeasure_offDiagonal
      hs D v hpure hpair)
    hrecon

/-- Polarized reconstruction version of
`secondOrderDifferentiableAEOn_of_directionalLineScalarSets_reconstruction`. -/
theorem secondOrderDifferentiableAEOn_of_directionalLineScalarSets_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i + v j) u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_sliceSet_polarized_reconstruction
    hs D v
    (measure_diff_directionalSliceEstimateSet_eq_zero_of_directionalLine_fullMeasure
      hs D v hpure hpair)
    hrecon

/-- Quotient-estimate polarized reconstruction version of
`secondOrderDifferentiableAEOn_of_directionalLineScalarSets_reconstruction`. -/
theorem secondOrderDifferentiableAEOn_of_directionalLineScalarQuotientSets_polarized_reconstruction
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_sliceQuotientSet_polarized_reconstruction
    hs D v
    (measure_diff_directionalSliceQuotientSet_eq_zero_of_directionalLine_fullMeasure
      hs D v hpure hpair)
    hrecon

/-- Polarized reconstruction version of
`secondOrderDifferentiableAEOn_of_directionalLineScalarSets_reconstruction_offDiagonal`. -/
theorem
    secondOrderDifferentiableAEOn_of_directionalLineScalarSets_polarized_reconstruction_offDiagonal
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      μ (s \ directionalLineScalarEstimateSet (v i + v j) u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_sliceSet_polarized_reconstruction
    hs D v
    (measure_diff_directionalSliceSet_eq_zero_of_directionalLine_fullMeasure_offDiagonal
      hs D v hpure hpair)
    hrecon

/-- Quotient-estimate polarized reconstruction version of
`secondOrderDifferentiableAEOn_of_directionalLineScalarSets_polarized_reconstruction_offDiagonal`.
-/
theorem
    secondOrderDifferentiableAEOn_of_directionalLineQuotientSets_polarized_recon_offDiagonal
    {ι : Type*} [DecidableEq ι] {μ : Measure E} {s : Set E} {u : E → ℝ}
    (hs : MeasurableSet s) (D : Finset ι) (v : ι → E)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i) u) = 0)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      μ (s \ directionalLineScalarQuotientEstimateSet (v i + v j) u) = 0)
    (hrecon : ∀ ⦃x : E⦄, x ∈ s →
      DirectionalSliceQuotientEstimateAt D v u x →
        PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_sliceQuotientSet_polarized_reconstruction
    hs D v
    (measure_diff_directionalSliceQuotientSet_eq_zero_of_directionalLine_fullMeasure_offDiagonal
      hs D v hpure hpair)
    hrecon


end AleksandrovDifferentiability
