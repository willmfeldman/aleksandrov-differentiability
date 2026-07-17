import AleksandrovDifferentiability.Statements.Aleksandrov.Equivalence
import AleksandrovDifferentiability.Statements.Aleksandrov.EstimateData
import AleksandrovDifferentiability.Statements.Aleksandrov.CountableAE

/-!
# Estimate-data reductions to null bad sets
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_quadraticEstimateData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_quadraticEstimateData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhds 0,
                  ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
                    ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_quadraticEstimateData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_quadraticQuotientEstimateData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_quadraticQuotientEstimateData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                  ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                      ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_quadraticQuotientEstimateData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_quadraticEstimateData_coefficients`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_quadraticEstimateData_coefficients
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ B : E →L[ℝ] E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            IsSymmetricOperator B ∧
              (∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhds 0,
                  ‖affineRemainder u x p (x + z) -
                      (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤ ε * ‖z‖ ^ 2) ∧
              (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
              (∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i) ∧
              (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
                inner ℝ (v i + v j) (B (v i + v j)) = r i j)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact measure_badSetOn_eq_zero_of_fullMeasure_quadraticEstimateData_coefficients
    (μ := volume) hΩ.measurableSet D v hframe hnull hG

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_quadraticQuotientData_coefficients`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_fullMeasure_quadraticQuotientData_coefficients
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ B : E →L[ℝ] E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            IsSymmetricOperator B ∧
              (∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                  ‖affineRemainder u x p (x + z) -
                      (1 / 2 : ℝ) * inner ℝ z (B z)‖ / ‖z‖ ^ 2 ≤ ε) ∧
              (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j) ∧
              (∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i) ∧
              (∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
                inner ℝ (v i + v j) (B (v i + v j)) = r i j)) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact measure_badSetOn_eq_zero_of_fullMeasure_quadraticQuotientData_coefficients
    (μ := volume) hΩ.measurableSet D v hframe hnull hG

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_mixedDirectionalQuadraticEstimateData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_mixedDirectionalQuadraticEstimateData
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ a : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  have hAE : SecondOrderDifferentiableAEOn volume Ω u :=
    secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticEstimateData
      (μ := volume) hΩ.measurableSet D v hnull hG
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_mixedDirectionalQuadraticQuotientData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_mixedDirectionalQuadraticQuotientData
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ a : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  have hAE : SecondOrderDifferentiableAEOn volume Ω u :=
    secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticQuotientData
      (μ := volume) hΩ.measurableSet D v hnull hG
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_polarizedMixedDirectionalQuadraticEstimateData`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_fullMeasure_polarizedDirectionalEstimateData
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  have hAE : SecondOrderDifferentiableAEOn volume Ω u :=
    secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuadraticEstimateData
      (μ := volume) hΩ.measurableSet D v hnull hG
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_fullMeasure_polarizedMixedDirectionalQuadraticQuotientData`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_fullMeasure_polarizedDirectionalQuotientData
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  have hAE : SecondOrderDifferentiableAEOn volume Ω u :=
    secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuadraticQuotientData
      (μ := volume) hΩ.measurableSet D v hnull hG
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Null-bad-set theorem-boundary reduction from full measure of the named ambient quadratic
estimate set. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_quadraticEstimateSet
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ quadraticEstimateSet u) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_quadraticEstimateSet
    (μ := volume) hΩ.measurableSet (hgood hΩ hu)

/-- Null-bad-set theorem-boundary reduction from full measure of the named ambient quadratic
quotient-estimate set. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_quadraticQuotientEstimateSet
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ quadraticQuotientEstimateSet u) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_quadraticQuotientEstimateSet
    (μ := volume) hΩ.measurableSet (hgood hΩ hu)

/-- Coordinate-model null-bad-set version of the ambient quadratic estimate-set endpoint. -/
theorem convexAleksandrovNullBadSetOnStatement_of_image_quadraticEstimateSet
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume (e '' Ω \ quadraticEstimateSet (u ∘ e.symm)) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_fullMeasure_quadraticEstimateSet
      E F e Ω u hgood)

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_image_quadraticEstimateSet`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_image_quadraticQuotientSet
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume (e '' Ω \ quadraticQuotientEstimateSet (u ∘ e.symm)) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_fullMeasure_quadraticQuotientEstimateSet
      E F e Ω u hgood)

/-- Restricted-measure coordinate-model null-bad-set version of the ambient quadratic
estimate-set endpoint. -/
theorem convexAleksandrovNullBadSetStatement_of_image_quadraticEstimateSet
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume (e '' Ω \ quadraticEstimateSet (u ∘ e.symm)) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_quadraticEstimateSet
      E F e Ω u hgood)

/-- Restricted-measure quotient-estimate version of
`convexAleksandrovNullBadSetStatement_of_image_quadraticEstimateSet`. -/
theorem convexAleksandrovNullBadSetStatement_of_image_quadraticQuotientSet
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume (e '' Ω \ quadraticQuotientEstimateSet (u ∘ e.symm)) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_quadraticQuotientSet
      E F e Ω u hgood)

/-- Null-bad-set theorem-boundary reduction from full measure of the named ambient
mixed-directional quadratic estimate set. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_mixedDirectionalQuadraticEstimateSet
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ mixedDirectionalQuadraticEstimateSet D v u) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_mixedDirectionalQuadraticEstimateSet
    (μ := volume) hΩ.measurableSet D v (hgood hΩ hu)

/-- Null-bad-set theorem-boundary reduction from full measure of the named ambient
mixed-directional quadratic quotient-estimate set. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_mixedDirectionalQuadraticQuotientSet
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ mixedDirectionalQuadraticQuotientEstimateSet D v u) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_mixedDirectionalQuadraticQuotientSet
    (μ := volume) hΩ.measurableSet D v (hgood hΩ hu)

/-- Null-bad-set theorem-boundary reduction from full measure of the named polarized
mixed-directional quadratic estimate set. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_polarizedMixedDirectionalQuadraticSet
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ polarizedMixedDirectionalQuadraticEstimateSet D v u) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_badSetOn_eq_zero_of_fullMeasure_polarizedMixedDirectionalQuadraticSet
    (μ := volume) hΩ.measurableSet D v (hgood hΩ hu)

/-- Null-bad-set theorem-boundary reduction from full measure of the named polarized
mixed-directional quotient-estimate set. -/
theorem convexAleksandrovNullBadSetOnStatement_of_fullMeasure_polarizedMixedDirectionalQuotientSet
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  exact measure_badSetOn_eq_zero_of_fullMeasure_polarizedMixedDirectionalQuotientSet
    (μ := volume) hΩ.measurableSet D v (hgood hΩ hu)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_fullMeasure_quadraticEstimateData`. -/
theorem convexAleksandrovNullBadSetStatement_of_fullMeasure_quadraticEstimateData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhds 0,
                  ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
                    ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fullMeasure_quadraticEstimateData
      E Ω u hgood)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_fullMeasure_quadraticQuotientEstimateData`. -/
theorem convexAleksandrovNullBadSetStatement_of_fullMeasure_quadraticQuotientEstimateData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                  ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                      ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fullMeasure_quadraticQuotientEstimateData
      E Ω u hgood)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_fullMeasure_mixedDirectionalQuadraticEstimateData`. -/
theorem
    convexAleksandrovNullBadSetStatement_of_fullMeasure_mixedDirectionalQuadraticEstimateData
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ a : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fullMeasure_mixedDirectionalQuadraticEstimateData
      D E Ω u v hgood)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_fullMeasure_mixedDirectionalQuadraticQuotientData`. -/
theorem
    convexAleksandrovNullBadSetStatement_of_fullMeasure_mixedDirectionalQuadraticQuotientData
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ a : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fullMeasure_mixedDirectionalQuadraticQuotientData
      D E Ω u v hgood)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_fullMeasure_polarizedDirectionalEstimateData`. -/
theorem convexAleksandrovNullBadSetStatement_of_fullMeasure_polarizedDirectionalEstimateData
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fullMeasure_polarizedDirectionalEstimateData
      D E Ω u v hgood)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_fullMeasure_polarizedDirectionalQuotientData`. -/
theorem convexAleksandrovNullBadSetStatement_of_fullMeasure_polarizedDirectionalQuotientData
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : Set E, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : E⦄, x ∈ Ω → x ∈ G →
          ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fullMeasure_polarizedDirectionalQuotientData
      D E Ω u v hgood)

/-- Restricted-measure null-bad-set theorem-boundary reduction from full measure of the named
ambient quadratic estimate set. -/
theorem convexAleksandrovNullBadSetStatement_of_fullMeasure_quadraticEstimateSet
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ quadraticEstimateSet u) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fullMeasure_quadraticEstimateSet
      E Ω u hgood)

/-- Restricted-measure null-bad-set theorem-boundary reduction from full measure of the named
ambient quadratic quotient-estimate set. -/
theorem convexAleksandrovNullBadSetStatement_of_fullMeasure_quadraticQuotientEstimateSet
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ quadraticQuotientEstimateSet u) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fullMeasure_quadraticQuotientEstimateSet
      E Ω u hgood)

/-- Restricted-measure null-bad-set theorem-boundary reduction from full measure of the named
ambient mixed-directional quadratic estimate set. -/
theorem convexAleksandrovNullBadSetStatement_of_fullMeasure_mixedDirectionalQuadraticEstimateSet
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ mixedDirectionalQuadraticEstimateSet D v u) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fullMeasure_mixedDirectionalQuadraticEstimateSet
      D E Ω u v hgood)

/-- Restricted-measure null-bad-set theorem-boundary reduction from full measure of the named
ambient mixed-directional quadratic quotient-estimate set. -/
theorem
    convexAleksandrovNullBadSetStatement_of_fullMeasure_mixedDirectionalQuadraticQuotientSet
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ mixedDirectionalQuadraticQuotientEstimateSet D v u) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fullMeasure_mixedDirectionalQuadraticQuotientSet
      D E Ω u v hgood)

/-- Restricted-measure null-bad-set theorem-boundary reduction from full measure of the named
polarized mixed-directional quadratic estimate set. -/
theorem convexAleksandrovNullBadSetStatement_of_fullMeasure_polarizedMixedDirectionalQuadraticSet
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ polarizedMixedDirectionalQuadraticEstimateSet D v u) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fullMeasure_polarizedMixedDirectionalQuadraticSet
      D E Ω u v hgood)

/-- Restricted-measure null-bad-set theorem-boundary reduction from full measure of the named
polarized mixed-directional quotient-estimate set. -/
theorem convexAleksandrovNullBadSetStatement_of_fullMeasure_polarizedMixedDirectionalQuotientSet
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_fullMeasure_polarizedMixedDirectionalQuotientSet
      D E Ω u v hgood)

/-- Coordinate-model null-bad-set version of the mixed estimate-set endpoint. -/
theorem convexAleksandrovNullBadSetOnStatement_of_image_mixedEstimateSet
    {ι : Type*} (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume
          (e '' Ω \ mixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i))
            (u ∘ e.symm)) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_fullMeasure_mixedDirectionalQuadraticEstimateSet
      D E F e Ω u v hgood)

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_image_mixedEstimateSet`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_image_mixedQuotientSet
    {ι : Type*} (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume
          (e '' Ω \ mixedDirectionalQuadraticQuotientEstimateSet D (fun i ↦ e (v i))
            (u ∘ e.symm)) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_fullMeasure_mixedDirectionalQuadraticQuotientSet
      D E F e Ω u v hgood)

/-- Coordinate-model null-bad-set version of the polarized mixed estimate-set endpoint. -/
theorem convexAleksandrovNullBadSetOnStatement_of_image_polarizedMixedEstimateSet
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume
          (e '' Ω \ polarizedMixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i))
            (u ∘ e.symm)) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_fullMeasure_polarizedMixedDirectionalQuadraticSet
      D E F e Ω u v hgood)

/-- Quotient-estimate version of
`convexAleksandrovNullBadSetOnStatement_of_image_polarizedMixedEstimateSet`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_image_polarizedMixedQuotientSet
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume
          (e '' Ω \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D
            (fun i ↦ e (v i)) (u ∘ e.symm)) = 0) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  (convexAleksandrovAEStatement_iff_nullBadSetOnStatement E Ω u).mp
    (convexAleksandrovAEStatement_of_image_fullMeasure_polarizedMixedDirectionalQuotientSet
      D E F e Ω u v hgood)

/-- Restricted-measure coordinate-model null-bad-set version of the mixed estimate-set endpoint.
-/
theorem convexAleksandrovNullBadSetStatement_of_image_mixedEstimateSet
    {ι : Type*} (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume
          (e '' Ω \ mixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i))
            (u ∘ e.symm)) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_mixedEstimateSet
      D E F e Ω u v hgood)

/-- Restricted-measure quotient-estimate version of
`convexAleksandrovNullBadSetStatement_of_image_mixedEstimateSet`. -/
theorem convexAleksandrovNullBadSetStatement_of_image_mixedQuotientSet
    {ι : Type*} (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume
          (e '' Ω \ mixedDirectionalQuadraticQuotientEstimateSet D (fun i ↦ e (v i))
            (u ∘ e.symm)) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_mixedQuotientSet
      D E F e Ω u v hgood)

/-- Restricted-measure coordinate-model null-bad-set version of the polarized mixed estimate-set
endpoint. -/
theorem convexAleksandrovNullBadSetStatement_of_image_polarizedMixedEstimateSet
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume
          (e '' Ω \ polarizedMixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i))
            (u ∘ e.symm)) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_polarizedMixedEstimateSet
      D E F e Ω u v hgood)

/-- Restricted-measure quotient-estimate version of
`convexAleksandrovNullBadSetStatement_of_image_polarizedMixedEstimateSet`. -/
theorem convexAleksandrovNullBadSetStatement_of_image_polarizedMixedQuotientSet
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume
          (e '' Ω \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D
            (fun i ↦ e (v i)) (u ∘ e.symm)) = 0) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_image_polarizedMixedQuotientSet
      D E F e Ω u v hgood)

end AleksandrovDifferentiability
