import AleksandrovDifferentiability.Statements.OneDimensional.RealLine
import AleksandrovDifferentiability.Statements.Aleksandrov.NullBadSet.StandardBasis

/-!
# Countable and real-line reductions to null bad sets
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_countable_fullMeasure_quadraticEstimateData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_countable_fullMeasure_quadraticEstimateData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhds 0,
                  ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
                    ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact measure_secondOrderBadSetOn_eq_zero_of_countable_fullMeasure_quadraticEstimateData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_countable_fullMeasure_quadraticQuotientEstimateData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_countable_quadraticQuotientEstimateData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                  ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                      ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact measure_secondOrderBadSetOn_eq_zero_of_countable_fullMeasure_quadraticQuotientEstimateData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_countable_quadraticEstimateData_coefficients`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_countable_quadraticEstimateData_coefficients
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
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
  exact measure_badSetOn_eq_zero_of_countable_quadraticEstimateData_coefficients
    (μ := volume) hΩ.measurableSet D v hframe hnull hG

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_countable_quadraticQuotientData_coefficients`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_countable_quadraticQuotientData_coefficients
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hframe : FiniteOrthonormalSpanningOn D v)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
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
  exact measure_badSetOn_eq_zero_of_countable_quadraticQuotientData_coefficients
    (μ := volume) hΩ.measurableSet D v hframe hnull hG

/-- Alias with the same naming scheme as the corresponding a.e. theorem. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_countable_fullMeasure_quadraticQuotientEstimateData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                  ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                      ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_countable_quadraticQuotientEstimateData
    E Ω u hgood

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_countable_mixedDirectionalQuadraticEstimateData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_countable_mixedDirectionalQuadraticEstimateData
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
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
    secondOrderDifferentiableAEOn_of_countable_mixedDirectionalQuadraticEstimateData
      (μ := volume) hΩ.measurableSet D v hnull hG
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_countable_mixedDirectionalQuadraticQuotientData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_countable_mixedDirectionalQuadraticQuotientData
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
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
    secondOrderDifferentiableAEOn_of_countable_mixedDirectionalQuadraticQuotientData
      (μ := volume) hΩ.measurableSet D v hnull hG
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_countable_polarizedMixedDirectionalQuadraticEstimateData`. -/
theorem convexAleksandrovNullBadSetOnStatement_of_countable_polarizedDirectionalEstimateData
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
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
    secondOrderDifferentiableAEOn_of_countable_polarizedMixedDirectionalQuadraticEstimateData
      (μ := volume) hΩ.measurableSet D v hnull hG
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Alias with the same naming scheme as the corresponding a.e. theorem. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_countable_polarizedMixedEstimateData
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_countable_polarizedDirectionalEstimateData
    D E Ω u v hgood

/-- Null-bad-set version of
`convexAleksandrovAEStatement_of_countable_polarizedMixedDirectionalQuadraticQuotientData`. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_countable_polarizedDirectionalQuotientData
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
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
    secondOrderDifferentiableAEOn_of_countable_polarizedMixedDirectionalQuadraticQuotientData
      (μ := volume) hΩ.measurableSet D v hnull hG
  exact (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    (μ := volume) (s := Ω) (u := u) hΩ.measurableSet).mp hAE

/-- Alias with the same naming scheme as the corresponding a.e. theorem. -/
theorem
    convexAleksandrovNullBadSetOnStatement_of_countable_polarizedMixedQuotientData
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetOnStatement E Ω u :=
  convexAleksandrovNullBadSetOnStatement_of_countable_polarizedDirectionalQuotientData
    D E Ω u v hgood

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_countable_fullMeasure_quadraticEstimateData`. -/
theorem convexAleksandrovNullBadSetStatement_of_countable_fullMeasure_quadraticEstimateData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhds 0,
                  ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
                    ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_countable_fullMeasure_quadraticEstimateData
      E Ω u hgood)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_countable_fullMeasure_quadraticQuotientEstimateData`.
-/
theorem
    convexAleksandrovNullBadSetStatement_of_countable_fullMeasure_quadraticQuotientEstimateData
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ B : E →L[ℝ] E,
            IsSymmetricOperator B ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                  ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
                      ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_countable_fullMeasure_quadraticQuotientEstimateData
      E Ω u hgood)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_countable_mixedDirectionalQuadraticEstimateData`. -/
theorem convexAleksandrovNullBadSetStatement_of_countable_mixedDirectionalQuadraticEstimateData
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ a : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_countable_mixedDirectionalQuadraticEstimateData
      D E Ω u v hgood)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_countable_mixedDirectionalQuadraticQuotientData`. -/
theorem convexAleksandrovNullBadSetStatement_of_countable_mixedDirectionalQuadraticQuotientData
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ a : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (mixedDirectionalQuadraticSum D v a z)‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_countable_mixedDirectionalQuadraticQuotientData
      D E Ω u v hgood)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_countable_polarizedDirectionalEstimateData`. -/
theorem convexAleksandrovNullBadSetStatement_of_countable_polarizedDirectionalEstimateData
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_countable_polarizedDirectionalEstimateData
      D E Ω u v hgood)

/-- Restricted-measure null-bad-set version of
`convexAleksandrovNullBadSetOnStatement_of_countable_polarizedDirectionalQuotientData`. -/
theorem convexAleksandrovNullBadSetStatement_of_countable_polarizedDirectionalQuotientData
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      ∃ G : ℕ → Set E, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : E⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : E, ∃ q : ι → ℝ, ∃ r : ι → ι → ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
                ‖affineRemainder u x p (x + z) -
                    (1 / 2 : ℝ) * inner ℝ z (polarizedMixedQuadraticSum D v q r z)‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetStatement E Ω u :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement E
    (convexAleksandrovNullBadSetOnStatement_of_countable_polarizedDirectionalQuotientData
      D E Ω u v hgood)

/-- Null-bad-set theorem-boundary reduction from real-line scalar local quadratic estimates. -/
theorem convexAleksandrovNullBadSetOnStatement_real_of_fullMeasure_scalarEstimate
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      ∃ G : Set ℝ, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : ℝ⦄, x ∈ Ω → x ∈ G →
          ∃ p : ℝ, ∃ q : ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f := by
  intro hΩ hf
  rcases hgood hΩ hf with ⟨G, hnull, hG⟩
  exact measure_secondOrderBadSetOn_eq_zero_real_of_fullMeasure_scalarEstimate
    (μ := volume) hΩ.measurableSet hnull hG

/-- Null-bad-set theorem-boundary reduction from real-line scalar quotient estimates. -/
theorem convexAleksandrovNullBadSetOnStatement_real_of_fullMeasure_scalarQuotientEstimate
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      ∃ G : Set ℝ, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : ℝ⦄, x ∈ Ω → x ∈ G →
          ∃ p : ℝ, ∃ q : ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
                ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f := by
  intro hΩ hf
  rcases hgood hΩ hf with ⟨G, hnull, hG⟩
  exact measure_secondOrderBadSetOn_eq_zero_real_of_fullMeasure_scalarQuotientEstimate
    (μ := volume) hΩ.measurableSet hnull hG

/-- Null-bad-set theorem-boundary reduction from countably many real-line scalar good sets. -/
theorem convexAleksandrovNullBadSetOnStatement_real_of_countable_scalarEstimate
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      ∃ G : ℕ → Set ℝ, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : ℝ⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : ℝ, ∃ q : ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f := by
  intro hΩ hf
  rcases hgood hΩ hf with ⟨G, hnull, hG⟩
  exact measure_secondOrderBadSetOn_eq_zero_real_of_countable_scalarEstimate
    (μ := volume) hΩ.measurableSet hnull hG

/-- Null-bad-set theorem-boundary reduction from countably many real-line scalar quotient good
sets. -/
theorem convexAleksandrovNullBadSetOnStatement_real_of_countable_scalarQuotientEstimate
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      ∃ G : ℕ → Set ℝ, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : ℝ⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : ℝ, ∃ q : ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
                ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f := by
  intro hΩ hf
  rcases hgood hΩ hf with ⟨G, hnull, hG⟩
  exact measure_secondOrderBadSetOn_eq_zero_real_of_countable_scalarQuotientEstimate
    (μ := volume) hΩ.measurableSet hnull hG

/-- Restricted-measure null-bad-set theorem-boundary reduction from real-line scalar local
quadratic estimates. -/
theorem convexAleksandrovNullBadSetStatement_real_of_fullMeasure_scalarEstimate
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      ∃ G : Set ℝ, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : ℝ⦄, x ∈ Ω → x ∈ G →
          ∃ p : ℝ, ∃ q : ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement ℝ
    (convexAleksandrovNullBadSetOnStatement_real_of_fullMeasure_scalarEstimate
      Ω f hgood)

/-- Restricted-measure null-bad-set theorem-boundary reduction from real-line scalar quotient
estimates. -/
theorem convexAleksandrovNullBadSetStatement_real_of_fullMeasure_scalarQuotientEstimate
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      ∃ G : Set ℝ, volume (Ω \ G) = 0 ∧
        ∀ ⦃x : ℝ⦄, x ∈ Ω → x ∈ G →
          ∃ p : ℝ, ∃ q : ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
                ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement ℝ
    (convexAleksandrovNullBadSetOnStatement_real_of_fullMeasure_scalarQuotientEstimate
      Ω f hgood)

/-- Restricted-measure null-bad-set theorem-boundary reduction from countably many real-line
scalar good sets. -/
theorem convexAleksandrovNullBadSetStatement_real_of_countable_scalarEstimate
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      ∃ G : ℕ → Set ℝ, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : ℝ⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : ℝ, ∃ q : ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhds 0,
                ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ ≤
                  ε * ‖z‖ ^ 2) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement ℝ
    (convexAleksandrovNullBadSetOnStatement_real_of_countable_scalarEstimate
      Ω f hgood)

/-- Restricted-measure null-bad-set theorem-boundary reduction from countably many real-line
scalar quotient good sets. -/
theorem convexAleksandrovNullBadSetStatement_real_of_countable_scalarQuotientEstimate
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      ∃ G : ℕ → Set ℝ, (∀ n : ℕ, volume (Ω \ G n) = 0) ∧
        ∀ ⦃x : ℝ⦄, x ∈ Ω → (∀ n : ℕ, x ∈ G n) →
          ∃ p : ℝ, ∃ q : ℝ,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
                ‖f (x + z) - f x - p * z - (1 / 2 : ℝ) * q * z ^ 2‖ /
                    ‖z‖ ^ 2 ≤ ε) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement ℝ
    (convexAleksandrovNullBadSetOnStatement_real_of_countable_scalarQuotientEstimate
      Ω f hgood)

/-- Restricted-measure null-bad-set theorem-boundary reduction from full measure of the named
real-line scalar estimate set. -/
theorem convexAleksandrovNullBadSetStatement_real_of_fullMeasure_scalarEstimateSet
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      volume (Ω \ realScalarQuadraticEstimateSet f) = 0) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement ℝ
    (convexAleksandrovNullBadSetOnStatement_real_of_fullMeasure_scalarEstimateSet
      Ω f hgood)

/-- Restricted-measure null-bad-set theorem-boundary reduction from full measure of the named
real-line scalar quotient-estimate set. -/
theorem convexAleksandrovNullBadSetStatement_real_of_fullMeasure_scalarQuotientEstimateSet
    (Ω : Set ℝ) (f : ℝ → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω f →
      volume (Ω \ realScalarQuadraticQuotientEstimateSet f) = 0) :
    ConvexAleksandrovNullBadSetStatement ℝ Ω f :=
  ConvexAleksandrovNullBadSetOnStatement.nullBadSetStatement ℝ
    (convexAleksandrovNullBadSetOnStatement_real_of_fullMeasure_scalarQuotientEstimateSet
      Ω f hgood)


end AleksandrovDifferentiability
