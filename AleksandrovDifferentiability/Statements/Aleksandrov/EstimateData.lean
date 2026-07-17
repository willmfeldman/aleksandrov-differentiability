import AleksandrovDifferentiability.Analysis.Directional.Assembly
import AleksandrovDifferentiability.Analysis.EstimateAssembly
import AleksandrovDifferentiability.Statements.Aleksandrov.Equivalence

/-!
# Estimate-data reductions to the a.e. theorem
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Final-assembly reduction from local quadratic remainder estimates. This is closer to the
analytic estimates expected from the density/blow-up part of the Aleksandrov proof than the raw
expansion-data reduction. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_quadraticEstimateData
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Final-assembly reduction from punctured normalized quadratic remainder estimates. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_quadraticQuotientEstimateData
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_fullMeasure_quadraticQuotientEstimateData
    (μ := volume) hΩ.measurableSet hnull hG

/-- Final-assembly reduction from local quadratic remainder estimates whose Hessian candidate is
assembled from a finite matrix of directional coefficients. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_mixedDirectionalQuadraticEstimateData
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticEstimateData
    (μ := volume) hΩ.measurableSet D v hnull hG

/-- Final-assembly reduction from punctured normalized local estimates whose Hessian candidate is
assembled from a finite matrix of directional coefficients. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_mixedDirectionalQuadraticQuotientData
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticQuotientData
    (μ := volume) hΩ.measurableSet D v hnull hG

/-- Final-assembly reduction from local quadratic remainder estimates whose Hessian candidate is
assembled from polarized pure and pairwise-sum directional coefficients. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_polarizedMixedDirectionalQuadraticEstimateData
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuadraticEstimateData
    (μ := volume) hΩ.measurableSet D v hnull hG

/-- Final-assembly reduction from punctured normalized local estimates whose Hessian candidate is
assembled from polarized pure and pairwise-sum directional coefficients. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_polarizedMixedDirectionalQuadraticQuotientData
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact
    secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuadraticQuotientData
      (μ := volume) hΩ.measurableSet D v hnull hG

/-- Final-assembly reduction from local quadratic remainder estimates whose arbitrary symmetric
ambient Hessian candidate has prescribed finite-frame pure and off-diagonal pairwise-sum
coefficients. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_quadraticEstimateData_coefficients
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateData_coefficients
    (μ := volume) hΩ.measurableSet D v hframe hnull hG

/-- Punctured normalized quotient version of
`convexAleksandrovAEStatement_of_fullMeasure_quadraticEstimateData_coefficients`. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_quadraticQuotientData_coefficients
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
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  rcases hgood hΩ hu with ⟨G, hnull, hG⟩
  exact secondOrderDifferentiableAEOn_of_fullMeasure_quadraticQuotientData_coefficients
    (μ := volume) hΩ.measurableSet D v hframe hnull hG

/-- Final-assembly reduction from full measure of the named ambient quadratic estimate set. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_quadraticEstimateSet
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ quadraticEstimateSet u) = 0) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_fullMeasure_quadraticEstimateSet
    (μ := volume) hΩ.measurableSet (hgood hΩ hu)

/-- Final-assembly reduction from full measure of the named ambient quadratic quotient-estimate
set. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_quadraticQuotientEstimateSet
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ quadraticQuotientEstimateSet u) = 0) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_fullMeasure_quadraticQuotientEstimateSet
    (μ := volume) hΩ.measurableSet (hgood hΩ hu)

/-- Coordinate-model version of
`convexAleksandrovAEStatement_of_fullMeasure_quadraticEstimateSet`.  It is enough to prove full
measure of the transported ambient quadratic estimate set on `e '' Ω` for `u ∘ e.symm`. -/
theorem convexAleksandrovAEStatement_of_image_fullMeasure_quadraticEstimateSet
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume (e '' Ω \ quadraticEstimateSet (u ∘ e.symm)) = 0) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_fullMeasure_quadraticEstimateSet E Ω u fun hΩ hu =>
    measure_diff_quadraticEstimateSet_image_linearIsometryEquiv_eq_zero
      (e := e) (u := u)
      (hgood (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu))

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_image_fullMeasure_quadraticEstimateSet`. -/
theorem convexAleksandrovAEStatement_of_image_fullMeasure_quadraticQuotientEstimateSet
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (Ω : Set E) (u : E → ℝ)
    (hgood : IsOpen (e '' Ω) → ConvexOn ℝ (e '' Ω) (u ∘ e.symm) →
      volume (e '' Ω \ quadraticQuotientEstimateSet (u ∘ e.symm)) = 0) :
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_fullMeasure_quadraticQuotientEstimateSet E Ω u fun hΩ hu =>
    measure_diff_quadraticQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
      (e := e) (u := u)
      (hgood (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu))

/-- Final-assembly reduction from full measure of the named ambient mixed-directional quadratic
estimate set. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_mixedDirectionalQuadraticEstimateSet
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ mixedDirectionalQuadraticEstimateSet D v u) = 0) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticEstimateSet
    (μ := volume) hΩ.measurableSet D v (hgood hΩ hu)

/-- Final-assembly reduction from full measure of the named ambient mixed-directional quadratic
quotient-estimate set. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_mixedDirectionalQuadraticQuotientSet
    {ι : Type*} (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ mixedDirectionalQuadraticQuotientEstimateSet D v u) = 0) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_fullMeasure_mixedDirectionalQuadraticQuotientSet
    (μ := volume) hΩ.measurableSet D v (hgood hΩ hu)

/-- Final-assembly reduction from full measure of the named polarized mixed-directional
quadratic estimate set. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_polarizedMixedDirectionalQuadraticSet
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ polarizedMixedDirectionalQuadraticEstimateSet D v u) = 0) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuadraticSet
    (μ := volume) hΩ.measurableSet D v (hgood hΩ hu)

/-- Final-assembly reduction from full measure of the named polarized mixed-directional
quotient-estimate set. -/
theorem convexAleksandrovAEStatement_of_fullMeasure_polarizedMixedDirectionalQuotientSet
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (Ω : Set E) (u : E → ℝ) (v : ι → E)
    (hgood : IsOpen Ω → ConvexOn ℝ Ω u →
      volume (Ω \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u) = 0) :
    ConvexAleksandrovAEStatement E Ω u := by
  intro hΩ hu
  exact secondOrderDifferentiableAEOn_of_fullMeasure_polarizedMixedDirectionalQuotientSet
    (μ := volume) hΩ.measurableSet D v (hgood hΩ hu)

/-- Coordinate-model version of
`convexAleksandrovAEStatement_of_fullMeasure_mixedDirectionalQuadraticEstimateSet`.  It is
enough to prove full measure of the transported mixed-directional estimate set on `e '' Ω` for
`u ∘ e.symm`. -/
theorem convexAleksandrovAEStatement_of_image_fullMeasure_mixedDirectionalQuadraticEstimateSet
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
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_fullMeasure_mixedDirectionalQuadraticEstimateSet
    D E Ω u v fun hΩ hu =>
      measure_diff_mixedDirectionalQuadraticEstimateSet_image_linearIsometryEquiv_eq_zero
        (e := e) (D := D) (v := v) (u := u)
        (hgood (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu))

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_image_fullMeasure_mixedDirectionalQuadraticEstimateSet`. -/
theorem
    convexAleksandrovAEStatement_of_image_fullMeasure_mixedDirectionalQuadraticQuotientSet
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
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_fullMeasure_mixedDirectionalQuadraticQuotientSet
    D E Ω u v fun hΩ hu =>
      measure_diff_mixedDirectionalQuadraticQuotientSet_image_linearIsometryEquiv_eq_zero
        (e := e) (D := D) (v := v) (u := u)
        (hgood (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu))

/-- Coordinate-model version of
`convexAleksandrovAEStatement_of_fullMeasure_polarizedMixedDirectionalQuadraticSet`. -/
theorem
    convexAleksandrovAEStatement_of_image_fullMeasure_polarizedMixedDirectionalQuadraticSet
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
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_fullMeasure_polarizedMixedDirectionalQuadraticSet
    D E Ω u v fun hΩ hu =>
      measure_diff_polarizedMixedDirectionalQuadraticSet_image_linearIsometryEquiv_eq_zero
        (e := e) (D := D) (v := v) (u := u)
        (hgood (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu))

/-- Quotient-estimate version of
`convexAleksandrovAEStatement_of_image_fullMeasure_polarizedMixedDirectionalQuadraticSet`. -/
theorem
    convexAleksandrovAEStatement_of_image_fullMeasure_polarizedMixedDirectionalQuotientSet
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
    ConvexAleksandrovAEStatement E Ω u :=
  convexAleksandrovAEStatement_of_fullMeasure_polarizedMixedDirectionalQuotientSet
    D E Ω u v fun hΩ hu =>
      measure_diff_polarizedMixedDirectionalQuotientSet_image_linearIsometryEquiv_eq_zero
        (e := e) (D := D) (v := v) (u := u)
        (hgood (isOpen_image_linearIsometryEquiv e hΩ) (ConvexOn.image_linearIsometryEquiv e hu))

end AleksandrovDifferentiability
