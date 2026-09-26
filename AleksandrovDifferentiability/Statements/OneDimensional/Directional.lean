module

public import AleksandrovDifferentiability.Statements.OneDimensional.Core
public import AleksandrovDifferentiability.Statements.OneDimensional.RealLine
public import AleksandrovDifferentiability.Statements.Aleksandrov.NullBadSet.StandardBasis
public import AleksandrovDifferentiability.Statements.Aleksandrov.SliceReconstruction.Basis
public import AleksandrovDifferentiability.Statements.Aleksandrov.SliceReconstruction.Fubini

/-!
# One-dimensional directional assembly

Real-line directional and Fubini/reconstruction wrappers built from the one-dimensional scalar
estimate theorem.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

theorem directionalLineScalarUnitFubiniStatement_real_of_oneDimensionalScalarEstimate
    (h : ConvexOneDimensionalScalarEstimateStatement) (Ω : Set ℝ) (f : ℝ → ℝ) :
    DirectionalLineScalarUnitFubiniStatement ℝ Ω f := by
  intro hΩ hf ξ _hξ
  exact measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    (realScalarQuadraticEstimateSet_subset_directionalLineScalarEstimateSet ξ f)
    (h Ω f hΩ hf)

/-- The one-dimensional scalar-estimate theorem implies the real-line all-directions slicing
target. -/
theorem directionalLineScalarEstimateFubiniStatement_real_of_oneDimensionalScalarEstimate
    (h : ConvexOneDimensionalScalarEstimateStatement) (Ω : Set ℝ) (f : ℝ → ℝ) :
    DirectionalLineScalarEstimateFubiniStatement ℝ Ω f :=
  DirectionalLineScalarUnitFubiniStatement.fubiniStatement ℝ
    (directionalLineScalarUnitFubiniStatement_real_of_oneDimensionalScalarEstimate h Ω f)

/-- The one-dimensional quotient scalar-estimate theorem implies the real-line unit-direction
quotient slicing target. -/
theorem directionalLineScalarQuotientUnitFubiniStatement_real_of_oneDimensionalQuotientEstimate
    (h : ConvexOneDimensionalScalarQuotientEstimateStatement) (Ω : Set ℝ) (f : ℝ → ℝ) :
    DirectionalLineScalarQuotientUnitFubiniStatement ℝ Ω f := by
  intro hΩ hf ξ _hξ
  exact measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    (realScalarQuadraticQuotientEstimateSet_subset_directionalLineScalarQuotientEstimateSet ξ f)
    (h Ω f hΩ hf)

/-- The one-dimensional quotient scalar-estimate theorem implies the real-line all-directions
quotient slicing target. -/
theorem directionalLineScalarQuotientFubiniStatement_real_of_oneDimensionalScalarQuotientEstimate
    (h : ConvexOneDimensionalScalarQuotientEstimateStatement) (Ω : Set ℝ) (f : ℝ → ℝ) :
    DirectionalLineScalarQuotientFubiniStatement ℝ Ω f :=
  DirectionalLineScalarQuotientUnitFubiniStatement.fubiniStatement ℝ
    (directionalLineScalarQuotientUnitFubiniStatement_real_of_oneDimensionalQuotientEstimate
      h Ω f)

/-- Real-line unit-direction slicing target for convex functions. -/
theorem directionalLineScalarUnitFubiniStatement_real (Ω : Set ℝ) (f : ℝ → ℝ) :
    DirectionalLineScalarUnitFubiniStatement ℝ Ω f :=
  directionalLineScalarUnitFubiniStatement_real_of_oneDimensionalScalarEstimate
    convexOneDimensionalScalarEstimateStatement Ω f

/-- Real-line all-directions slicing target for convex functions. -/
theorem directionalLineScalarEstimateFubiniStatement_real (Ω : Set ℝ) (f : ℝ → ℝ) :
    DirectionalLineScalarEstimateFubiniStatement ℝ Ω f :=
  directionalLineScalarEstimateFubiniStatement_real_of_oneDimensionalScalarEstimate
    convexOneDimensionalScalarEstimateStatement Ω f

/-- Real-line unit-direction quotient slicing target for convex functions. -/
theorem directionalLineScalarQuotientUnitFubiniStatement_real (Ω : Set ℝ) (f : ℝ → ℝ) :
    DirectionalLineScalarQuotientUnitFubiniStatement ℝ Ω f :=
  directionalLineScalarQuotientUnitFubiniStatement_real_of_oneDimensionalQuotientEstimate
    convexOneDimensionalScalarQuotientEstimateStatement Ω f

/-- Real-line all-directions quotient slicing target for convex functions. -/
theorem directionalLineScalarQuotientFubiniStatement_real (Ω : Set ℝ) (f : ℝ → ℝ) :
    DirectionalLineScalarQuotientFubiniStatement ℝ Ω f :=
  directionalLineScalarQuotientFubiniStatement_real_of_oneDimensionalScalarQuotientEstimate
    convexOneDimensionalScalarQuotientEstimateStatement Ω f

/-- Real-line reconstruction from unit standard-basis slice data.  This is a genuine
one-dimensional reconstruction sanity check: the sole standard-basis direction is the unit
direction, so the line estimate is exactly the ambient real scalar estimate at the base point. -/
theorem polarizedDirectionalSliceReconstructionStatement_real_stdOrthonormalBasis
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    PolarizedDirectionalSliceReconstructionStatement
      Finset.univ ℝ Ω f (stdOrthonormalBasis ℝ ℝ) := by
  intro hframe _hΩ _hf x _hx hslice
  let i0 : Fin (Module.finrank ℝ ℝ) := ⟨0, by simp⟩
  have hi0 : i0 ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ ℝ))) := by
    simp
  let ξ : ℝ := stdOrthonormalBasis ℝ ℝ i0
  have hξ_ne : ξ ≠ 0 := by
    have hinner : inner ℝ ξ ξ = 1 := by
      simp [ξ]
    intro hξ_zero
    simp [hξ_zero] at hinner
  have hlineξ : RealScalarQuadraticEstimateAt (lineRestriction f x ξ) 0 := by
    simpa [ξ] using hslice.1 hi0
  have hline : RealScalarQuadraticEstimateAt (lineRestriction f x 1) 0 := by
    exact
      (RealScalarQuadraticEstimateAt.lineRestriction_smul_iff
        (u := f) (x := x) (v := (1 : ℝ)) (c := ξ) hξ_ne).mp
        (by simpa using hlineξ)
  rcases hline with ⟨p0, q0, hlineEst⟩
  have hest : RealScalarQuadraticEstimateWithDataAt f x p0 q0 := by
    intro ε hε
    simpa [lineRestriction] using hlineEst ε hε
  let B : ℝ →L[ℝ] ℝ := q0 • (1 : ℝ →L[ℝ] ℝ)
  let qCoeff : Fin (Module.finrank ℝ ℝ) → ℝ :=
    fun i => inner ℝ (stdOrthonormalBasis ℝ ℝ i) (B (stdOrthonormalBasis ℝ ℝ i))
  let rCoeff : Fin (Module.finrank ℝ ℝ) → Fin (Module.finrank ℝ ℝ) → ℝ :=
    fun i j =>
      inner ℝ (stdOrthonormalBasis ℝ ℝ i + stdOrthonormalBasis ℝ ℝ j)
        (B (stdOrthonormalBasis ℝ ℝ i + stdOrthonormalBasis ℝ ℝ j))
  have hB : IsSymmetricOperator B := by
    simpa [B] using isSymmetricOperator_real_smul_one q0
  have hambient : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖affineRemainder f x p0 (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
          ε * ‖z‖ ^ 2 := by
    intro ε hε
    filter_upwards [hest ε hε] with z hz
    have hnorm :
        ‖affineRemainder f x p0 (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ =
          ‖f (x + z) - f x - p0 * z - (1 / 2 : ℝ) * q0 * z ^ 2‖ := by
      congr 1
      simp [affineRemainder, B, mul_assoc, mul_left_comm, mul_comm, pow_two]
      ring
    rw [hnorm]
    exact hz
  refine
    polarizedMixedDirectionalQuadraticEstimateAt_of_quadraticEstimateData_coefficients
      (hv := hframe) (hB := hB) (q := qCoeff) (r := rCoeff) hambient ?_ ?_ ?_
  · intro i _hi j _hj
    simp [rCoeff, add_comm]
  · intro i _hi
    rfl
  · intro i _hi j _hj _hij
    rfl

/-- Punctured normalized quotient version of
`polarizedDirectionalSliceReconstructionStatement_real_stdOrthonormalBasis`. -/
theorem polarizedDirectionalSliceQuotientReconstructionStatement_real_stdOrthonormalBasis
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    PolarizedDirectionalSliceQuotientReconstructionStatement
      Finset.univ ℝ Ω f (stdOrthonormalBasis ℝ ℝ) := by
  intro hframe _hΩ _hf x _hx hslice
  let i0 : Fin (Module.finrank ℝ ℝ) := ⟨0, by simp⟩
  have hi0 : i0 ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ ℝ))) := by
    simp
  let ξ : ℝ := stdOrthonormalBasis ℝ ℝ i0
  have hξ_ne : ξ ≠ 0 := by
    have hinner : inner ℝ ξ ξ = 1 := by
      simp [ξ]
    intro hξ_zero
    simp [hξ_zero] at hinner
  have hlineξ : RealScalarQuadraticQuotientEstimateAt (lineRestriction f x ξ) 0 := by
    simpa [ξ] using hslice.1 hi0
  have hline : RealScalarQuadraticQuotientEstimateAt (lineRestriction f x 1) 0 := by
    exact
      (RealScalarQuadraticQuotientEstimateAt.lineRestriction_smul_iff
        (u := f) (x := x) (v := (1 : ℝ)) (c := ξ) hξ_ne).mp
        (by simpa using hlineξ)
  rcases hline with ⟨p0, q0, hlineEst⟩
  have hest : RealScalarQuadraticQuotientEstimateWithDataAt f x p0 q0 := by
    intro ε hε
    simpa [lineRestriction] using hlineEst ε hε
  let B : ℝ →L[ℝ] ℝ := q0 • (1 : ℝ →L[ℝ] ℝ)
  let qCoeff : Fin (Module.finrank ℝ ℝ) → ℝ :=
    fun i => inner ℝ (stdOrthonormalBasis ℝ ℝ i) (B (stdOrthonormalBasis ℝ ℝ i))
  let rCoeff : Fin (Module.finrank ℝ ℝ) → Fin (Module.finrank ℝ ℝ) → ℝ :=
    fun i j =>
      inner ℝ (stdOrthonormalBasis ℝ ℝ i + stdOrthonormalBasis ℝ ℝ j)
        (B (stdOrthonormalBasis ℝ ℝ i + stdOrthonormalBasis ℝ ℝ j))
  have hB : IsSymmetricOperator B := by
    simpa [B] using isSymmetricOperator_real_smul_one q0
  have hambient : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
        ‖affineRemainder f x p0 (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε := by
    intro ε hε
    filter_upwards [hest ε hε] with z hz
    have hnorm :
        ‖affineRemainder f x p0 (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ =
          ‖f (x + z) - f x - p0 * z - (1 / 2 : ℝ) * q0 * z ^ 2‖ := by
      congr 1
      simp [affineRemainder, B, mul_assoc, mul_left_comm, mul_comm, pow_two]
      ring
    rw [hnorm]
    exact hz
  refine
    polarizedMixedDirectionalQuadraticQuotientEstimateAt_of_quadraticQuotientData_coefficients
      (hv := hframe) (hB := hB) (q := qCoeff) (r := rCoeff) hambient ?_ ?_ ?_
  · intro i _hi j _hj
    simp [rCoeff, add_comm]
  · intro i _hi
    rfl
  · intro i _hi j _hj _hij
    rfl

/-- Real-line polarized reconstruction for any finite orthonormal spanning family.  A nonzero
selected direction exists by spanning; scalar slice data along that direction recovers a scalar
real-line quadratic estimate, which is then promoted to the ambient polarized model. -/
theorem polarizedDirectionalSliceReconstructionStatement_real
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) :
    PolarizedDirectionalSliceReconstructionStatement D ℝ Ω f v := by
  intro hframe _hΩ _hf x _hx hslice
  rcases hframe.exists_ne_zero_of_nonzero (z := (1 : ℝ)) one_ne_zero with ⟨i, hi, hvi⟩
  have hlinev : RealScalarQuadraticEstimateAt (lineRestriction f x (v i)) 0 :=
    hslice.1 hi
  have hline1 : RealScalarQuadraticEstimateAt (lineRestriction f x 1) 0 := by
    exact
      (RealScalarQuadraticEstimateAt.lineRestriction_smul_iff
        (u := f) (x := x) (v := (1 : ℝ)) (c := v i) hvi).mp
        (by simpa using hlinev)
  rcases RealScalarQuadraticEstimateAt.of_real_lineRestriction_one hline1 with ⟨p0, q0, hest⟩
  let B : ℝ →L[ℝ] ℝ := q0 • (1 : ℝ →L[ℝ] ℝ)
  let qCoeff : ι → ℝ := fun i => inner ℝ (v i) (B (v i))
  let rCoeff : ι → ι → ℝ := fun i j => inner ℝ (v i + v j) (B (v i + v j))
  have hB : IsSymmetricOperator B := by
    simpa [B] using isSymmetricOperator_real_smul_one q0
  have hambient : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖affineRemainder f x p0 (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
          ε * ‖z‖ ^ 2 := by
    intro ε hε
    filter_upwards [hest ε hε] with z hz
    have hnorm :
        ‖affineRemainder f x p0 (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ =
          ‖f (x + z) - f x - p0 * z - (1 / 2 : ℝ) * q0 * z ^ 2‖ := by
      congr 1
      simp [affineRemainder, B, mul_assoc, mul_left_comm, mul_comm, pow_two]
      ring
    rw [hnorm]
    exact hz
  refine
    polarizedMixedDirectionalQuadraticEstimateAt_of_quadraticEstimateData_coefficients
      (hv := hframe) (hB := hB) (q := qCoeff) (r := rCoeff) hambient ?_ ?_ ?_
  · intro i _hi j _hj
    simp [rCoeff, add_comm]
  · intro i _hi
    rfl
  · intro i _hi j _hj _hij
    rfl

/-- Punctured normalized quotient version of
`polarizedDirectionalSliceReconstructionStatement_real`. -/
theorem polarizedDirectionalSliceQuotientReconstructionStatement_real
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) :
    PolarizedDirectionalSliceQuotientReconstructionStatement D ℝ Ω f v := by
  intro hframe _hΩ _hf x _hx hslice
  rcases hframe.exists_ne_zero_of_nonzero (z := (1 : ℝ)) one_ne_zero with ⟨i, hi, hvi⟩
  have hlinev : RealScalarQuadraticQuotientEstimateAt (lineRestriction f x (v i)) 0 :=
    hslice.1 hi
  have hline1 : RealScalarQuadraticQuotientEstimateAt (lineRestriction f x 1) 0 := by
    exact
      (RealScalarQuadraticQuotientEstimateAt.lineRestriction_smul_iff
        (u := f) (x := x) (v := (1 : ℝ)) (c := v i) hvi).mp
        (by simpa using hlinev)
  rcases RealScalarQuadraticQuotientEstimateAt.of_real_lineRestriction_one hline1 with
    ⟨p0, q0, hest⟩
  let B : ℝ →L[ℝ] ℝ := q0 • (1 : ℝ →L[ℝ] ℝ)
  let qCoeff : ι → ℝ := fun i => inner ℝ (v i) (B (v i))
  let rCoeff : ι → ι → ℝ := fun i j => inner ℝ (v i + v j) (B (v i + v j))
  have hB : IsSymmetricOperator B := by
    simpa [B] using isSymmetricOperator_real_smul_one q0
  have hambient : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
        ‖affineRemainder f x p0 (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε := by
    intro ε hε
    filter_upwards [hest ε hε] with z hz
    have hnorm :
        ‖affineRemainder f x p0 (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ =
          ‖f (x + z) - f x - p0 * z - (1 / 2 : ℝ) * q0 * z ^ 2‖ := by
      congr 1
      simp [affineRemainder, B, mul_assoc, mul_left_comm, mul_comm, pow_two]
      ring
    rw [hnorm]
    exact hz
  refine
    polarizedMixedDirectionalQuadraticQuotientEstimateAt_of_quadraticQuotientData_coefficients
      (hv := hframe) (hB := hB) (q := qCoeff) (r := rCoeff) hambient ?_ ?_ ?_
  · intro i _hi j _hj
    simp [rCoeff, add_comm]
  · intro i _hi
    rfl
  · intro i _hi j _hj _hij
    rfl

/-- Real-line compatible reconstruction for any finite orthonormal spanning family.  A nonzero
selected direction exists by spanning; compatible slice data along that direction recovers a
scalar real-line quadratic estimate, which is then promoted to the ambient polarized model. -/
theorem compatiblePolarizedDirectionalSliceReconstructionStatement_real
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) :
    CompatiblePolarizedDirectionalSliceReconstructionStatement D ℝ Ω f v := by
  intro hframe _hΩ _hf x _hx hslice
  rcases hframe.exists_ne_zero_of_nonzero (z := (1 : ℝ)) one_ne_zero with ⟨i, hi, hvi⟩
  rcases hslice with ⟨_p, _q, _r, hpure, _hpair⟩
  have hlinev : RealScalarQuadraticEstimateAt (lineRestriction f x (v i)) 0 :=
    (hpure hi).realScalarQuadraticEstimateAt
  have hline1 : RealScalarQuadraticEstimateAt (lineRestriction f x 1) 0 := by
    exact
      (RealScalarQuadraticEstimateAt.lineRestriction_smul_iff
        (u := f) (x := x) (v := (1 : ℝ)) (c := v i) hvi).mp
        (by simpa using hlinev)
  rcases RealScalarQuadraticEstimateAt.of_real_lineRestriction_one hline1 with ⟨p0, q0, hest⟩
  let B : ℝ →L[ℝ] ℝ := q0 • (1 : ℝ →L[ℝ] ℝ)
  let qCoeff : ι → ℝ := fun i => inner ℝ (v i) (B (v i))
  let rCoeff : ι → ι → ℝ := fun i j => inner ℝ (v i + v j) (B (v i + v j))
  have hB : IsSymmetricOperator B := by
    simpa [B] using isSymmetricOperator_real_smul_one q0
  have hambient : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖affineRemainder f x p0 (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
          ε * ‖z‖ ^ 2 := by
    intro ε hε
    filter_upwards [hest ε hε] with z hz
    have hnorm :
        ‖affineRemainder f x p0 (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ =
          ‖f (x + z) - f x - p0 * z - (1 / 2 : ℝ) * q0 * z ^ 2‖ := by
      congr 1
      simp [affineRemainder, B, mul_assoc, mul_left_comm, mul_comm, pow_two]
      ring
    rw [hnorm]
    exact hz
  refine
    polarizedMixedDirectionalQuadraticEstimateAt_of_quadraticEstimateData_coefficients
      (hv := hframe) (hB := hB) (q := qCoeff) (r := rCoeff) hambient ?_ ?_ ?_
  · intro i _hi j _hj
    simp [rCoeff, add_comm]
  · intro i _hi
    rfl
  · intro i _hi j _hj _hij
    rfl

/-- Punctured normalized quotient version of
`compatiblePolarizedDirectionalSliceReconstructionStatement_real`. -/
theorem compatiblePolarizedDirectionalSliceQuotientReconstructionStatement_real
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) :
    CompatiblePolarizedDirectionalSliceQuotientReconstructionStatement D ℝ Ω f v := by
  intro hframe _hΩ _hf x _hx hslice
  rcases hframe.exists_ne_zero_of_nonzero (z := (1 : ℝ)) one_ne_zero with ⟨i, hi, hvi⟩
  rcases hslice with ⟨_p, _q, _r, hpure, _hpair⟩
  have hlinev : RealScalarQuadraticQuotientEstimateAt (lineRestriction f x (v i)) 0 :=
    (hpure hi).realScalarQuadraticQuotientEstimateAt
  have hline1 : RealScalarQuadraticQuotientEstimateAt (lineRestriction f x 1) 0 := by
    exact
      (RealScalarQuadraticQuotientEstimateAt.lineRestriction_smul_iff
        (u := f) (x := x) (v := (1 : ℝ)) (c := v i) hvi).mp
        (by simpa using hlinev)
  rcases RealScalarQuadraticQuotientEstimateAt.of_real_lineRestriction_one hline1 with
    ⟨p0, q0, hest⟩
  let B : ℝ →L[ℝ] ℝ := q0 • (1 : ℝ →L[ℝ] ℝ)
  let qCoeff : ι → ℝ := fun i => inner ℝ (v i) (B (v i))
  let rCoeff : ι → ι → ℝ := fun i j => inner ℝ (v i + v j) (B (v i + v j))
  have hB : IsSymmetricOperator B := by
    simpa [B] using isSymmetricOperator_real_smul_one q0
  have hambient : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : ℝ) {z : ℝ | z ≠ 0},
        ‖affineRemainder f x p0 (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε := by
    intro ε hε
    filter_upwards [hest ε hε] with z hz
    have hnorm :
        ‖affineRemainder f x p0 (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ =
          ‖f (x + z) - f x - p0 * z - (1 / 2 : ℝ) * q0 * z ^ 2‖ := by
      congr 1
      simp [affineRemainder, B, mul_assoc, mul_left_comm, mul_comm, pow_two]
      ring
    rw [hnorm]
    exact hz
  refine
    polarizedMixedDirectionalQuadraticQuotientEstimateAt_of_quadraticQuotientData_coefficients
      (hv := hframe) (hB := hB) (q := qCoeff) (r := rCoeff) hambient ?_ ?_ ?_
  · intro i _hi j _hj
    simp [rCoeff, add_comm]
  · intro i _hi
    rfl
  · intro i _hi j _hj _hij
    rfl

/-- The one-dimensional scalar-estimate theorem gives compatible finite-slice full measure for
any finite family of real directions. -/
theorem compatibleDirectionalSliceFullMeasureStatement_real_of_oneDimensionalScalarEstimate
    {ι : Type*} (D : Finset ι)
    (h : ConvexOneDimensionalScalarEstimateStatement) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) :
    CompatibleDirectionalSliceFullMeasureStatement D ℝ Ω f v := by
  intro hΩ hf
  refine measure_mono_null ?_ (h Ω f hΩ hf)
  intro x hx
  rcases hx with ⟨hxΩ, hxnot⟩
  refine ⟨hxΩ, ?_⟩
  intro hxScalar
  exact hxnot hxScalar.compatibleDirectionalSliceEstimateAt_real

/-- Punctured normalized quotient version of
`compatibleDirectionalSliceFullMeasureStatement_real_of_oneDimensionalScalarEstimate`. -/
theorem
    compatibleDirectionalSliceQuotientFullMeasureStatement_real_of_oneDimensionalQuotientEstimate
    {ι : Type*} (D : Finset ι)
    (h : ConvexOneDimensionalScalarQuotientEstimateStatement) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) :
    CompatibleDirectionalSliceQuotientFullMeasureStatement D ℝ Ω f v := by
  intro hΩ hf
  refine measure_mono_null ?_ (h Ω f hΩ hf)
  intro x hx
  rcases hx with ⟨hxΩ, hxnot⟩
  refine ⟨hxΩ, ?_⟩
  intro hxScalar
  exact hxnot hxScalar.compatibleDirectionalSliceQuotientEstimateAt_real

/-- Real-line compatible finite-slice full-measure theorem for convex functions. -/
theorem compatibleDirectionalSliceFullMeasureStatement_real
    {ι : Type*} (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ) (v : ι → ℝ) :
    CompatibleDirectionalSliceFullMeasureStatement D ℝ Ω f v :=
  compatibleDirectionalSliceFullMeasureStatement_real_of_oneDimensionalScalarEstimate
    D convexOneDimensionalScalarEstimateStatement Ω f v

/-- Real-line compatible quotient finite-slice full-measure theorem for convex functions. -/
theorem compatibleDirectionalSliceQuotientFullMeasureStatement_real
    {ι : Type*} (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ) (v : ι → ℝ) :
    CompatibleDirectionalSliceQuotientFullMeasureStatement D ℝ Ω f v :=
  compatibleDirectionalSliceQuotientFullMeasureStatement_real_of_oneDimensionalQuotientEstimate
    D convexOneDimensionalScalarQuotientEstimateStatement Ω f v

/-- Real-line symmetric-compatible finite-slice full-measure theorem for convex functions. -/
theorem symmetricCompatibleDirectionalSliceFullMeasureStatement_real
    {ι : Type*} (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ) (v : ι → ℝ) :
    SymmetricCompatibleDirectionalSliceFullMeasureStatement D ℝ Ω f v :=
  CompatibleDirectionalSliceFullMeasureStatement.symmetric D ℝ
    (compatibleDirectionalSliceFullMeasureStatement_real D Ω f v)

/-- Real-line symmetric-compatible quotient finite-slice full-measure theorem for convex
functions. -/
theorem symmetricCompatibleDirectionalSliceQuotientFullMeasureStatement_real
    {ι : Type*} (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ) (v : ι → ℝ) :
    SymmetricCompatibleDirectionalSliceQuotientFullMeasureStatement D ℝ Ω f v :=
  CompatibleDirectionalSliceQuotientFullMeasureStatement.symmetric D ℝ
    (compatibleDirectionalSliceQuotientFullMeasureStatement_real D Ω f v)

/-- Real-line Aleksandrov a.e. theorem through the standard-basis compatible full-measure route. -/
theorem convexAleksandrovAEStatement_real_stdBasis_compatibleFullMeasure
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_stdOrthonormalBasis_compatibleFullMeasure ℝ Ω f
    (compatibleDirectionalSliceFullMeasureStatement_real Finset.univ Ω f
      (stdOrthonormalBasis ℝ ℝ))
    (polarizedSliceRecon_to_compatible
      (polarizedDirectionalSliceReconstructionStatement_real_stdOrthonormalBasis Ω f))

/-- Real-line Aleksandrov a.e. theorem through the standard-basis compatible quotient
full-measure route. -/
theorem convexAleksandrovAEStatement_real_stdBasis_compatibleQuotientFullMeasure
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_stdOrthonormalBasis_compatibleQuotientFullMeasure ℝ Ω f
    (compatibleDirectionalSliceQuotientFullMeasureStatement_real Finset.univ Ω f
      (stdOrthonormalBasis ℝ ℝ))
    (polarizedSliceQuotientRecon_to_compatible
      (polarizedDirectionalSliceQuotientReconstructionStatement_real_stdOrthonormalBasis Ω f))

/-- Mixed-strength real-line Aleksandrov a.e. theorem through compatible full measure and
quotient reconstruction. -/
theorem convexAleksandrovAEStatement_real_stdBasis_compatible_quotientRecon
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_stdOrthonormalBasis_compatibleFullMeasure_quotientRecon ℝ Ω f
    (compatibleDirectionalSliceFullMeasureStatement_real Finset.univ Ω f
      (stdOrthonormalBasis ℝ ℝ))
    (polarizedSliceQuotientRecon_to_compatible
      (polarizedDirectionalSliceQuotientReconstructionStatement_real_stdOrthonormalBasis Ω f))

/-- Null-bad-set real-line theorem through the standard-basis compatible full-measure route. -/
theorem convexAleksandrovNullBadSetOnStatement_real_stdBasis_compatibleFullMeasure
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_compatibleFullMeasure ℝ Ω f
    (compatibleDirectionalSliceFullMeasureStatement_real Finset.univ Ω f
      (stdOrthonormalBasis ℝ ℝ))
    (polarizedSliceRecon_to_compatible
      (polarizedDirectionalSliceReconstructionStatement_real_stdOrthonormalBasis Ω f))

/-- Quotient null-bad-set real-line theorem through the standard-basis compatible
full-measure route. -/
theorem convexAleksandrovNullBadSetOnStatement_real_stdBasis_compatibleQuotient
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_compatibleQuotientFullMeasure
    ℝ Ω f
    (compatibleDirectionalSliceQuotientFullMeasureStatement_real Finset.univ Ω f
      (stdOrthonormalBasis ℝ ℝ))
    (polarizedSliceQuotientRecon_to_compatible
      (polarizedDirectionalSliceQuotientReconstructionStatement_real_stdOrthonormalBasis Ω f))

/-- Mixed-strength null-bad-set real-line theorem through compatible full measure and quotient
reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_real_stdBasis_compatible_quotientRecon
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_compatibleQuotientRecon ℝ Ω f
    (compatibleDirectionalSliceFullMeasureStatement_real Finset.univ Ω f
      (stdOrthonormalBasis ℝ ℝ))
    (polarizedSliceQuotientRecon_to_compatible
      (polarizedDirectionalSliceQuotientReconstructionStatement_real_stdOrthonormalBasis Ω f))

/-- Real-line Aleksandrov a.e. theorem through compatible full measure on an arbitrary finite
orthonormal real frame. -/
theorem convexAleksandrovAEStatement_real_finiteFrame_compatibleFullMeasure
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_compatibleFullMeasure_and_reconstruction
    D ℝ Ω f v hframe
    (compatibleDirectionalSliceFullMeasureStatement_real D Ω f v)
    (compatiblePolarizedDirectionalSliceReconstructionStatement_real D Ω f v)

/-- Quotient compatible full-measure real-line Aleksandrov a.e. theorem through an arbitrary
finite orthonormal real frame. -/
theorem convexAleksandrovAEStatement_real_finiteFrame_compatibleQuotientFullMeasure
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_compatibleQuotientFullMeasure_and_reconstruction
    D ℝ Ω f v hframe
    (compatibleDirectionalSliceQuotientFullMeasureStatement_real D Ω f v)
    (compatiblePolarizedDirectionalSliceQuotientReconstructionStatement_real D Ω f v)

/-- Mixed-strength compatible real-line Aleksandrov a.e. theorem through an arbitrary finite
orthonormal real frame. -/
theorem convexAleksandrovAEStatement_real_finiteFrame_compatible_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_compatibleFullMeasure_and_quotientReconstruction
    D ℝ Ω f v hframe
    (compatibleDirectionalSliceFullMeasureStatement_real D Ω f v)
    (compatiblePolarizedDirectionalSliceQuotientReconstructionStatement_real D Ω f v)

/-- Null-bad-set real-line theorem through compatible full measure on an arbitrary finite
orthonormal real frame. -/
theorem convexAleksandrovNullBadSetOnStatement_real_finiteFrame_compatibleFullMeasure
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_reconstruction
    D ℝ Ω f v hframe
    (compatibleDirectionalSliceFullMeasureStatement_real D Ω f v)
    (compatiblePolarizedDirectionalSliceReconstructionStatement_real D Ω f v)

/-- Quotient compatible full-measure null-bad-set real-line theorem through an arbitrary finite
orthonormal real frame. -/
theorem convexAleksandrovNullBadSetOnStatement_real_finiteFrame_compatibleQuotientFullMeasure
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_compatibleQuotientFullMeasure_and_reconstruction
    D ℝ Ω f v hframe
    (compatibleDirectionalSliceQuotientFullMeasureStatement_real D Ω f v)
    (compatiblePolarizedDirectionalSliceQuotientReconstructionStatement_real D Ω f v)

/-- Mixed-strength compatible null-bad-set real-line theorem through an arbitrary finite
orthonormal real frame. -/
theorem convexAleksandrovNullBadSetOnStatement_real_finiteFrame_compatible_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_compatibleFullMeasure_and_quotientReconstruction
    D ℝ Ω f v hframe
    (compatibleDirectionalSliceFullMeasureStatement_real D Ω f v)
    (compatiblePolarizedDirectionalSliceQuotientReconstructionStatement_real D Ω f v)

/-- Real-line Aleksandrov a.e. theorem through the standard-basis symmetric-compatible
full-measure route. -/
theorem convexAleksandrovAEStatement_real_stdBasis_symmetricFullMeasure
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_stdOrthonormalBasis_symmetricFullMeasure ℝ Ω f
    (symmetricCompatibleDirectionalSliceFullMeasureStatement_real Finset.univ Ω f
      (stdOrthonormalBasis ℝ ℝ))
    (compatibleSliceRecon_to_symmetric
      (polarizedSliceRecon_to_compatible
        (polarizedDirectionalSliceReconstructionStatement_real_stdOrthonormalBasis Ω f)))

/-- Real-line Aleksandrov a.e. theorem through the standard-basis symmetric-compatible quotient
full-measure route. -/
theorem convexAleksandrovAEStatement_real_stdBasis_symmetricQuotientFullMeasure
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_stdOrthonormalBasis_symmetricQuotientFullMeasure ℝ Ω f
    (symmetricCompatibleDirectionalSliceQuotientFullMeasureStatement_real Finset.univ Ω f
      (stdOrthonormalBasis ℝ ℝ))
    (compatibleSliceQuotientRecon_to_symmetric
      (polarizedSliceQuotientRecon_to_compatible
        (polarizedDirectionalSliceQuotientReconstructionStatement_real_stdOrthonormalBasis Ω f)))

/-- Mixed-strength real-line Aleksandrov a.e. theorem through symmetric-compatible full measure
and quotient reconstruction. -/
theorem convexAleksandrovAEStatement_real_stdBasis_symmetric_quotientRecon
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_stdOrthonormalBasis_symmetricQuotientRecon ℝ Ω f
    (symmetricCompatibleDirectionalSliceFullMeasureStatement_real Finset.univ Ω f
      (stdOrthonormalBasis ℝ ℝ))
    (compatibleSliceQuotientRecon_to_symmetric
      (polarizedSliceQuotientRecon_to_compatible
        (polarizedDirectionalSliceQuotientReconstructionStatement_real_stdOrthonormalBasis Ω f)))

/-- Null-bad-set real-line theorem through the standard-basis symmetric-compatible
full-measure route. -/
theorem convexAleksandrovNullBadSetOnStatement_real_stdBasis_symmetricFullMeasure
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_symmetricFullMeasure ℝ Ω f
    (symmetricCompatibleDirectionalSliceFullMeasureStatement_real Finset.univ Ω f
      (stdOrthonormalBasis ℝ ℝ))
    (compatibleSliceRecon_to_symmetric
      (polarizedSliceRecon_to_compatible
        (polarizedDirectionalSliceReconstructionStatement_real_stdOrthonormalBasis Ω f)))

/-- Quotient null-bad-set real-line theorem through the standard-basis symmetric-compatible
full-measure route. -/
theorem convexAleksandrovNullBadSetOnStatement_real_stdBasis_symmetricQuotient
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_symmetricQuotientFullMeasure
    ℝ Ω f
    (symmetricCompatibleDirectionalSliceQuotientFullMeasureStatement_real Finset.univ Ω f
      (stdOrthonormalBasis ℝ ℝ))
    (compatibleSliceQuotientRecon_to_symmetric
      (polarizedSliceQuotientRecon_to_compatible
        (polarizedDirectionalSliceQuotientReconstructionStatement_real_stdOrthonormalBasis Ω f)))

/-- Mixed-strength null-bad-set real-line theorem through symmetric-compatible full measure and
quotient reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_real_stdBasis_symmetric_quotientRecon
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_symmetricQuotientRecon ℝ Ω f
    (symmetricCompatibleDirectionalSliceFullMeasureStatement_real Finset.univ Ω f
      (stdOrthonormalBasis ℝ ℝ))
    (compatibleSliceQuotientRecon_to_symmetric
      (polarizedSliceQuotientRecon_to_compatible
        (polarizedDirectionalSliceQuotientReconstructionStatement_real_stdOrthonormalBasis Ω f)))

/-- Real-line Aleksandrov a.e. theorem through symmetric-compatible full measure on an arbitrary
finite orthonormal real frame. -/
theorem convexAleksandrovAEStatement_real_finiteFrame_symmetricFullMeasure
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_symmetricCompatibleFullMeasure_reconstruction
    D ℝ Ω f v hframe
    (symmetricCompatibleDirectionalSliceFullMeasureStatement_real D Ω f v)
    (compatibleSliceRecon_to_symmetric
      (compatiblePolarizedDirectionalSliceReconstructionStatement_real D Ω f v))

/-- Quotient symmetric-compatible real-line Aleksandrov a.e. theorem through an arbitrary finite
orthonormal real frame. -/
theorem convexAleksandrovAEStatement_real_finiteFrame_symmetricQuotientFullMeasure
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_symmetricCompatibleQuotientFullMeasure_quotientRecon
    D ℝ Ω f v hframe
    (symmetricCompatibleDirectionalSliceQuotientFullMeasureStatement_real D Ω f v)
    (compatibleSliceQuotientRecon_to_symmetric
      (compatiblePolarizedDirectionalSliceQuotientReconstructionStatement_real D Ω f v))

/-- Mixed-strength symmetric-compatible real-line Aleksandrov a.e. theorem through an arbitrary
finite orthonormal real frame. -/
theorem convexAleksandrovAEStatement_real_finiteFrame_symmetric_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_symmetricCompatibleFullMeasure_quotientRecon
    D ℝ Ω f v hframe
    (symmetricCompatibleDirectionalSliceFullMeasureStatement_real D Ω f v)
    (compatibleSliceQuotientRecon_to_symmetric
      (compatiblePolarizedDirectionalSliceQuotientReconstructionStatement_real D Ω f v))

/-- Null-bad-set real-line theorem through symmetric-compatible full measure on an arbitrary
finite orthonormal real frame. -/
theorem convexAleksandrovNullBadSetOnStatement_real_finiteFrame_symmetricFullMeasure
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_symmetricCompatibleFullMeasure_reconstruction
    D ℝ Ω f v hframe
    (symmetricCompatibleDirectionalSliceFullMeasureStatement_real D Ω f v)
    (compatibleSliceRecon_to_symmetric
      (compatiblePolarizedDirectionalSliceReconstructionStatement_real D Ω f v))

/-- Quotient symmetric-compatible null-bad-set real-line theorem through an arbitrary finite
orthonormal real frame. -/
theorem convexAleksandrovNullBadSetOnStatement_real_finiteFrame_symmetricQuotientFullMeasure
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_symmetricCompatibleQuotientFullMeasure_quotientRecon
    D ℝ Ω f v hframe
    (symmetricCompatibleDirectionalSliceQuotientFullMeasureStatement_real D Ω f v)
    (compatibleSliceQuotientRecon_to_symmetric
      (compatiblePolarizedDirectionalSliceQuotientReconstructionStatement_real D Ω f v))

/-- Mixed-strength symmetric-compatible null-bad-set real-line theorem through an arbitrary finite
orthonormal real frame. -/
theorem convexAleksandrovNullBadSetOnStatement_real_finiteFrame_symmetric_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_symmetricCompatibleFullMeasure_quotientRecon
    D ℝ Ω f v hframe
    (symmetricCompatibleDirectionalSliceFullMeasureStatement_real D Ω f v)
    (compatibleSliceQuotientRecon_to_symmetric
      (compatiblePolarizedDirectionalSliceQuotientReconstructionStatement_real D Ω f v))

/-- Real-line Aleksandrov a.e. theorem through the general standard-basis Fubini plus
polarized-reconstruction theorem boundary.  This validates that the final finite-dimensional
interface specializes correctly in dimension one. -/
theorem convexAleksandrovAEStatement_real_of_stdOrthonormalBasis_fubini_reconstruction
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_stdOrthonormalBasis_fubini_and_reconstruction ℝ Ω f
    (directionalLineScalarEstimateFubiniStatement_real Ω f)
    (polarizedDirectionalSliceReconstructionStatement_real_stdOrthonormalBasis Ω f)

/-- Quotient-estimate real-line Aleksandrov a.e. theorem through the general standard-basis
Fubini plus polarized-reconstruction theorem boundary. -/
theorem convexAleksandrovAEStatement_real_of_stdOrthonormalBasis_quotient_fubini_reconstruction
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_stdOrthonormalBasis_quotient_fubini_and_reconstruction ℝ Ω f
    (directionalLineScalarQuotientFubiniStatement_real Ω f)
    (polarizedDirectionalSliceQuotientReconstructionStatement_real_stdOrthonormalBasis Ω f)

/-- Mixed-strength real-line Aleksandrov a.e. theorem through the general standard-basis
interface: non-quotient Fubini data can be paired with quotient reconstruction. -/
theorem convexAleksandrovAEStatement_real_of_stdOrthonormalBasis_fubini_quotient_reconstruction
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_stdOrthonormalBasis_fubini_and_quotient_reconstruction ℝ Ω f
    (directionalLineScalarEstimateFubiniStatement_real Ω f)
    (polarizedDirectionalSliceQuotientReconstructionStatement_real_stdOrthonormalBasis Ω f)

/-- Null-bad-set version of
`convexAleksandrovAEStatement_real_of_stdOrthonormalBasis_fubini_reconstruction`. -/
theorem convexAleksandrovNullBadSetOnStatement_real_of_stdOrthonormalBasis_fubini_reconstruction
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_fubini_and_reconstruction ℝ Ω f
    (directionalLineScalarEstimateFubiniStatement_real Ω f)
    (polarizedDirectionalSliceReconstructionStatement_real_stdOrthonormalBasis Ω f)

/-- Quotient-estimate null-bad-set real-line theorem through the general standard-basis
Fubini plus polarized-reconstruction theorem boundary. -/
theorem
    convexAleksandrovNullBadSetOnStatement_real_stdBasis_quotientFubini_reconstruction
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_quotient_fubini_and_reconstruction
    ℝ Ω f
    (directionalLineScalarQuotientFubiniStatement_real Ω f)
    (polarizedDirectionalSliceQuotientReconstructionStatement_real_stdOrthonormalBasis Ω f)

/-- Mixed-strength null-bad-set real-line theorem through the general standard-basis interface:
non-quotient Fubini data can be paired with quotient reconstruction. -/
theorem
    convexAleksandrovNullBadSetOnStatement_real_stdBasis_fubini_quotientReconstruction
    (Ω : Set ℝ) (f : ℝ → ℝ) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_stdOrthonormalBasis_fubini_and_quotient_reconstruction
    ℝ Ω f
    (directionalLineScalarEstimateFubiniStatement_real Ω f)
    (polarizedDirectionalSliceQuotientReconstructionStatement_real_stdOrthonormalBasis Ω f)

/-- Real-line Aleksandrov a.e. theorem through an arbitrary finite orthonormal real frame,
ordinary directional-line Fubini, and polarized reconstruction. -/
theorem convexAleksandrovAEStatement_real_finiteFrame_fubini_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_fubini_and_polarized_reconstruction D ℝ Ω f v hframe
    (directionalLineScalarEstimateFubiniStatement_real Ω f)
    (polarizedDirectionalSliceReconstructionStatement_real D Ω f v)

/-- Quotient-estimate real-line Aleksandrov a.e. theorem through an arbitrary finite
orthonormal real frame. -/
theorem convexAleksandrovAEStatement_real_finiteFrame_quotientFubini_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_quotient_fubini_and_polarized_reconstruction
    D ℝ Ω f v hframe
    (directionalLineScalarQuotientFubiniStatement_real Ω f)
    (polarizedDirectionalSliceQuotientReconstructionStatement_real D Ω f v)

/-- Mixed-strength real-line Aleksandrov a.e. theorem through an arbitrary finite orthonormal
real frame: ordinary Fubini data is paired with quotient polarized reconstruction. -/
theorem convexAleksandrovAEStatement_real_finiteFrame_fubini_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovAEStatement ℝ Ω f :=
  convexAleksandrovAEStatement_of_fubini_and_quotient_polarized_reconstruction
    D ℝ Ω f v hframe
    (directionalLineScalarEstimateFubiniStatement_real Ω f)
    (polarizedDirectionalSliceQuotientReconstructionStatement_real D Ω f v)

/-- Null-bad-set real-line theorem through an arbitrary finite orthonormal real frame,
ordinary directional-line Fubini, and polarized reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_real_finiteFrame_fubini_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_fubini_and_polarized_reconstruction
    D ℝ Ω f v hframe
    (directionalLineScalarEstimateFubiniStatement_real Ω f)
    (polarizedDirectionalSliceReconstructionStatement_real D Ω f v)

/-- Quotient-estimate null-bad-set real-line theorem through an arbitrary finite orthonormal
real frame. -/
theorem convexAleksandrovNullBadSetOnStatement_real_finiteFrame_quotientFubini_reconstruction
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_quotient_fubini_and_polarized_reconstruction
    D ℝ Ω f v hframe
    (directionalLineScalarQuotientFubiniStatement_real Ω f)
    (polarizedDirectionalSliceQuotientReconstructionStatement_real D Ω f v)

/-- Mixed-strength null-bad-set real-line theorem through an arbitrary finite orthonormal real
frame: ordinary Fubini data is paired with quotient polarized reconstruction. -/
theorem convexAleksandrovNullBadSetOnStatement_real_finiteFrame_fubini_quotientRecon
    {ι : Type*} [DecidableEq ι] (D : Finset ι) (Ω : Set ℝ) (f : ℝ → ℝ)
    (v : ι → ℝ) (hframe : FiniteOrthonormalSpanningOn D v) :
    ConvexAleksandrovNullBadSetOnStatement ℝ Ω f :=
  convexAleksandrovNullBadSetOnStatement_of_fubini_and_quotient_reconstruction
    D ℝ Ω f v hframe
    (directionalLineScalarEstimateFubiniStatement_real Ω f)
    (polarizedDirectionalSliceQuotientReconstructionStatement_real D Ω f v)

end AleksandrovDifferentiability
