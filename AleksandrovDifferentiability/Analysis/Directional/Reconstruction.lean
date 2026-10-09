module

public import AleksandrovDifferentiability.Analysis.Directional.EstimateDefs
public import AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Frame
public import AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Operators
public import AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Polarization
public import AleksandrovDifferentiability.Analysis.LineRestriction.Basic
public import AleksandrovDifferentiability.Analysis.LineSecondOrder
public import AleksandrovDifferentiability.Analysis.QuadraticTrap.AmbientEstimate
public import AleksandrovDifferentiability.Analysis.QuadraticTrap.Basic
public import AleksandrovDifferentiability.Analysis.QuadraticTrap.RealScalar
public import AleksandrovDifferentiability.Foundation.SecondOrder

/-!
# Reconstruction from directional quadratic data

This file converts mixed directional quadratic estimate data into the project-local
second-order differentiability predicate.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Mixed-directional quadratic estimate data implies second-order differentiability. -/
theorem MixedDirectionalQuadraticEstimateAt.secondOrderDifferentiableAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAt u x := by
  rcases h with ⟨p, a, hest⟩
  exact secondOrderDifferentiableAt_of_eventually_norm_affineRemainder_sub_quadratic_le_mul
    (isSymmetricOperator_mixedDirectionalQuadraticSum D v a) hest

/-- Mixed-directional quadratic quotient data implies second-order differentiability. -/
theorem MixedDirectionalQuadraticQuotientEstimateAt.secondOrderDifferentiableAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : MixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAt u x := by
  rcases h with ⟨p, a, hest⟩
  exact secondOrderDifferentiableAt_of_eventually_norm_affineRemainder_sub_quadratic_div_norm_sq_le
    (isSymmetricOperator_mixedDirectionalQuadraticSum D v a) hest

/-- Polarized coefficient estimate data is a special case of mixed-directional estimate data. -/
theorem PolarizedMixedDirectionalQuadraticEstimateAt.mixedDirectionalQuadraticEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    MixedDirectionalQuadraticEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hest⟩
  refine ⟨p, polarizedMixedCoefficient q r, ?_⟩
  simpa [polarizedMixedQuadraticSum] using hest

namespace PolarizedMixedDirectionalQuadraticQuotientEstimateAt

/-- Punctured normalized polarized coefficient estimate data is a special case of
mixed-directional quotient estimate data. -/
theorem mixedDirectionalQuadraticQuotientEstimateAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    MixedDirectionalQuadraticQuotientEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hest⟩
  refine ⟨p, polarizedMixedCoefficient q r, ?_⟩
  simpa [polarizedMixedQuadraticSum] using hest

end PolarizedMixedDirectionalQuadraticQuotientEstimateAt

/-- Polarized mixed-directional estimate data implies second-order differentiability. -/
theorem PolarizedMixedDirectionalQuadraticEstimateAt.secondOrderDifferentiableAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticEstimateAt D v u x) :
    SecondOrderDifferentiableAt u x :=
  h.mixedDirectionalQuadraticEstimateAt.secondOrderDifferentiableAt

/-- Polarized mixed-directional quotient estimate data implies second-order differentiability. -/
theorem PolarizedMixedDirectionalQuadraticQuotientEstimateAt.secondOrderDifferentiableAt
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x) :
    SecondOrderDifferentiableAt u x :=
  h.mixedDirectionalQuadraticQuotientEstimateAt.secondOrderDifferentiableAt

/-- If a symmetric ambient quadratic estimate has the prescribed pure and off-diagonal
pairwise-sum quadratic coefficients on a finite orthonormal spanning frame, then it is the
canonical polarized mixed-directional estimate.  The algebraic identification of the Hessian
candidate is handled by finite-frame off-diagonal uniqueness. -/
theorem polarizedMixedDirectionalQuadraticEstimateAt_of_quadraticEstimateData_coefficients
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn D v) {u : E → ℝ} {x p : E}
    {B : E →L[ℝ] E} (hB : IsSymmetricOperator B) {q : ι → ℝ} {r : ι → ι → ℝ}
    (hest : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0,
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ ≤
          ε * ‖z‖ ^ 2)
    (hr : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      inner ℝ (v i + v j) (B (v i + v j)) = r i j) :
    PolarizedMixedDirectionalQuadraticEstimateAt D v u x := by
  have hEq :=
    hv.eq_polarizedMixedQuadraticSum_of_quadraticForm_eq_on_frame_and_add_offDiagonal
      hB hr hpure hpair
  refine ⟨p, q, r, ?_⟩
  simpa [hEq] using hest

/-- Punctured normalized quotient version of
`polarizedMixedDirectionalQuadraticEstimateAt_of_quadraticEstimateData_coefficients`. -/
theorem
    polarizedMixedDirectionalQuadraticQuotientEstimateAt_of_quadraticQuotientData_coefficients
    {ι : Type*} [DecidableEq ι] {D : Finset ι} {v : ι → E}
    (hv : FiniteOrthonormalSpanningOn D v) {u : E → ℝ} {x p : E}
    {B : E →L[ℝ] E} (hB : IsSymmetricOperator B) {q : ι → ℝ} {r : ι → ι → ℝ}
    (hest : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
        ‖affineRemainder u x p (x + z) - (1 / 2 : ℝ) * inner ℝ z (B z)‖ /
            ‖z‖ ^ 2 ≤ ε)
    (hr : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → r j i = r i j)
    (hpure : ∀ ⦃i : ι⦄, i ∈ D → inner ℝ (v i) (B (v i)) = q i)
    (hpair : ∀ ⦃i : ι⦄, i ∈ D → ∀ ⦃j : ι⦄, j ∈ D → i ≠ j →
      inner ℝ (v i + v j) (B (v i + v j)) = r i j) :
    PolarizedMixedDirectionalQuadraticQuotientEstimateAt D v u x := by
  have hEq :=
    hv.eq_polarizedMixedQuadraticSum_of_quadraticForm_eq_on_frame_and_add_offDiagonal
      hB hr hpure hpair
  refine ⟨p, q, r, ?_⟩
  simpa [hEq] using hest

/-- Compatible finite slice data forgets to the existential finite slice target. -/
theorem CompatibleDirectionalSliceEstimateAt.directionalSliceEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : CompatibleDirectionalSliceEstimateAt D v u x) :
    DirectionalSliceEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hpure, hpair⟩
  exact
    ⟨fun i hi => (hpure hi).realScalarQuadraticEstimateAt,
      fun i hi j hj => (hpair hi hj).realScalarQuadraticEstimateAt⟩

/-- Symmetric compatible finite slice data forgets to compatible finite slice data. -/
theorem SymmetricCompatibleDirectionalSliceEstimateAt.compatibleDirectionalSliceEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : SymmetricCompatibleDirectionalSliceEstimateAt D v u x) :
    CompatibleDirectionalSliceEstimateAt D v u x := by
  rcases h with ⟨p, q, r, _hr, hpure, hpair⟩
  exact ⟨p, q, r, hpure, hpair⟩

/-- Compatible finite slice data can be represented with symmetric pairwise-sum coefficients by
averaging the two ordered pair coefficients. -/
theorem CompatibleDirectionalSliceEstimateAt.symmetricCompatibleDirectionalSliceEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : CompatibleDirectionalSliceEstimateAt D v u x) :
    SymmetricCompatibleDirectionalSliceEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hpure, hpair⟩
  let rsym : ι → ι → ℝ := fun i j => (r i j + r j i) / 2
  refine ⟨p, q, rsym, ?_, hpure, ?_⟩
  · intro i _hi j _hj
    simp [rsym, add_comm]
  · intro i hi j hj
    have hji :
        RealScalarQuadraticEstimateWithDataAt (lineRestriction u x (v i + v j)) 0
          (inner ℝ p (v i + v j)) (r j i) := by
      simpa [add_comm] using (hpair hj hi)
    exact (hpair hi hj).average hji

/-- Compatible finite quotient-slice data forgets to the existential finite quotient-slice
target. -/
theorem CompatibleDirectionalSliceQuotientEstimateAt.directionalSliceQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : CompatibleDirectionalSliceQuotientEstimateAt D v u x) :
    DirectionalSliceQuotientEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hpure, hpair⟩
  exact
    ⟨fun i hi => (hpure hi).realScalarQuadraticQuotientEstimateAt,
      fun i hi j hj => (hpair hi hj).realScalarQuadraticQuotientEstimateAt⟩

/-- Symmetric compatible finite quotient-slice data forgets to compatible finite quotient-slice
data. -/
theorem
    SymmetricCompatibleDirectionalSliceQuotientEstimateAt.compatibleQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x) :
    CompatibleDirectionalSliceQuotientEstimateAt D v u x := by
  rcases h with ⟨p, q, r, _hr, hpure, hpair⟩
  exact ⟨p, q, r, hpure, hpair⟩

/-- Compatible finite quotient-slice data can be represented with symmetric pairwise-sum
coefficients by averaging the two ordered pair coefficients. -/
theorem
    CompatibleDirectionalSliceQuotientEstimateAt.symmetricCompatibleQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : CompatibleDirectionalSliceQuotientEstimateAt D v u x) :
    SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hpure, hpair⟩
  let rsym : ι → ι → ℝ := fun i j => (r i j + r j i) / 2
  refine ⟨p, q, rsym, ?_, hpure, ?_⟩
  · intro i _hi j _hj
    simp [rsym, add_comm]
  · intro i hi j hj
    have hji :
        RealScalarQuadraticQuotientEstimateWithDataAt (lineRestriction u x (v i + v j)) 0
          (inner ℝ p (v i + v j)) (r j i) := by
      simpa [add_comm] using (hpair hj hi)
    exact (hpair hi hj).average hji

/-- Compatible finite slice data gives compatible finite quotient-slice data with the same
ambient slope and scalar quadratic coefficients. -/
theorem CompatibleDirectionalSliceEstimateAt.compatibleDirectionalSliceQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : CompatibleDirectionalSliceEstimateAt D v u x) :
    CompatibleDirectionalSliceQuotientEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hpure, hpair⟩
  refine ⟨p, q, r, ?_, ?_⟩
  · intro i hi
    exact (hpure hi).quadraticQuotientEstimateWithDataAt
  · intro i hi j hj
    exact (hpair hi hj).quadraticQuotientEstimateWithDataAt

/-- Symmetric compatible finite slice data gives symmetric compatible finite quotient-slice data
with the same ambient slope and scalar quadratic coefficients. -/
theorem
    SymmetricCompatibleDirectionalSliceEstimateAt.symmetricCompatibleQuotientEstimateAt
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} {x : E}
    (h : SymmetricCompatibleDirectionalSliceEstimateAt D v u x) :
    SymmetricCompatibleDirectionalSliceQuotientEstimateAt D v u x := by
  rcases h with ⟨p, q, r, hr, hpure, hpair⟩
  refine ⟨p, q, r, hr, ?_, ?_⟩
  · intro i hi
    exact (hpure hi).quadraticQuotientEstimateWithDataAt
  · intro i hi j hj
    exact (hpair hi hj).quadraticQuotientEstimateWithDataAt

/-- The compatible finite slice-estimate set is contained in the symmetric compatible finite
slice-estimate set. -/
theorem compatibleDirectionalSliceEstimateSet_subset_symmetricCompatibleDirectionalSliceEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    compatibleDirectionalSliceEstimateSet D v u ⊆
      symmetricCompatibleDirectionalSliceEstimateSet D v u := by
  intro x hx
  exact hx.symmetricCompatibleDirectionalSliceEstimateAt

/-- The compatible finite slice-estimate set is contained in the compatible finite quotient-slice
estimate set. -/
theorem compatibleDirectionalSliceEstimateSet_subset_compatibleDirectionalSliceQuotientEstimateSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    compatibleDirectionalSliceEstimateSet D v u ⊆
      compatibleDirectionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.compatibleDirectionalSliceQuotientEstimateAt

/-- The symmetric compatible finite slice-estimate set is contained in the symmetric compatible
finite quotient-slice estimate set. -/
theorem
    symmetricCompatibleDirectionalSliceEstimateSet_subset_symmetricCompatibleQuotientSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    symmetricCompatibleDirectionalSliceEstimateSet D v u ⊆
      symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.symmetricCompatibleQuotientEstimateAt

/-- The compatible finite quotient-slice estimate set is contained in the symmetric compatible
finite quotient-slice estimate set. -/
theorem
    compatibleDirectionalSliceQuotientSet_subset_symmetricCompatibleDirectionalSliceQuotientSet
    {ι : Type*} {D : Finset ι} {v : ι → E} {u : E → ℝ} :
    compatibleDirectionalSliceQuotientEstimateSet D v u ⊆
      symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u := by
  intro x hx
  exact hx.symmetricCompatibleQuotientEstimateAt

end AleksandrovDifferentiability
