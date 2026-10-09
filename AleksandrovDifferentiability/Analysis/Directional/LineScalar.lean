module

public import AleksandrovDifferentiability.Analysis.Directional.EstimateDefs
public import AleksandrovDifferentiability.Analysis.LineRestriction.Basic
public import AleksandrovDifferentiability.Analysis.LineSecondOrder
public import AleksandrovDifferentiability.Analysis.QuadraticTrap.AmbientEstimate
public import AleksandrovDifferentiability.Analysis.QuadraticTrap.RealScalar

/-!
# Scalar estimates along affine lines

This file records zero-direction cases and transport wrappers for scalar quadratic estimates on
line restrictions.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every point is good for the zero-direction scalar estimate set. -/
theorem mem_directionalLineScalarEstimateSet_zero (u : E → ℝ) (x : E) :
    x ∈ directionalLineScalarEstimateSet (0 : E) u :=
  realScalarQuadraticEstimateAt_lineRestriction_zero_direction u x

/-- Every point is good for the zero-direction scalar quotient-estimate set. -/
theorem mem_directionalLineScalarQuotientEstimateSet_zero (u : E → ℝ) (x : E) :
    x ∈ directionalLineScalarQuotientEstimateSet (0 : E) u :=
  realScalarQuadraticQuotientEstimateAt_lineRestriction_zero_direction u x

@[simp]
theorem directionalLineScalarEstimateSet_zero (u : E → ℝ) :
    directionalLineScalarEstimateSet (0 : E) u = Set.univ := by
  ext x
  exact ⟨fun _ => trivial, fun _ => mem_directionalLineScalarEstimateSet_zero u x⟩

@[simp]
theorem directionalLineScalarQuotientEstimateSet_zero (u : E → ℝ) :
    directionalLineScalarQuotientEstimateSet (0 : E) u = Set.univ := by
  ext x
  exact ⟨fun _ => trivial, fun _ => mem_directionalLineScalarQuotientEstimateSet_zero u x⟩

/-- Nonzero scalar rescaling of a direction does not change the scalar directional-line good set. -/
theorem directionalLineScalarEstimateSet_smul_eq
    {v : E} {c : ℝ} (hc : c ≠ 0) (u : E → ℝ) :
    directionalLineScalarEstimateSet (c • v) u = directionalLineScalarEstimateSet v u := by
  ext x
  exact RealScalarQuadraticEstimateAt.lineRestriction_smul_iff (u := u) (x := x) (v := v) hc

/-- Quotient-estimate version of `directionalLineScalarEstimateSet_smul_eq`. -/
theorem directionalLineScalarQuotientEstimateSet_smul_eq
    {v : E} {c : ℝ} (hc : c ≠ 0) (u : E → ℝ) :
    directionalLineScalarQuotientEstimateSet (c • v) u =
      directionalLineScalarQuotientEstimateSet v u := by
  ext x
  exact
    RealScalarQuadraticQuotientEstimateAt.lineRestriction_smul_iff (u := u) (x := x) (v := v) hc

/-- The fixed-direction scalar estimate good set is contained in its punctured normalized
quotient version. -/
theorem directionalLineScalarEstimateSet_subset_directionalLineScalarQuotientEstimateSet
    {v : E} {u : E → ℝ} :
    directionalLineScalarEstimateSet v u ⊆ directionalLineScalarQuotientEstimateSet v u := by
  intro x hx
  exact hx.quadraticQuotientEstimateAt

/-- On `ℝ`, scalar quadratic estimate data at a point gives scalar estimate data on the
restriction to any real affine line through that point. -/
theorem RealScalarQuadraticEstimateAt.real_lineRestriction
    {f : ℝ → ℝ} {x ξ : ℝ} (h : RealScalarQuadraticEstimateAt f x) :
    RealScalarQuadraticEstimateAt
      (AleksandrovDifferentiability.lineRestriction f x ξ) 0 := by
  rcases h with ⟨p, q, hest⟩
  have hwith : RealScalarQuadraticEstimateWithDataAt f x p q := hest
  exact
    (RealScalarQuadraticEstimateWithDataAt.real_lineRestriction
      (ξ := ξ) hwith).realScalarQuadraticEstimateAt

/-- A scalar estimate for the unit real-line restriction through `x` is exactly a scalar estimate
at `x`. -/
theorem RealScalarQuadraticEstimateAt.of_real_lineRestriction_one
    {f : ℝ → ℝ} {x : ℝ}
    (h : RealScalarQuadraticEstimateAt
      (AleksandrovDifferentiability.lineRestriction f x 1) 0) :
    RealScalarQuadraticEstimateAt f x := by
  rcases h with ⟨p, q, hest⟩
  refine ⟨p, q, ?_⟩
  intro ε hε
  simpa [AleksandrovDifferentiability.lineRestriction] using hest ε hε

/-- Quotient-estimate version of `RealScalarQuadraticEstimateAt.real_lineRestriction`. -/
theorem RealScalarQuadraticQuotientEstimateAt.real_lineRestriction
    {f : ℝ → ℝ} {x ξ : ℝ} (h : RealScalarQuadraticQuotientEstimateAt f x) :
    RealScalarQuadraticQuotientEstimateAt
      (AleksandrovDifferentiability.lineRestriction f x ξ) 0 := by
  rcases h with ⟨p, q, hest⟩
  have hwith : RealScalarQuadraticQuotientEstimateWithDataAt f x p q := hest
  exact
    (RealScalarQuadraticQuotientEstimateWithDataAt.real_lineRestriction
      (ξ := ξ) hwith).realScalarQuadraticQuotientEstimateAt

/-- Punctured normalized quotient version of
`RealScalarQuadraticEstimateAt.of_real_lineRestriction_one`. -/
theorem RealScalarQuadraticQuotientEstimateAt.of_real_lineRestriction_one
    {f : ℝ → ℝ} {x : ℝ}
    (h : RealScalarQuadraticQuotientEstimateAt
      (AleksandrovDifferentiability.lineRestriction f x 1) 0) :
    RealScalarQuadraticQuotientEstimateAt f x := by
  rcases h with ⟨p, q, hest⟩
  refine ⟨p, q, ?_⟩
  intro ε hε
  simpa [AleksandrovDifferentiability.lineRestriction] using hest ε hε

/-- On the real line, scalar quadratic estimate data at a point supplies compatible finite
slice data for any finite family of real directions: every line slope is obtained from the same
ambient scalar first-order coefficient. -/
theorem RealScalarQuadraticEstimateAt.compatibleDirectionalSliceEstimateAt_real
    {ι : Type*} {D : Finset ι} {v : ι → ℝ} {f : ℝ → ℝ} {x : ℝ}
    (h : RealScalarQuadraticEstimateAt f x) :
    CompatibleDirectionalSliceEstimateAt D v f x := by
  rcases h with ⟨p, q, hest⟩
  have hwith : RealScalarQuadraticEstimateWithDataAt f x p q := hest
  refine ⟨p, (fun i => v i ^ 2 * q), (fun i j => (v i + v j) ^ 2 * q), ?_, ?_⟩
  · intro i _hi
    have hi := hwith.real_lineRestriction (ξ := v i)
    simpa [Real.inner_apply, mul_comm] using hi
  · intro i _hi j _hj
    have hij := hwith.real_lineRestriction (ξ := v i + v j)
    simpa [Real.inner_apply, mul_comm] using hij

/-- Punctured normalized quotient version of
`RealScalarQuadraticEstimateAt.compatibleDirectionalSliceEstimateAt_real`. -/
theorem RealScalarQuadraticQuotientEstimateAt.compatibleDirectionalSliceQuotientEstimateAt_real
    {ι : Type*} {D : Finset ι} {v : ι → ℝ} {f : ℝ → ℝ} {x : ℝ}
    (h : RealScalarQuadraticQuotientEstimateAt f x) :
    CompatibleDirectionalSliceQuotientEstimateAt D v f x := by
  rcases h with ⟨p, q, hest⟩
  have hwith : RealScalarQuadraticQuotientEstimateWithDataAt f x p q := hest
  refine ⟨p, (fun i => v i ^ 2 * q), (fun i j => (v i + v j) ^ 2 * q), ?_, ?_⟩
  · intro i _hi
    have hi := hwith.real_lineRestriction (ξ := v i)
    simpa [Real.inner_apply, mul_comm] using hi
  · intro i _hi j _hj
    have hij := hwith.real_lineRestriction (ξ := v i + v j)
    simpa [Real.inner_apply, mul_comm] using hij

/-- On the real line, the ordinary scalar-estimate good set is contained in every directional
line scalar-estimate good set. -/
theorem realScalarQuadraticEstimateSet_subset_directionalLineScalarEstimateSet
    (ξ : ℝ) (f : ℝ → ℝ) :
    realScalarQuadraticEstimateSet f ⊆ directionalLineScalarEstimateSet ξ f := by
  intro x hx
  exact hx.real_lineRestriction

/-- Quotient-estimate version of
`realScalarQuadraticEstimateSet_subset_directionalLineScalarEstimateSet`. -/
theorem realScalarQuadraticQuotientEstimateSet_subset_directionalLineScalarQuotientEstimateSet
    (ξ : ℝ) (f : ℝ → ℝ) :
    realScalarQuadraticQuotientEstimateSet f ⊆ directionalLineScalarQuotientEstimateSet ξ f := by
  intro x hx
  exact hx.real_lineRestriction

/-- Normalizing a nonzero direction by the inverse of its norm gives a unit direction. -/
lemma norm_inv_norm_smul_eq_one {w : E} (hw : w ≠ 0) :
    ‖‖w‖⁻¹ • w‖ = 1 := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  exact inv_mul_cancel₀ hn

end AleksandrovDifferentiability
