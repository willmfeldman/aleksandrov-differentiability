module

public import AleksandrovDifferentiability.Analysis.OneDimConvex
public import AleksandrovDifferentiability.Foundation.Subgradient
public import AleksandrovDifferentiability.Foundation.UpperContact
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Restrictions to affine lines

This file starts the bridge between ambient convex/subgradient statements and the
one-dimensional restrictions used in the Aleksandrov proof.
-/

@[expose] public section

namespace AleksandrovDifferentiability

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The one-dimensional restriction of `u` to the affine line `x + ℝ v`. -/
def lineRestriction (u : E → ℝ) (x v : E) : ℝ → ℝ :=
  fun t ↦ u (x + t • v)

/-- The set of line parameters whose corresponding points lie in `s`. -/
def lineDomain (s : Set E) (x v : E) : Set ℝ :=
  {t | x + t • v ∈ s}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The image of an open set under a linear isometry equivalence is open. This packages the
domain side of an orthonormal coordinate change. -/
theorem isOpen_image_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) {s : Set E} (hs : IsOpen s) :
    IsOpen (e '' s) := by
  rw [e.image_eq_preimage_symm]
  exact hs.preimage e.symm.continuous

/-- The image of a convex set under a linear isometry equivalence is convex. -/
theorem convex_image_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) {s : Set E} (hs : Convex ℝ s) :
    Convex ℝ (e '' s) :=
  hs.linear_image e.toLinearEquiv.toLinearMap

/-- Convexity of a function on a set is preserved by rebasing through a linear isometry
equivalence. -/
theorem ConvexOn.image_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) {s : Set E} {u : E → ℝ} (hu : ConvexOn ℝ s u) :
    ConvexOn ℝ (e '' s) (u ∘ e.symm) := by
  refine ⟨convex_image_linearIsometryEquiv e hu.1, ?_⟩
  intro y hy z hz a b ha hb hab
  rcases hy with ⟨x, hx, rfl⟩
  rcases hz with ⟨w, hw, rfl⟩
  have hpoint : e (a • x + b • w) = a • e x + b • e w := by
    simp only [map_add, map_smul]
  have hconv := hu.2 hx hw ha hb hab
  rw [← hpoint]
  simpa [Function.comp_def] using hconv

/-- The line domain of an open ambient set is open. -/
theorem isOpen_lineDomain {s : Set E} {x v : E} (hs : IsOpen s) :
    IsOpen (lineDomain s x v) := by
  have hcont : Continuous fun t : ℝ ↦ x + t • v := by
    fun_prop
  change IsOpen ((fun t : ℝ => x + t • v) ⁻¹' s)
  exact hs.preimage hcont

@[simp]
theorem lineRestriction_zero (u : E → ℝ) (x v : E) :
    lineRestriction u x v 0 = u x := by
  simp [lineRestriction]

theorem zero_mem_lineDomain {s : Set E} {x v : E} (hx : x ∈ s) :
    0 ∈ lineDomain s x v := by
  simpa [lineDomain]

/-- If the base point is interior to the ambient domain, then `0` is interior to the
line-restricted domain in every direction. -/
theorem zero_mem_interior_lineDomain {s : Set E} {x v : E} (hx : x ∈ interior s) :
    (0 : ℝ) ∈ interior (lineDomain s x v) := by
  rw [mem_interior_iff_mem_nhds]
  have hs : s ∈ nhds x := mem_interior_iff_mem_nhds.mp hx
  have hs0 : s ∈ nhds (x + (0 : ℝ) • v) := by
    simpa using hs
  have hcont : ContinuousAt (fun t : ℝ ↦ x + t • v) 0 :=
    continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  change ((fun t : ℝ => x + t • v) ⁻¹' s) ∈ nhds 0
  exact hcont.preimage_mem_nhds hs0

/-- If a point on the line lies in the interior of the ambient domain, then the corresponding
line parameter lies in the interior of the line domain. -/
theorem mem_interior_lineDomain_of_line_mem_interior
    {s : Set E} {x v : E} {t : ℝ} (ht : x + t • v ∈ interior s) :
    t ∈ interior (lineDomain s x v) := by
  rw [mem_interior_iff_mem_nhds]
  have hs : s ∈ nhds (x + t • v) := mem_interior_iff_mem_nhds.mp ht
  have hcont : ContinuousAt (fun r : ℝ ↦ x + r • v) t :=
    continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  change ((fun r : ℝ => x + r • v) ⁻¹' s) ∈ nhds t
  exact hcont.preimage_mem_nhds hs

/-- An ambient subgradient at the point with line parameter `t` restricts to a one-dimensional
subgradient at `t`. -/
theorem SubgradientOn.lineRestriction_subgradientOn_at
    {s : Set E} {u : E → ℝ} {x p v : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • v) p) :
    SubgradientOn (lineDomain s x v) (AleksandrovDifferentiability.lineRestriction u x v) t
      (inner ℝ p v) := by
  refine ⟨hp.mem, ?_⟩
  intro r hr
  have hsupport := hp.supporting_inequality (y := x + r • v) hr
  have hdiff : x + r • v - (x + t • v) = (r - t) • v := by
    calc
      x + r • v - (x + t • v) = r • v - t • v := by abel
      _ = (r - t) • v := by rw [sub_smul]
  rw [hdiff] at hsupport
  have hlin :
      inner ℝ p ((r - t) • v) = inner ℝ (inner ℝ p v) (r - t) := by
    simp [real_inner_smul_right]
  simpa [AleksandrovDifferentiability.lineRestriction, lineDomain, hlin] using hsupport

/-- An ambient upper quadratic contact with a specified slope restricts to an upper quadratic
contact on every affine line, with slope paired against the line direction and opening scaled by
the squared length of the direction vector. -/
theorem HasUpperContactWithSlopeOn.lineRestriction
    {s : Set E} {u : E → ℝ} {x p v : E} {a : ℝ}
    (h : HasUpperContactWithSlopeOn s u x p a) :
    HasUpperContactWithSlopeOn (lineDomain s x v) (lineRestriction u x v) 0
      (inner ℝ p v) (a * ‖v‖ ^ 2) := by
  refine ⟨zero_mem_lineDomain h.mem, ?_⟩
  intro t ht
  have hline := h.upper_inequality (y := x + t • v) ht
  have hquad :
      (a / 2) * ‖t • v‖ ^ 2 =
        ((a * ‖v‖ ^ 2) / 2) * ‖t - 0‖ ^ 2 := by
    simp only [norm_smul, Real.norm_eq_abs, sub_zero, mul_pow]
    rw [sq_abs]
    ring
  have hlin : inner ℝ p (t • v) = inner ℝ (inner ℝ p v) (t - 0) := by
    simp [real_inner_smul_right]
  simp only [lineRestriction_zero]
  change u (x + t • v) ≤
    u x + inner ℝ (inner ℝ p v) (t - 0) +
      ((a * ‖v‖ ^ 2) / 2) * ‖t - 0‖ ^ 2
  simpa [hlin, hquad] using hline

/-- Convexity restricts to every affine line. -/
theorem ConvexOn.lineRestriction
    {s : Set E} {u : E → ℝ} {x v : E} (hu : ConvexOn ℝ s u) :
    ConvexOn ℝ (lineDomain s x v) (lineRestriction u x v) := by
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x (x + v)
  have hg : (fun t : ℝ ↦ g t) = fun t : ℝ ↦ x + t • v := by
    funext t
    simp [g, AffineMap.lineMap_apply_module', add_comm]
  have h := hu.comp_affineMap g
  change ConvexOn ℝ ((fun t : ℝ => x + t • v) ⁻¹' s)
    (u ∘ fun t : ℝ => x + t • v)
  simpa only [hg] using h

/-- A differentiable convex function has its derivative as a subgradient, expressed with an
explicit inner-product representative of the Fréchet derivative.  The proof follows the
source-document convex route: restrict to the line segment from `x` to `y` and apply the
one-dimensional supporting-line statement. -/
theorem ConvexOn.subgradientOn_of_hasFDerivAt_of_forall_eq_inner
    {s : Set E} {u : E → ℝ} {x p : E} {ℓ : E →L[ℝ] ℝ}
    (hu : ConvexOn ℝ s u) (hx : x ∈ interior s)
    (hd : HasFDerivAt u ℓ x) (hℓ : ∀ v : E, ℓ v = inner ℝ p v) :
    SubgradientOn s u x p := by
  refine ⟨interior_subset hx, ?_⟩
  intro y hy
  let v : E := y - x
  have hderLine :
      HasDerivAt (AleksandrovDifferentiability.lineRestriction u x v) (ℓ v) 0 := by
    have hline : HasLineDerivAt ℝ u (ℓ v) x v := hd.hasLineDerivAt v
    change HasDerivAt (fun t : ℝ => u (x + t • v)) (ℓ v) 0
    simpa only [HasLineDerivAt] using hline
  have hsubLine :
      SubgradientOn (lineDomain s x v) (AleksandrovDifferentiability.lineRestriction u x v) 0
        (ℓ v) :=
    AleksandrovDifferentiability.ConvexOn.subgradientOn_of_hasDerivAt
      (S := lineDomain s x v)
      (f := AleksandrovDifferentiability.lineRestriction u x v) (x := 0)
      (p := ℓ v)
      (AleksandrovDifferentiability.ConvexOn.lineRestriction (x := x) (v := v) hu)
      (zero_mem_interior_lineDomain hx) hderLine
  have h1 : (1 : ℝ) ∈ lineDomain s x v := by
    dsimp [lineDomain, v]
    simpa [one_smul] using hy
  have hsupport := hsubLine.supporting_inequality (y := 1) h1
  have hℓv : ℓ v = inner ℝ p (y - x) := by
    simpa [v] using hℓ v
  simpa [AleksandrovDifferentiability.lineRestriction, v, hℓv, Real.inner_apply, one_smul]
    using hsupport

/-- For a convex affine-line restriction, the right derivative at an interior line parameter is
itself a one-dimensional subgradient. This is the one-dimensional half of the source-document
identity `d⁺/dt u(x + t z) = sup {p · z | p ∈ ∂u(x + t z)}`. -/
theorem ConvexOn.lineRestriction_rightDeriv_subgradientOn_at
    {s : Set E} {u : E → ℝ} {x v : E} {t : ℝ} (hu : ConvexOn ℝ s u)
    (ht : t ∈ interior (lineDomain s x v)) :
    SubgradientOn (lineDomain s x v) (AleksandrovDifferentiability.lineRestriction u x v) t
      (rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) t) := by
  have huLine : ConvexOn ℝ (lineDomain s x v)
      (AleksandrovDifferentiability.lineRestriction u x v) :=
    ConvexOn.lineRestriction (x := x) (v := v) hu
  exact
    AleksandrovDifferentiability.ConvexOn.subgradientOn_of_leftDeriv_le_of_le_rightDeriv
      (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
      (x := t) (p := rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) t)
      huLine ht
      (AleksandrovDifferentiability.ConvexOn.leftDeriv_le_rightDeriv
        (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
        (x := t) huLine ht)
      le_rfl

/-- Ambient-interior version of
`ConvexOn.lineRestriction_rightDeriv_subgradientOn_at`. -/
theorem ConvexOn.lineRestriction_rightDeriv_subgradientOn_at_of_line_mem_interior
    {s : Set E} {u : E → ℝ} {x v : E} {t : ℝ} (hu : ConvexOn ℝ s u)
    (ht : x + t • v ∈ interior s) :
    SubgradientOn (lineDomain s x v) (AleksandrovDifferentiability.lineRestriction u x v) t
      (rightDeriv (AleksandrovDifferentiability.lineRestriction u x v) t) :=
  AleksandrovDifferentiability.ConvexOn.lineRestriction_rightDeriv_subgradientOn_at
    (s := s) (u := u) (x := x) (v := v) (t := t) hu
    (mem_interior_lineDomain_of_line_mem_interior ht)

end AleksandrovDifferentiability
