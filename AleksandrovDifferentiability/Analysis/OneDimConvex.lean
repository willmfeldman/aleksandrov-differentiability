module

public import AleksandrovDifferentiability.Foundation.Subgradient
public import AleksandrovDifferentiability.Foundation.UpperContact
public import Mathlib.Analysis.Calculus.Monotone
public import Mathlib.Analysis.Convex.Deriv

/-!
# One-dimensional convex analysis

This file gives project-local names for the one-dimensional slope and one-sided derivative facts
used at the start of the convex Aleksandrov proof route.
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter Set
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- The right derivative of a real function at `x`, represented by Mathlib's derivative within
the open ray to the right of `x`. -/
def rightDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  derivWithin f (Ioi x) x

/-- The left derivative of a real function at `x`, represented by Mathlib's derivative within
the open ray to the left of `x`. -/
def leftDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  derivWithin f (Iio x) x

/-- The set where the project-local right derivative is differentiable within the interior of
the one-dimensional domain. -/
def rightDerivDifferentiabilitySet (S : Set ℝ) (f : ℝ → ℝ) : Set ℝ :=
  {x | DifferentiableWithinAt ℝ (rightDeriv f) (interior S) x}

/-- The set where the project-local left derivative is differentiable within the interior of
the one-dimensional domain. -/
def leftDerivDifferentiabilitySet (S : Set ℝ) (f : ℝ → ℝ) : Set ℝ :=
  {x | DifferentiableWithinAt ℝ (leftDeriv f) (interior S) x}

/-- The set where both project-local one-sided derivative functions are differentiable within the
interior of the one-dimensional domain. -/
def oneSidedDerivDifferentiabilitySet (S : Set ℝ) (f : ℝ → ℝ) : Set ℝ :=
  rightDerivDifferentiabilitySet S f ∩ leftDerivDifferentiabilitySet S f

/-- The local estimate saying that the affine remainder is asymptotically the average of the
endpoint right-derivative increment times the displacement.

For convex functions this is the one-dimensional averaging ingredient that remains between the
currently formalized derivative-good information and the final scalar quadratic Taylor estimate. -/
def HasRightDerivAverageRemainderAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ z in nhds 0,
      ‖f (x + z) - f x - rightDeriv f x * z -
        (1 / 2 : ℝ) * (rightDeriv f (x + z) - rightDeriv f x) * z‖ ≤
        ε * ‖z‖ ^ 2

/-- Points where the averaged right-derivative remainder estimate holds. -/
def rightDerivAverageRemainderSet (f : ℝ → ℝ) : Set ℝ :=
  {x | HasRightDerivAverageRemainderAt f x}

variable {S : Set ℝ} {f : ℝ → ℝ} {x y : ℝ}

@[simp]
theorem mem_rightDerivDifferentiabilitySet :
    x ∈ rightDerivDifferentiabilitySet S f ↔
      DifferentiableWithinAt ℝ (rightDeriv f) (interior S) x :=
  Iff.rfl

@[simp]
theorem mem_leftDerivDifferentiabilitySet :
    x ∈ leftDerivDifferentiabilitySet S f ↔
      DifferentiableWithinAt ℝ (leftDeriv f) (interior S) x :=
  Iff.rfl

/-- A convex function has the project-local right derivative at interior points. -/
theorem ConvexOn.hasDerivWithinAt_rightDeriv
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    HasDerivWithinAt f (rightDeriv f x) (Ioi x) x := by
  simpa [rightDeriv] using hf.hasDerivWithinAt_rightDeriv_of_mem_interior hx

/-- A convex function has the project-local left derivative at interior points. -/
theorem ConvexOn.hasDerivWithinAt_leftDeriv
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    HasDerivWithinAt f (leftDeriv f x) (Iio x) x := by
  simpa [leftDeriv] using hf.hasDerivWithinAt_leftDeriv_of_mem_interior hx

/-- Right derivatives of a one-dimensional convex function are monotone on the interior. -/
theorem ConvexOn.monotoneOn_projectRightDeriv (hf : ConvexOn ℝ S f) :
    MonotoneOn (rightDeriv f) (interior S) := by
  change MonotoneOn (fun x => derivWithin f (Ioi x) x) (interior S)
  exact hf.monotoneOn_rightDeriv

/-- Left derivatives of a one-dimensional convex function are monotone on the interior. -/
theorem ConvexOn.monotoneOn_projectLeftDeriv (hf : ConvexOn ℝ S f) :
    MonotoneOn (leftDeriv f) (interior S) := by
  change MonotoneOn (fun x => derivWithin f (Iio x) x) (interior S)
  exact hf.monotoneOn_leftDeriv

/-- The project-local right derivative of a one-dimensional convex function is differentiable
almost everywhere on the interior, in implication form. -/
theorem ConvexOn.ae_differentiableWithinAt_projectRightDeriv_of_mem
    (hf : ConvexOn ℝ S f) :
    ∀ᵐ x, x ∈ interior S →
      DifferentiableWithinAt ℝ (rightDeriv f) (interior S) x :=
  (AleksandrovDifferentiability.ConvexOn.monotoneOn_projectRightDeriv
    (S := S) (f := f) hf).ae_differentiableWithinAt_of_mem

/-- The project-local left derivative of a one-dimensional convex function is differentiable
almost everywhere on the interior, in implication form. -/
theorem ConvexOn.ae_differentiableWithinAt_projectLeftDeriv_of_mem
    (hf : ConvexOn ℝ S f) :
    ∀ᵐ x, x ∈ interior S →
      DifferentiableWithinAt ℝ (leftDeriv f) (interior S) x :=
  (AleksandrovDifferentiability.ConvexOn.monotoneOn_projectLeftDeriv
    (S := S) (f := f) hf).ae_differentiableWithinAt_of_mem

/-- Both project-local one-sided derivative functions are differentiable within the interior
almost everywhere, in implication form. -/
theorem ConvexOn.ae_mem_oneSidedDerivDifferentiabilitySet_of_mem
    (hf : ConvexOn ℝ S f) :
    ∀ᵐ x, x ∈ interior S → x ∈ oneSidedDerivDifferentiabilitySet S f := by
  filter_upwards [
    AleksandrovDifferentiability.ConvexOn.ae_differentiableWithinAt_projectRightDeriv_of_mem
      (S := S) (f := f) hf,
    AleksandrovDifferentiability.ConvexOn.ae_differentiableWithinAt_projectLeftDeriv_of_mem
      (S := S) (f := f) hf] with x hright hleft hx
  exact ⟨hright hx, hleft hx⟩

/-- The exceptional set inside the interior where one of the one-sided derivative functions is
not differentiable has zero Lebesgue measure. -/
theorem ConvexOn.measure_interior_diff_oneSidedDerivDifferentiabilitySet_eq_zero
    (hf : ConvexOn ℝ S f) :
    volume (interior S \ oneSidedDerivDifferentiabilitySet S f) = 0 := by
  have hae :=
    AleksandrovDifferentiability.ConvexOn.ae_mem_oneSidedDerivDifferentiabilitySet_of_mem
      (S := S) (f := f) hf
  rw [ae_iff] at hae
  have hset :
      {x | ¬(x ∈ interior S → x ∈ oneSidedDerivDifferentiabilitySet S f)} =
        interior S \ oneSidedDerivDifferentiabilitySet S f := by
    ext x
    simp [oneSidedDerivDifferentiabilitySet]
  simpa only [hset] using hae

/-- The left derivative is bounded by the right derivative at an interior point of a convex
function. -/
theorem ConvexOn.leftDeriv_le_rightDeriv
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    leftDeriv f x ≤ rightDeriv f x := by
  simpa [leftDeriv, rightDeriv] using hf.leftDeriv_le_rightDeriv_of_mem_interior hx

/-- At an interior point, the right derivative is bounded above by every forward secant slope. -/
theorem ConvexOn.rightDeriv_le_slope
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) (hy : y ∈ S) (hxy : x < y) :
    rightDeriv f x ≤ slope f x y := by
  simpa [rightDeriv] using hf.rightDeriv_le_slope_of_mem_interior hx hy hxy

/-- At an interior point, every backward secant slope is bounded above by the left derivative. -/
theorem ConvexOn.slope_le_leftDeriv
    (hf : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ interior S) (hxy : x < y) :
    slope f x y ≤ leftDeriv f y := by
  simpa [leftDeriv] using hf.slope_le_leftDeriv_of_mem_interior hx hy hxy

/-- The project-local right derivative of a one-dimensional convex function is right-continuous
at interior points. -/
theorem ConvexOn.tendsto_rightDeriv_nhdsGT
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    Tendsto (rightDeriv f) (nhdsWithin x (Ioi x)) (nhds (rightDeriv f x)) := by
  have hright_deriv :
      Tendsto (slope f x) (nhdsWithin x (Ioi x)) (nhds (rightDeriv f x)) :=
    (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp
      (AleksandrovDifferentiability.ConvexOn.hasDerivWithinAt_rightDeriv
        (S := S) (f := f) (x := x) hf hx)
  have hright_cont :
      Tendsto f (nhdsWithin x (Ioi x)) (nhds (f x)) :=
    (AleksandrovDifferentiability.ConvexOn.hasDerivWithinAt_rightDeriv
      (S := S) (f := f) (x := x) hf hx).continuousWithinAt
  have hinterior :
      ∀ᶠ y in nhdsWithin x (Ioi x), y ∈ interior S :=
    nhdsWithin_le_nhds (isOpen_interior.mem_nhds hx)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro l hl
    filter_upwards [hinterior, self_mem_nhdsWithin] with y hyS hxy
    exact hl.trans_le
      (AleksandrovDifferentiability.ConvexOn.monotoneOn_projectRightDeriv
        (S := S) (f := f) hf hx hyS hxy.le)
  · intro m hm
    have hslope_event :
        ∀ᶠ y in nhdsWithin x (Ioi x), slope f x y < m :=
      hright_deriv.eventually (Iio_mem_nhds hm)
    rcases (hslope_event.and (hinterior.and self_mem_nhdsWithin)).exists with
      ⟨d, hd_slope, hdS, hxd⟩
    have hden_ne : d - x ≠ 0 := by linarith
    have hden_tendsto :
        Tendsto (fun y : ℝ => d - y) (nhdsWithin x (Ioi x)) (nhds (d - x)) := by
      have hcont : ContinuousAt (fun y : ℝ => d - y) x := by fun_prop
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hslope_to_fixed :
        Tendsto (fun y : ℝ => slope f y d) (nhdsWithin x (Ioi x))
          (nhds (slope f x d)) := by
      have hquot :
          Tendsto (fun y : ℝ => (f d - f y) / (d - y)) (nhdsWithin x (Ioi x))
            (nhds ((f d - f x) / (d - x))) :=
        (tendsto_const_nhds.sub hright_cont).div hden_tendsto hden_ne
      simpa [slope_def_field] using hquot
    have hfixed_slope_event :
        ∀ᶠ y in nhdsWithin x (Ioi x), slope f y d < m :=
      hslope_to_fixed.eventually (Iio_mem_nhds hd_slope)
    have hy_lt_d :
        ∀ᶠ y in nhdsWithin x (Ioi x), y < d :=
      nhdsWithin_le_nhds (Iio_mem_nhds hxd)
    filter_upwards [hinterior, self_mem_nhdsWithin, hy_lt_d, hfixed_slope_event] with
      y hyS _ hyd hy_slope
    exact (AleksandrovDifferentiability.ConvexOn.rightDeriv_le_slope
      (S := S) (f := f) (x := y) (y := d) hf hyS (interior_subset hdS) hyd).trans_lt
        hy_slope

/-- The left limit of the project-local right derivative of a one-dimensional convex function is
the project-local left derivative at interior points. -/
theorem ConvexOn.tendsto_rightDeriv_nhdsLT_leftDeriv
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    Tendsto (rightDeriv f) (nhdsWithin x (Iio x)) (nhds (leftDeriv f x)) := by
  have hleft_deriv :
      Tendsto (slope f x) (nhdsWithin x (Iio x)) (nhds (leftDeriv f x)) :=
    (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp
      (AleksandrovDifferentiability.ConvexOn.hasDerivWithinAt_leftDeriv
        (S := S) (f := f) (x := x) hf hx)
  have hleft_cont :
      Tendsto f (nhdsWithin x (Iio x)) (nhds (f x)) :=
    (AleksandrovDifferentiability.ConvexOn.hasDerivWithinAt_leftDeriv
      (S := S) (f := f) (x := x) hf hx).continuousWithinAt
  have hinterior :
      ∀ᶠ y in nhdsWithin x (Iio x), y ∈ interior S :=
    nhdsWithin_le_nhds (isOpen_interior.mem_nhds hx)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro l hl
    have hslope_event :
        ∀ᶠ y in nhdsWithin x (Iio x), l < slope f x y :=
      hleft_deriv.eventually (Ioi_mem_nhds hl)
    rcases (hslope_event.and (hinterior.and self_mem_nhdsWithin)).exists with
      ⟨d, hd_slope, hdS, hdx⟩
    have hden_ne : x - d ≠ 0 := by linarith
    have hden_tendsto :
        Tendsto (fun y : ℝ => y - d) (nhdsWithin x (Iio x)) (nhds (x - d)) := by
      have hcont : ContinuousAt (fun y : ℝ => y - d) x := by fun_prop
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hslope_from_fixed :
        Tendsto (fun y : ℝ => slope f d y) (nhdsWithin x (Iio x))
          (nhds (slope f d x)) := by
      have hquot :
          Tendsto (fun y : ℝ => (f y - f d) / (y - d)) (nhdsWithin x (Iio x))
            (nhds ((f x - f d) / (x - d))) :=
        (hleft_cont.sub tendsto_const_nhds).div hden_tendsto hden_ne
      simpa [slope_def_field] using hquot
    have hfixed_slope_event :
        ∀ᶠ y in nhdsWithin x (Iio x), l < slope f d y :=
      hslope_from_fixed.eventually (Ioi_mem_nhds (by simpa [slope_comm f x d] using hd_slope))
    have hd_lt_y :
        ∀ᶠ y in nhdsWithin x (Iio x), d < y :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hdx)
    filter_upwards [hinterior, self_mem_nhdsWithin, hd_lt_y, hfixed_slope_event] with
      y hyS _ hdy hy_slope
    have hslope_le_left :
        slope f d y ≤ leftDeriv f y :=
      AleksandrovDifferentiability.ConvexOn.slope_le_leftDeriv
        (S := S) (f := f) (x := d) (y := y) hf (interior_subset hdS) hyS hdy
    have hleft_le_right :
        leftDeriv f y ≤ rightDeriv f y :=
      AleksandrovDifferentiability.ConvexOn.leftDeriv_le_rightDeriv
        (S := S) (f := f) (x := y) hf hyS
    exact hy_slope.trans_le (hslope_le_left.trans hleft_le_right)
  · intro m hm
    filter_upwards [hinterior, self_mem_nhdsWithin] with y hyS hyx
    have hright_le_slope :
        rightDeriv f y ≤ slope f y x :=
      AleksandrovDifferentiability.ConvexOn.rightDeriv_le_slope
        (S := S) (f := f) (x := y) (y := x) hf hyS (interior_subset hx) hyx
    have hslope_le_left :
        slope f y x ≤ leftDeriv f x :=
      AleksandrovDifferentiability.ConvexOn.slope_le_leftDeriv
        (S := S) (f := f) (x := y) (y := x) hf (interior_subset hyS) hx hyx
    exact (hright_le_slope.trans hslope_le_left).trans_lt hm

/-- A one-dimensional subgradient at an interior point is bounded above by the right derivative. -/
theorem SubgradientOn.le_rightDeriv_of_convex
    {p : ℝ} (hp : SubgradientOn S f x p) (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    p ≤ rightDeriv f x := by
  rw [rightDeriv, hf.rightDeriv_eq_sInf_slope_of_mem_interior hx]
  refine le_csInf ?_ ?_
  · obtain ⟨y, hxy, hyS⟩ := Eventually.exists_gt (mem_interior_iff_mem_nhds.mp hx)
    exact ⟨slope f x y, ⟨y, ⟨hyS, hxy⟩, rfl⟩⟩
  · rintro _ ⟨y, ⟨hyS, hxy⟩, rfl⟩
    have hsupport := hp.supporting_inequality (y := y) hyS
    have hden : 0 < y - x := sub_pos.mpr hxy
    rw [slope_def_field]
    have hmul : p * (y - x) ≤ f y - f x := by
      simpa [mul_comm] using sub_le_sub_right hsupport (f x)
    exact (le_div_iff₀ hden).mpr hmul

/-- The left derivative is bounded above by any one-dimensional subgradient at an interior point. -/
theorem SubgradientOn.leftDeriv_le_of_convex
    {p : ℝ} (hp : SubgradientOn S f x p) (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    leftDeriv f x ≤ p := by
  rw [leftDeriv, hf.leftDeriv_eq_sSup_slope_of_mem_interior hx]
  refine csSup_le ?_ ?_
  · obtain ⟨y, hyx, hyS⟩ := Eventually.exists_lt (mem_interior_iff_mem_nhds.mp hx)
    exact ⟨slope f x y, ⟨y, ⟨hyS, hyx⟩, rfl⟩⟩
  · rintro _ ⟨y, ⟨hyS, hyx⟩, rfl⟩
    have hsupport := hp.supporting_inequality (y := y) hyS
    have hden : y - x < 0 := sub_neg.mpr hyx
    rw [slope_def_field]
    have hmul : p * (y - x) ≤ f y - f x := by
      simpa [mul_comm] using sub_le_sub_right hsupport (f x)
    exact (div_le_iff_of_neg hden).mpr hmul

/-- Conversely, a slope lying between the left and right derivatives of a one-dimensional convex
function at an interior point is a subgradient. -/
theorem ConvexOn.subgradientOn_of_leftDeriv_le_of_le_rightDeriv
    {p : ℝ} (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hl : leftDeriv f x ≤ p) (hr : p ≤ rightDeriv f x) :
    SubgradientOn S f x p := by
  refine ⟨interior_subset hx, ?_⟩
  intro y hy
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have hslope : slope f y x ≤ p :=
      (AleksandrovDifferentiability.ConvexOn.slope_le_leftDeriv
        (S := S) (f := f) (x := y) (y := x) hf hy hx hyx).trans hl
    rw [slope_def_field] at hslope
    have hden : 0 < x - y := sub_pos.mpr hyx
    have hmul : f x - f y ≤ p * (x - y) :=
      (div_le_iff₀ hden).mp hslope
    have hsupport : f x + p * (y - x) ≤ f y := by
      linarith
    simpa [mul_comm] using hsupport
  · simp
  · have hslope : p ≤ slope f x y :=
      hr.trans (AleksandrovDifferentiability.ConvexOn.rightDeriv_le_slope
        (S := S) (f := f) (x := x) (y := y) hf hx hy hxy)
    rw [slope_def_field] at hslope
    have hden : 0 < y - x := sub_pos.mpr hxy
    have hmul : p * (y - x) ≤ f y - f x :=
      (le_div_iff₀ hden).mp hslope
    have hsupport : f x + p * (y - x) ≤ f y := by
      linarith
    simpa [mul_comm] using hsupport

/-- At an interior point of a one-dimensional convex function, being a subgradient is equivalent
to lying between the left and right derivatives. -/
theorem ConvexOn.subgradientOn_iff_leftDeriv_le_and_le_rightDeriv
    {p : ℝ} (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    SubgradientOn S f x p ↔ leftDeriv f x ≤ p ∧ p ≤ rightDeriv f x := by
  constructor
  · intro hp
    exact ⟨hp.leftDeriv_le_of_convex hf hx, hp.le_rightDeriv_of_convex hf hx⟩
  · rintro ⟨hl, hr⟩
    exact AleksandrovDifferentiability.ConvexOn.subgradientOn_of_leftDeriv_le_of_le_rightDeriv
      (S := S) (f := f) (x := x) (p := p) hf hx hl hr

/-- At a differentiability point of a one-dimensional convex function, the ordinary derivative is
the subgradient slope. -/
theorem ConvexOn.subgradientOn_of_hasDerivAt
    {p : ℝ} (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hd : HasDerivAt f p x) :
    SubgradientOn S f x p := by
  have hright : rightDeriv f x = p := by
    simpa [rightDeriv] using
      (hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x))
  have hleft : leftDeriv f x = p := by
    simpa [leftDeriv] using
      (hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x))
  exact AleksandrovDifferentiability.ConvexOn.subgradientOn_of_leftDeriv_le_of_le_rightDeriv
    (S := S) (f := f) (x := x) (p := p) hf hx (le_of_eq hleft) (le_of_eq hright.symm)

/-- A one-dimensional upper quadratic contact gives an upper bound on forward secant slopes. -/
theorem HasUpperContactWithSlopeOn.slope_le_of_lt
    {p a : ℝ} (h : HasUpperContactWithSlopeOn S f x p a) (hy : y ∈ S) (hxy : x < y) :
    slope f x y ≤ p + (a / 2) * (y - x) := by
  have hupper := h.upper_inequality (y := y) hy
  have hden : 0 < y - x := sub_pos.mpr hxy
  rw [slope_def_field]
  have hnorm : ‖y - x‖ ^ 2 = (y - x) ^ 2 := by
    simp [sq, Real.norm_eq_abs]
  have hmul : f y - f x ≤ (p + (a / 2) * (y - x)) * (y - x) := by
    rw [hnorm] at hupper
    simp only [Real.inner_apply] at hupper
    nlinarith
  exact (div_le_iff₀ hden).mpr hmul

/-- A one-dimensional upper quadratic contact gives a lower bound on backward secant slopes. -/
theorem HasUpperContactWithSlopeOn.le_slope_of_lt
    {p a : ℝ} (h : HasUpperContactWithSlopeOn S f x p a) (hy : y ∈ S) (hyx : y < x) :
    p + (a / 2) * (y - x) ≤ slope f x y := by
  have hupper := h.upper_inequality (y := y) hy
  have hden : y - x < 0 := sub_neg.mpr hyx
  rw [slope_def_field]
  have hnorm : ‖y - x‖ ^ 2 = (y - x) ^ 2 := by
    simp [sq, Real.norm_eq_abs]
  have hmul : f y - f x ≤ (p + (a / 2) * (y - x)) * (y - x) := by
    rw [hnorm] at hupper
    simp only [Real.inner_apply] at hupper
    nlinarith
  exact (le_div_iff_of_neg hden).mpr hmul

/-- At an interior point of a convex one-dimensional function, an upper quadratic contact bounds
the right derivative above by the contact slope. -/
theorem HasUpperContactWithSlopeOn.rightDeriv_le_of_convex
    {p a : ℝ} (h : HasUpperContactWithSlopeOn S f x p a)
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    rightDeriv f x ≤ p := by
  have hderiv :
      Tendsto (slope f x) (nhdsWithin x (Ioi x)) (nhds (rightDeriv f x)) :=
    (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp
      (AleksandrovDifferentiability.ConvexOn.hasDerivWithinAt_rightDeriv
        (S := S) (f := f) (x := x) hf hx)
  have hbound :
      Tendsto (fun y : ℝ => p + (a / 2) * (y - x)) (nhdsWithin x (Ioi x)) (nhds p) := by
    have hcont : ContinuousAt (fun y : ℝ => p + (a / 2) * (y - x)) x := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hS : ∀ᶠ y in nhdsWithin x (Ioi x), y ∈ S :=
    nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hx)
  have hevent :
      ∀ᶠ y in nhdsWithin x (Ioi x), slope f x y ≤ p + (a / 2) * (y - x) := by
    filter_upwards [self_mem_nhdsWithin, hS] with y hyIoi hyS
    exact h.slope_le_of_lt hyS hyIoi
  exact le_of_tendsto_of_tendsto hderiv hbound hevent

/-- At an interior point of a convex one-dimensional function, an upper quadratic contact bounds
the contact slope above by the left derivative. -/
theorem HasUpperContactWithSlopeOn.le_leftDeriv_of_convex
    {p a : ℝ} (h : HasUpperContactWithSlopeOn S f x p a)
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    p ≤ leftDeriv f x := by
  have hderiv :
      Tendsto (slope f x) (nhdsWithin x (Iio x)) (nhds (leftDeriv f x)) :=
    (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp
      (AleksandrovDifferentiability.ConvexOn.hasDerivWithinAt_leftDeriv
        (S := S) (f := f) (x := x) hf hx)
  have hbound :
      Tendsto (fun y : ℝ => p + (a / 2) * (y - x)) (nhdsWithin x (Iio x)) (nhds p) := by
    have hcont : ContinuousAt (fun y : ℝ => p + (a / 2) * (y - x)) x := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hS : ∀ᶠ y in nhdsWithin x (Iio x), y ∈ S :=
    nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hx)
  have hevent :
      ∀ᶠ y in nhdsWithin x (Iio x), p + (a / 2) * (y - x) ≤ slope f x y := by
    filter_upwards [self_mem_nhdsWithin, hS] with y hyIio hyS
    exact h.le_slope_of_lt hyS hyIio
  exact le_of_tendsto_of_tendsto hbound hderiv hevent

/-- A convex one-dimensional function with an upper quadratic contact at an interior point has
matching one-sided derivatives there, equal to the contact slope. -/
theorem HasUpperContactWithSlopeOn.leftDeriv_eq_and_rightDeriv_eq_of_convex
    {p a : ℝ} (h : HasUpperContactWithSlopeOn S f x p a)
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    leftDeriv f x = p ∧ rightDeriv f x = p := by
  have hleft_le_right :=
    AleksandrovDifferentiability.ConvexOn.leftDeriv_le_rightDeriv
      (S := S) (f := f) (x := x) hf hx
  have hp_le_left := h.le_leftDeriv_of_convex hf hx
  have hright_le_p := h.rightDeriv_le_of_convex hf hx
  constructor <;> linarith

/-- For a convex one-dimensional function, the slope of an upper quadratic contact at an interior
point is a subgradient. -/
theorem HasUpperContactWithSlopeOn.subgradientOn_of_convex
    {p a : ℝ} (h : HasUpperContactWithSlopeOn S f x p a)
    (hf : ConvexOn ℝ S f) (hx : x ∈ interior S) :
    SubgradientOn S f x p := by
  rcases h.leftDeriv_eq_and_rightDeriv_eq_of_convex hf hx with ⟨hleft, hright⟩
  exact AleksandrovDifferentiability.ConvexOn.subgradientOn_of_leftDeriv_le_of_le_rightDeriv
    (S := S) (f := f) (x := x) (p := p) hf hx (le_of_eq hleft) (le_of_eq hright.symm)

end AleksandrovDifferentiability
