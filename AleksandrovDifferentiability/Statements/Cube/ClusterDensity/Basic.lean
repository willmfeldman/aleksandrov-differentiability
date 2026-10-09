module

public import AleksandrovDifferentiability.Analysis.RockafellarCluster
public import AleksandrovDifferentiability.Statements.Cube.SecondOrder
public import AleksandrovDifferentiability.Statements.Cube.Stieltjes.Measurability.Secant

/-!
# Source-cube subgradient cluster-density boundary

This file names the remaining finite-dimensional convex-analysis input in the source cube proof.
It does not prove the density theorem.  It packages its exact source-aligned quantifiers and
records that, once this density input is available, the normalized cube Aleksandrov theorem follows
from the already-formalized upper-contact/Stieltjes route and second-order assembly.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory
open scoped Topology

namespace AleksandrovDifferentiability

/-- Fixed-function form of the source subgradient cluster-density theorem.

For each good base point `x`, and for nearby punctured points `y`, every subgradient of `u` at
`y` relative to the large source cube `Q_3` lies in the closed convex hull of ambient cluster
values of the Fréchet gradient along differentiability points in `Q_{3/2}` approaching `y`.

This is the precise Lean form of the density input corresponding to the preparatory convex source
note's subgradient-extension lemma.  The approach to `y` is ambient; there is no linewise
accumulation requirement. -/
def SourceCubeSubgradientClusterDensity (n : ℕ) (u : SourceCubeSpace n → ℝ) : Prop :=
  ∀ (x : SourceCubeSpace n) (m : ℕ),
    x ∈ cubeGoodSet n u (m : ℝ) →
      ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
        ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
          p ∈ closure
            (convexHull ℝ
              (HasSubgradientLinearizationOnAt.GradientClusterSet
                (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
                (frechetGradient u) y))

set_option linter.unusedSectionVars false in
/-- In a source cube, sufficiently small positive steps in any fixed direction remain in the
same cube.  This is the source-cube form of the open-domain ray lemma used in the interior
Rockafellar route. -/
theorem sourceOpenCube_exists_pos_forall_pos_lt_add_smul_mem
    {n : ℕ} {r : ℝ} {y normal : SourceCubeSpace n}
    (hy : y ∈ sourceOpenCube n r) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ⦃t : ℝ⦄, 0 < t → t < δ → y + t • normal ∈ sourceOpenCube n r :=
  IsOpen.exists_pos_forall_pos_lt_add_smul_mem
    (domain := sourceOpenCube n r) (normal := normal)
    (isOpen_sourceOpenCube (n := n) r) hy

set_option linter.unusedSectionVars false in
/-- One-step version of Rockafellar's `ε^2` differentiability-point choice along a ray.

If the ray point `y + ε • normal` remains in `Q_1`, density of differentiability points in
`Q_1` gives a differentiability point within distance `ε^2` of that ray point. -/
theorem exists_sourceCubeDifferentiabilitySet_one_norm_sub_ray_lt_sq_of_mem
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    {y normal : SourceCubeSpace n} {ε : ℝ}
    (hε : 0 < ε) (hray : y + ε • normal ∈ sourceOpenCube n 1) :
    ∃ w : SourceCubeSpace n,
      w ∈ sourceCubeDifferentiabilitySet n 1 u ∧
        ‖w - (y + ε • normal)‖ < ε ^ 2 := by
  have hclosure :
      y + ε • normal ∈ closure (sourceCubeDifferentiabilitySet n 1 u) :=
    sourceOpenCube_one_subset_closure_sourceCubeDifferentiabilitySet_one_of_convex hu hray
  rcases Metric.mem_closure_iff.mp hclosure (ε ^ 2) (sq_pos_of_pos hε) with
    ⟨w, hw, hdist⟩
  refine ⟨w, hw, ?_⟩
  have hdist' : dist w (y + ε • normal) < ε ^ 2 := by
    simpa [dist_comm] using hdist
  simpa [dist_eq_norm] using hdist'

set_option linter.unusedSectionVars false in
/-- Filter-level choice of Rockafellar differentiability samples near an exposing ray.

For any scalar family `ε a` whose positive ray points eventually remain in `Q_1`, choose
differentiability samples `φ a ∈ D_1` eventually satisfying the `ε a ^ 2` ray estimate. -/
theorem exists_sourceCubeDifferentiabilitySet_one_ray_samples
    {ι : Type*} {l : Filter ι} {n : ℕ} {u : SourceCubeSpace n → ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    {y normal : SourceCubeSpace n} {ε : ι → ℝ}
    (hεpos : ∀ᶠ a in l, 0 < ε a)
    (hray : ∀ᶠ a in l, y + ε a • normal ∈ sourceOpenCube n 1) :
    ∃ φ : ι → SourceCubeSpace n,
      (∀ᶠ a in l, φ a ∈ sourceCubeDifferentiabilitySet n 1 u) ∧
        ∀ᶠ a in l, ‖φ a - (y + ε a • normal)‖ ≤ (ε a) ^ 2 := by
  classical
  let good : Set ι := {a | 0 < ε a ∧ y + ε a • normal ∈ sourceOpenCube n 1}
  have hexists :
      ∀ a : ι, a ∈ good →
        ∃ w : SourceCubeSpace n,
          w ∈ sourceCubeDifferentiabilitySet n 1 u ∧
            ‖w - (y + ε a • normal)‖ < (ε a) ^ 2 := by
    intro a ha
    exact exists_sourceCubeDifferentiabilitySet_one_norm_sub_ray_lt_sq_of_mem
      hu ha.1 ha.2
  let φ : ι → SourceCubeSpace n := fun a =>
    if h : a ∈ good then Classical.choose (hexists a h) else 0
  refine ⟨φ, ?_, ?_⟩
  · filter_upwards [hεpos, hray] with a hpos hmem
    have hgood : a ∈ good := ⟨hpos, hmem⟩
    have hspec := Classical.choose_spec (hexists a hgood)
    simpa [φ, hgood] using hspec.1
  · filter_upwards [hεpos, hray] with a hpos hmem
    have hgood : a ∈ good := ⟨hpos, hmem⟩
    have hspec := Classical.choose_spec (hexists a hgood)
    exact le_of_lt (by simpa [φ, hgood] using hspec.2)

set_option linter.unusedSectionVars false in
/-- Rockafellar differentiability samples along sufficiently small positive ray parameters.

This is the filter-level source-cube form of the sequence choice in Rockafellar 25.6:
if `ε a -> 0` through positive values and the base point is in `Q_1`, then openness of `Q_1`
puts the ray points `y + ε a • normal` eventually in `Q_1`, where differentiability points are
dense. -/
theorem exists_sourceCubeDifferentiabilitySet_one_ray_samples_tendsto_zero
    {ι : Type*} {l : Filter ι} {n : ℕ} {u : SourceCubeSpace n → ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    {y normal : SourceCubeSpace n} {ε : ι → ℝ}
    (hy : y ∈ sourceOpenCube n 1)
    (hε : Filter.Tendsto ε l (𝓝 0))
    (hεpos : ∀ᶠ a in l, 0 < ε a) :
    ∃ φ : ι → SourceCubeSpace n,
      (∀ᶠ a in l, φ a ∈ sourceCubeDifferentiabilitySet n 1 u) ∧
        ∀ᶠ a in l, ‖φ a - (y + ε a • normal)‖ ≤ (ε a) ^ 2 := by
  rcases sourceOpenCube_exists_pos_forall_pos_lt_add_smul_mem
      (n := n) (r := 1) (y := y) (normal := normal) hy with
    ⟨δ, hδpos, hδmem⟩
  have hlt : ∀ᶠ a in l, ε a < δ := by
    have hlt_mem : ∀ᶠ a in l, ε a ∈ Set.Iio δ :=
      hε.eventually (Iio_mem_nhds hδpos)
    simpa [Set.mem_Iio] using hlt_mem
  have hray : ∀ᶠ a in l, y + ε a • normal ∈ sourceOpenCube n 1 := by
    filter_upwards [hεpos, hlt] with a hpos hltδ
    exact hδmem hpos hltδ
  exact exists_sourceCubeDifferentiabilitySet_one_ray_samples hu hεpos hray

set_option linter.unusedSectionVars false in
/-- Inner-cube source-cube cluster density from Rockafellar's concrete ray sequence.

This is the source-faithful `Q_1` version: the differentiability samples live in `D_1`, and the
resulting cluster hull is enlarged to `D_{3/2}` by monotonicity. -/
theorem SourceCubeSubgradientClusterDensity.of_bounded_straszewiczClosure_ray_sourceCube_one
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hstrasz :
      ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ({q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}.extremePoints ℝ) ⊆
          closure
            (exposedPoints
              {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}))
    (houter :
      ∀ ⦃y p : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          p ∈ exposedPoints
            {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} →
            ∃ (normal : SourceCubeSpace n), ‖normal‖ = 1 ∧
              ExposesPoint
                {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} normal p ∧
                ∃ (ι : Type*) (l : Filter ι) (φ : ι → SourceCubeSpace n) (ε : ι → ℝ),
                  l.NeBot ∧
                    Filter.Tendsto ε l (𝓝 0) ∧
                      (∀ᶠ a in l, 0 < ε a) ∧
                        (∀ᶠ a in l, φ a ∈ sourceCubeDifferentiabilitySet n 1 u) ∧
                          (∀ᶠ a in l, ‖φ a - (y + ε a • normal)‖ ≤ (ε a) ^ 2) ∧
                            (Filter.Tendsto
                              (fun a => ‖φ a - y‖⁻¹ • (φ a - y)) l (𝓝 normal) →
                                ∀ δ > 0,
                                  ∀ᶠ a in l,
                                    frechetGradient u (φ a) ∈
                                      normThickening
                                        (exposedFace
                                          {q : SourceCubeSpace n |
                                            SubgradientOn (sourceOpenCube n 3) u y q}
                                          normal) δ)) :
    SourceCubeSubgradientClusterDensity n u := by
  have hlocal :
      LocalSubgradientClusterDensityOn (sourceOpenCube n 3) (sourceOpenCube n 1) u := by
    refine localSubgradientClusterDensityOn_of_bounded_straszewiczClosure_rayOuter
      (domain := sourceOpenCube n 3)
      (sample := sourceOpenCube n 1)
      (u := u)
      ?_ hstrasz ?_
    · intro y hy
      exact sourceCube_subgradient_set_isBounded_of_boundedOn_three_halves hbounded
        (sourceOpenCube_subset_of_le (n := n) (r := 1) (R := (3 / 2 : ℝ))
          (by norm_num) hy)
    · intro y p hy hp
      rcases houter hy hp with
        ⟨normal, hnormal, hexposed, ι, l, φ, ε, hne, hε, hεpos, hmem, hclose, hthickening⟩
      refine ⟨normal, hnormal, hexposed, ι, l, φ, ε, hne, hε, hεpos, ?_, hclose, ?_⟩
      · simpa [differentiabilitySetOn, sourceCubeDifferentiabilitySet,
          firstOrderDifferentiabilitySet] using hmem
      · intro hdir δ hδ
        simpa [differentiabilitySetOn, sourceCubeDifferentiabilitySet,
          firstOrderDifferentiabilitySet, frechetGradient, gradient] using
          hthickening hdir δ hδ
  intro x m hxgood
  have hxQ1 : x ∈ sourceOpenCube n 1 :=
    cubeGoodSet_subset_sourceOpenCube_one hxgood
  have hQ1_nhds : sourceOpenCube n 1 ∈ 𝓝 x :=
    (isOpen_sourceOpenCube (n := n) 1).mem_nhds hxQ1
  have hQ1_event_nhds : ∀ᶠ y in 𝓝 x, y ∈ sourceOpenCube n 1 :=
    hQ1_nhds
  have hQ1_event :
      ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x, y ∈ sourceOpenCube n 1 :=
    hQ1_event_nhds.filter_mono inf_le_left
  filter_upwards [hQ1_event] with y hyQ1 p hp
  have hdensity := hlocal hyQ1 hp
  have hD :
      differentiabilitySetOn (sourceOpenCube n 1) u ⊆
        differentiabilitySetOn (sourceOpenCube n (3 / 2 : ℝ)) u := by
    intro w hw
    exact
      ⟨sourceOpenCube_subset_of_le (n := n) (r := 1) (R := (3 / 2 : ℝ))
          (by norm_num) hw.1,
        hw.2⟩
  have hmono :=
    HasSubgradientLinearizationOnAt.GradientClusterSet.mem_closure_convexHull_mono
      (D₁ := differentiabilitySetOn (sourceOpenCube n 1) u)
      (D₂ := differentiabilitySetOn (sourceOpenCube n (3 / 2 : ℝ)) u)
      (G := gradient u) (y := y) (p := p) hD hdensity
  simpa only [differentiabilitySetOn, sourceCubeDifferentiabilitySet,
    firstOrderDifferentiabilitySet, frechetGradient_eq_gradient] using hmono

set_option linter.unusedSectionVars false in
/-- Inner-cube source-cube cluster density from Rockafellar's concrete ray sequence, with the
unit exposing normal chosen from exposed-point membership.

The positive-dimensional hypothesis supplies an ambient unit vector for the degenerate singleton
case of an exposed point.  Thus callers only need to prove the ray construction and directional
outer-semicontinuity estimate for whichever unit exposing normal is selected. -/
theorem SourceCubeSubgradientClusterDensity.of_bounded_straszewiczClosure_ray_one_unitOuter
    {n : ℕ} (hn : 0 < n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hstrasz :
      ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ({q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}.extremePoints ℝ) ⊆
          closure
            (exposedPoints
              {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}))
    (houter :
      ∀ ⦃y p normal : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          p ∈ exposedPoints
            {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} →
            ‖normal‖ = 1 →
              ExposesPoint
                {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} normal p →
                ∃ (ι : Type*) (l : Filter ι) (φ : ι → SourceCubeSpace n) (ε : ι → ℝ),
                  l.NeBot ∧
                    Filter.Tendsto ε l (𝓝 0) ∧
                      (∀ᶠ a in l, 0 < ε a) ∧
                        (∀ᶠ a in l, φ a ∈ sourceCubeDifferentiabilitySet n 1 u) ∧
                          (∀ᶠ a in l, ‖φ a - (y + ε a • normal)‖ ≤ (ε a) ^ 2) ∧
                            (Filter.Tendsto
                              (fun a => ‖φ a - y‖⁻¹ • (φ a - y)) l (𝓝 normal) →
                                ∀ δ > 0,
                                  ∀ᶠ a in l,
                                    frechetGradient u (φ a) ∈
                                      normThickening
                                        (exposedFace
                                          {q : SourceCubeSpace n |
                                            SubgradientOn (sourceOpenCube n 3) u y q}
                                          normal) δ)) :
    SourceCubeSubgradientClusterDensity n u :=
  SourceCubeSubgradientClusterDensity.of_bounded_straszewiczClosure_ray_sourceCube_one
    hbounded hstrasz
    (fun {y p} hy hp => by
      rcases exists_unit_exposesPoint_of_mem_exposedPoints_of_exists_unit_vector hp
          (exists_unit_sourceCubeSpace_of_pos hn) with
        ⟨normal, hnormal, hexposed⟩
      rcases houter hy hp hnormal hexposed with
        ⟨ι, l, φ, ε, hne, hε, hεpos, hmem, hclose, hthickening⟩
      exact
        ⟨normal, hnormal, hexposed, ι, l, φ, ε, hne, hε, hεpos, hmem, hclose,
          hthickening⟩)

set_option linter.unusedSectionVars false in
/-- Inner-cube source-cube cluster density from scalar ray parameters and directional outer
semicontinuity.

Compared with `SourceCubeSubgradientClusterDensity.of_bounded_straszewiczClosure_ray_one_unitOuter`,
this wrapper does not ask the caller to construct the differentiability samples.  For each exposed
subgradient and selected unit exposing normal, the caller supplies only a positive scalar filter
`ε -> 0` and an outer-semicontinuity estimate applying to any differentiability samples satisfying
Rockafellar's `ε^2` ray estimate.  The samples themselves are chosen from density of
differentiability points in `Q_1`. -/
theorem SourceCubeSubgradientClusterDensity.of_bounded_straszewiczClosure_ray_one_unitOuter_scalars
    {n : ℕ} (hn : 0 < n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hstrasz :
      ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ({q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}.extremePoints ℝ) ⊆
          closure
            (exposedPoints
              {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}))
    (houter :
      ∀ ⦃y p normal : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          p ∈ exposedPoints
            {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} →
            ‖normal‖ = 1 →
              ExposesPoint
                {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} normal p →
                ∃ (ι : Type*) (l : Filter ι) (ε : ι → ℝ),
                  l.NeBot ∧
                    Filter.Tendsto ε l (𝓝 0) ∧
                      (∀ᶠ a in l, 0 < ε a) ∧
                        ∀ ⦃φ : ι → SourceCubeSpace n⦄,
                          (∀ᶠ a in l, φ a ∈ sourceCubeDifferentiabilitySet n 1 u) →
                            (∀ᶠ a in l,
                              ‖φ a - (y + ε a • normal)‖ ≤ (ε a) ^ 2) →
                              (Filter.Tendsto
                                (fun a => ‖φ a - y‖⁻¹ • (φ a - y)) l (𝓝 normal) →
                                  ∀ δ > 0,
                                    ∀ᶠ a in l,
                                      frechetGradient u (φ a) ∈
                                        normThickening
                                          (exposedFace
                                            {q : SourceCubeSpace n |
                                              SubgradientOn (sourceOpenCube n 3) u y q}
                                            normal) δ)) :
    SourceCubeSubgradientClusterDensity n u :=
  SourceCubeSubgradientClusterDensity.of_bounded_straszewiczClosure_ray_one_unitOuter
    hn hbounded hstrasz
    (fun {y p normal} hy hp hnormal hexposed => by
      rcases houter hy hp hnormal hexposed with
        ⟨ι, l, ε, hne, hε, hεpos, hthickening⟩
      rcases exists_sourceCubeDifferentiabilitySet_one_ray_samples_tendsto_zero
          hconvex hy hε hεpos with
        ⟨φ, hmem, hclose⟩
      exact
        ⟨ι, l, φ, ε, hne, hε, hεpos, hmem, hclose,
          hthickening (φ := φ) hmem hclose⟩)

set_option linter.unusedSectionVars false in
/-- Inner-cube source-cube cluster density using the canonical positive scalar sequence.

This fixes Rockafellar's `ε_i ↓ 0` choice to the already-used source sequence
`sourceForwardSecantStep k`.  Thus the remaining exposed-point input is only the directional
outer-semicontinuity estimate along differentiability samples satisfying the `ε_k^2` ray estimate.
-/
theorem SourceCubeSubgradientClusterDensity.of_bounded_straszewiczClosure_ray_one_unitOuter_seq
    {n : ℕ} (hn : 0 < n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hstrasz :
      ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ({q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}.extremePoints ℝ) ⊆
          closure
            (exposedPoints
              {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}))
    (houter :
      ∀ ⦃y p normal : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          p ∈ exposedPoints
            {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} →
            ‖normal‖ = 1 →
              ExposesPoint
                {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} normal p →
                ∀ ⦃φ : ℕ → SourceCubeSpace n⦄,
                  (∀ᶠ k in Filter.atTop, φ k ∈ sourceCubeDifferentiabilitySet n 1 u) →
                    (∀ᶠ k in Filter.atTop,
                      ‖φ k - (y + sourceForwardSecantStep k • normal)‖ ≤
                        (sourceForwardSecantStep k) ^ 2) →
                      (Filter.Tendsto
                        (fun k => ‖φ k - y‖⁻¹ • (φ k - y)) Filter.atTop (𝓝 normal) →
                          ∀ δ > 0,
                            ∀ᶠ k in Filter.atTop,
                              frechetGradient u (φ k) ∈
                                normThickening
                                  (exposedFace
                                    {q : SourceCubeSpace n |
                                      SubgradientOn (sourceOpenCube n 3) u y q}
                                    normal) δ)) :
    SourceCubeSubgradientClusterDensity n u :=
  SourceCubeSubgradientClusterDensity.of_bounded_straszewiczClosure_ray_one_unitOuter_scalars
    hn hbounded hconvex hstrasz
    (fun {y p normal} hy hp hnormal hexposed => by
      refine ⟨ℕ, Filter.atTop, sourceForwardSecantStep, inferInstance,
        tendsto_sourceForwardSecantStep, ?_, ?_⟩
      · exact Filter.Eventually.of_forall sourceForwardSecantStep_pos
      · intro φ hmem hclose
        exact houter hy hp hnormal hexposed hmem hclose)

set_option linter.unusedSectionVars false in
/-- Inner-cube source-cube cluster density from the canonical ray sequence, with Mathlib's
`Set.exposedPoints` notation.

This is the Mathlib-shaped version of
`SourceCubeSubgradientClusterDensity.of_bounded_straszewiczClosure_ray_one_unitOuter_seq`: the
Straszewicz and exposed-point hypotheses are stated using `Set.exposedPoints`, while the scalar
sequence is fixed to `sourceForwardSecantStep`. -/
theorem SourceCubeSubgradientClusterDensity.of_bounded_mathlibStraszewicz_ray_one_unitOuter_seq
    {n : ℕ} (hn : 0 < n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hstrasz :
      ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ({q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}.extremePoints ℝ) ⊆
          closure
            (Set.exposedPoints ℝ
              {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q}))
    (houter :
      ∀ ⦃y p normal : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          p ∈ Set.exposedPoints ℝ
            {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} →
            ‖normal‖ = 1 →
              ExposesPoint
                {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} normal p →
                ∀ ⦃φ : ℕ → SourceCubeSpace n⦄,
                  (∀ᶠ k in Filter.atTop, φ k ∈ sourceCubeDifferentiabilitySet n 1 u) →
                    (∀ᶠ k in Filter.atTop,
                      ‖φ k - (y + sourceForwardSecantStep k • normal)‖ ≤
                        (sourceForwardSecantStep k) ^ 2) →
                      (Filter.Tendsto
                        (fun k => ‖φ k - y‖⁻¹ • (φ k - y)) Filter.atTop (𝓝 normal) →
                          ∀ δ > 0,
                            ∀ᶠ k in Filter.atTop,
                              frechetGradient u (φ k) ∈
                                normThickening
                                  (exposedFace
                                    {q : SourceCubeSpace n |
                                      SubgradientOn (sourceOpenCube n 3) u y q}
                                    normal) δ)) :
    SourceCubeSubgradientClusterDensity n u :=
  SourceCubeSubgradientClusterDensity.of_bounded_straszewiczClosure_ray_one_unitOuter_seq
    hn hbounded hconvex
    (fun {y} hy => by
      simpa [exposedPoints_eq_mathlib_exposedPoints] using hstrasz hy)
    (fun {y p normal} hy hp hnormal hexposed => by
      have hp_mathlib :
          p ∈ Set.exposedPoints ℝ
            {q : SourceCubeSpace n | SubgradientOn (sourceOpenCube n 3) u y q} := by
        simpa [exposedPoints_eq_mathlib_exposedPoints] using hp
      exact houter hy hp_mathlib hnormal hexposed)

end AleksandrovDifferentiability
