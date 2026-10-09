module

public import AleksandrovDifferentiability.Analysis.DirectionalQuadratic.Frame

/-!
# Directional quadratic operators

Rank-one and mixed directional quadratic operators, together with finite sums.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Symmetric operators are closed under finite sums. -/
theorem isSymmetricOperator_sum {ι : Type*} {s : Finset ι} {B : ι → E →L[ℝ] E}
    (hB : ∀ i ∈ s, IsSymmetricOperator (B i)) :
    IsSymmetricOperator (∑ i ∈ s, B i) := by
  intro x y
  change inner ℝ ((∑ i ∈ s, B i) x) y = inner ℝ x ((∑ i ∈ s, B i) y)
  rw [sum_apply, sum_apply]
  rw [sum_inner, inner_sum]
  exact Finset.sum_congr rfl fun i hi => hB i hi x y

/-- The symmetric mixed rank-two operator associated to directions `v` and `w`. Its quadratic
form is the product of the two directional coordinates. -/
def mixedDirectionalQuadraticOperator (v w : E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) •
    (InnerProductSpace.rankOne ℝ v w + InnerProductSpace.rankOne ℝ w v)

@[simp]
theorem mixedDirectionalQuadraticOperator_apply (v w z : E) :
    mixedDirectionalQuadraticOperator v w z =
      (1 / 2 : ℝ) • (inner ℝ w z • v + inner ℝ v z • w) := by
  simp [mixedDirectionalQuadraticOperator]

/-- The mixed directional operator is symmetric. -/
theorem isSymmetricOperator_mixedDirectionalQuadraticOperator (v w : E) :
    IsSymmetricOperator (mixedDirectionalQuadraticOperator v w) := by
  intro x y
  change inner ℝ (mixedDirectionalQuadraticOperator v w x) y =
    inner ℝ x (mixedDirectionalQuadraticOperator v w y)
  rw [mixedDirectionalQuadraticOperator_apply, mixedDirectionalQuadraticOperator_apply]
  simp [inner_add_left, inner_add_right, real_inner_smul_right, real_inner_comm]
  ring

/-- The quadratic form of the mixed directional operator is the product of the corresponding
directional coordinates. -/
theorem inner_mixedDirectionalQuadraticOperator_self (v w z : E) :
    inner ℝ z (mixedDirectionalQuadraticOperator v w z) =
      inner ℝ v z * inner ℝ w z := by
  rw [mixedDirectionalQuadraticOperator_apply]
  simp [inner_add_right, real_inner_smul_right, real_inner_comm]
  ring

/-- A finite matrix of mixed directional quadratic operators. The coefficient `a i j` multiplies
the operator with quadratic form `inner ℝ (v i) z * inner ℝ (v j) z`. -/
def mixedDirectionalQuadraticSum {ι : Type*} (s : Finset ι) (v : ι → E)
    (a : ι → ι → ℝ) : E →L[ℝ] E :=
  ∑ i ∈ s, ∑ j ∈ s, a i j • mixedDirectionalQuadraticOperator (v i) (v j)

/-- Finite coefficient matrices of mixed directional quadratic operators are symmetric. -/
theorem isSymmetricOperator_mixedDirectionalQuadraticSum
    {ι : Type*} (s : Finset ι) (v : ι → E) (a : ι → ι → ℝ) :
    IsSymmetricOperator (mixedDirectionalQuadraticSum s v a) := by
  unfold mixedDirectionalQuadraticSum
  refine isSymmetricOperator_sum fun i _ => ?_
  refine isSymmetricOperator_sum fun j _ => ?_
  exact (isSymmetricOperator_mixedDirectionalQuadraticOperator (v i) (v j)).smul (a i j)

/-- The quadratic form of a finite mixed directional sum is the corresponding coefficient
matrix expression in the directional coordinates. -/
theorem inner_mixedDirectionalQuadraticSum_self
    {ι : Type*} (s : Finset ι) (v : ι → E) (a : ι → ι → ℝ) (z : E) :
    inner ℝ z (mixedDirectionalQuadraticSum s v a z) =
      ∑ i ∈ s, ∑ j ∈ s,
        a i j * inner ℝ (v i) z * inner ℝ (v j) z := by
  unfold mixedDirectionalQuadraticSum
  rw [sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [smul_apply, real_inner_smul_right,
    inner_mixedDirectionalQuadraticOperator_self]
  ring

/-- The coefficient matrix recovered from pure directional quadratic coefficients `q i` and
pairwise-sum coefficients `r i j` by the usual polarization formula.  The diagonal is kept equal
to the pure coefficient, and off-diagonal entries use
`(r i j - q i - q j) / 2`. -/
def polarizedMixedCoefficient {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) (r : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i j => if i = j then q i else (r i j - q i - q j) / 2

@[simp]
theorem polarizedMixedCoefficient_self
    {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (r : ι → ι → ℝ) (i : ι) :
    polarizedMixedCoefficient q r i i = q i := by
  simp [polarizedMixedCoefficient]

theorem polarizedMixedCoefficient_of_ne
    {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (r : ι → ι → ℝ)
    {i j : ι} (hij : i ≠ j) :
    polarizedMixedCoefficient q r i j = (r i j - q i - q j) / 2 := by
  simp [polarizedMixedCoefficient, hij]

/-- The mixed-directional quadratic operator assembled from pure coefficients `q i` and
pairwise-sum coefficients `r i j` by polarization. -/
def polarizedMixedQuadraticSum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → E) (q : ι → ℝ) (r : ι → ι → ℝ) : E →L[ℝ] E :=
  mixedDirectionalQuadraticSum s v (polarizedMixedCoefficient q r)

/-- The polarized mixed-directional quadratic operator is symmetric. -/
theorem isSymmetricOperator_polarizedMixedQuadraticSum
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → E)
    (q : ι → ℝ) (r : ι → ι → ℝ) :
    IsSymmetricOperator (polarizedMixedQuadraticSum s v q r) :=
  isSymmetricOperator_mixedDirectionalQuadraticSum s v (polarizedMixedCoefficient q r)

end AleksandrovDifferentiability
