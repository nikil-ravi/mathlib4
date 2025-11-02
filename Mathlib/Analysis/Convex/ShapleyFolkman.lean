import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finset.Basic

variable {𝕜 E ι : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [Fintype ι] [DecidableEq ι]


open scoped Pointwise BigOperators


lemma mem_finset_sum_sets {\iota E : Type*} [DecidableEq \iota] [Add E]
  [Fintype \iota] (A : \iota → Set E) {y : E} :
  y ∈ (∑ i, A i) ↔ ∃ f : ι → E, (∀ i, f i ∈ A i) ∧ y = ∑ i, f i := by
  sorry


/- Convex hull commutes with a finite Minkowski sum -/
lemma convexHull_sum (X : ι → Set E) :
  convexHull 𝕜 (∑ i, X i) = ∑ i, convexHull 𝕜 (X i) := by
  sorry


lemma caratheodory_decomposition: sorry



lemma shapleyFolkman_rounding: sorry





/-- Shapley-Folkman lemma

In a finite-dimensional vector space of dimension `d`,
any point in the Minkowski sum of convex hulls of a family of sets
`X_i` can be expressed as a sum of points `x_i` such that
at most `d` indices are taken from convex hulls, and all others
are directly from `X_i` .


A lean-compatible version (for convenience while formalizing) of the same statement is below.

In a finite-dimensional real vector space of dimension `finrank k E = d`,
any point `y` in the Minkowski sum of convex hulls `∑ i, convexHull k (X i)`,
of a family of sets `X : ι -> Set E`,
there exists a choice of points `x i` (one for each index) and a finite
subset `S: Finset ι` such that:
* `S.card ≤ d` (at most `d` indices are taken from convex hulls)
* for all `i ∉ S`, `x i ∈ X i` (all other indices are taken directly from `X_i`)
* for all `i ∈ S`, `x i ∈ convexHull k (X i)` (the indices in `S` are taken from convex hulls)
* and `y = ∑ i, x i`.
-/

theorem shapley_folkman {X : \iota → Set E} {y : E}
  (hy : y ∈ ∑ i, convexHull 𝕜 (X i)) :
  ∃ (x : \iota \-> E) (S: Finset ι),
    S.card ≤ Module.finrank 𝕜 E ∧
    (∀ i ∉ S, x i ∈ X i) ∧
    (∀ i ∈ S, x i ∈ convexHull 𝕜 (X i)) ∧
    y = ∑ i, x i := by
classical

-- first, use convexHull_sum to move convex hull outside minkowski sum

-- use caratheodory_decomposition to express y as a convex combination of finitely many points z j \in \sum i, X i

-- (tbd)
