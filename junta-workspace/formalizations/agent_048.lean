import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-- The slice `binom([n], k)`: subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- Indicator vector `Fin n → ℝ` of a slice point (`1` on the set, `0` off it). -/
def sliceIndicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ (S : Finset (Fin n)) then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it takes only the values `0` and `1`. -/
def IsBooleanSlice {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* on the slice: there is a real polynomial in `n` variables of
total degree `≤ d` whose evaluation at the indicator vector agrees with `f` at every
slice point.  (Restricting the polynomial to be multilinear yields the same notion, since
on `{0,1}` inputs every monomial power collapses, so it is left unconstrained here.) -/
def IsSliceDegreeLE (n k d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (sliceIndicator S) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the
value `f S` depends only on `S ∩ J`. -/
def IsJunta (n k m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k,
      (S : Finset (Fin n)) ∩ J = (T : Finset (Fin n)) ∩ J → f S = f T

/-- **Filmus–Ihringer, positive direction.**
For every `d ≥ 1` there is a bound `m = m(d)` such that whenever `k ≥ 2d` and `n ≥ 2k`,
every Boolean degree-`d` function on the slice `binom([n], k)` is an `m`-junta. -/
theorem filmus_ihringer_junta_of_degree :
    ∀ d : ℕ, 1 ≤ d →
      ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ,
          IsBooleanSlice f → IsSliceDegreeLE n k d f → IsJunta n k m f := by
  sorry

/-- **Filmus–Ihringer, sharpness (converse).**
If `1 ≤ k < 2d` then for every `m` there exist some `n ≥ 2k` and a Boolean degree-`d`
function on the slice `binom([n], k)` that is not an `m`-junta. -/
theorem filmus_ihringer_not_junta :
    ∀ d k : ℕ, 1 ≤ d → 1 ≤ k → k < 2 * d →
      ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ,
          IsBooleanSlice f ∧ IsSliceDegreeLE n k d f ∧ ¬ IsJunta n k m f := by
  sorry

end FilmusIhringer
