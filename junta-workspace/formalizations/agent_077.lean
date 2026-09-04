import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Both directions of the theorem are stated; every theorem
ends in `:= by sorry` and nothing is proved.

* Main direction: for `d ≥ 1` there is `m(d)` such that if `k ≥ 2d` and `n ≥ 2k`, every
  Boolean degree-`d` function on `binom([n],k)` is an `m(d)`-junta.
* Converse (tightness): if `1 ≤ k < 2d`, then for every `m` there are `n ≥ 2k` and a
  Boolean degree-`d` function on `binom([n],k)` that is not an `m`-junta.

The explicit witnessing family from the source statement is *not* included (see the
accompanying `agent_077.md`); the converse is stated with an existential witness.
-/

open scoped BigOperators

namespace FilmusIhringer

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector in `ℝ^n` of a point of the slice. -/
def indicatorVec {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ (S : Finset (Fin n)) then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it takes only the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- A function on the slice has *degree `≤ d`* if it agrees, at every point of the slice,
with the evaluation at the `0/1` indicator vector of some real multivariate polynomial of
total degree `≤ d`.

Because `xᵢ^2 = xᵢ` on `{0,1}`, additionally requiring the polynomial to be multilinear
yields the same notion, so multilinearity is not imposed here. -/
def HasSliceDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (indicatorVec S) p

/-- A function on the slice is an *`m`-junta* if there is a set `J` of at most `m`
coordinates such that the value of the function depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k,
      (S : Finset (Fin n)) ∩ J = (T : Finset (Fin n)) ∩ J → f S = f T

/-- **Filmus–Ihringer, main direction.**
For every `d ≥ 1` there is a constant `m = m(d)` such that whenever `k ≥ 2d` and `n ≥ 2k`,
every Boolean degree-`d` function on the slice `binom([n], k)` is an `m`-junta. -/
theorem isJunta_of_isBoolean_of_hasSliceDegreeLE (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasSliceDegreeLE d f → IsJunta m f := by
  sorry

/-- **Filmus–Ihringer, converse (tightness).**
If `1 ≤ k < 2d`, then no uniform junta bound exists: for every `m` there is some `n ≥ 2k`
and a Boolean degree-`d` function on the slice `binom([n], k)` that is not an `m`-junta. -/
theorem exists_not_isJunta_of_lt_two_mul
    (d k : ℕ) (hd : 1 ≤ d) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasSliceDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

end FilmusIhringer
