import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

Reference: Y. Filmus, F. Ihringer, *Boolean constant-degree functions on the slice
are juntas* (2019).
-/

open scoped BigOperators

namespace FilmusIhringer

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`. -/
def Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-indicator vector of a finite set, viewed as a point of `ℝ^n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- A real-valued function on the slice is *Boolean* if all its values lie in `{0,1}`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ x : Slice n k, f x = 0 ∨ f x = 1

/-- A function on the slice has *degree `≤ d`* if it agrees, at every point of the
slice, with the evaluation at the indicator vector of some real polynomial in `n`
variables of total degree `≤ d`.

On `{0,1}`-inputs one may freely assume the polynomial multilinear (replacing
`X i ^ a` by `X i` for `a ≥ 1` changes neither the values on `{0,1}` nor increases
the total degree); we therefore do not impose multilinearity, since it yields the
same notion. -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    ∀ x : Slice n k, f x = MvPolynomial.eval (indicator x.1) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that
the value `f x` depends only on `x ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ x y : Slice n k, (x.1 ∩ J : Finset (Fin n)) = y.1 ∩ J → f x = f y

/-- The Filmus–Ihringer tightness family, as an explicit polynomial:
`∏_{i=0}^{ℓ-1} ( ∑_{j=0}^{e-1} X_{i·e + j} )`
(the paper's `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, reindexed from `0`).
Coordinates whose index is `≥ n` contribute `0`; they never occur when `n ≥ ℓ·e`. -/
noncomputable def tightnessPoly (n ℓ e : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then (MvPolynomial.X ⟨i * e + j, h⟩ : MvPolynomial (Fin n) ℝ)
      else 0)

/-- The tightness family as a function on the slice `binom([n], k)`. -/
noncomputable def tightnessFun (n k ℓ e : ℕ) : Slice n k → ℝ :=
  fun x => MvPolynomial.eval (indicator x.1) (tightnessPoly n ℓ e)

/-!
## Forward direction (the junta theorem)

For every `d ≥ 1` there is a bound `m = m(d)` such that whenever `k ≥ 2d` and
`n ≥ 2k`, every Boolean degree-`≤ d` function on `binom([n], k)` is an `m`-junta.
The constant `m(d)` is packaged as an existential inside the statement.
-/
theorem boolean_degree_isJunta :
    ∀ d : ℕ, 1 ≤ d →
      ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta m f := by
  sorry

/-!
## Converse direction (tightness of the range `k ≥ 2d`)

If `1 ≤ k < 2d` then the junta bound cannot be made uniform: for every `m` there is
a slice `binom([n], k)` with `n ≥ 2k` carrying a Boolean degree-`≤ d` function that
is not an `m`-junta.
-/
theorem boolean_degree_not_isJunta :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d →
      ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-!
## Explicit witnesses for the converse

With `e = min d k`, for `n ≥ 2·ℓ·e` the function `tightnessFun n k ℓ e` is a Boolean
degree-`≤ d` function on `binom([n], k)` that is not an `(ℓ·e)`-junta, as stated in
Filmus–Ihringer.  Letting `ℓ` grow makes `ℓ·e` exceed any prescribed `m`, which
yields `boolean_degree_not_isJunta`.
-/
theorem tightnessFun_witness :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d →
      ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ e : ℕ, e = min d k →
        ∀ n : ℕ, 2 * (ℓ * e) ≤ n →
          IsBoolean (tightnessFun n k ℓ e) ∧
          HasDegreeLE d (tightnessFun n k ℓ e) ∧
          ¬ IsJunta (ℓ * e) (tightnessFun n k ℓ e) := by
  sorry

end FilmusIhringer
