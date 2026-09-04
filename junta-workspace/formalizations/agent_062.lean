import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every `theorem` ends in `:= by sorry`.

## Encoding choices

* **Ambient coordinates.**  Variables are indexed by `ℕ`.  The slice `binom([n],k)` is
  the set of finite subsets of `{0, 1, …, n-1}` of size exactly `k`
  (`abbrev Slice`).  Using `ℕ`-indexed variables (rather than `Fin n`) lets us write the
  explicit witness polynomial `∏_i ∑_j X (i*e+j)` with no dependent index arithmetic.
* **Boolean codomain.**  Functions are `ℝ`-valued together with the predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`.  A real codomain is forced by the definition
  of degree (agreement with a real polynomial).
* **Degree ≤ d.**  `HasDegreeLE d f`: there is a *multilinear* `p : MvPolynomial ℕ ℝ`
  (`IsMultilinear`: every monomial uses each variable at most once) with
  `p.totalDegree ≤ d` that agrees with `f` at the `0/1` indicator vector of every slice
  set.
* **m-junta.**  `IsJunta m f`: some `J : Finset ℕ` with `J.card ≤ m` such that `f S`
  depends only on `S ∩ J`.
* **`m(d)`.**  An existential `∃ m : ℕ`, quantified *after* fixing `d` but *before* `k`
  and `n`, so it depends on `d` only.
-/

/-- The slice `binom([n],k)`: subsets of `{0,…,n-1}` of size exactly `k`. -/
abbrev Slice (n k : ℕ) : Type :=
  {S : Finset ℕ // S.card = k ∧ ∀ x ∈ S, x < n}

/-- A real-valued function on the slice is *Boolean* if it takes only the values `0`, `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- The `0/1` indicator vector of a slice set, as a point of `ℕ → ℝ`. -/
def indicator {n k : ℕ} (S : Slice n k) : ℕ → ℝ :=
  fun x => if x ∈ S.val then (1 : ℝ) else 0

/-- `p` is *multilinear*: every monomial in its support uses each variable at most once. -/
def IsMultilinear (p : MvPolynomial ℕ ℝ) : Prop :=
  ∀ t ∈ p.support, ∀ x : ℕ, t x ≤ 1

/-- A function on the slice has *degree ≤ d* if it agrees, on every slice set, with the
evaluation at the indicator vector of some multilinear real polynomial of total degree
`≤ d`. -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial ℕ ℝ,
    IsMultilinear p ∧ p.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *m-junta*: there is a coordinate set `J` of size `≤ m` such that `f S`
depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset ℕ, J.card ≤ m ∧
    ∀ S T : Slice n k, S.val ∩ J = T.val ∩ J → f S = f T

/-- The explicit witness polynomial
`∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)e+j} )`, written with `0`-based indices: block `i`
(for `i < ℓ`) is the coordinate set `{ i*e, i*e+1, …, i*e+e-1 }`. -/
noncomputable def witnessPoly (ℓ e : ℕ) : MvPolynomial ℕ ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (MvPolynomial.X (i * e + j) : MvPolynomial ℕ ℝ)

/-- The explicit witness function on the slice: `witnessPoly` evaluated at the indicator
vector. -/
noncomputable def witnessFun (n k ℓ e : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicator S) (witnessPoly ℓ e)

/-- **Filmus–Ihringer.**  Fix `d ≥ 1`.

* *Junta direction.*  There is a constant `m` (depending on `d` only) such that whenever
  `k ≥ 2d`, for every `n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)` is an
  `m`-junta.
* *Sharpness direction.*  Whenever `1 ≤ k < 2d`, for every `m` there are `n ≥ 2k` and a
  Boolean degree-`d` function on `binom([n],k)` that is not an `m`-junta.
-/
theorem filmus_ihringer (d : ℕ) (hd : 1 ≤ d) :
    (∃ m : ℕ,
      ∀ k, 2 * d ≤ k → ∀ n, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta m f)
    ∧ (∀ k, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
        ∃ n, 2 * k ≤ n ∧
          ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f) := by
  sorry

/-- **Sharpness direction, with the explicit witnessing family.**

Let `1 ≤ k < 2d` and put `e = min d k`.  For every `m`, choosing `ℓ` with `ℓ * e > m` and
any `n ≥ 2 * ℓ * e` (which also gives `n ≥ 2k`), the function `witnessFun n k ℓ e` — given
on the slice by `∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)e+j} )` evaluated at the indicator
vector — is a Boolean degree-`d` function on `binom([n],k)` that depends on all `ℓ*e` block
coordinates and hence is not an `m`-junta.

(The clause `¬ IsJunta (ℓ * e - 1) …` is the reading of "not `ℓe`-juntas": the function
genuinely uses all `ℓ*e` block coordinates.  Taken with `m < ℓ * e` this yields the
`¬ IsJunta m …` clause.) -/
theorem filmus_ihringer_witness
    (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2 : k < 2 * d)
    (e : ℕ) (he : e = min d k) :
    ∀ m : ℕ, ∃ ℓ n : ℕ,
      m < ℓ * e ∧ 2 * ℓ * e ≤ n ∧ 2 * k ≤ n ∧
      IsBoolean (witnessFun n k ℓ e) ∧
      HasDegreeLE d (witnessFun n k ℓ e) ∧
      ¬ IsJunta (ℓ * e - 1) (witnessFun n k ℓ e) ∧
      ¬ IsJunta m (witnessFun n k ℓ e) := by
  sorry

end FilmusIhringer
