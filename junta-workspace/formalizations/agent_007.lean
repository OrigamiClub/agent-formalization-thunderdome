import Mathlib

open Finset MvPolynomial

namespace FilmusIhringer

/-!
# Filmus–Ihringer junta threshold for Boolean degree-`d` functions on the slice

Statement-only formalization: every theorem ends in `:= by sorry` and nothing is proved.

Reference: Y. Filmus, *Junta threshold for low degree Boolean functions on the
slice*, arXiv:2203.04760 — the sharp `k = 2d` threshold, refining Filmus–Ihringer,
*Boolean constant degree functions on the slice are juntas* (Discrete Math. 2019).

## Encoding summary

* A point of the slice `binom([n], k)` is a `S : Finset (Fin n)` with `S.card = k`.
* A "Boolean function on the slice" is `f : Finset (Fin n) → ℝ` that is `{0,1}`-valued
  on `{S | S.card = k}` (`BooleanOn`).
* "Degree `≤ d`" (`DegreeLEOn`): `f` agrees on the slice with the evaluation, at
  indicator vectors, of a multilinear `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`.  Multilinearity is `∀ u ∈ p.support, ∀ i, u i ≤ 1`.
* "`m`-junta" (`JuntaOn`): a coordinate set `J`, `J.card ≤ m`, with `f S` determined
  by `S ∩ J` on the slice.
* `m(d)` is an existential inside the positive statement.
-/

variable {n : ℕ}

/-- The real indicator vector of `S ⊆ Fin n`, a point of `ℝ^n`. -/
noncomputable def ind (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- The `k`-slice `binom([n], k)`: subsets of `Fin n` of size exactly `k`. -/
def slice (n k : ℕ) : Set (Finset (Fin n)) := {S | S.card = k}

/-- `f` is `{0,1}`-valued on the `k`-slice. -/
def BooleanOn (k : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → f S = 0 ∨ f S = 1

/-- `f` has degree `≤ d` on the `k`-slice: it agrees there with the evaluation, at
indicator vectors, of a *multilinear* real polynomial of total degree `≤ d`.
The clause `∀ u ∈ p.support, ∀ i, u i ≤ 1` says every monomial of `p` is squarefree
(multilinear). -/
def DegreeLEOn (k d : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ u ∈ p.support, ∀ i, u i ≤ 1) ∧
    ∀ S : Finset (Fin n), S.card = k → f S = MvPolynomial.eval (ind S) p

/-- `f` is an `m`-junta on the `k`-slice: there is a set `J` of at most `m`
coordinates such that `f S` depends only on `S ∩ J`. -/
def JuntaOn (k m : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ ⦃S T : Finset (Fin n)⦄, S.card = k → T.card = k → S ∩ J = T ∩ J → f S = f T

/-- **Positive direction (Filmus–Ihringer).** For every `d ≥ 1` there is a bound
`m(d)` (existentially quantified) such that whenever `k ≥ 2d` and `n ≥ 2k`, every
Boolean degree-`d` function on `binom([n], k)` is an `m(d)`-junta. -/
theorem juntaThreshold_pos (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ ⦃k : ℕ⦄, 2 * d ≤ k → ∀ ⦃n : ℕ⦄, 2 * k ≤ n →
      ∀ f : Finset (Fin n) → ℝ,
        BooleanOn k f → DegreeLEOn k d f → JuntaOn k m f := by
  sorry

/-- **Converse direction.** If `1 ≤ k < 2d` then the junta bound fails: for every
`m` there are `n ≥ 2k` and a Boolean degree-`d` function on `binom([n], k)` that is
not an `m`-junta. -/
theorem juntaThreshold_neg
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Finset (Fin n) → ℝ,
      BooleanOn k f ∧ DegreeLEOn k d f ∧ ¬ JuntaOn k m f := by
  sorry

/-- The explicit witnessing family
`∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e + j}` with `e = min d k`, read as a function of
`S`: the number of the `ℓ` pairwise-disjoint size-`e` blocks
`Bᵢ = { x i 0, …, x i (e-1) }` that are entirely contained in `S`.
The coordinate map `x` is supplied abstractly and pinned to
`x i j = (i * e + j : Fin n)` in `witness_spec`. -/
noncomputable def witness (e ℓ : ℕ) (x : ℕ → ℕ → Fin n) :
    Finset (Fin n) → ℝ :=
  fun S => ∑ i ∈ range ℓ, ∏ j ∈ range e, (if x i j ∈ S then (1 : ℝ) else 0)

/-- **Explicit witnesses for the converse.** With `e = min d k` and `1 ≤ k < 2d`,
for every number of blocks `ℓ` and every ambient `n` with `n ≥ 2·ℓ·e` and `n ≥ 2k`,
the function `witness e ℓ x` (coordinates `x i j = i·e + j`) is Boolean on the
slice, has degree `≤ d`, and is not an `m`-junta for any `m < ℓ·e`.  Taking `ℓ`
with `ℓ·e > m` therefore defeats any prescribed `m`, giving `juntaThreshold_neg`.

(The value `witness e ℓ x` lands in `{0,1}` precisely because `k < 2d ≤ 2e`, so a
`k`-set `S` cannot contain two of the disjoint size-`e` blocks.) -/
theorem witness_spec
    (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2 : k < 2 * d) (ℓ : ℕ)
    (hn₁ : 2 * (ℓ * min d k) ≤ n) (hn₂ : 2 * k ≤ n)
    (x : ℕ → ℕ → Fin n)
    (hx : ∀ i, i < ℓ → ∀ j, j < min d k → (x i j : ℕ) = i * min d k + j) :
    BooleanOn k (witness (min d k) ℓ x) ∧
    DegreeLEOn k d (witness (min d k) ℓ x) ∧
    ∀ m : ℕ, m < ℓ * min d k → ¬ JuntaOn k m (witness (min d k) ℓ x) := by
  sorry

end FilmusIhringer
