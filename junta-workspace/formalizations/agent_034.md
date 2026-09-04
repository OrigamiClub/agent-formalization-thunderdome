# Agent 034 — formalization note

## What I stated

**Both directions**, as two separate `theorem ... := by sorry`:

- `filmus_ihringer_junta` — the forward/junta direction: `∀ d ≥ 1, ∃ m, ∀ k ≥ 2d, ∀ n ≥ 2k, ...`
  every Boolean degree-`≤ d` function on `binom([n],k)` is an `m`-junta.
- `filmus_ihringer_tight` — the converse (tightness of `k ≥ 2d`): for `1 ≤ k < 2d`, for every
  `m` there exist `n ≥ 2k` and a Boolean degree-`≤ d` function on `binom([n],k)` that is not an
  `m`-junta.

I did **not** put the explicit witnessing family into the theorem statement (see "Uncertainties").
It appears only as an unused reference `def lowerConstruction`, with no asserted properties.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset (Fin n)` — makes
  `S ∩ J` and cardinality bookkeeping directly available.
- **Codomain / "Boolean"**: functions are `Slice n k → ℝ`, with `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1`.
  Real-valued was chosen so that "degree" can be phrased with genuine real polynomials with no coercion
  friction.
- **"Degree ≤ d"**: `HasDegreeLE d f` = there is `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, multilinear (`∀ i, p.degreeOf i ≤ 1`), such that `f S = eval (indicatorVec S.1) p`
  for every slice point, where `indicatorVec S i = if i ∈ S then 1 else 0`. This is the "agrees on the
  slice with a multilinear real polynomial of total degree ≤ d evaluated at the indicator vector"
  reading. "degree-d" is read as "degree ≤ d" (the usual meaning of the class `B_d`).
- **"m-junta"**: `IsJunta m f` = `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
  I.e. the value depends only on `S ∩ J`.
- **`m(d)`**: existential *inside* the statement, quantified before `k` and `n`
  (`∃ m : ℕ, ∀ k n, ...`), so it depends only on `d`.
- **Carrying `n, k, d`**: plain `ℕ` arguments/quantifiers; `n ≥ 2k` and `k ≥ 2d` written as
  `2 * k ≤ n` and `2 * d ≤ k`. Ambient coordinate set is `Fin n`.
- **Explicit family**: given only as `lowerConstruction n e ℓ : (Fin n → ℝ) → ℝ`, the polynomial
  `∏_{i<ℓ} (∑_{j<e} x_{i*e+j})` (0-indexed; out-of-range terms zeroed via `dite`). Not referenced by
  the theorems.

## Uncertainties

- **The literal witnessing family is not asserted.** Under a naive reading, `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})`
  with `e = min d k` is not `{0,1}`-valued on the slice: e.g. `d = 2`, `k = 3` (so `k < 2d`), `e = 2`,
  `ℓ = 2`, blocks `{1,2},{3,4}`, and `S = {1,2,3}` gives `(x_1+x_2)(x_3+x_4) = 2·1 = 2`. Also its
  polynomial degree is `ℓ`, not obviously `d`, and its non-junta behaviour needs `ℓ` unbounded while
  `k < 2d` is bounded. Rather than encode a clause I could not vouch for, I kept the converse as a pure
  existential (which is exactly the mathematical content of tightness) and left the construction as an
  un-asserted `def` for the reader. The paper presumably intends a normalization / additional structure
  I did not reconstruct.
- `MvPolynomial.degreeOf`, `MvPolynomial.totalDegree`, `MvPolynomial.eval` — believed correct Mathlib
  names and signatures; `p.degreeOf i` elaborates to `MvPolynomial.degreeOf i p`.
- The multilinearity clause `∀ i, p.degreeOf i ≤ 1` is included for faithfulness to "multilinear
  polynomial", but it is WLOG on `{0,1}` inputs and could be dropped without changing the class of
  functions.
- `Finset` intersection `S.1 ∩ J` uses the `DecidableEq (Fin n)` instance (available).
- `∏ i ∈ Finset.range ℓ, ...` binder notation assumes a recent Mathlib.
