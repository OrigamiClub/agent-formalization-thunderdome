# Agent 031 — formalization note

## What I stated

All three pieces, as separate `sorry`-terminated theorems:

1. `boolean_degree_junta` — the **positive direction**: `∀ d ≥ 1, ∃ m, ∀ k ≥ 2d, ∀ n ≥ 2k`,
   every Boolean degree-`d` function on the slice is an `m`-junta.
2. `boolean_degree_not_junta` — the **converse / sharpness**, in pure existential form:
   `∀ d ≥ 1, ∀ k with 1 ≤ k < 2d, ∀ m, ∃ n ≥ 2k, ∃ f` Boolean, degree `≤ d`, not an `m`-junta.
3. `fiFamily` + `fiFamily_witnesses` — the **explicit witnessing family**
   `∏_{i=1}^{ℓ}(∑_{j=1}^{e} x_{(i-1)e+j})`, `e = min d k`, tying it to the converse: given `m`,
   for some `ℓ` with `ℓ·e > m` and `n ≥ 2ℓe`, `fiFamily` is Boolean, degree `≤ d`, not an `m`-junta.

## Encoding decisions

- **Slice**: `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset (Fin n)`;
  `abbrev` so the projection `S.1` and the coercion to `Finset` work transparently. Coordinate set
  is `Fin n`, carried by the parameter `n`.
- **Boolean codomain**: functions are `Slice n k → ℝ` together with a separate predicate
  `IsBooleanOn f : ∀ S, f S = 0 ∨ f S = 1`. Real codomain keeps the degree definition friction-free
  (no coercions inside `MvPolynomial.eval`).
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` that is multilinear
  (`∀ u ∈ p.support, ∀ i, u i ≤ 1`), has `p.totalDegree ≤ d`, and agrees with `f` at every slice
  point when evaluated at the `0/1` indicator vector `fun i => if i ∈ S.1 then 1 else 0`.
  Multilinearity is included to match the problem's "multilinear real polynomial" wording; it is
  mathematically WLOG on `{0,1}^n` (multilinearization does not raise total degree), so it does not
  change the content of either direction.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
- **m(d)**: existential *inside* the statement (`∃ m : ℕ, …`), not an external `m : ℕ → ℕ`.
- **n, k, d**: plain `ℕ` universally quantified in each theorem; thresholds written `2 * d ≤ k`,
  `2 * k ≤ n`, `1 ≤ k`, `k < 2 * d`.
- **Explicit family** (`fiFamily n k d ℓ`): `∏ i ∈ range ℓ, ∑ j ∈ range (min d k), …` over the
  indicator of coordinate `i * min d k + j`; a `dite` guard sends out-of-range indices to `0`, so the
  definition needs no side condition relating `ℓ`, `e`, `n`. Marked `noncomputable` defensively.

## Uncertainties

- **Guessed Mathlib identifiers**: `MvPolynomial.eval`, `MvPolynomial.totalDegree`,
  `MvPolynomial.support` (with `u i` as `Finsupp` application), `Finset.range`, and the `∏ / ∑`
  big-operator notation. These match my recollection of current Mathlib but were not compiler-checked.
- **"not ℓe-juntas"**: taken literally under my `IsJunta`, `fiFamily` *is* an `ℓe`-junta (it depends
  only on the first `ℓe` coordinates). I read the paper's intent as "the minimal junta size is `ℓe`,
  and `ℓ` is unbounded", and encoded it as `m < ℓ * min d k ∧ ¬ IsJunta m (fiFamily …)`. This makes
  `fiFamily_witnesses` a strict strengthening of `boolean_degree_not_junta`'s witness clause.
- I did **not** independently verify that the product family has slice-degree `≤ d` (as a polynomial
  it has degree `ℓ`); `HasDegreeLE d (fiFamily …)` transcribes the problem's assertion that these are
  degree-`d` functions. Likewise `IsBooleanOn (fiFamily …)` is taken on the problem's word.
- The constant in the positive direction is left as a bare `∃ m`; the paper gives an explicit
  `m(d)` (roughly `d · 2^d`), not reproduced here.
