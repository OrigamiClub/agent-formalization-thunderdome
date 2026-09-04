# Agent 077 — formalization note

## What is stated

Both directions of the Filmus–Ihringer theorem, statement only, each ending in `:= by sorry`:

1. `isJunta_of_isBoolean_of_hasSliceDegreeLE` — the main direction: for `d ≥ 1` there
   *exists* `m : ℕ` (the constant `m(d)`) such that for all `k, n` with `k ≥ 2d` and
   `n ≥ 2k`, every Boolean degree-`d` function on the slice is an `m`-junta.
2. `exists_not_isJunta_of_lt_two_mul` — the converse/tightness direction: for fixed `d, k`
   with `1 ≤ k < 2d`, for every `m` there exist `n ≥ 2k` and a Boolean degree-`d` function
   on `binom([n], k)` that is not an `m`-junta.

The explicit witnessing family was **not** included (see "Uncertainties" below); the
converse uses a plain existential witness `∃ f, ...`.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset (Fin n)`
  cut out by the cardinality condition. Chosen for direct access to `S ∩ J` (`Finset`
  intersection) in the junta definition and to the membership predicate for the indicator
  vector.
- **Boolean codomain**: functions are `Slice n k → ℝ`, with a separate predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Keeping the codomain `ℝ` lets "degree" be stated
  without any coercion friction; Booleanity is an explicit hypothesis (main direction) /
  conjunct (converse), matching "Boolean degree-`d` function".
- **Degree `≤ d`**: `HasSliceDegreeLE d f` says there is `p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d` and `f S = MvPolynomial.eval (indicatorVec S) p` for every slice point,
  where `indicatorVec S i = if i ∈ S then 1 else 0`. This is the standard "agrees on the
  slice with a real polynomial of total degree `≤ d` at the `0/1` indicator vector".
  Multilinearity is deliberately not imposed: since `xᵢ^2 = xᵢ` on `{0,1}`, the set of
  achievable `(function, degree-bound)` pairs is unchanged, and omitting it keeps the
  definition shorter. A comment in the file records this.
- **`m`-junta**: `IsJunta m f` = `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, ↑S ∩ J = ↑T ∩ J
  → f S = f T`. "Value depends only on `S ∩ J`", with `J` of size `≤ m`. `J = ∅` correctly
  degenerates to "`f` constant".
- **`m(d)`**: existential inside the statement (`∃ m : ℕ, ...` under fixed `d`), matching
  "there is a constant `m(d)`". Not exposed as an explicit `m : ℕ → ℕ`.
- **Parameters**: `d` is a top-level hypothesis with `hd : 1 ≤ d`. In the main direction
  `k, n` are universally quantified inside (so a single `m` works for all admissible `k, n`).
  In the converse `k` is a top-level parameter (with `1 ≤ k`, `k < 2d`) and `n` is
  existentially chosen per `m`. The ambient coordinate set is `Fin n` throughout.
- **`n ≥ 2k`** is used verbatim as the ambient-size hypothesis; note it already forces
  `n - k ≥ k ≥ 2d`, so both the slice and its complement are large, as the theorem needs.

## Uncertainties

- **Explicit family omitted.** The source describes the counterexamples as
  `∏_{i=1}^{ℓ}(Σ_{j=1}^{e} x_{(i-1)e+j})` with `e = min(d, k)`, "not `ℓe`-juntas for
  `n ≥ 2ℓe`". Parsing this literally with `0/1` variables on a *fixed* slice `binom([n], k)`
  with `k < 2d` fixed: once `ℓ > k` at least one block sum is `0` for every `S` with
  `|S| = k`, so the product is identically `0` — an `m`-junta — which would make an included
  "not an `ℓe`-junta" statement false. The construction presumably uses `±1` (Fourier)
  variables and/or a growing slice parameter, and the exact Booleanity argument is subtle.
  Rather than risk encoding a false statement, I stated the converse with an existential
  witness, which faithfully captures "no uniform `m(d)` bound for `k < 2d`". The task
  explicitly permits choosing which parts and whether to include the family.
- **Mathlib identifiers** used and believed current: `MvPolynomial (Fin n) ℝ`,
  `MvPolynomial.totalDegree`, `MvPolynomial.eval` (as `(σ → R) → MvPolynomial σ R →+* R`,
  applied `MvPolynomial.eval v p`), `Finset.card`, `Finset` intersection `∩` (via
  `DecidableEq (Fin n)`), subtype coercion `↑S : Finset (Fin n)`. These are stable names;
  the only mild risk is the precise `eval` application form.
- Not type-checked against a compiler (none available); written from Mathlib knowledge.
