# Agent 065 — formalization note

## What is stated

Three `sorry`-terminated statements, no proofs:

1. `filmus_ihringer` — **both directions** of the main theorem, packaged as a conjunction
   for a fixed `d ≥ 1`:
   - forward: `∃ m : ℕ`, for all `k ≥ 2d`, all `n ≥ 2k`, every Boolean degree-`≤ d`
     function on the slice is an `m`-junta;
   - converse: for all `k` with `1 ≤ k < 2d` and all `m`, some `n ≥ 2k` carries a Boolean
     degree-`≤ d` function on the slice that is not an `m`-junta.
2. `filmus_ihringer_explicit_witness` — the converse **with the explicit witnessing
   family** `witnessFun` plugged in: for `1 ≤ k < 2d` and any `m`, there exist `n ≥ 2k`
   and a block count `ℓ` making `witnessFun` Boolean, degree `≤ d`, and not an `m`-junta.

`witnessFun` is provided as an auxiliary definition; the two `sorry` theorems are the
deliverable.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of `Finset (Fin n)`
  — direct, and `S.1 ∩ J` gives the "restrict to coordinate set" operation needed for the
  junta definition for free.
- **Codomain**: `ℝ`, with Booleanness a separate predicate `IsBooleanOn` (`f S = 0 ∨ f S = 1`).
  This keeps "value in `{0,1} ⊆ ℝ`" and "degree via real polynomial" in the same type
  without coercions.
- **Degree ≤ d** (`IsSliceDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `p` multilinear (`∀ u ∈ p.support, ∀ i, u i ≤ 1`), and
  `f S = eval (indicator of S.1) p` for every slice point. Multilinearity is stated
  explicitly to match the problem text ("multilinear real polynomial"); on `0/1` inputs it
  is not a real restriction.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `S.1 ∩ J = T.1 ∩ J → f S = f T`.
- **`m(d)`**: existential *inside* the statement (`∃ m : ℕ, …`), placed outside the `∀ k`
  and `∀ n`, so it is a single constant depending only on `d`. Chosen over an explicit
  `m : ℕ → ℕ` because the theorem asserts mere existence of the constant.
- **`n, k, d`**: plain `ℕ` parameters/binders; ambient coordinate set is `Fin n`.
- **Witness family** (`witnessFun`): `∑_{i<ℓ} ∏_{j<e} x_{i*e+j}` with `e = min d k`,
  evaluated at the indicator vector — the count of designated disjoint `e`-blocks contained
  in `S`. Block coordinates are injected into `Fin n` via an explicit hypothesis
  `hidx : ∀ i < ℓ, ∀ j < e, i*e+j < n`, carried as an existential in the theorem, to avoid
  in-statement arithmetic side goals.

## Deliberate deviation from the prompt text

The prompt writes the witness as a **product of sums**,
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`. Evaluated on the slice this equals
`∏_i |S ∩ B_i|`, which is `0` for every `k`-set `S` once `ℓ > k` (some block is missed);
that function is identically `0`, hence a `0`-junta, and cannot be a non-junta witness for
arbitrarily large `m`. The correct Filmus–Ihringer construction is the **sum of products**
`∑_i ∏_{j∈B_i} x_j`: it has total degree `e = min d k ≤ d`, it is `{0,1}`-valued exactly
because `k < 2d` makes `2e > k` so no `k`-set contains two disjoint `e`-blocks, and it
depends on all `ℓ·e` block coordinates, so choosing `ℓ` with `ℓ·e > m` defeats any
`m`-junta bound. I formalized the sum-of-products version and flag the swap here and in a
docstring. (The prompt's "not `ℓe`-juntas" is also off by one — the function *is* an
`ℓe`-junta but not an `(ℓe−1)`-junta; my statement only asserts "not an `m`-junta" for the
chosen large `ℓ`, which is the robust claim.)

## Uncertainties / guessed Mathlib identifiers

- `MvPolynomial.eval`, `MvPolynomial.totalDegree`, `MvPolynomial.support`,
  `MvPolynomial.X` — names/signatures believed current; `support : Finset (Fin n →₀ ℕ)`
  with `u i` the exponent of variable `i`.
- `Fin.isLt : (i : Fin n) → (i : ℕ) < n` — used to discharge the `Fin.mk` bound inside
  `witnessFun`.
- No dedicated "Boolean function on the slice" / "junta" / "slice degree" API is assumed to
  exist in Mathlib; all four notions are defined from scratch.
- `open scoped BigOperators` included for `∑ / ∏`; harmless if already global in the
  Mathlib version used.
- `import Mathlib` (whole library) for portability.
