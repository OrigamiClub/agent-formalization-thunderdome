# Agent 055 — formalization note

## What I stated

Statement only (all `:= by sorry`). I formalized **all three** pieces:

1. `filmus_ihringer_juntas` — the positive direction: `d ≥ 1` gives an
   existentially-quantified constant `M = m(d)` (depending only on `d`, bound
   before the `∀ n k`) such that `k ≥ 2d`, `n ≥ 2k` force every Boolean
   degree-`d` slice function to be an `M`-junta.
2. `filmus_ihringer_sharp` — the converse in pure existential form: for
   `1 ≤ k < 2d` and every `m`, some `n ≥ 2k` and some Boolean degree-`d`
   function that is not an `m`-junta.
3. `filmus_ihringer_explicit_family` — the converse witnessed by the explicit
   family, with the block count `ℓ` as the free parameter; for `n ≥ 2ℓe`
   (`e = min d k`) the function is Boolean, degree `≤ d`, and not an `m`-junta
   for any `m < ℓe`.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. `{1..n}` is
  `Fin n`; a subset is a `Finset (Fin n)`; the indicator vector is
  `fun i => if i ∈ S.1 then (1:ℝ) else 0`. Chosen for directness; no `Fintype`
  instance is needed for the statements.
- **Boolean codomain**: functions `Slice n k → ℝ` with
  `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1`. Real codomain makes the degree
  definition (polynomial evaluation) completely natural, and `{0,1} ⊆ ℝ` is the
  convention in the source.
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, multilinear, agreeing with `f` at every slice point under
  `MvPolynomial.eval` of the `0/1` indicator vector. Multilinearity is encoded
  as `∀ t ∈ p.support, ∀ i, t i ≤ 1` (no variable occurs squared) — I did not
  assume a Mathlib `IsMultilinear` predicate for `MvPolynomial` exists. Note
  that evaluation only ever happens at `0/1` points, so the multilinearity
  clause is not logically essential, but I kept it to match the source's
  wording ("agrees with a multilinear polynomial").
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n), J.card ≤ m ∧
  ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`. "Depends only on `S ∩ J`".
- **m(d)**: existential `∃ M : ℕ` inside the statement (source says "there is a
  constant"), placed so it depends only on `d`.
- **n, k, d, ambient set**: all plain `ℕ`; ambient coordinates `Fin n`. Side
  conditions `2*d ≤ k`, `2*k ≤ n`, `k < 2*d`, `1 ≤ k` as hypotheses.
- **Explicit family indexing**: blocks `B_i = {i·e, …, i·e+e-1}` for `i ∈ range ℓ`,
  `e = min d k` passed as a variable with `he : e = min d k`. Coordinates built
  with a `dite` on `i*e+j < n` (out-of-range terms contribute `0`), so the `def`
  needs no proof argument. "Not an `ℓe`-junta" from the source is rendered as
  "not an `m`-junta for every `m < ℓ·e`" (the function has exactly `ℓe` relevant
  coordinates, so it is trivially an `ℓe`-junta but not an `(ℓe−1)`-junta; taking
  `ℓ` large defeats any fixed `m`).

## Uncertainties

- **The explicit formula.** The source writes
  `∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)e+j} )` (product of block-sums). Read
  literally that is `∏_i |S ∩ B_i|`, which is not `{0,1}`-valued and has total
  degree `ℓ` (not `≤ d`), so it cannot be the family of Boolean degree-`d`
  non-`m`-juntas claimed. I believe the intended function is the
  **sum of block-products** `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` = "`S`
  contains one of `ℓ` disjoint size-`e` blocks": degree `e = min d k ≤ d`,
  multilinear, and `{0,1}`-valued on `binom([n],k)` precisely because `k < 2d`
  forces at most one block to be contained. `filmus_ihringer_explicit_family`
  is stated for that form (`explicitFamily`); the literal transcription is kept
  as `explicitFamilyLiteral`, unused, for transparency.
- **Mathlib identifiers** used, believed current: `MvPolynomial`,
  `MvPolynomial.totalDegree`, `MvPolynomial.eval`, `MvPolynomial.support` (the
  support is a `Finset (Fin n →₀ ℕ)`, elements applied as `t i : ℕ`),
  `Finset.card`, `Finset.range`, `Finset.sum`/`Finset.prod` big-operator
  notation `∑ x ∈ s, _` / `∏ x ∈ s, _`. No lemmas are invoked (statement only).
- `Slice` is a `def`, not `abbrev`; fine here since no typeclass needs to see
  through it.
- I did not verify the exact optimal `m(d)` bound; it is existential, as in the
  source's "there is a constant".
