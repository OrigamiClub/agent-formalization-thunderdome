# Agent 076 — formalization note

## What is stated

All statements only, every theorem ends in `:= by sorry`. I stated **both
directions plus the explicit witnessing family**:

1. `filmus_ihringer_forward` — the junta upper bound: `∃ m, ∀ k ≥ 2d, ∀ n ≥ 2k`,
   every Boolean degree-`≤ d` slice function is an `m`-junta.
2. `filmus_ihringer_converse` — for `1 ≤ k < 2d` and every `m`, some `n ≥ 2k`
   carries a Boolean degree-`≤ d` slice function that is not an `m`-junta.
3. `filmus_ihringer_converse_witness` — the concrete family, with the three
   properties (Boolean, degree `≤ d`, not an `m`-junta for `m < ℓ·e`).

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset` is the lightest faithful model of `binom([n],k)`; the coordinate
  universe is `Fin n`, and `n`, `k`, `d` are plain `ℕ` arguments.
- **Boolean codomain**: functions are `Slice n k → ℝ` with a side predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real-valued is the natural choice
  because "degree" is defined through real polynomials; a `Bool`/`Fin 2` codomain
  would force casts at every use of `eval`.
- **Degree**: `HasDegreeLE f d` says there is `p : MvPolynomial (Fin n) ℝ` that
  is multilinear (`IsMultilinear`: every exponent in every support monomial is
  `≤ 1`), has `p.totalDegree ≤ d`, and satisfies
  `f S = MvPolynomial.eval (sliceIndicator S) p` for all slice points, where
  `sliceIndicator S i = if i ∈ S.val then 1 else 0`. This matches Filmus's
  definition ("`ℝ`-linear combination of products of `≤ d` distinct variables").
  I included multilinearity explicitly to mirror "multilinear real polynomial" in
  the prompt; dropping it would give a provably equivalent class, so this is a
  conservative choice.
- **Junta**: `IsJunta f m` = `∃ J, J.card ≤ m ∧ ∀ S T, S.val ∩ J = T.val ∩ J →
  f S = f T`. This is exactly "value depends only on `S ∩ J`", and it correctly
  captures the slice subtlety (two slice points agreeing on `J` may differ
  outside `J` because of the cardinality constraint).
- **`m(d)`**: an existential `∃ m : ℕ` inside the statement rather than an
  explicit `m : ℕ → ℕ`. The theorem asserts existence of the constant; making it
  a supplied function would require committing to a particular (unspecified)
  bound.
- **Quantifier order (forward)**: `∃ m, ∀ k ≥ 2d, ∀ n ≥ 2k, ∀ f, …` — `m`
  depends only on `d`, as required.

## The explicit family

The prompt writes the witnesses as `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with
`e = min(d,k)`, "not `ℓe`-juntas" for `n ≥ 2ℓe`. I instead formalized the
**sum-of-block-monomials**

    juntaWitness(S) = ∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}  at the indicator of S
                    = #{ blocks B_i entirely contained in S }.

Reasons for the deviation:

- With the literal `∏_i (∑_j …)` the polynomial has total degree `ℓ`, not `≤ d`,
  and its slice values are `∏_i |S ∩ B_i|`, which for `d < k < 2d` (e.g.
  `d=10, k=15, ℓ=3`) take values like `125` — not Boolean. The `∑_i ∏_j` form has
  each monomial of degree `e = min(d,k) ≤ d` and, because `1 ≤ k < 2d` implies
  `k < 2·min(d,k)`, at most one block fits in `S`, so it is genuinely Boolean.
  I believe this is the intended construction (the literal formula in the prompt
  looks like a `∏`/`∑` transposition).
- "Not `ℓe`-juntas" is stated here as **`¬ IsJunta … m` for every `m` with
  `m + 1 ≤ ℓ·e`**, i.e. not an `(ℓe−1)`-junta. The function manifestly *is* an
  `ℓe`-junta (it depends only on the `ℓe` block coordinates), so the defensible
  claim is that it needs *all* `ℓe` of them; combined with `ℓ → ∞` this yields
  the "no uniform junta bound" conclusion.

Indexing: `blockCoord` sends `(i : Fin ℓ, j : Fin e)` to
`Fin.castLE hℓ (finProdFinEquiv (i, j)) : Fin n`, packing the `ℓ·e` block
coordinates into `{0, …, ℓe−1} ⊆ Fin n` (0-indexed analogue of `(i-1)e+j`). The
hypothesis `hℓ : ℓ * min d k ≤ n` is carried explicitly so the definition
type-checks; `hn : 2 * (ℓ * min d k) ≤ n` is the "`n ≥ 2ℓe`" hypothesis from the
statement.

## Uncertainties / guessed identifiers

- `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)` — name and orientation from
  memory. If it is `Fin (n * m)` or named differently (`finProdFinEquiv'`,
  `Equiv.finProdFinEquiv`), `blockCoord` needs `hℓ` adjusted to `min d k * ℓ ≤ n`
  or the equiv swapped. An alternative that avoids it: give `blockCoord` as an
  abstract injective `Fin ℓ → Fin e → Fin n` hypothesis.
- `Fin.castLE (h : a ≤ b) : Fin a → Fin b` — believed current.
- `MvPolynomial.support`, `MvPolynomial.totalDegree`, `MvPolynomial.eval`, and
  the `Finsupp` coercion `c i` for `c ∈ p.support` — standard, but the exact form
  of `IsMultilinear` (`∀ c ∈ p.support, ∀ i, c i ≤ 1`) may need
  `Finsupp.coe`/`⇑` massaging.
- I assume no ready-made Mathlib notion of "Boolean degree on the slice" exists,
  so `HasDegreeLE` is defined from scratch.
- `import Mathlib` (whole library) for a statement-only file.
