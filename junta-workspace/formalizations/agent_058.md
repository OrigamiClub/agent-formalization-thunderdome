# Agent 058 — formalization note

## What is stated

All statement-only, every theorem closes with `:= by sorry`; nothing is proved.

1. **`boolean_degree_d_junta_forward`** — the positive direction.
2. **`boolean_degree_d_junta_converse`** — sharpness of `k ≥ 2d`, stated abstractly
   ("there exists a bad function").
3. **`boolean_degree_d_junta_explicit`** — the explicit witnessing family that
   drives the converse.

## Encoding decisions

- **Slice**: `Slice n k := {S : Finset (Fin n) // S.card = k}`. Subtype of
  `Finset (Fin n)`; `S ∩ J` is literal `Finset` intersection, matching the
  problem's "depends only on `S ∩ J`".
- **Boolean codomain**: real-valued `f : Slice n k → ℝ` together with a predicate
  `IsBoolean f : ∀ S, f S = 0 ∨ f S = 1`. Real values chosen so that "degree"
  is a statement about a real polynomial with no coercion juggling.
- **Degree ≤ d** (`HasDegreeLE`): `∃ p : MvPolynomial (Fin n) ℝ` with
  `p.totalDegree ≤ d`, `p` multilinear, and `f S = eval (indicator S.1) p` for
  every slice point, where `indicator S i = if i ∈ S then 1 else 0`. Multilinearity
  is hand-rolled as `IsMultilinearPoly p : ∀ m ∈ p.support, ∀ i, m i ≤ 1`
  (every monomial square-free). Included to match the problem's "Terms" wording
  ("a multilinear real polynomial"); on the slice requiring multilinearity or not
  gives the same class of functions (reduce `xᵢ^r ↦ xᵢ` without raising total
  degree), so this is a faithful, harmless choice.
- **m-junta** (`IsJunta f m`): `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T,
  S.1 ∩ J = T.1 ∩ J → f S = f T`.
- **`m(d)`**: an existential `∃ m : ℕ` taken *after* fixing `d`, mirroring the
  phrasing "Let `d ≥ 1`. There is a constant `m(d)` …". Equivalent to pulling out
  a single `∃ m : ℕ → ℕ` in front; I kept the per-`d` form for readability.
- **Parameters `n, k, d`**: plain `ℕ`s, universally quantified inside each
  theorem; the ambient coordinate set is `Fin n`.

## The explicit family — deviation from the prompt

The prompt writes the witness as `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})` with
`e = min(d,k)`. Taken literally as a product of `ℓ` linear forms this cannot
witness "not an `m`-junta for *every* `m`":

- On `binom([n],k)` the product of sums is identically `0` as soon as `ℓ > k`
  (a `k`-set cannot meet more than `k` disjoint nonempty blocks), and for `ℓ = k`
  it is a fixed function on `k·min(d,k) < 2d²` coordinates — a constant-size
  junta. So no choice of `ℓ` beats a large `m`.

I therefore formalized the witness as the **sum of `ℓ` disjoint degree-`e`
monomials**

  `p = ∑_{i<ℓ} ∏_{c ∈ B i} X c`,   `f S = #{ i | B i ⊆ S }`,   `e = min d k`,

which I believe is the intended object (Σ and ∏ swapped in the prompt). This `f`:

- is Boolean on `binom([n],k)` **precisely because `k < 2d`**: with `e = min(d,k)`,
  two disjoint blocks have `2e > k` elements, so a `k`-set contains at most one
  whole block, hence `f S ∈ {0,1}`;
- has polynomial total degree `e = min(d,k) ≤ d`, multilinear (blocks disjoint);
- depends on all `ℓe` block-coordinates once `n ≥ 2ℓe`, so it is not an `m`-junta
  for any `m < ℓe`.

Since `ℓ` is free, sending `ℓ → ∞` gives the converse for every `m`. The
parenthetical "not `ℓe`-juntas" in the prompt is read as "not an `m`-junta for
any `m < ℓe`" (the function *is* an `ℓe`-junta, on `J = ⋃ B i`, and genuinely
depends on all `ℓe` of those coordinates).

- **Block indexing**: blocks are given abstractly as
  `B : Fin ℓ → Finset (Fin n)`, pairwise disjoint with `(B i).card = e`, rather
  than the concrete `B i = {i·e+1, …, i·e+e}`, to avoid `Fin n` index-arithmetic
  side goals in the statement. The concrete family is the special case.
- The explicit theorem exposes `p` and `f` as hypotheses (`hp`, `hf`) instead of
  `let`-bindings, purely for robustness of elaboration.

## Uncertainties / guessed identifiers

- Mathlib names used from memory: `MvPolynomial.totalDegree`,
  `MvPolynomial.eval`, `MvPolynomial.support`, `MvPolynomial.X`, `Pairwise`,
  `Finset.filter` (with `DecidablePred` for `B i ⊆ S.1` coming from `Finset`'s
  decidable subset instance). Signatures believed correct but not compiler-checked.
- `IsMultilinearPoly` is bespoke — Mathlib may have no ready `MvPolynomial`
  "multilinear" predicate; `m i` uses the `Fin n →₀ ℕ` coercion to a function.
- Whether Filmus–Ihringer's "degree" is defined with or without multilinearity —
  equivalent on the slice; I included multilinearity to match the prompt's Terms.
- No attempt to pin the actual value of `m(d)` (in the paper it matches the
  hypercube maximal-junta size); left as a bare existential.
