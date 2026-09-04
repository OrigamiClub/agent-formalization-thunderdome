# Agent 086 — formalization note

## What I stated

Three `sorry`-terminated theorems in `agent_086.lean`:

1. **`boolean_degree_le_isJunta`** — the forward / main direction. For every `d ≥ 1`
   there **exists** `m : ℕ` such that for all `n, k` with `2d ≤ k` and `2k ≤ n`, every
   Boolean degree-`≤ d` function on the slice is an `m`-junta.
2. **`exists_boolean_degree_le_not_isJunta`** — the converse in bare existential form:
   for `1 ≤ k < 2d` and every `m`, some `n ≥ 2k` carries a Boolean degree-`≤ d`
   non-`m`-junta.
3. **`blockWitness_not_isJunta`** — the converse together with the explicit witnessing
   family, indexed by `ℓ`.

I stated both directions plus the explicit family, to expose my reading of the witness
construction.

## Encoding decisions

- **Slice**: `abbrev Slice n k := { S : Finset (Fin n) // S.card = k }`. The subtype of
  `Finset (Fin n)` was the least-friction choice for expressing both "junta" (needs
  `S ∩ J`) and the polynomial evaluation.
- **Coordinates / ambient set**: `n, k, d, ℓ` are all plain `ℕ` universally quantified
  inside each theorem. `m(d)` is an **existential** `∃ m : ℕ` inside statement 1
  (faithful to "there is a constant `m(d)`"); I did not commit to an explicit `ℕ → ℕ`.
- **Boolean codomain**: real-valued `f : Slice n k → ℝ` plus `IsBooleanValued f`
  (`∀ S, f S = 0 ∨ f S = 1`). Keeping `f` real-valued lets "degree" be stated directly
  via polynomial evaluation without a coercion layer.
- **Degree ≤ d** (`HasDegreeLE`): there is `p : MvPolynomial ℕ ℝ` that is
  (a) multilinear — every monomial in `p.support` is squarefree, `∀ m ∈ p.support, ∀ i, m i ≤ 1`;
  (b) `p.totalDegree ≤ d`;
  (c) agrees with `f` on every slice element after evaluation at the indicator point.
  Variables are indexed by **`ℕ`** rather than `Fin n` deliberately: it removes all
  `i < n` bound-proof obligations from the `blockWitness` definition. Indicator
  coordinates `i ≥ n` are pinned to `0` by `sliceIndicator`, so out-of-range variables
  are harmless.
- **Indicator** (`sliceIndicator n k S : ℕ → ℝ`): `1` on elements of `S` (via
  `⟨i, h⟩ : Fin n` when `i < n`), else `0`.
- **m-junta** (`IsJunta`): `∃ J : Finset (Fin n)`, `J.card ≤ m`, and
  `∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`. This is the "value depends only on `S ∩ J`"
  formulation.
- **Explicit family** (`blockWitness d k ℓ`): I used
  `∑ i ∈ range ℓ, ∏ j ∈ range (min d k), X (i * min d k + j)` — an OR of `ℓ` disjoint
  size-`e` block-ANDs, `e = min d k`. The `(i-1)e + j` indexing of the source (with
  `i ∈ [1,ℓ]`, `j ∈ [1,e]`) becomes `i * e + j` with `i ∈ range ℓ`, `j ∈ range e`,
  covering `0 … ℓe-1`.

## Uncertainties and deviations

- **Sum-of-products vs product-of-sums.** The source describes the witnesses as
  `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`. Evaluated on the slice this product is
  **not** `{0,1}`-valued in general: e.g. `d = 2`, `k = 3`, `e = 2`, `ℓ = 2`, and
  `S = {0,1,2}` gives factor values `2` and `1`, product `2`. The **sum of block
  products** `∑_i ∏_j x_{(i-1)e+j}` (= number of blocks fully contained in `S`) *is*
  Boolean here, because `k < 2·min(d,k)` (a consequence of `k < 2d` together with
  `e = min(d,k)`) forbids two disjoint `e`-blocks inside a `k`-set. I formalized the
  sum-of-products reading and believe the source's "∏(∑…)" is a transcription swap of
  the two symbols. This is my most significant interpretive choice.
- **"not `ℓe`-juntas".** Taken literally this is false: `blockWitness` reads only the
  `ℓe` block coordinates, so it *is* an `ℓe`-junta. I encoded the evidently-intended
  claim, **`¬ IsJunta (ℓ * min d k - 1) f`** ("not an `(ℓe−1)`-junta", i.e. depends on
  all `ℓe` block coordinates). With `ℓ` unbounded this still defeats every fixed `m`.
- **Multilinearity predicate.** I did not find a ready-made `MvPolynomial.IsMultilinear`
  in Mathlib, so I spelled it out as squarefree support. If a named predicate exists,
  that conjunct should be replaced by it. Note that on `{0,1}` inputs multilinearity is
  free (does not change the function or its degree), so dropping the conjunct entirely
  would also be a defensible statement.
- **Mathlib identifiers used** (believed current): `MvPolynomial`, `MvPolynomial.X`,
  `MvPolynomial.eval`, `MvPolynomial.totalDegree`, `MvPolynomial.support` (elements
  `m : ℕ →₀ ℕ`, with `m i : ℕ`), `Finset.range`, `∑ … ∈ …`, `∏ … ∈ …`, `Finset.card`,
  `Finset.instInter` for `S.1 ∩ J`. Not compiler-checked.
- **`n ≥ 2k` for the converse.** The source says "there exist `n ≥ 2k`"; I carry
  `2 * k ≤ n` as a conjunct on the witnessed `n` in statement 2, and the stronger
  `2 * (ℓ * min d k) ≤ n` hypothesis in statement 3 (the source's `n ≥ 2ℓe`).
