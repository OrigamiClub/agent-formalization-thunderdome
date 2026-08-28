# agent_018 — improved sunflower lemma, statement only

## Form chosen

A single closed `theorem improved_sunflower_lemma : ∃ C : ℝ, 0 < C ∧ ... := by sorry`,
plus one auxiliary `structure IsSunflower`.

- Ambient type: arbitrary `α : Type*` with `[DecidableEq α]` (needed for `Finset` `∩`).
- A "set" is a `Finset α`; the family `W` is a `Finset (Finset α)`.
- Uniform size: hypothesis `∀ S ∈ W, S.card = k` (cardinality via `Finset.card`).
- Bound: `(C * r * Real.log (k + 1)) ^ k < (W.card : ℝ)`, i.e. strict `|W| > RHS`.
- Conclusion: `∃ 𝒜 ⊆ W, ∃ Y, 𝒜.card = r ∧ IsSunflower 𝒜 Y`.

## `IsSunflower 𝒜 Y`

A `structure` with two fields:
1. `core_subset`: `Y ⊆ S` for every `S ∈ 𝒜`;
2. `pairwise_inter`: `S ∩ T = Y` for all distinct `S, T ∈ 𝒜`.

Number of petals = `𝒜.card`. "Sunflower with `r` petals" is expressed as
`∃ Y, 𝒜.card = r ∧ IsSunflower 𝒜 Y`.

Rationale: the "pairwise intersections all coincide (and equal the core)"
formulation is the most elementary and needs no quotient/choice to name `Y`.
Field 1 is logically redundant once `2 ≤ 𝒜.card` (then `Y = S ∩ T ⊆ S`), but
it fixes `Y` in the trivial cases `𝒜.card ≤ 1`; keeping it makes the predicate
well-behaved without a side condition `2 ≤ r`. Pairwise-disjointness of the
petals `S \ Y` follows from field 2, so it is not stated separately.
Distinctness of the `r` members is automatic: they are elements of a `Finset`
and `𝒜.card = r`.

## Encoding decisions and why

- **Finset over an ambient type**, not `Set` + finiteness: gives free
  distinctness, decidable `card`, and a genuinely finite `|W|` as a `ℕ`.
- **`Real.log`** (natural log). Changing the logarithm base multiplies the
  argument by a constant, absorbed into `C`; `Real.logb 2` or `Nat.log 2`
  would be equally valid. Real-valued log keeps the RHS a clean real power
  `(... : ℝ) ^ k` compared against `(W.card : ℝ)`.
- **`log (k + 1)` instead of `log k`**: at `k = 1`, `log 1 = 0` makes
  `(C r log k)^k = 0`, and `|W| > 0` does *not* force an `r`-sunflower, so the
  literal formula is false for `k = 1`. Using `k + 1` keeps the statement true
  for *all* positive `k` while only perturbing the absolute constant for large
  `k`. An equally acceptable alternative would keep `Real.log k` verbatim and
  add the hypothesis `2 ≤ k`.
- **`C` existentially quantified inside** the theorem (rather than a section
  variable or named `def`): makes the statement self-contained and parameter
  free, matching "there is an absolute constant `C`".
- **Strict inequality** `RHS < |W|` mirrors the "`|W| >`" in the source.
- `0 < k` and `0 < r` hypotheses record "positive integers".

## Uncertainties / guessed identifiers

- I do not believe current Mathlib contains a sunflower predicate or the
  sunflower lemma, so `IsSunflower` is defined here from scratch inside
  `namespace Agent018` to avoid any name clash. If Mathlib does have one
  (plausible names: `Finset.IsSunflower`, `IsSunflower`, `SetFamily.Sunflower`),
  this definition should be replaced by it.
- `Real.log`, `Finset.card`, the `∃ x ⊆ s, _` and `∃ x ⊆ s, ∃ y, _` binder
  notations, and `Finset` `∩` (requiring `[DecidableEq α]`) are all standard
  and used as-is; I am confident these exist. Not machine-checked (no compiler
  available).
- Placing `∀ (α : Type*) [DecidableEq α] ...` under `∃ C : ℝ, 0 < C ∧ ...`
  introduces a universe parameter on the theorem; this is fine but makes the
  statement universe-polymorphic in `α`.
