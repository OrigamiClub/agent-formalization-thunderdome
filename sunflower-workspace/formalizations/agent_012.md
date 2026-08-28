# Agent 012 — improved sunflower lemma, statement formalization

## Form chosen

Single theorem `ImprovedSunflower.improved_sunflower_lemma`, the "dense family"
version:

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α), (∀ s ∈ W, s.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
      ∃ core petals, petals ⊆ W ∧ IsSunflower r core petals
```

Plus an auxiliary `structure IsSunflower r core petals` capturing "sunflower with
`r` petals".

## Encoding decisions and why

- **Set representation.** `Finset α` for individual sets; a family is
  `Finset (Finset α)` over an arbitrary ambient type `α`. `Finset` makes
  "finite family" and "cardinality exactly `k`" immediate, and membership of the
  family being a `Finset` gives distinctness of the `r` petals for free.
  `[DecidableEq α]` is needed for `Finset.inter` (`∩`).

- **`C` is absolute.** `∃ C` is the outermost binder and `α, k, r, W` are all
  quantified *inside* it, so `C` cannot depend on the ambient type or on
  `k, r`. (Putting `α` as an outside section variable would have let `C` depend on
  `α`, a strictly weaker claim.)

- **Sunflower definition.** Explicit core. Fields:
  `card_petals : petals.card = r` (exactly `r` distinct petals),
  `pairwise_inter_eq_core : ∀ S ∈ petals, ∀ T ∈ petals, S ≠ T → S ∩ T = core`,
  and `core_subset_petals : ∀ S ∈ petals, core ⊆ S`.
  The third field is redundant for `r ≥ 2` (it follows from the second) but is
  kept so the statement is unambiguous for all `r` and matches "there is a core
  set `Y` with `S_i ∩ S_j = Y`". Pairwise-disjoint nonempty petals `S \ core`
  are a consequence for `r ≥ 2`, not separately imposed.

- **Petals nonempty.** Not imposed; automatic for `r ≥ 2` with `k`-sets (distinct
  `k`-sets meeting in `core` force `core ⊊ S`).

- **Logarithm.** `Real.log` (natural log). The base only changes `C`, and the
  source papers write `log` base-free. `k` is coerced `ℕ → ℝ`.

- **Small `k`.** Hypothesis `2 ≤ k`, so `Real.log k > 0`. At `k = 1` the RHS is
  `0` and the inequality `0 < |W|` cannot force an `r`-petal sunflower (any `r`
  distinct singletons are already one), so the statement is false there; the
  degenerate positive-integer case `k = 1` is excluded rather than patched (e.g.
  via `log (k+1)`). `k = 0` similarly excluded.

- **`r`.** Hypothesis `1 ≤ r`.

- **Conclusion.** `∃ core, ∃ petals ⊆ W, IsSunflower r core petals`. Distinctness
  of petals is inside `IsSunflower` via `Finset` + `card_petals`.

- **Cardinality.** `Finset.card` throughout; comparison `(W.card : ℝ)` against the
  real RHS.

## Uncertainties / guessed identifiers

- **Whether Mathlib already has a sunflower notion.** I did not find one from
  memory and defined `IsSunflower` locally so the file is self-contained. If
  Mathlib does have it, plausible names are `Finset.IsSunflower`,
  `SetFamily.IsSunflower`, or a file `Mathlib/Combinatorics/SetFamily/Sunflower.lean`;
  the local definition should be dropped in favour of that.
- `Real.log` is the correct Mathlib identifier for the natural logarithm (high
  confidence).
- Blanket `import Mathlib` used for safety rather than pinpointing modules.
- Elaboration of instance-implicit/implicit binders (`∀ {α} [DecidableEq α] …`)
  inside the body of `∃ C, …` is believed valid Lean 4; not machine-checked (no
  compiler available).
- The exact bound in the literature is stated up to the absolute constant; I did
  not commit to `1 ≤ C` (only `0 < C`), which is enough.
