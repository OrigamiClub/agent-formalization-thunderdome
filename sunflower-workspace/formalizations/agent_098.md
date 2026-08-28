# Agent 098 — improved sunflower lemma (statement only)

## Form chosen

A single `theorem improved_sunflower_lemma : ∃ C : ℝ, 0 < C ∧ ∀ ... := by sorry`.

- Sets: `Finset (Finset α)` over an ambient `Type` with `[DecidableEq α]`. The
  family `W` is a `Finset (Finset α)`; each member is a `Finset α` of card `k`.
- Sunflower: my own auxiliary predicate `IsSunflower 𝒮 Y`, defined by "all
  pairwise intersections of distinct members equal `Y`". Petal count = `𝒮.card`.
- Conclusion: `∃ 𝒮 ⊆ W, ∃ Y, 𝒮.card = r ∧ IsSunflower 𝒮 Y`.

## Encoding decisions and why

- **Constant `C`**: existentially quantified at the very front, before the
  quantifiers over `α, k, r, W`. This is what "absolute constant" means — one `C`
  works uniformly. Stated with `0 < C`.
- **`α : Type`** (not `Type*`): the universe is irrelevant for the mathematics and
  keeping it in `Type` keeps `C` unambiguously ahead of everything. Instance
  `[DecidableEq α]` is needed for `Finset` intersection / `∩` on `Finset α`.
- **Logarithm**: `Real.log` (natural log). Base choice is absorbed into `C`, so
  any fixed base gives an equivalent statement; natural log is the Mathlib
  default and needs no extra import.
- **`k` / `r` range**: hypotheses `2 ≤ k` and `1 ≤ r`. The `2 ≤ k` restriction
  sidesteps `Real.log 1 = 0` (which would make the bound `0` and the statement
  false for `k = 1, r ≥ 2`). `1 ≤ r` keeps "r petals" meaningful.
- **The bound**: `(C * (r:ℝ) * Real.log k) ^ k < (W.card : ℝ)`, a strict
  inequality with `W.card` cast to `ℝ`, matching `|W| > (C r log k)^k`.
- **Distinctness of members**: automatic — `W` and `𝒮` are `Finset`s, and
  `𝒮.card = r` pins down exactly `r` distinct sets.
- **Petals nonempty**: not stated; it follows automatically, since distinct sets
  `S ≠ T` with `S ∩ T = Y` force `Y ⊊ S`.
- **Subfamily**: expressed as `∃ 𝒮 ⊆ W, ...` (i.e. `𝒮 ⊆ W` as Finsets).

## Uncertainties

- **Mathlib sunflower predicate**: I defined `IsSunflower` locally to be safe. I
  believe Mathlib may have a similar notion (I would guess a name like
  `Finset.IsSunflower` / `Set.IsSunflower` in
  `Mathlib/Combinatorics/SetFamily/`), possibly with signature
  `IsSunflower (𝒜 : Finset (Finset α)) (t : Finset α) : Prop` given by the same
  "pairwise intersections equal `t`" condition. Unverified — no compiler
  available. If it exists, the local definition can be replaced by it directly.
- `import Mathlib` is used for simplicity; the real dependencies are `Finset` and
  `Real.log`.
- The `∀ (α : Type) [DecidableEq α] ...` binder appearing under `∃ C, 0 < C ∧ ...`
  should parse fine in Lean 4, but I could not machine-check it.
- Whether the community-standard statement fixes `k ≥ 2` or instead writes
  `Real.log (k+1)` / `max (Real.log k) 1` to cover `k = 1`; I chose the `k ≥ 2`
  hypothesis as the least intrusive faithful option.
