# agent_095 — improved sunflower lemma (statement)

## Form chosen

One `theorem improved_sunflower_lemma := by sorry`, plus two auxiliary `def`s
(`IsSunflower`, `HasSunflower`). No Mathlib sunflower API is assumed to exist.

Shape:

```
∃ C : ℝ, 0 < C ∧
  ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 1 ≤ k → 1 ≤ r →
    ∀ W : Finset (Finset α),
      (∀ S ∈ W, S.card = k) →
      (C * r * Real.log (k + 1)) ^ k < (W.card : ℝ) →
      HasSunflower W r
```

## Encoding decisions and rationale

- **Set family**: `W : Finset (Finset α)` over an arbitrary `α` with
  `[DecidableEq α]`. Finset gives a clean `.card`, a clean `𝒮 ⊆ W`, and makes
  distinctness of members automatic (no separate injectivity/distinctness
  hypothesis needed). `∩` on `Finset` needs `DecidableEq`.
- **Absolute constant**: `∃ C : ℝ, 0 < C ∧ …` with the `∃ C` placed *outside*
  the quantifier over `α`, `k`, `r`. This is the faithful reading of "absolute
  constant" — `C` cannot depend on the ambient type or on `k`, `r`. Consequently
  `α` is universally quantified *inside* the statement body (a nested
  `∀ (α : Type*) [DecidableEq α]`), which is slightly unusual but valid.
- **Sunflower predicate**: `IsSunflower petals core` :=
  `∀ S ∈ petals, ∀ T ∈ petals, S ≠ T → S ∩ T = core`
  (the "all pairwise intersections coincide" form, with an explicit core).
  The consequences in the prose (element in ≥2 sets ⇒ in all; petals `S \ core`
  pairwise disjoint) follow from this and are not separately stated.
- **Petals nonempty**: not imposed. With `petals.card ≥ 2` one gets
  `core = S ∩ T ⊆ S` automatically, and since here all members have the same
  card `k`, distinctness forces `core ⊊ S`, so petals are nonempty anyway.
  Kept the definition minimal; noted this in the Lean docstring.
- **"contains a sunflower with r petals"**: `HasSunflower W r` :=
  `∃ 𝒮 ⊆ W, 𝒮.card = r ∧ ∃ Y, IsSunflower 𝒮 Y`. Exactly `r` petals
  (`𝒮.card = r`), as an `r`-element subfamily of `W`.
- **Cardinality**: `Finset.card` throughout, cast to `ℝ` only for the final
  inequality.
- **Logarithm**: `Real.log` (natural log). Base is irrelevant to the theorem
  (change of base is a constant factor absorbed into `C`).
- **k = 0 / k = 1 edge**: handled by (a) hypothesis `1 ≤ k`, and (b) writing
  `Real.log ((k : ℝ) + 1)` instead of `Real.log k`. This avoids the degenerate
  `log 1 = 0` (which would make the threshold `0` and the statement false for
  `k = 1`) and `log 0`. The `k ↦ k+1` shift inflates the bound by at most a
  constant factor and preserves the `(C r log k)^k` rate, so it is still the
  improved bound. `r` ranges over all positives (`1 ≤ r`); `r ≥ 3` is the
  substantive range.
- **Threshold direction**: strict `<` between the real bound and `(W.card : ℝ)`,
  matching "|W| > (C r log k)^k".

## Uncertainties

- Whether Mathlib currently has a `Sunflower` / `IsSunflower` definition. I did
  not assume one and defined my own; if one exists the name/shape may differ
  (I would expect something like `Finset.IsSunflower` or a structure in
  `Mathlib.Combinatorics.SetFamily`).
- `import Mathlib` (blanket) used for safety; the statement only needs
  `Mathlib.Analysis.SpecialFunctions.Log.Basic` (for `Real.log`) and
  `Mathlib.Data.Finset.*`.
- Syntactic point: a mid-`∀` instance binder `[DecidableEq α]` inside a
  term-level proposition and a `∀ (α : Type*)` inside the theorem body are both
  valid Lean 4 but stylistically uncommon; an alternative is to fix `α := ℕ`
  (every finite set family embeds into `ℕ`) and keep `∃ C` at the front, which
  would be simpler but marginally less general on its face.
- Coercions `(r : ℝ)`, `((k : ℝ) + 1)`, `(W.card : ℝ)` written explicitly to
  avoid elaboration ambiguity; exact minimal cast placement not compiler-checked.
