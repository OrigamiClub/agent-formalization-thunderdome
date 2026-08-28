# Agent 099 — improved sunflower lemma, statement only

## Form chosen

A single `theorem improved_sunflower_lemma : ... := by sorry`, preceded by one
auxiliary definition `IsSunflower`.

Shape:

```
∃ C : ℝ, 0 < C ∧
  ∀ {α} [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
    ∀ W : Finset (Finset α),
      (∀ s ∈ W, s.card = k) →
      (C * r * Real.log k) ^ k < (W.card : ℝ) →
      ∃ core 𝒮, 𝒮 ⊆ W ∧ IsSunflower r core 𝒮
```

## Encoding decisions

- **Set representation.** Sets are `Finset α` over an ambient type `α`; the family
  `W` is a `Finset (Finset α)`. This gives a genuinely finite family with no extra
  finiteness hypothesis, and `Finset.card` for all cardinalities.
- **Sunflower predicate.** Mathlib has no sunflower definition (checked: no match
  for "unflower" anywhere in a local Mathlib checkout), so `IsSunflower r core
  petals` is defined here: `petals.card = r` together with `A ∩ B = core` for all
  distinct `A, B ∈ petals`. Using a `Finset (Finset α)` makes the `r` members
  automatically distinct; `petals.card = r` fixes the count, so no separate
  injectivity/distinctness clause is needed.
- **Core.** Given explicitly (existentially quantified in the conclusion) rather
  than via "all pairwise intersections coincide". The `A ∩ B = core` formulation
  immediately yields the standard consequences (elements in ≥ 2 members lie in
  `core`; petals `A \ core` pairwise disjoint).
- **Petals nonempty?** Not required — matches the "family of `r` distinct sets"
  definition in the problem statement. At most one member can equal `core`.
- **Logarithm.** `Real.log` (natural log). The RHS `(C * r * Real.log k) ^ k` is
  real; compared to `W.card` by coercing the `Nat` to `ℝ`.
- **k = 1 / k = 0.** `k = 0` excluded by `0 < k`. For `k = 1`, `Real.log 1 = 0`,
  so the premise becomes `0 < (W.card : ℝ)`; correctness there is carried by the
  freedom in the existential constant `C`. The classical statement is really about
  `k ≥ 2`; I kept `0 < k` to match "positive integers k and r" verbatim rather
  than inserting `max 2 k` or `k + 1` inside the log.
- **Constant C.** Existentially quantified *inside* the theorem (`∃ C, 0 < C ∧ …`),
  the most direct reading of "there is an absolute constant".
- **r.** Hypothesis `0 < r` ("positive integers r"). For `r = 1` any single set is
  trivially a sunflower; the content is large `r`.
- **Conclusion.** Exhibits a subfamily `𝒮 ⊆ W` with `IsSunflower r core 𝒮`, i.e.
  `W` *contains* a sunflower.
- **Strict inequality.** Used `<` (`RHS < |W|`), matching "|W| > (C r log k)^k".

## Uncertainties

- Only identifiers used are `Real.log`, `Finset.card`, `Finset.instInter`
  (`A ∩ B`), and `Finset` subset — all stable in current Mathlib. `import Mathlib`
  is used to avoid guessing precise module paths.
- Whether to bound `log k` away from `0`/negatives for small `k` is a genuine
  modelling choice; I left it faithful to the informal statement and documented
  the `k = 1` degeneracy.
- Placing `∀ {α : Type*} [DecidableEq α] …` under an `∃ C : ℝ` is well-formed in
  Lean 4 (the constant is chosen uniformly, before `α`), which is exactly the
  intended "absolute constant" reading.
- Not proved (statement-only task); ends in `:= by sorry`.
