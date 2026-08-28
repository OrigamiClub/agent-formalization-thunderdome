# Agent 014 — Improved sunflower lemma, statement only

## Form chosen

One `theorem improved_sunflower_lemma := by sorry`, with the absolute constant `C`
**existentially quantified inside** the statement (`∃ C : ℝ, 0 < C ∧ …`). This is
the most self-contained reading of "there is an absolute constant `C`" and avoids
committing to a particular numeric value.

A helper predicate `IsSunflower r Y P` is defined.

## Encoding decisions

- **Set representation.** Sets are `Finset α` over an ambient type `α` with
  `[DecidableEq α]`. A *family* of sets is `W : Finset (Finset α)`. This makes
  `|W|`, membership, and the sunflower subfamily all finite and decidable without
  carrying separate finiteness hypotheses.
- **Sunflower predicate.** Defined explicitly with an explicit core `Y`:
  `P.card = r` together with `∀ S₁ ∈ P, ∀ S₂ ∈ P, S₁ ≠ S₂ → S₁ ∩ S₂ = Y`.
  This is verbatim the definition given in the task ("a core set `Y` with
  `S_i ∩ S_j = Y` for every `i ≠ j`"). I did not assume a Mathlib sunflower
  predicate exists (I am not confident one does); the definition is local.
- **Distinctness of members.** Free: the `r` sets are the elements of the
  `Finset` `P`, and `P.card = r` pins the count. No separate injectivity
  hypothesis is needed.
- **Petals nonempty.** Not required. For `r ≥ 2` the condition `S₁ ∩ S₂ = Y`
  forces `Y ⊆ Sᵢ`, and at most one member can equal `Y`, so at most one petal is
  empty; the classical lemma does not demand nonempty petals, so neither do I.
- **Core ⊆ petals.** Not added to `IsSunflower`; it is a consequence of the
  pairwise-intersection condition when `r ≥ 2`, and keeping the definition minimal
  matches the task's wording.
- **Cardinality.** `Finset.card` throughout (`S.card = k`, `P.card = r`,
  `W.card`).
- **The bound.** `(C * r * Real.log k) ^ k < W.card`, with `r`, `k` cast to `ℝ`
  inside, `Real.log` the natural logarithm, and `W.card` cast to `ℝ`. The `^ k`
  is `Monoid.npow` (natural exponent), which is the intended meaning.
- **Logarithm choice / small `k`.** `Real.log` (natural log). `k = 0` is excluded
  and `k = 1` is excluded via the hypothesis `2 ≤ k`, because `Real.log 1 = 0`
  makes the RHS `0` and the statement false there (`f(1,r) = r`).
  Bell–Chueluecha–Warnke likewise state the `(C r log k)^k` bound for `k ≥ 2`.
  The base of the log is irrelevant to the truth of the statement since `C` is
  existentially quantified (changing base rescales `C`).
- **`r`.** Kept as a positive integer via `1 ≤ r`.
- **Conclusion.** `∃ Y, ∃ P, P ⊆ W ∧ IsSunflower r Y P` — an actual subfamily of
  the given family is a sunflower.

## Uncertainties

- Whether Mathlib already has a `Sunflower` / `IsSunflower` definition or the
  lemma itself. I assumed not and defined the predicate locally; if one exists the
  name and exact shape may differ.
- Exact Mathlib spelling of coercions (`(k : ℝ)`, `(W.card : ℝ)`) and whether
  `Real.log` needs `open Real` — written defensively with explicit casts and
  fully-qualified `Real.log`.
- Faithfulness tradeoff: the task says "for all positive integers `k` and `r`",
  but the literal `Real.log k` bound is false at `k = 1`, so I restricted to
  `2 ≤ k` rather than silently altering the log argument (e.g. `Real.log (k+1)`).
