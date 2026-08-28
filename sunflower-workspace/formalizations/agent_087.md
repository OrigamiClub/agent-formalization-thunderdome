# Agent 087 — improved sunflower lemma, statement formalization

## Form chosen

Single `theorem improved_sunflower_lemma := by sorry` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
  ∀ W : Finset (Finset α), (∀ S ∈ W, S.card = k) →
    (C * r * Real.log (k + 1)) ^ k < (W.card : ℝ) →
      ∃ Y 𝒮, 𝒮 ⊆ W ∧ IsSunflower r Y 𝒮
```

plus a small auxiliary `structure IsSunflower r Y 𝒮`.

## Encoding decisions and why

- **Set representation:** `Finset (Finset α)` over an arbitrary ambient `α : Type*`
  with `[DecidableEq α]`. `Finset` gives `card` directly and makes members / petals
  distinct for free. `α` is quantified *inside* the existential for `C`, so the
  constant is genuinely absolute (one `C` for all types, `k`, `r`, `W`).
- **Sunflower predicate:** defined locally as a `structure` with three fields:
  `𝒮.card = r` (exactly `r` distinct petals), `Y ⊆ S` for every `S ∈ 𝒮` (genuine
  core), and `S ∩ T = Y` for distinct `S T ∈ 𝒮` ("pairwise intersections all
  coincide"). Pairwise-disjoint petals and the "in two ⇒ in all" property are
  logical consequences, so they are documented rather than posited.
- **"Contains a sunflower":** `∃ Y 𝒮, 𝒮 ⊆ W ∧ IsSunflower r Y 𝒮`.
- **Logarithm:** `Real.log` (natural log). Base is irrelevant since it only changes
  `C` by a constant factor.
- **k = 1 / k = 0 handling:** I use `Real.log (k + 1)` instead of `Real.log k`.
  With `Real.log k` the bound is `0` at `k = 1` (`Real.log 1 = 0`), which would
  falsely claim any nonempty family of singletons contains an `r`-petal sunflower.
  `Real.log (k + 1)` is `> 0` for all `k ≥ 1`; for `k ≥ 2` it differs from
  `Real.log k` by a bounded factor absorbed into `C`, so the statement is
  equivalent to the textbook `(C r log k)^k`. Hypothesis `0 < k` is also imposed
  ("positive integers k"); `k = 0` is thus excluded outright.
- **C:** existentially quantified at the front, together with `0 < C`.
- **Distinctness:** not stated explicitly; it follows from `Finset` membership and
  from `𝒮.card = r`.
- **Nonempty petals:** not required; noted as immaterial for `r ≥ 2`, `k ≥ 1`.
- **Cardinality:** `Finset.card` throughout (`S.card`, `W.card`, `𝒮.card`).

## Uncertainties

- I do not believe current Mathlib has a sunflower / Δ-system predicate or the
  Erdős–Rado sunflower lemma, so `IsSunflower` is defined from scratch. If a
  predicate such as `Finset.IsSunflower` does exist, this local one should be
  reconciled with it.
- Exact acceptability of `∀ (α : Type*) [DecidableEq α] ...` appearing under
  `∃ C : ℝ, 0 < C ∧ ...` — this is a universe-polymorphic `∀` into `Prop`; I
  believe it elaborates, but have no compiler to confirm. Falling back to
  `α : Type` (universe 0) is a safe alternative if needed.
- Coercions: `(r : ℝ)`, `((k : ℝ) + 1)`, `(W.card : ℝ)` written explicitly; the
  `^ k` is `Monoid.npow` (real base, `ℕ` exponent).
