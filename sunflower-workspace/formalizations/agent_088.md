# agent_088 — improved sunflower lemma (statement only)

## Form chosen

A single `theorem improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ (α) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α),
    (∀ A ∈ W, A.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ T ⊆ W, ∃ Y : Finset α, IsSunflowerWith r T Y
```

plus an auxiliary predicate `ImprovedSunflower.IsSunflowerWith`.

## Encoding decisions and why

- **Set representation.** `Finset (Finset α)` over an arbitrary ambient type `α` with
  `[DecidableEq α]`. This gives distinctness of the family's members for free (and of any
  subfamily `T ⊆ W`), so no separate injectivity/distinctness hypothesis is needed. Each
  member set has `A.card = k` (exact cardinality), stated with `Finset.card`.

- **Sunflower definition.** Own predicate `IsSunflowerWith r petals core :=
  petals.card = r ∧ (∀ A ∈ petals, ∀ B ∈ petals, A ≠ B → A ∩ B = core)`. This is the
  "explicit core, all pairwise intersections coincide" formulation. `petals.card = r`
  pins down the petal count and forces `r` distinct sets. The disjoint-petals and
  "element in ≥2 members ⇒ in all members" properties are consequences, so they are noted
  in the docstring but not imposed.

- **Petals nonempty.** Not required. For `r ≥ 2`, `A ≠ B` with `A ∩ B = core` already
  forces `core ⊊ A`, so each set-theoretic petal `A \ core` is nonempty automatically.

- **Which logarithm.** `Real.log` (natural log). The base only rescales the absolute
  constant `C`, which is existentially quantified, so the choice is immaterial to the
  truth of the statement. Casts `(r : ℝ)`, `(k : ℝ)`, `(W.card : ℝ)` are explicit.

- **k = 0 / k = 1.** Excluded via hypothesis `2 ≤ k`. For `k ≤ 1` the bound is genuinely
  false: `f(1, r) = r` sets are needed to force a sunflower, but `(C · r · log 1)^1 = 0`.
  For `k ≥ 2`, `Real.log k ≥ Real.log 2 > 0`, so the bound is meaningful and positive.

- **r.** Hypothesis `1 ≤ r` (a "sunflower with `r` petals" is only interesting for
  `r ≥ 1`; `r = 1` and `r = 2` are already covered by the predicate).

- **The constant `C`.** Existentially quantified *inside* the theorem, together with
  `0 < C`, and placed outermost so it cannot depend on `α, k, r, W`. This matches
  "there is an absolute constant `C`".

- **Inequality direction.** `|W| > (C r log k)^k` is written as
  `(C * r * Real.log k) ^ k < (W.card : ℝ)` (strict), matching the problem statement.

- **Conclusion.** `∃ T ⊆ W, ∃ Y, IsSunflowerWith r T Y`: a subfamily of `W` that is a
  sunflower with `r` petals and some core `Y`.

## Uncertainties

- **Mathlib sunflower predicate.** Mathlib has a sunflower development (I believe
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean`, contributing something like
  `Finset.IsSunflower` / `IsSunflower r t 𝒮` defined via `Set.Pairwise (· ∩ · = t)` and a
  classical `(r-1)^k · k!` existence lemma). I was not confident of the exact name and
  argument order, so I defined a local predicate `IsSunflowerWith` instead of relying on
  it. If the Mathlib name is `IsSunflower`, this statement could be rephrased in terms of
  it directly.

- **`import Mathlib`.** Used the umbrella import for safety/self-containment rather than
  pinpointing the minimal set (`Mathlib.Analysis.SpecialFunctions.Log.Basic`,
  `Mathlib.Data.Finset.Card`, ...).

- **Universe-polymorphic `∀ (α : Type*)` under an existential.** I believe this elaborates
  fine in Lean 4 / Mathlib (the theorem becomes universe-polymorphic); not machine-checked
  here.

- **Coercion of `Real.log (k : ℝ)`** with `k : ℕ` — explicit cast used; should be fine.
