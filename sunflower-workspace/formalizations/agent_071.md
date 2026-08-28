# Agent 071 — improved sunflower lemma (statement only)

## Form chosen

A single `theorem improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ (α : Type*) [DecidableEq α] (k r : ℕ),
  2 ≤ k → 1 ≤ r → ∀ W : Finset (Finset α),
  (∀ s ∈ W, s.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  HasSunflower W r
```

plus two supporting `def`s: `IsSunflower T Y` and `HasSunflower W r`.

## Encoding decisions and rationale

- **Set representation.** `Finset (Finset α)` over an ambient type `α` with
  `[DecidableEq α]`. Everything finite is then automatic (`Finset.card`, no separate
  finiteness hypothesis), and `∩` on `Finset` is available. `α` is universally
  quantified *inside* the theorem, after `∃ C`, so `C` is a true absolute constant not
  depending on the carrier type.

- **"Each set has cardinality exactly k".** `∀ s ∈ W, s.card = k`. Uniform `k`-sets, as
  in the statement.

- **Sunflower predicate.** Defined locally as
  `IsSunflower T Y := ∀ ⦃s⦄ ∈ T, ∀ ⦃t⦄ ∈ T, s ≠ t → s ∩ t = Y`
  i.e. the "all pairwise intersections coincide (with an explicit core `Y`)" form,
  restricted to distinct pairs. I chose an explicit core `Y` rather than "pairwise
  intersections all equal" because it reads closest to the informal definition and makes
  the core available to any downstream proof. Mathlib may already have such a predicate
  (I believe there is a `Mathlib/Combinatorics/…/Sunflower.lean` with something like
  `Finset.IsSunflower : Finset (Finset α) → Finset α → Prop`, from the classical
  Erdős–Rado bound formalization). I did **not** rely on it: the exact name/signature is
  a guess, so a self-contained local definition is safer for a statement-only artifact.
  If the Mathlib predicate exists and matches, `IsSunflower` here can be swapped for it.

- **"Contains a sunflower with r petals".** `HasSunflower W r` asks for a subfamily
  `T ⊆ W` with `T.card = r` that is a sunflower. Members of `T` are distinct for free
  (it is a `Finset`), and `T.card = r` fixes the petal count, so no separate
  distinctness hypothesis is needed.

- **Petals nonempty?** Not required. The combinatorial sunflower function counts
  sunflowers where at most one petal may be empty; adding `∀ s ∈ T, (s \ Y).Nonempty`
  would be a (mild) strengthening of the conclusion and is omitted.

- **Logarithm.** `Real.log` (natural log). The base only rescales `C`, which is
  existential, so the base is immaterial. `k` is cast `(k : ℝ)` inside `Real.log`.

- **Constant `C`.** Existentially quantified with `0 < C`, matching "there is an
  absolute constant `C`". Placed outermost so it precedes `α, k, r, W`.

- **`k = 0, 1` corner.** For `k ≤ 1`, `Real.log k = 0` (`Real.log` is `0` at `0` and at
  `1`), so `(C·r·log k)^k` degenerates and the literal statement becomes false (e.g.
  many distinct singletons, large `r`). I guard with `2 ≤ k`. An alternative that keeps
  all `k ≥ 1` would replace `Real.log k` by `Real.log k + 1` or `max (Real.log k) 1`;
  I preferred the clean `Real.log k` with the `2 ≤ k` hypothesis, which is how the
  refined bound is usually quoted.

- **`r`.** Guarded by `1 ≤ r` for cleanliness; the statement is uninteresting/trivial
  below that.

- **Inequality direction.** Written `RHS < (W.card : ℝ)`, i.e. `|W| > (C r log k)^k`.

## Uncertainties

- Whether Mathlib already provides a sunflower predicate and, if so, its exact name and
  argument order (`Finset.IsSunflower` is my best guess). Handled by using a local
  definition instead.
- Whether elaboration needs the explicit casts I wrote (`(r : ℝ)`, `(k : ℝ)`,
  `(W.card : ℝ)`); I inserted them explicitly to be safe.
- `import Mathlib` (the whole library) is used for simplicity; only `Mathlib.Data.Finset.*`
  and `Mathlib.Analysis.SpecialFunctions.Log.Basic` are actually needed.
- Whether to use strict-implicit `⦃ ⦄` binders in `IsSunflower` (chosen so the predicate
  unfolds conveniently); plain `∀ s ∈ T` would also be fine for a statement.
