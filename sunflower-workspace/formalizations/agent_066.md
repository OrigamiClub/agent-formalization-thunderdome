# agent_066 — improved sunflower lemma (statement only)

## Form chosen

One theorem, `improved_sunflower_lemma`, of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ (α) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α),
    (∀ S ∈ W, S.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ Y, ∃ petals ⊆ W, IsSunflower r Y petals
```

Ends with `:= by sorry`. An auxiliary `def IsSunflower` gives the sunflower
predicate.

## Encoding decisions and why

- **Set representation.** `Finset α` for individual sets, `Finset (Finset α)`
  for the family `W`. This makes "finite family" automatic and gives
  `Finset.card` for all cardinalities with no side finiteness hypotheses. `α`
  is universally quantified (universe-polymorphic) so the constant `C` cannot
  secretly depend on the ambient type.

- **Sunflower predicate.** Defined explicitly with a named core `Y`:
  `petals.card = r`, `Y ⊆ S` for each petal, and `S ∩ T = Y` for distinct
  petals. The pairwise-intersection form is the standard definition; adding
  `Y ⊆ S` makes the core meaningful even in the degenerate `r = 1` case (where
  the pairwise condition is vacuous). "Every element in ≥ 2 sets is in all of
  them" and "petals pairwise disjoint" are consequences, so not stated.

- **Distinctness.** Encoded by `petals.card = r` with `petals ⊆ W`; no separate
  injectivity statement needed.

- **Petal nonemptiness.** Not stated: for `k ≥ 2`, distinct equal-cardinality
  `S, T` satisfy `S ∩ T ⊊ S`, so each petal `S \ Y` is nonempty automatically.

- **Logarithm.** `Real.log` (natural log). The lemma is usually quoted with
  `log` base `e` or base `2`; the base only changes the absolute constant `C`,
  which is existentially bound, so the choice is immaterial.

- **Handling small `k`.** Hypothesis `2 ≤ k`. For `k ≤ 1`, `Real.log k ≤ 0`
  and the bound `(C r log k)^k` degenerates; for `k = 1` the statement as
  written is actually false (take `W` a single singleton, `r ≥ 2`:
  `0 < |W|` holds but there is no `2`-petal sunflower). The `k = 1` case is
  elementary (any `> r` distinct singletons form a sunflower with core `∅`) and
  is conventionally excluded from the "`(C r log k)^k`" statement.

- **`r`.** `1 ≤ r`. `r = 1` is allowed and trivial; `r = 0` excluded as
  "sunflower with 0 petals" is vacuous.

- **`C`.** Existentially quantified inside the theorem, placed outside the `∀ α`
  binder, so it is a single absolute constant. `0 < C` recorded.

- **Inequality direction.** Hypothesis `(C r log k)^k < (W.card : ℝ)`, matching
  "`|W| >` bound". Cast `W.card` to `ℝ`.

## Uncertainties

- **Mathlib sunflower predicate.** Mathlib may already contain a sunflower
  definition and the Erdős–Rado lemma (plausibly in
  `Mathlib.Combinatorics.SetFamily`, under a name like `Finset.IsSunflower`,
  `IsSunflower`, or `Sunflower`). I did not rely on it and defined `IsSunflower`
  locally; if a canonical one exists the statement could be rephrased against
  it. The name/existence is a guess.

- **`import Mathlib`.** Used the umbrella import for safety; the statement only
  needs `Real.log` and `Finset`, so a narrower import (e.g.
  `Mathlib.Analysis.SpecialFunctions.Log.Basic` plus `Mathlib.Data.Finset.*`)
  would also work.

- **`∀ (α : Type*) [DecidableEq α]` after `∃ C, 0 < C ∧ …`.** Believed to
  elaborate fine as a `Prop`; not machine-checked (no compiler available).

- **Exact constant/shape in the literature.** Bell–Chueluecha–Warnke and Rao
  give `f(k,r) ≤ (C r log k)^k` (natural log, `k ≥ 2`); some write
  `log(rk)` or `log k` with extra lower-order factors. The `Real.log k` form
  with an absolute `C` and `k ≥ 2` is the standard modern statement.
