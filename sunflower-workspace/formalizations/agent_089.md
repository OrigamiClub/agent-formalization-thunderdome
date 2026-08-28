# agent_089 — improved sunflower lemma (statement only)

## Form chosen

A single `theorem improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ (k r : ℕ), 1 ≤ k → 1 ≤ r → ∀ {α} [DecidableEq α] (W : Finset (Finset α)),
  (∀ A ∈ W, A.card = k) →
  (C * r * Real.log (k + 1)) ^ k < (W.card : ℝ) →
  ∃ P Y, P ⊆ W ∧ P.card = r ∧ IsSunflower P Y
```

with a supporting `def IsSunflower`.

## Encoding decisions

- **Set representation.** `Finset α` for individual sets, `Finset (Finset α)` for the
  family `W`, over an arbitrary ambient `α` with `[DecidableEq α]` (needed for `∩`).
  Using a `Finset` for `W` makes "distinct sets" automatic, so no distinctness
  hypothesis is stated. The sunflower `P` is delivered as `P ⊆ W` with `P.card = r`;
  again distinctness of the `r` petals is free.
- **Uniform cardinality.** `∀ A ∈ W, A.card = k` (Finset.card), "exactly `k`".
- **Sunflower predicate.** Defined locally, matching the problem's wording literally:
  all pairwise intersections of distinct members equal a common `core`. I did *not*
  add `core ⊆ A` or "petals nonempty": neither is required by the classical notion,
  and `A ∩ B = core` already forces `core ⊆ A` whenever `P` has ≥ 2 members. For
  `r = 1` the predicate is vacuous, which is the usual (harmless) degeneracy.
- **Logarithm.** `Real.log`. The base is immaterial (absorbed into `C`), so I did not
  use `Real.logb 2`. Natural log matches the literature convention.
- **The `k = 1` / `log k = 0` issue.** With a literal `Real.log k` the bound at `k = 1`
  is `(…·0)^1 = 0`, turning the claim into "`|W| > 0 ⟹ r-sunflower`", which is *false*
  for `r ≥ 2`. To keep the statement true for every positive `k` I use
  `Real.log (k + 1)`. For `k ≥ 2` this is within a constant factor of `Real.log k`
  (`log(k+1) ≤ 2 log k`), so it is absorbed by the existential `C` and the asymptotics
  are unchanged; for `k = 1` it gives threshold `≈ 0.69·C·r`, and a large enough `C`
  makes the claim hold (any `> r` distinct singletons form an `r`-sunflower with core
  `∅`). `k = 0` is vacuous (exponent `0`, threshold `1`, and all `0`-sets are `∅` so
  `|W| ≤ 1`). An alternative I rejected: keep `Real.log k` but add hypothesis `2 ≤ k`;
  that is also faithful but does not cover "all positive integers `k`".
- **Constant `C`.** Existentially quantified *inside* the theorem, and placed outside
  the quantifier over `α`, so it is genuinely absolute (cannot depend on `k`, `r`, or
  the ambient type). Only `0 < C` is asserted (matches "there is an absolute
  constant"); the true constant is `≥ 1`.
- **Counting.** `Finset.card`, compared in `ℝ` after coercion (`(W.card : ℝ)`), because
  the threshold is real-valued. Strict `<` encodes the strict `|W| > …`.

## Uncertainties

- Mathlib may already contain a sunflower predicate (plausibly in
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean`, something like `Set.IsSunflower` /
  `Finset.IsSunflower` taking a core `t`, plus a classical `exists_sunflower` with the
  Erdős–Rado bound). I did not rely on it and defined `IsSunflower` myself so the file
  is self-contained; if the Mathlib name exists, this local def should be
  definitionally close to it.
- The mixed binder chain `∀ (k r : ℕ), … → ∀ {α : Type*} [DecidableEq α] (W …), …`
  inside a term-level statement is, to my knowledge, syntactically valid in Lean 4 /
  Mathlib, but I have no compiler to confirm.
- `import Mathlib` is used for brevity; the minimal imports would be the `Finset`
  combinatorics files plus `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
