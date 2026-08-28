# agent_044 — improved sunflower lemma (statement only)

## Form chosen

A single existential-constant theorem:

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] {k r : ℕ}, 2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α),
    (∀ S ∈ W, S.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ContainsSunflowerWith W r
```

with two auxiliary definitions, all in namespace `Agent044`.

## Encoding decisions

- **Set family:** `W : Finset (Finset α)` over an ambient type `α` with
  `[DecidableEq α]`. Finiteness is then free, and "each set has cardinality
  exactly `k`" is `∀ S ∈ W, S.card = k` via `Finset.card`.
- **Absolute constant:** `C` is existentially quantified *outside* the
  quantifier over `α`, `k`, `r`, `W`, so it genuinely cannot depend on any of
  them — this is what "absolute constant" means. Stated as a real with `0 < C`.
- **`∀ {α}` under the `∃ C`:** Lean allows a universe-polymorphic `∀ {α : Type*}`
  as an ordinary `Pi` inside a proposition; keeping `α` inside the body (rather
  than as a section variable) is what makes `C` uniform over all carrier types.
- **Sunflower predicate:** defined locally as `IsSunflowerWith P r Y`
  (a `structure`): `P.card = r`, every petal `⊇ Y`, and distinct petals satisfy
  `S ∩ T = Y`. The explicit core `Y` is the "there is a core set `Y`"
  formulation from the problem statement. `core_subset` is kept as a field so
  that `Y` is pinned down even in degenerate small-`r` cases (for `r ≥ 2` it is
  implied by `pairwise_inter`).
- **Petals distinct:** automatic — `P` is a `Finset (Finset α)` of cardinality
  `r`, so it has `r` distinct members. No separate distinctness hypothesis.
- **Petals nonempty:** *not* required. The standard improved-lemma statement
  does not need it; by distinctness at most one petal `S \ Y` can be empty.
- **"Contains a sunflower":** `ContainsSunflowerWith W r := ∃ P ⊆ W, ∃ Y,
  IsSunflowerWith P r Y`.
- **Logarithm:** `Real.log` (natural log). Choice is immaterial to the truth of
  the statement since a change of log base is absorbed into `C`; natural log is
  the most common in the source papers and the least friction in Mathlib.
- **`k` edge cases:** hypothesis `2 ≤ k` is imposed. For `k = 1`, `Real.log 1 = 0`
  makes the RHS `0`, and the implication would be false (a family of `> 0`
  distinct singletons need not contain an `r`-petal sunflower for `r ≥ 2`); for
  `k = 0` the family has at most one element. `2 ≤ k` is the usual guard in
  statements of this lemma. `1 ≤ r` is imposed for symmetry with "positive
  integers `r`"; the body is still meaningful (though weak) at `r = 1`.
- **Cardinality comparison** done in `ℝ` with explicit coercions of `r`, `k`,
  `W.card`; the strict `>` of the informal statement is written as
  `(C * r * Real.log k) ^ k < (W.card : ℝ)`.

## Uncertainties

- I did not verify against a compiler.
- Mathlib very likely already contains a sunflower development
  (`Mathlib/Combinatorics/SetFamily/Sunflower.lean`), plausibly with names such
  as `Finset.IsSunflower`, `Finset.IsSunflowerWith`, and an
  Erdős–Ko–Rado-style existence theorem `Finset.exists_sunflower` giving the
  classical bound `(r - 1) ^ k * k ! < W.card`. Exact identifiers/signatures are
  guessed; I deliberately used the `Agent044` namespace and my own `structure`
  to avoid any clash under `import Mathlib`. If the Mathlib predicate exists and
  matches, the local `IsSunflowerWith` could be replaced by it.
- `import Mathlib` is used for convenience; the only real dependencies are
  `Finset` and `Real.log`.
- Whether to make `C` a named constant or a hypothesis rather than an inner
  existential is a judgement call; the inner `∃ C` keeps the statement fully
  self-contained and makes the "absolute" quantifier order explicit.
