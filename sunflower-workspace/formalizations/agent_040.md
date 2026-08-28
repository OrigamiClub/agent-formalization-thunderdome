# agent_040 — improved sunflower lemma (statement only)

## Form chosen

A single theorem `ImprovedSunflower.improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ {α} (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α),
    (∀ s ∈ W, s.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ Y S, S ⊆ W ∧ IsSunflowerWith r Y S
```

plus one auxiliary definition `IsSunflowerWith`.

## Encoding decisions

- **Set family representation.** `Finset (Finset α)` over an arbitrary ambient type `α`. This
  is Mathlib's standard setting for the sunflower API, gives distinctness of members for free,
  and makes "cardinality" unambiguous (`Finset.card`). The family `W` and the sunflower
  subfamily `S` are both `Finset (Finset α)`; `S ⊆ W` is `Finset` inclusion.

- **Sunflower predicate.** Defined locally as
  `IsSunflowerWith r Y S := S.card = r ∧ (S : Set (Finset α)).Pairwise (fun A B => A ∩ B = Y)`,
  i.e. the "explicit core" + "all pairwise intersections coincide" formulation, with the petal
  count `r` recorded as `S.card = r`. Kept self-contained rather than depending on a Mathlib
  identifier (see uncertainties). For `r ≥ 2` this entails `Y ⊆ A` for all `A ∈ S` and pairwise
  disjoint petals `A \ Y`, so the extra conditions from the informal definition are consequences
  and are not separately asserted.

- **Petals nonempty.** Not required. Distinctness of members (automatic in `Finset (Finset α)`)
  already rules out a repeated set; at most one member can coincide with the core. The standard
  statement of the improved lemma does not demand nonempty petals.

- **Distinctness.** Not stated explicitly — it is automatic for elements of a `Finset`.

- **Cardinality.** `Finset.card` throughout (`s.card = k`, `S.card = r`, `W.card`).

- **Logarithm.** `Real.log` (natural log), applied to the cast `(k : ℝ)`. The base is
  irrelevant to the statement since changing base only rescales the absolute constant `C`.

- **k = 0 / k = 1.** Excluded via the hypothesis `2 ≤ k`. For `k = 0`, `Real.log 0 = 0` in
  Mathlib (junk value) and the bound degenerates; for `k = 1`, `Real.log 1 = 0` so the RHS is
  `0` and the naive statement would wrongly claim any nonempty family of singletons contains an
  `r`-petal sunflower even when `|W| < r`. Restricting to `k ≥ 2` sidesteps both; the excluded
  cases are combinatorially trivial. `r` is constrained by `1 ≤ r`.

- **The constant `C`.** Existentially quantified at the very front, before `α`, `k`, `r`, `W`,
  so it is genuinely absolute. Bundled with `0 < C`.

- **Inequality direction.** Hypothesis `(C * r * Real.log k) ^ k < (W.card : ℝ)`, matching
  "|W| > (C · r · log k)^k". `W.card` is cast to `ℝ` for the comparison.

## Uncertainties

- Mathlib very likely already has a sunflower predicate (I believe
  `Finset.IsSunflower : ℕ → Finset α → Finset (Finset α) → Prop`, in
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean`, with the classic Erdős–Rado bound stated as
  something like `Finset.exists_sunflower`). I did not rely on it: exact name, argument order,
  and whether the petal-count is part of the predicate are from memory and may be wrong. The
  local `IsSunflowerWith` is meant to be defeq-equivalent to whatever Mathlib uses.
- The improved (ALWZ / Rao / BCW) bound itself is, to my knowledge, **not** in Mathlib.
- `import Mathlib` is used for convenience; the only real dependencies are `Real.log`,
  `Finset`, and `Set.Pairwise`.
- No Lean compiler was available; identifiers such as `Set.Pairwise` and `Real.log` are used
  from memory of current Mathlib.
