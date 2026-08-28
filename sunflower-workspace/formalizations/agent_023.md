# agent_023 — improved sunflower lemma, statement only

## Form chosen

A single existential theorem `ImprovedSunflower.improved_sunflower_lemma`:

```
∃ C : ℝ, 0 < C ∧
  ∀ (k r : ℕ), 0 < k → 0 < r →
    ∀ {α} [DecidableEq α] (W : Finset (Finset α)),
      (∀ s ∈ W, s.card = k) →
      (C * r * Real.log k) ^ k < (W.card : ℝ) →
      ContainsSunflower W r
```

with two auxiliary definitions, `IsSunflower` and `ContainsSunflower`.

## Encoding decisions

- **Set representation.** Sets are `Finset α` over an ambient type `α` with
  `[DecidableEq α]`; a family is `Finset (Finset α)`. This makes `|W|`,
  `s.card`, and "exactly `r` members" all `Finset.card`, and needs no separate
  finiteness hypotheses. `DecidableEq α` is only there to make `A ∩ B` and
  `Finset` membership computable; it is no real loss of generality.

- **Sunflower predicate.** Defined explicitly rather than assuming a Mathlib
  identifier. `IsSunflower T Y := (T : Set (Finset α)).Pairwise (fun A B => A ∩ B = Y)`.
  `Set.Pairwise` ranges over distinct pairs only, matching "for every `i ≠ j`".
  The core `Y` is an explicit parameter; `ContainsSunflower` existentially
  quantifies it. The "every element in ≥ 2 sets is in all" phrasing and the
  pairwise-disjoint-petals phrasing are equivalent to this and are not separately
  stated.

- **`r` petals / distinctness.** Encoded as a subfamily `T : Finset (Finset α)`
  with `T ⊆ W` and `T.card = r`. Using a `Finset` of cardinality `r` builds in
  that the `r` petals are pairwise distinct, so no extra `distinct` hypothesis is
  needed.

- **Petals nonempty.** Not stated. For `r ≥ 2`, distinct equal-cardinality
  members with `A ∩ B = Y` force `Y ⊊ A`, so petals are automatically nonempty;
  for `r ≤ 1` the notion is degenerate anyway. Left implicit deliberately.

- **Logarithm.** `Real.log` (natural log), applied to `(k : ℝ)`. The bound is
  compared in `ℝ` against `(W.card : ℝ)`. Base choice only changes the absolute
  constant `C`, so natural log is the least-friction choice in Mathlib.

- **`k = 0`, `k = 1`.** Excluded / degenerate. `0 < k` is required. Note that at
  `k = 1`, `Real.log 1 = 0`, so the RHS is `0` and the hypothesis becomes
  `0 < |W|`; the literal statement then over-claims for `k = 1`. This is the
  well-known wart of the "`(C r log k)^k`" phrasing; faithful transcriptions of
  the theorem as usually quoted have it too. A cleaner variant would hypothesize
  `2 ≤ k`, or replace `Real.log k` by `Real.log k + 1` / `max 1 (Real.log k)`.
  I kept the quoted form and flag it here.

- **Constant `C`.** Existentially quantified *inside* the theorem, outermost
  (before `k`, `r`, `α`, `W`), so it is a single absolute constant. Not supplied
  as a hypothesis, not a named def.

- **Strict inequality.** Used `<` (`(C r log k)^k < |W|`), i.e. `|W| >
  (C r log k)^k`, exactly as stated. The `f(k,r) ≤ (C r log k)^k` phrasing is the
  contrapositive-flavoured equivalent and is not separately formalized.

## Uncertainties

- Mathlib has `Mathlib/Combinatorics/SetFamily/Sunflower.lean` with a sunflower
  predicate (I believe `Finset.IsSunflower` or an `IsSunflower` taking a family
  and a core, via `Set.Pairwise`) and the classical Erdős–Rado bound. I did not
  rely on its exact name; I defined my own `ImprovedSunflower.IsSunflower` in a
  private namespace to avoid any clash under `import Mathlib`. The improved
  (ALWZ) bound is not in Mathlib as far as I know.
- `import Mathlib` (whole library) is used for convenience; the real needs are
  `Mathlib.Data.Finset.*`, `Mathlib.Analysis.SpecialFunctions.Log.Basic`, and
  `Mathlib.Data.Set.Pairwise.Basic`.
- Exact spelling of `Set.Pairwise` on a coerced `Finset` (`(T : Set _).Pairwise …`)
  and the `ℕ → ℝ` coercions are written from memory; the intent is standard.
- Not machine-checked: no Lean compiler was available.
