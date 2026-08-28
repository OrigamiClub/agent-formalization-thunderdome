# agent_046 — improved sunflower lemma (statement)

## Form chosen

One theorem, `ImprovedSunflower.improved_sunflower_lemma`, of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
  2 ≤ k → 1 ≤ r → (∀ s ∈ W, s.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  ∃ T ⊆ W, T.card = r ∧ IsSunflower T
```

plus an auxiliary `def IsSunflower`.

## Encoding decisions

- **Set representation.** `Finset α` for individual sets, `Finset (Finset α)` for
  the family `W`. Finiteness and "each set has cardinality exactly `k`" are then
  cheap (`Finset.card`), and distinctness of members / of petals is free.
- **`α` quantified inside.** `C` is introduced by an outer `∃`, and `α`, `k`,
  `r`, `W` all sit under it, so `C` is a single constant serving every ambient
  type — the honest reading of "absolute constant".
- **`C` existential, with `0 < C`.** Matches "there is an absolute constant `C`".
  Positivity is included so the statement cannot be satisfied by a vacuous/absurd
  `C`.
- **Sunflower predicate.** Defined locally as: `∃ Y, ∀ s t ∈ T, s ≠ t → s ∩ t = Y`
  (all pairwise intersections coincide). This is the standard definition and is
  equivalent to "core `Y` with pairwise-disjoint petals `s \ Y`"; for `T.card ≥ 2`
  it already forces `Y ⊆ s` for all `s ∈ T`. Put in a namespace to avoid any
  clash with a possible Mathlib `Sunflower`/`IsSunflower`.
- **Number of petals = `T.card`**, and `T ⊆ W`. `T.card = r` gives `r` distinct
  members automatically.
- **Petals nonempty:** not stated. With all members of cardinality `k`, for
  `r ≥ 2` containment between distinct equal-size sets is impossible, so every
  petal `s \ Y` is nonempty automatically.
- **Logarithm:** `Real.log` (natural log; base is immaterial, absorbed into `C`).
  Threshold compared against `(W.card : ℝ)`.
- **`k = 0, 1` handling:** excluded via `2 ≤ k`. For `k ≤ 1`, `Real.log k ≤ 0`
  makes `(C r log k)^k` non-positive (or `1` at `k = 0`), so the threshold would
  be vacuous or the claim false (`k = 1`: a family of `> 0` singletons need not
  contain `r ≥ 2` petals). Literature uses the bound in the `k ≥ 2` regime.
- **`r`:** `1 ≤ r` (positive). `r = 1` is trivial but true (`W` nonempty ⇒ pick
  one set); kept for faithfulness to "all positive integers `r`".

## Uncertainties

- Whether current Mathlib already has a sunflower definition (`Finset.Sunflower`,
  `IsSunflower`, file `Mathlib/Combinatorics/SetFamily/Sunflower.lean`). I did not
  rely on it; the local `IsSunflower` is namespaced so `import Mathlib` cannot
  clash.
- `import Mathlib` is used for brevity; the only real need is `Real.log`
  (`Mathlib.Analysis.SpecialFunctions.Log.Basic`) and `Finset`.
- Coercions written explicitly (`(r : ℝ)`, `Real.log (k : ℝ)`) to avoid
  elaboration ambiguity; exact need for the annotations is a guess.
- Binder syntax `∀ {α : Type*} [DecidableEq α] (k r : ℕ) ...` under an `∃`/`∧`
  should elaborate, but I have no compiler to confirm.
