# Agent 038 — improved sunflower lemma, statement

## Form chosen

A single theorem `ImprovedSunflower.improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ),
  2 ≤ k → 1 ≤ r → ∀ W : Finset (Finset α),
    (∀ s ∈ W, s.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ Y S, S ⊆ W ∧ IsSunflower r Y S
```

plus a local definition `IsSunflower r Y S`.

## Encoding decisions and rationale

- **Set representation**: `Finset α` over an arbitrary type `α` with `[DecidableEq α]` (needed for
  `∩`). The family is `W : Finset (Finset α)`; a candidate sunflower is `S : Finset (Finset α)` with
  `S ⊆ W`. Using `Finset` avoids separate finiteness hypotheses, and `S : Finset (...)` with
  `S.card = r` already encodes "`r` distinct sets", so distinctness needs no extra clause.

- **`IsSunflower` definition**: explicit core `Y : Finset α`, with three conjuncts —
  `S.card = r`, `∀ s ∈ S, Y ⊆ s`, and `(S : Set _).Pairwise (fun A B => A ∩ B = Y)`. The
  "pairwise intersections all equal `Y`" clause is the mathematical core; `Y ⊆ s` is redundant when
  `r ≥ 2` but makes the predicate well-behaved for `r ≤ 1`. Petals `s \ Y` are **not** required
  nonempty, matching the "family of `r` distinct sets with `S_i ∩ S_j = Y`" phrasing.

- **Logarithm**: `Real.log` (natural log). The base is irrelevant since it is absorbed into `C`.

- **`k = 0, 1`**: excluded via `2 ≤ k`. For `k = 1`, `Real.log 1 = 0` makes the displayed bound
  `0`, which is genuinely too weak (one still needs `|W| ≥ r`), so including `k = 1` would make the
  statement false as written. `k ≥ 2` is the standard regime for this bound (`log k > 0`).

- **Constant `C`**: existentially quantified at the very front with `0 < C`, directly encoding
  "there is an absolute constant `C`". `α` is quantified *inside* the existential so that one `C`
  works for all ambient types.

- **Cardinality**: `Finset.card` throughout. The hypothesis inequality is cast to `ℝ`
  (`(W.card : ℝ)`) because the right-hand side is real.

- **`r`**: `1 ≤ r` (equivalent to "positive").

## Uncertainties

- Mathlib has `Mathlib/Combinatorics/SetFamily/Sunflower.lean` (the classical Erdős–Rado bound). I
  believe it defines something like `Finset.IsSunflower (r : ℕ) (t : Finset α) (𝒮 : Finset (Finset α))`,
  but I am not certain of the exact name/argument order, so I defined `IsSunflower` locally rather
  than depend on it. If the Mathlib predicate exists with that spelling, this local definition
  should be (propositionally) equivalent for `r ≥ 2`.
- `Set.Pairwise` and the `Finset (Finset α) → Set (Finset α)` coercion are used; these are standard
  Mathlib and I am confident they exist. `Real.log` on a `Nat` argument is written with an explicit
  cast `Real.log (k : ℝ)`.
- `import Mathlib` is used for brevity/safety rather than minimal imports.
