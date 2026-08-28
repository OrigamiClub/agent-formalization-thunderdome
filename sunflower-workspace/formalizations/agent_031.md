# Agent 031 — improved sunflower lemma (statement only)

## Form chosen

A single existential-constant theorem:

```
∃ C : ℝ, 0 < C ∧ ∀ (k r : ℕ), 1 ≤ k → 1 ≤ r → ∀ W : Finset (Finset α),
  (∀ S ∈ W, S.card = k) →
  (C * r * Real.log (k + 1)) ^ k < (W.card : ℝ) →
  ∃ P Y, P ⊆ W ∧ IsSunflower P r Y
```

plus an auxiliary `structure IsSunflower (P : Finset (Finset α)) (r : ℕ) (Y : Finset α)`.

## Encoding decisions and rationale

- **Set representation:** `Finset α` over an ambient type `α` with
  `[DecidableEq α]`; the family `W` is `Finset (Finset α)`. This makes
  finiteness, decidable intersections, and `Finset.card` available with no
  side hypotheses. No `[Infinite α]` is assumed — the statement is true for
  any `α` (for small finite `α` the cardinality hypothesis is just
  unsatisfiable).
- **Sunflower predicate:** defined locally as a `structure` with two fields:
  `card_petals : P.card = r` and
  `inter_eq_core : ∀ A ∈ P, ∀ B ∈ P, A ≠ B → A ∩ B = Y`.
  I used the "all pairwise intersections coincide (with an explicit core `Y`)"
  formulation. `Y ⊆ A`, pairwise-disjoint petals, and "element in ≥2 sets is in
  all" are all consequences, so they are not imposed. Petals are allowed to be
  empty (classical Erdős–Rado convention).
- **Distinctness:** automatic — elements of a `Finset` are distinct; `P.card = r`
  fixes the petal count at exactly `r`. So no explicit injectivity/distinctness
  hypothesis is stated.
- **Membership of the sunflower in `W`:** stated as `P ⊆ W`.
- **Logarithm:** `Real.log` (natural log), applied to `(k : ℝ) + 1`, not `k`.
  Reason: `Real.log 1 = 0`, so `(C r log k)^k` would be `0` at `k = 1`, making
  the literal statement false for `k = 1, r ≥ 2` (r distinct singletons need
  `|W| ≥ r`, not `|W| > 0`). `Real.log (k+1)` fixes `k = 1` and only rescales
  `C` for `k ≥ 2` since `log(k+1) = Θ(log k)` there. The base of the log is
  absorbed into `C`.
- **The constant `C`:** existentially quantified inside the theorem with
  `0 < C`, matching "there is an absolute constant `C`".
- **Cardinality:** `Finset.card`, cast to `ℝ`, strict inequality `<` matching
  `|W| > (...)`.
- **Range of `k`, `r`:** hypotheses `1 ≤ k` and `1 ≤ r` ("positive integers").

## Uncertainties

- **Mathlib sunflower predicate:** Mathlib may already have a sunflower
  definition (plausibly in `Mathlib/Combinatorics/SetFamily/Sunflower.lean`,
  something like `Finset.IsSunflower` / `Set.IsSunflower`), and possibly the
  classical Erdős–Rado bound. I did not rely on it: I could not recall the exact
  name or argument order, and the task asks for a self-contained file, so I
  defined `Agent031.IsSunflower` in its own namespace to avoid any clash.
- **`import Mathlib`:** used the umbrella import for safety; only
  `Real.log`, `Finset`, and basic order/cast lemmas are actually needed.
- **Coercions:** wrote `(r : ℝ)`, `(k : ℝ)`, `(W.card : ℝ)` explicitly rather
  than trusting automatic insertion; `(... : ℝ) ^ (k : ℕ)` is `Monoid.npow`,
  which is the intended reading.
- No Lean compiler was available; identifiers and syntax are from memory of
  Mathlib.
