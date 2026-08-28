# Agent 025 — improved sunflower lemma, statement formalization

## Form chosen

Two equivalent statements, both `:= by sorry`:

1. `improved_sunflower_lemma` — "large family ⇒ contains an `r`-petal sunflower".
2. `improved_sunflower_lemma_bound` — contrapositive "sunflower-free ⇒ family is small",
   matching `f(k,r) ≤ (C r log k)^k`.

Both begin `∃ C : ℝ, 0 < C ∧ ∀ k r, 2 ≤ k → 1 ≤ r → ∀ {α} [DecidableEq α] (W …)`.

## Encoding decisions

- **Set representation.** Sets are `Finset α` over an ambient type `α`; the family `W` is a
  `Finset (Finset α)`. This gives finiteness of `W` and of each member for free, and makes
  `card` unambiguous (`Finset.card`). `α` is quantified *inside* each theorem so each
  statement is self-contained.
- **"Each of cardinality exactly k".** Hypothesis `∀ s ∈ W, s.card = k`.
- **Sunflower predicate.** I define my own `IsSunflower r Y P` rather than rely on a
  Mathlib identifier I cannot verify. It says `P.card = r` together with: any two distinct
  members of `P` intersect in exactly the core `Y`. The pairwise-disjoint-petals and
  "in two ⇒ in all" properties follow from this, so they are not separately stated.
  The subfamily is delivered as `P ⊆ W` plus `IsSunflower r Y P`, with `Y` existentially
  bound.
- **Distinctness of the r sets.** Encoded by `P.card = r` on a `Finset`; no extra
  injectivity hypothesis needed.
- **Petals nonempty?** Not required. The core may equal a member only if `P` has ≤ 1
  element; for `r ≥ 2` distinct members with equal pairwise intersection the petals are
  automatically nonempty, so no generality is lost by omitting it. Empty petals are
  harmless for `r ≤ 1`.
- **Logarithm.** `Real.log` (natural log). The base is irrelevant to the statement since
  the absolute constant `C` absorbs any constant factor / base change.
- **k = 0, 1 handling.** Restricted to `2 ≤ k`, which makes `Real.log k > 0` and avoids the
  degenerate bound `(… · log 1)^1 = 0`. In the literature `k = 1` is treated separately
  (a family of `k`-sets with `|W| ≥ r` distinct singletons is trivially a sunflower). So
  `2 ≤ k` loses nothing essential for "the improved bound".
- **r.** `1 ≤ r` ("positive integers r"). No upper structural constraint.
- **The bound.** `(C * (r:ℝ) * Real.log (k:ℝ)) ^ k < (W.card : ℝ)` with `W.card` cast to
  `ℝ`; exponent `^ k` is `Monoid.npow` with `k : ℕ`.
- **C.** Existentially quantified with `0 < C`, expressing "there is an absolute constant".

## Uncertainties

- Mathlib does contain a classical sunflower development (roughly
  `Mathlib/Combinatorics/…/Sunflower`), plausibly with a predicate named `IsSunflower` or
  `Finset.IsSunflower` and a lemma like `sunflower_exists` for the `(r-1)^k k!` bound. I did
  **not** rely on it because I cannot verify the exact name/argument order without a
  compiler. If that predicate exists and matches, `IsSunflower` here could be replaced by
  it (argument order there may differ, e.g. `(𝒮) (t) (r)` vs my `(r) (Y) (P)`).
- `∀ {α : Type*} [DecidableEq α] …` appearing after value binders inside a `∀`-chain is
  valid Lean 4 / Mathlib syntax (implicit + instance binders in a pi type); universe is
  auto-bound. Believed correct but unverified here.
- `import Mathlib` (the whole library) is used for convenience; only `Real.log` and
  `Finset` are actually needed.
- Whether to state `>` strictly (I did: `bound < W.card`) vs `≥` — the theorem as usually
  quoted uses strict `>`, and the contrapositive form then gives `≤`.
