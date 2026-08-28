# Agent 019 — improved sunflower lemma, statement formalization

## Form chosen

A single `theorem improved_sunflower_lemma : ∃ C : ℝ, 0 < C ∧ ∀ ... := by sorry`,
plus one auxiliary `def IsSunflower`. Import is `import Mathlib` for
self-containedness.

## Encoding decisions

- **Set representation.** `Finset α` over an arbitrary ambient type `α` with
  `[DecidableEq α]`. The family under study is `W : Finset (Finset α)`. Finsets
  give free finiteness and free distinctness of members, matching extremal
  set-theory practice in Mathlib.
- **Absolute constant `C`.** Existentially quantified as a `C : ℝ` with `0 < C`,
  and crucially the type `α` (and `k`, `r`, `W`) are bound *inside* that
  existential. So the statement asserts one universal constant working for every
  ambient type, exactly as "absolute constant" intends.
- **`k`-uniformity.** `∀ S ∈ W, S.card = k` (cardinality exactly `k`, via
  `Finset.card`).
- **Size hypothesis.** `(C * (r : ℝ) * Real.log k) ^ k < (W.card : ℝ)`, i.e. the
  literal `|W| > (C r log k)^k`. Exponent `^ k` is `Monoid.npow` on `ℝ`.
- **Logarithm.** `Real.log` (natural log). Base choice only rescales `C`, so it is
  immaterial to the statement.
- **`k = 1 / k = 0`.** Restricted to `2 ≤ k`. With `Real.log 1 = 0` the literal
  RHS collapses to `0`, which would make the claim false at `k = 1` for `r ≥ 2`
  (a family of `> 0` singletons need not contain `r` of them). `k ≤ 1` is the
  degenerate/trivial regime. Documented alternative that admits all positive `k`:
  use `Real.log k + 1` or `Real.log (k + 1)` in place of `Real.log k`.
- **`r`.** `1 ≤ r` ("positive integers"). `r = 1` and `r = 2` are permitted; the
  definition stays meaningful (for `r = 1` the pairwise condition is vacuous).
- **"Sunflower" definition.** Own predicate `IsSunflower r Y 𝒮`:
  `𝒮.card = r` and `∀ S ∈ 𝒮, Y ⊆ S` and
  `∀ S₁ S₂ ∈ 𝒮, S₁ ≠ S₂ → S₁ ∩ S₂ = Y`.
  The explicit-core formulation. The pairwise-intersection clause already implies
  petal disjointness `(S₁ \ Y) ∩ (S₂ \ Y) = ∅` and (for `r ≥ 2`) that `Y` is the
  set of elements in ≥ 2 members; the `Y ⊆ S` clause is added so `Y` is a genuine
  core even in degenerate small-`r` cases.
- **Petals nonempty.** Not required (no `Y ⊊ S`); the lemma holds without it and
  it keeps the predicate minimal.
- **Distinctness of members.** Automatic: `𝒮 : Finset (Finset α)` and
  `𝒮.card = r` gives `r` distinct sets.
- **Exactly vs at least `r` petals.** Conclusion gives a subfamily `𝒮 ⊆ W` with
  exactly `r` petals (`𝒮.card = r`); a larger sunflower can always be thinned to
  this.

## Uncertainties

- I did **not** rely on any Mathlib sunflower API. I believe Mathlib as of the
  knowledge cutoff does not contain the Erdős–Rado / improved sunflower lemma;
  there may be a `Finset`-level `IsSunflower`-style predicate somewhere
  (`Mathlib/Combinatorics/SetFamily/...`), but I was not confident of the exact
  name or signature, so I defined my own. If a canonical
  `Finset.IsSunflower core petals` exists, this `def` should be replaced by it.
- Identifier `Real.log` and the `ℕ → ℝ` coercion in `Real.log k` are standard and
  I am confident of them.
- Binding `∀ {α : Type*} [DecidableEq α] ...` inside the body of the existential
  is legal Lean 4 term syntax; universe-polymorphism there resolves to a universe
  parameter of the theorem. I am confident this elaborates, though a reviewer may
  prefer to hoist `α` to a section variable (which would, however, weaken the
  "single absolute constant across all `α`" reading).
