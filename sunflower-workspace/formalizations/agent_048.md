# agent_048 — improved sunflower lemma, statement only

## Form chosen

A single `theorem improved_sunflower_lemma : ∃ C : ℝ, 0 < C ∧ ∀ ... := by sorry`,
plus one auxiliary `def IsSunflower`.

## Encoding decisions

- **Set representation.** `Finset α` for individual sets, `Finset (Finset α)` for
  the family `W`. This gives finiteness for free and makes `|W|` just `W.card`.
  `[DecidableEq α]` is needed for `Finset` intersection.
- **Sunflower predicate.** Defined locally as: all pairwise intersections of
  distinct members equal a common core `Y`
  (`∀ s ∈ B, ∀ t ∈ B, s ≠ t → s ∩ t = Y`). Chosen over an explicit
  "core ⊆ each set + petals pairwise disjoint + petals nonempty" bundle because,
  under the lemma's hypotheses (uniform cardinality `k ≥ 2`, `r ≥ 2` petals),
  the compact form already implies `Y ⊆ s`, pairwise-disjoint petals, and
  nonempty petals. The docstring records these consequences.
- **Number of petals.** Stated as `B.card = r` on a `Finset`, which also supplies
  distinctness of the `r` sets, so no separate distinctness hypothesis is needed.
- **The constant `C`.** Existentially quantified, `C : ℝ` with `0 < C`. It is
  bound *before* the implicit `{α : Type*}`, so it is independent of the ambient
  type — a true absolute constant, matching "there is an absolute constant C".
- **Logarithm.** `Real.log` (natural log). Base is irrelevant since it only
  rescales `C`. `k` is cast to `ℝ` inside `Real.log`.
- **`k = 0, 1` handling.** Added hypothesis `2 ≤ k`, which forces
  `Real.log k > 0` and a positive right-hand side. For `k = 1`, `log k = 0` makes
  the bound `0` while sunflower-free families of singletons of size `< r` exist,
  so the natural-log form is genuinely false there and must be excluded (or the
  argument of `log` shifted, e.g. `log (r*k)` or `log (k+1)`; I kept the literal
  `log k` from the problem statement and restricted `k`).
- **`r`.** `1 ≤ r` ("positive integers r"). For `r = 1` the conclusion is
  trivial (`IsSunflower` is vacuous); the mathematical content is at `r ≥ 2`.
- **Comparison.** Strict `<` between the real bound and `(W.card : ℝ)`, matching
  `|W| > (C r log k)^k`.

## Uncertainties

- Mathlib very likely already has a sunflower development
  (`Mathlib/Combinatorics/Sunflower.lean`, plausibly `Finset.IsSunflower` and an
  Erdős–Rado `exists_*` theorem), but I am not confident of the exact identifier
  names or argument order, so I defined `IsSunflower` locally to keep the file
  self-contained. If the Mathlib predicate exists, it may take `r` as an explicit
  argument and/or order `(core, family)` differently.
- The syntax `∀ {α : Type*} [DecidableEq α] (k r : ℕ), ...` as the body of an
  existential is, to my knowledge, valid Lean 4 (implicit and instance binders
  are allowed in `∀`), but I could not machine-check it (no compiler available).
- `import Mathlib` (the whole library) is used for simplicity; the only real
  dependencies are `Finset` and `Real.log`.
- I did not formalize the `f(k, r)` (sunflower-function) restatement; it would
  require defining `f` via `sInf`/`Nat.find`, adding avoidable surface area. It
  is mentioned in the docstring only.
