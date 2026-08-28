# agent_091 — improved sunflower lemma (statement only)

## Form chosen

A single `theorem improved_sunflower_lemma : ∃ C : ℝ, 0 < C ∧ ∀ ... := by sorry`,
plus one auxiliary definition `IsSunflower`.

Informal content: there is an absolute `C > 0` such that for all positive integers
`k, r`, any finite family `W` of exactly-`k`-element sets with
`|W| > (C · r · log k)^k` contains a sunflower with `r` petals.

## Encoding decisions

- **Set representation.** `Finset α` for individual sets, `Finset (Finset α)` for
  the family `W`, over an arbitrary `α` with `[DecidableEq α]`.
  - Finiteness of the family ("finite family W") is free.
  - Distinctness of the members of `W`, and of the `r` chosen petals, is free
    (elements of a `Finset` are distinct), so no explicit distinctness hypothesis
    is needed; `T.card = r` then really means `r` distinct sets.
- **Sunflower predicate.** Defined explicitly as `IsSunflower T r Y`:
  `T.card = r ∧ ∀ s ∈ T, ∀ t ∈ T, s ≠ t → s ∩ t = Y`.
  This is the "all pairwise intersections coincide (with the explicit core `Y`)"
  formulation. The core `Y` is existentially quantified in the conclusion
  (`∃ T ⊆ W, ∃ Y, IsSunflower T r Y`).
  - The "common core" and "disjoint petals" properties follow from this and are
    noted in the docstring rather than baked in.
  - Petals are **not** required to be nonempty in the definition. (Under the
    hypotheses — all members of `W` have card `k` and `r ≥ 2` — nonemptiness is
    automatic, since a member equal to the core would be a proper subset of
    another equal-cardinality member.)
- **Constant `C`.** Existentially quantified *inside* the theorem and *outermost*,
  before the type `α` and before `k, r`. This captures "absolute constant": the
  same `C` serves all ambient types and all `k, r`. `0 < C` is asserted.
- **Logarithm.** `Real.log` (natural log). The choice of base only rescales `C`,
  so it is immaterial to the statement; natural log is the Mathlib default and
  keeps the coercion story simple. `k` is coerced `ℕ → ℝ` inside `Real.log`.
- **Cardinality.** `Finset.card`, with `W.card` and the bound both compared in `ℝ`
  after coercion: `(C * r * Real.log k) ^ k < (W.card : ℝ)`. The exponent `k` is a
  `ℕ` (monoid power).
- **Positivity hypotheses.** `0 < k` and `0 < r`, matching "positive integers `k`
  and `r`" literally.

## Uncertainties / caveats

- **`k = 1` degeneracy.** With `Real.log 1 = 0`, the bound becomes
  `(C · r · 0)^1 = 0`, so the hypothesis reduces to `0 < |W|`. For `r ≥ 2` this is
  not enough to force a sunflower with `r` petals (`W` could be a single
  singleton). So the statement as written — faithful to the informal
  "for all positive integers `k`" with `log k` — is vacuously-strong / false at
  `k = 1, r ≥ 2`. This is a well-known wrinkle of the `log k` phrasing; standard
  fixes, any of which could be substituted:
  - add the hypothesis `2 ≤ k` (the lemma is an asymptotic statement in `k`); or
  - use `Real.log (r * k)` in place of `Real.log k` (Rao's phrasing), which is
    `> 0` for all positive `k, r`; or
  - use `max 1 (Real.log k)`.
  I kept the literal `Real.log k` with `0 < k` to stay closest to the problem
  statement, and flag the issue here.
- **Mathlib overlap.** Mathlib has a sunflower file
  (`Mathlib/Combinatorics/SetFamily/Sunflower.lean`) with a sunflower predicate
  and the classical Erdős–Ko–Rado sunflower lemma. I could not verify the exact
  current identifier / argument order (candidates: `Finset.IsSunflower`,
  `Finset.Set.IsSunflower`, with arguments in some order among family / petal
  count / core), and the *improved* bound is (to my knowledge) not in Mathlib. To
  keep the file self-contained and unambiguous I defined `IsSunflower` locally;
  a reconciliation with the Mathlib predicate would be a drop-in replacement.
- **Universe handling.** `∀ {α : Type*} [DecidableEq α]` sits under the outer
  `∃ C : ℝ`. This is well-formed in Lean 4 (auto-bound universe on the inner
  binder); if a concrete universe is preferred, replace with `Type`.
- `import Mathlib` is used for brevity; the statement only needs `Finset` and
  `Real.log`.
