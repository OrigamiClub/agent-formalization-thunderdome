# Agent 008 — Improved sunflower lemma, formalization note

## Form chosen

A single theorem `ImprovedSunflower.improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧
  ∀ {α} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
    ∀ W : Finset (Finset α),
      (∀ s ∈ W, s.card = k) →
      (C * r * Real.log k) ^ k < (W.card : ℝ) →
      ∃ S ⊆ W, S.card = r ∧ ∃ Y, IsSunflower S Y
```

plus an auxiliary `def IsSunflower`.

## Encoding decisions and rationale

- **Set representation.** Sets are `Finset α` over an ambient type `α` with
  `[DecidableEq α]`; the family is `W : Finset (Finset α)`. This gives finiteness
  for free, makes `∩`, `\`, `card`, `⊆` all computable/standard, and makes the
  distinctness of family members automatic (a `Finset` has no duplicates).

- **`α` and `C` scoping.** Both `C` and `α` are quantified so that `C` is a
  genuine *absolute* constant: `∃ C, 0 < C ∧ ∀ {α} …`. `C` is existential inside
  the statement rather than a hypothesis or a named opaque constant, which is the
  most faithful reading of "there is an absolute constant `C`".

- **Sunflower predicate.** Defined explicitly with an explicit core `Y`:
  `(∀ s ∈ S, Y ⊆ s) ∧ (∀ s ∈ S, ∀ t ∈ S, s ≠ t → s ∩ t = Y)`.
  The pairwise-intersection clause is the mathematical heart; the `Y ⊆ s` clause
  is redundant once `|S| ≥ 2` but makes the predicate well-behaved for the
  degenerate `r = 1` case. Pairwise-disjoint petals and "any point in ≥ 2 members
  is in all" are consequences, so they are not stated.

- **"with `r` petals".** Encoded as a subfamily `S ⊆ W` with `S.card = r`
  (exactly `r`; a larger sunflower trivially yields an `r`-petal one by taking a
  subset). Petals are the members of `S` themselves (equivalently `s \ Y`);
  they are not required to be nonempty.

- **Cardinality.** `Finset.card` throughout. The final numeric comparison casts
  `W.card : ℕ` to `ℝ`. Members of `W` have card *exactly* `k`
  (`∀ s ∈ W, s.card = k`), matching the "each of cardinality exactly `k`"
  hypothesis (a `k`-uniform family).

- **Logarithm and small `k`.** `Real.log` (natural log). The bound
  `(C r log k)^k` is only meaningful when `log k > 0`, so the statement assumes
  `2 ≤ k` (then `Real.log k ≥ Real.log 2 > 0`). The excluded cases are trivial:
  `k = 0` forces every member to be `∅`, so `|W| ≤ 1`; `k = 1` is the family of
  singletons, where any `r` distinct members already form a sunflower with core
  `∅`. Using natural `log` vs `Real.logb 2` only changes `C`, so it is
  immaterial to the statement. `r ≥ 1` is imposed ("positive integers `r`").

- **Strict vs non-strict bound.** Stated as `RHS < |W|` (strictly greater than
  the threshold implies a sunflower), matching "`|W| > (C r log k)^k`".

- **Import.** `import Mathlib` for a self-contained file (only `Real.log`,
  `Finset` API are actually needed).

## Uncertainties

- **Possible Mathlib duplication.** Mathlib may already contain a sunflower
  predicate and/or the classical sunflower lemma (I could not verify names
  without a compiler). Plausible locations/identifiers:
  `Mathlib.Combinatorics.SetFamily.Sunflower`, with something like
  `Finset.IsSunflower` / `Finset.Sunflower` and a lemma
  `Finset.exists_sunflower`. To stay robust I defined `IsSunflower` locally under
  a private namespace; if the Mathlib predicate exists it is almost certainly
  definitionally close (core + pairwise intersection).

- **Binder syntax.** `∀ {α : Type*} [DecidableEq α] (k r : ℕ), …` appearing
  under an `∃ C, …` is expected to elaborate fine in Lean 4 / Mathlib, but I
  could not run the elaborator. If instance binders in that position are
  awkward, an alternative is to make `α`/`[DecidableEq α]` section variables and
  quantify `C` outside; this weakens "absolute" only cosmetically.

- **`r = 1` / small `r`.** With `1 ≤ r` the `r = 1` "sunflower" is vacuous-ish
  (any `Y ⊆ s` works). Some sources require `r ≥ 2` or `r ≥ 3`. I kept `r ≥ 1`
  to match "all positive integers `r`"; tightening to `2 ≤ r` would be a
  defensible variant.

- **Exact `S.card = r` vs `r ≤ S.card`.** Chose equality; both are standard and
  equivalent for the lemma's content.
