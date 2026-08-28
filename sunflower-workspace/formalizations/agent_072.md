# Agent 072 — improved sunflower lemma, statement only

## Form chosen

A single theorem `ImprovedSunflower.improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ (α : Type*) [DecidableEq α] (W : Finset (Finset α)),
    (∀ s ∈ W, s.card = k) →
    (C * r * Real.log k) ^ k < W.card →
    ∃ P ⊆ W, IsSunflowerWith P r
```

plus two auxiliary definitions `IsSunflower` (family + explicit core) and
`IsSunflowerWith` (sunflower with a prescribed number of petals).

## Encoding decisions

- **Constant `C`.** Existentially quantified *inside* the theorem, as an absolute
  constant, with `0 < C`. The quantifier over the ambient type `α` is nested inside the
  `∃ C`, so the one constant must serve every type — this is the intended reading of
  "absolute constant".

- **Set representation.** `Finset (Finset α)` over an ambient type `α` with
  `[DecidableEq α]` (needed for `Finset` intersection). The family `W`, the candidate
  sunflower `P`, and every member are `Finset`s, so all finiteness is structural and no
  side hypotheses are needed. `α` is left completely arbitrary (`Type*`).

- **"Sunflower" definition.** Explicit core, via pairwise intersections:
  `IsSunflower P Y := ∀ s ∈ P, ∀ t ∈ P, s ≠ t → s ∩ t = Y`.
  `IsSunflowerWith P r := P.card = r ∧ ∃ Y, IsSunflower P Y`.
  I did not depend on Mathlib's existing sunflower material (see uncertainties), and
  rolled self-contained definitions instead.

- **"Contains a sunflower".** Returned as a sub-family `P ⊆ W` with `IsSunflowerWith P r`.

- **Distinctness of the `r` members.** Automatic: `P : Finset (Finset α)` with
  `P.card = r` is exactly a family of `r` distinct sets. Not separately stated.

- **Petals nonempty.** Not stated. For the meaningful range `r ≥ 2` it is automatic
  here: two distinct sets of the same size `k` whose intersection is the core `Y` must
  have `Y.card < k`, so each petal `s \ Y` is nonempty. Adding it would be redundant.

- **Cardinality.** `Finset.card` throughout: `s.card = k` for members, `W.card` for the
  family, `P.card = r` for the petal count. `W.card` and `k`, `r` are cast `ℕ → ℝ` for
  the inequality.

- **Logarithm.** `Real.log` (natural log). The base only rescales `C`, so it is
  immaterial to the truth of the statement; natural log is the lightest choice in
  Mathlib. `k : ℕ` is cast to `ℝ` inside `Real.log`.

- **Small `k`.** Guarded by the hypothesis `2 ≤ k`. For `k ∈ {0, 1}` one has
  `Real.log k = 0`, the right-hand side becomes `0`, and "`0 < W.card` implies an
  `r`-petal sunflower" is false (e.g. `k = 1`, distinct singletons, `W.card` between `1`
  and `r - 1`). The standard modern statements (Bell–Chueluecha–Warnke) are likewise
  phrased for `k ≥ 2`. Alternative encodings that keep all positive `k`:
  replace `Real.log k` by `Real.log (k + 1)`, or by `max 1 (Real.log k)`; these change
  the family only in the harmless small cases but deviate from the literal formula.

- **`r`.** Required `1 ≤ r`. `r = 1` is trivially true (any singleton sub-family), the
  content is `r ≥ 2`.

## Uncertainties

- No Lean compiler was available; identifiers and elaboration are from memory of
  Mathlib.
- Mathlib does contain a sunflower file (around
  `Mathlib.Combinatorics.SetFamily.Sunflower`) with a sunflower predicate and the
  *classical* Erdős–Ko sunflower lemma bound `(r - 1)^k * k!`; I could not verify the
  exact current names (candidates: `Finset.IsSunflower` / `Set.IsSunflower`,
  `Finset.exists_sunflower` / `exists_sunflower_of_card_lt`). To stay self-contained and
  avoid a wrong `import`-level dependency I defined my own predicates. If the Mathlib
  predicate matches `Set.Pairwise (· ∩ · = Y)` on the coe of `P`, my `IsSunflower` is
  definitionally that.
- Placement of the binders `∀ (α : Type*) [DecidableEq α] ...` inside `∃ C, 0 < C ∧ ...`
  is, to my knowledge, accepted (a `∀` into `Prop` with an instance binder), and makes
  the theorem universe-polymorphic in `α`. I could not machine-check this.
- `(... ) ^ k` is `Monoid.npow` on `ℝ` with `k : ℕ`; standard.
