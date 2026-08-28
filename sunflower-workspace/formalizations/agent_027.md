# agent_027 — improved sunflower lemma, statement only

## Form chosen

One theorem, `Agent027.improved_sunflower_lemma`, of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
  ∀ W : Finset (Finset α),
    (∀ s ∈ W, s.card = k) →
    (C * r * Real.log (k + 1)) ^ k < (W.card : ℝ) →
    ∃ Y P, P ⊆ W ∧ IsSunflower r Y P
```

plus one auxiliary `def IsSunflower`.

## Encoding decisions and why

- **Set representation:** `Finset α` for the sets, `W : Finset (Finset α)` for
  the family, over an arbitrary `α` with `[DecidableEq α]`. Finsets are the
  idiomatic choice for this finite combinatorial statement: cardinality is just
  `Finset.card` into `ℕ` (no `Set.Finite` side conditions), and membership in a
  `Finset (Finset α)` already forces the members of `W` to be distinct, so no
  separate distinctness hypothesis on `W` is needed. `DecidableEq α` is required
  to form `Finset (Finset α)` and the intersections `s ∩ t`.
- **Sunflower predicate:** defined explicitly with a core `Y : Finset α`:
  `P.card = r` together with `s ∩ t = Y` for all distinct `s, t ∈ P`. This is
  the "all pairwise intersections coincide" formulation with the common value
  named. `P.card = r` supplies "`r` distinct petals" (a `Finset` has distinct
  elements). `Y ⊆ s`, pairwise-disjoint petals `s \ Y`, and the "in ≥ 2 ⇒ in
  all" property are consequences for `r ≥ 2` and are noted in the docstring
  rather than baked in, to keep the definition minimal.
- **Petals nonempty:** not required. The classical/improved lemma does not
  assume it; for `r ≥ 2` at most one member can equal the core anyway.
- **`2 ≤ r`:** not imposed (neither in `IsSunflower` nor the theorem), to match
  "for all positive integers r". For `r = 1` the conclusion degenerates to
  "`W` has a member", which is still true under the hypothesis, so the statement
  stays correct.
- **Which logarithm / `k = 1` handling:** `Real.log` (natural log), applied to
  `(k : ℝ) + 1` rather than `k`. With bare `Real.log k` the statement is
  *false* at `k = 1`: `Real.log 1 = 0` makes the bound `0`, so any nonempty
  family of singletons would be forced to contain an `r`-petal sunflower for
  every `r`. Using `k + 1` avoids the `log 0`/`log 1 = 0` boundary; since
  `log(k+1) ≍ log k` for `k ≥ 2`, the change is absorbed into the absolute
  constant `C` and does not affect the mathematical content. Alternatives that
  would also work: keep `Real.log k` but add a hypothesis `2 ≤ k`; or use
  `Real.logb 2`. The base only rescales `C`.
- **The constant `C`:** existentially quantified as the very first binder, so it
  cannot depend on `α`, `k`, `r`, or `W` — i.e. genuinely absolute. Stated as
  `∃ C : ℝ, 0 < C ∧ …` rather than as a hypothesis or an opaque named constant.
- **Cardinality:** `Finset.card` throughout; the final comparison is in `ℝ`
  (`(C * r * log (k+1))^k < (W.card : ℝ)`) with `^ k` the natural-number power
  on `ℝ`.
- **Conclusion:** `∃ Y P, P ⊆ W ∧ IsSunflower r Y P` — the sunflower is a
  sub-family of `W`.

## Uncertainties

- **Mathlib already has a sunflower notion?** I believe Mathlib contains the
  classical Erdős–Rado sunflower lemma, but I am not certain of the identifier.
  Plausible names: `Finset.IsSunflower`, `Set.IsSunflower`, or a predicate in a
  `Sunflower` namespace, possibly parameterised by petal count or phrased via
  `Set.PairwiseDisjoint (· \ t)`. To stay self-contained and unambiguous I
  defined my own `Agent027.IsSunflower`. If a Mathlib predicate exists it is
  likely equivalent (for `r ≥ 2`) up to how the core / petal count is packaged.
  The *improved* (ALWZ / Rao / BCW) bound is, to my knowledge, not in Mathlib.
- **`Real.log`** is the standard Mathlib name for the real natural logarithm
  (`Mathlib.Analysis.SpecialFunctions.Log.Basic`); high confidence.
- **Universe / binder syntax:** the inner `∀ {α : Type u} [DecidableEq α] …`
  inside the statement term relies on auto-bound universe `u` and on binding an
  instance-implicit inside a `∀`. Both are expected to be accepted by Lean 4;
  not machine-checked here (no compiler available).
- `import Mathlib` is used for convenience rather than a minimal import set.
