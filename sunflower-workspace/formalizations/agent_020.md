# Agent 020 — improved sunflower lemma (statement only)

## Form chosen

A single `theorem improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ k r, 2 ≤ k → 1 ≤ r → ∀ W : Finset (Finset α),
  (∀ S ∈ W, S.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  ∃ core P, P ⊆ W ∧ IsSunflower r core P
```

plus an auxiliary predicate `IsSunflower`.

## Encoding decisions

- **Set representation.** `Finset α` for individual sets over an arbitrary ambient type
  `α` with `[DecidableEq α]` (needed for `Finset.card` and `∩`). The family is
  `W : Finset (Finset α)`, so finiteness of the family and distinctness of its members are
  free. "Contains a sunflower" is `∃ P : Finset (Finset α), P ⊆ W ∧ IsSunflower r core P`.

- **Sunflower definition.** Explicit core. `IsSunflower r core petals` says
  `petals.card = r` (this simultaneously fixes the number of petals and forces the `r`
  sets to be distinct) together with: any two distinct members of `petals` intersect in
  exactly `core`. I did **not** add "core ⊆ each petal" or "petals pairwise disjoint after
  removing the core" — both follow automatically once `2 ≤ r` (noted in the doc comment).
  Petals are not required to be nonempty; a member may equal the core.

- **Logarithm.** `Real.log` (natural log). The base only changes the constant, which is
  existentially quantified, so any fixed base gives an equivalent statement. `Real.log (k : ℝ)`
  with an explicit cast.

- **`k = 1` / `k = 0` handling.** Restricted to `2 ≤ k`. For `k = 1`, `Real.log 1 = 0`, so the
  bound collapses to `0` and the claim "`|W| > 0` implies an `r`-sunflower" is false for
  `r ≥ 2` (e.g. `W = {{a}}`). `k = 0` is even more degenerate. Excluding `k ≤ 1` is the
  minimal honest restriction; the mathematical content ("positive integers `k`") is
  unchanged for the range where the statement is true. An alternative would be to replace
  `Real.log k` by `max (Real.log k) 1` and keep `1 ≤ k`; I preferred keeping the bound
  expression verbatim.

- **Constant `C`.** Existentially quantified inside the theorem (`∃ C : ℝ, 0 < C ∧ …`),
  matching "there is an absolute constant `C`". `0 < C` is included so the bound is a
  genuine positive threshold.

- **Cardinality comparison.** `Finset.card` throughout; the family-size inequality is
  stated in `ℝ` as `(bound) < (W.card : ℝ)` (strict, matching `|W| > …`).

- **Which form of the bound.** The "family `W`" form rather than an explicit sunflower
  function `f(k,r)`. The two are equivalent; the `f(k,r) ≤ (C r log k)^k` phrasing would
  require first defining `f` as a least/`sInf`, adding avoidable machinery and identifier
  risk.

- **Distinctness of members.** Not stated separately for `W` (a `Finset` already has
  distinct elements); for the sunflower it is captured by `petals.card = r`.

## Uncertainties

- I am fairly confident current Mathlib has **no** ready-made sunflower predicate or the
  sunflower lemma itself, so I define `IsSunflower` locally. If a predicate such as
  `Finset.IsSunflower` / `SetFamily.Sunflower` does exist, it should be used instead; the
  intended meaning here is the standard one.
- `Real.log` is a stable Mathlib identifier; the cast `(k : ℝ)` and the `ℕ`→`ℝ` coercions
  in `C * (r : ℝ) * Real.log (k : ℝ)` should elaborate, but I have no compiler to confirm.
- `import Mathlib` is used for self-containedness rather than pinning the specific files
  (`Mathlib.Analysis.SpecialFunctions.Log.Basic`, `Mathlib.Data.Finset.*`).
- Binder-implicit brackets `⦃S⦄` in `IsSunflower` are a stylistic choice (semi-implicit so
  the predicate is convenient to apply); plain `∀ S ∈ petals, …` would be equivalent.
