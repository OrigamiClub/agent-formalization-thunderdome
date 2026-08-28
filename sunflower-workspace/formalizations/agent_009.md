# Agent 009 — note on the formalization

## Form chosen

A single existential over an absolute constant `C`, then a universally quantified
statement over the ambient type, `k`, `r`, and the family `W`:

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
  2 ≤ k → 1 ≤ r → (∀ A ∈ W, A.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  ∃ P ⊆ W, P.card = r ∧ ∃ Y, IsSunflower P Y
```

A second, equivalent theorem `improved_sunflower_lemma_const` takes `C` as an
explicit hypothesis instead of existentially quantifying it (body `True := by
sorry`, since it only records the alternative phrasing).

## Encoding decisions

- **Set representation.** `Finset (Finset α)` over an ambient type `α` with
  `[DecidableEq α]`. This is the representation Mathlib's own sunflower material
  uses, keeps "finite family" and "cardinality" primitive via `Finset.card`, and
  needs no separate finiteness hypothesis.
- **Members of exact size `k`.** `∀ A ∈ W, A.card = k` (Finset.card, a `Nat`).
- **Sunflower predicate.** Defined locally as
  `IsSunflower P Y := (P : Set (Finset α)).Pairwise (fun A B => A ∩ B = Y)`,
  i.e. "all pairwise intersections of distinct members coincide (with the core
  `Y`)". This is exactly the standard characterisation and implies the petals
  `A \ Y` are pairwise disjoint. I kept the core `Y` explicit (bound by an inner
  `∃ Y`) rather than only asserting "pairwise intersections all coincide",
  because it matches the informal statement's "there is a core set `Y`" and the
  Mathlib shape.
- **"`r` petals".** Captured by `P ⊆ W` together with `P.card = r`. Using a
  `Finset` sub-family with `card = r` bakes in that the `r` sets are pairwise
  distinct, so no separate distinctness hypothesis is needed.
- **Petals nonempty?** Not required. With uniform size `k ≥ 2` and `r ≥ 2`
  distinct members whose pairwise intersections all equal `Y`, no member can
  equal `Y` (that would force `|Y| = k` and hence another member `⊇ Y` of size
  `k` to equal `Y`, contradicting distinctness), so every petal is automatically
  nonempty. For `r = 1` the pairwise condition is vacuous, which is the usual
  convention for a 1-petal sunflower.
- **Logarithm.** `Real.log` (natural log), applied to `(k : ℝ)`. The base only
  changes `C` by a constant factor, so any fixed base is equivalent; `Real.log`
  is the most frictionless in Mathlib.
- **`k = 0, 1`.** Handled by the hypothesis `2 ≤ k`, which guarantees
  `Real.log k ≥ Real.log 2 > 0`. For `k = 1` the canonical bound
  `(C r log 1)^1 = 0` is genuinely wrong (it would claim any nonempty family of
  singletons has an `r`-petal sunflower), and `k = 0` forces `W ⊆ {∅}`; both are
  degenerate, so restricting to `k ≥ 2` keeps the clean `(C r log k)^k` form
  without a `max`/`+1` patch. `r ≥ 1` is imposed by `1 ≤ r`.
- **Constant `C`.** Existentially quantified inside the theorem
  (`∃ C : ℝ, 0 < C ∧ …`) — the direct reading of "there is an absolute
  constant `C`". The `_const` variant supplies it as a hypothesis.
- **Cardinality comparison.** Done in `ℝ`: `(C r log k)^k < (W.card : ℝ)`, with
  `W.card` cast from `ℕ`. Strict `<`, matching "`|W| > (C r log k)^k`".

## Uncertainties / guessed identifiers

- Mathlib does contain sunflower material in
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean`. I did not rely on it: the
  exact name and signature of its predicate (whether it is `Finset.IsSunflower`,
  whether it takes the petal count `r` and/or the core `t` as explicit
  arguments, whether it bundles `r ≤ 𝒮.card`) I am not certain of, so I inlined
  an equivalent local definition. If aligning with Mathlib, the intended
  correspondence is `IsSunflower P Y ↔ (Mathlib predicate with core `Y`)`, plus
  `P.card = r` for the petal count.
- `import Mathlib` (the whole library) is used for simplicity; the only real
  dependencies are `Finset`, `Set.Pairwise`, and `Real.log`.
- The `∀ {α : Type*} [DecidableEq α] …` binders occurring under `∃ C` are, to my
  knowledge, accepted by Lean 4 / Mathlib; if a particular elaboration setting
  rejects implicit/instance binders there, moving `α` and its `DecidableEq`
  instance to `variable`s before the theorem (or into `improved_sunflower_lemma_const`
  style) is an equivalent fix.
- No Lean compiler was available; identifiers and syntax are from memory of
  Mathlib.
