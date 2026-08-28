# agent_017 — improved sunflower lemma (statement only)

## Form chosen

A single primary theorem `improved_sunflower_lemma` of shape

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
  1 ≤ k → 1 ≤ r → (∀ s ∈ W, s.card = k) →
  (C * r * max (Real.log k) 1) ^ k < (W.card : ℝ) →
  ∃ P Y, P ⊆ W ∧ P.card = r ∧ IsSunflower P Y
```

plus a secondary `improved_sunflower_lemma_function` giving the `f(k,r) ≤ (C r log k)^k`
reformulation, with the sunflower function `f` passed abstractly via its defining property
(there is no canonical Mathlib `f` to refer to).

Both end in `:= by sorry`. Nothing is proved.

## Encoding decisions and why

- **Set representation.** `Finset α` over an ambient type `α : Type*` with
  `[DecidableEq α]`; the family is `W : Finset (Finset α)`. This makes "finite family",
  "each set has cardinality exactly `k`" (`Finset.card`), and "distinct members"
  all cheap. The ambient type is universe-polymorphic and quantified *inside* the
  existential over `C`, which is legal since the body is a `Prop`.

- **Sunflower predicate.** Defined locally:
  `IsSunflower P Y := (↑P : Set (Finset α)).Pairwise (fun s t => s ∩ t = Y)`.
  `Set.Pairwise` already builds in `s ≠ t`, so this says exactly "all pairwise
  intersections of distinct petals equal the core `Y`". The petal count is expressed
  separately as `P.card = r`. For `r ≥ 2` this predicate implies the usual
  "any element in ≥ 2 petals is in all petals" property, and the petals `s \ Y` are then
  pairwise disjoint.

- **Distinctness.** Free: `P : Finset (Finset α)` with `P.card = r` gives `r` distinct
  sets.

- **Petals nonempty?** Not required (classical definition; the task allows an empty core
  and does not demand nonempty petals).

- **Which logarithm / small `k`.** `Real.log` (natural log). Because `Real.log 1 = 0`
  (and `Real.log 0 = 0`), the literal bound `(C r log k)^k` is *false* at `k = 1`
  (a family of `> 0` singletons need not contain `r ≥ 2` distinct sets). I use
  `max (Real.log k) 1`: identical asymptotics, agrees with `log k` once `k` is large,
  and keeps the statement true and non-vacuous for every `k ≥ 1`. Hypotheses
  `1 ≤ k`, `1 ≤ r` cover "positive integers"; `k = 0` is excluded.

- **The constant `C`.** Existentially quantified inside the theorem (`∃ C : ℝ, 0 < C ∧ …`),
  matching "there is an absolute constant". Kept real-valued.

- **Bound comparison.** Strict `<` with `W.card` coerced to `ℝ`, matching
  `|W| > (C r log k)^k`.

- **Conclusion.** `∃ P Y, P ⊆ W ∧ P.card = r ∧ IsSunflower P Y` — an explicit core `Y`
  and an explicit `r`-element subfamily of `W`.

## Uncertainties

- **Mathlib may already define a sunflower.** I believe there is
  `Mathlib.Combinatorics.SetFamily.Sunflower` with something like `Finset.IsSunflower`
  (possibly a 3-argument version bundling the petal count `r`, and an Erdős–Rado
  existence lemma such as `Finset.sunflower_exists` / `exists_isSunflower`). I could not
  verify the exact identifiers, so I defined `IsSunflower` locally to keep the file
  self-contained. If the Mathlib name exists, this local def should be defeq/equivalent
  to the "pairwise intersections coincide" formulation.

- **`import Mathlib`** is used for simplicity; only `Real.log`, `Finset`, and
  `Set.Pairwise` are actually needed.

- The `f`-reformulation theorem takes `f` and its specification as hypotheses rather than
  referring to a named constant; if Mathlib has an official sunflower function the
  statement should be rephrased against it.

- Not machine-checked: no Lean compiler was available. Possible minor issues: coercion
  elaboration in `(C * (r:ℝ) * max (Real.log (k:ℝ)) 1) ^ k`, and the exact spelling of
  the `Finset → Set` coercion inside `Set.Pairwise`.
