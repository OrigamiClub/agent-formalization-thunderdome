# agent_059 — improved sunflower lemma (statement only)

## Form chosen

One existential statement:

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α), (∀ S ∈ W, S.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) → HasSunflowerWith W r
```

with two auxiliary defs `IsSunflower` and `HasSunflowerWith`.

## Encoding decisions

- **Set representation.** Ambient type `α`, each set is `Finset α`, the family is
  `W : Finset (Finset α)`. This makes "finite family" and "each member finite"
  automatic, and cardinalities are plain `Finset.card`.
- **`α` and `W` quantified inside `∃ C`.** `C` must not depend on the ground type or
  the family, so the universal quantifiers sit under the existential. `α` is re-bound
  there (shadowing the section variable) together with its `DecidableEq` instance,
  which `Finset.inter` needs.
- **Sunflower predicate.** Defined explicitly rather than relying on Mathlib. A
  sunflower is a subfamily `P ⊆ W` with `P.card = r` and all pairwise intersections of
  distinct members equal to a common core `Y`. Distinctness of the `r` members is free
  because `P` is a `Finset`; `P.card = r` pins the count. The "core is contained in
  every set / petals disjoint / any element in ≥2 sets is in all" phrasing is
  equivalent to this for `r ≥ 2` and is noted in the docstring. Petals are not required
  nonempty (a sunflower with core `= ` one of its sets is still allowed, as is standard).
- **Which logarithm.** `Real.log` (natural log). The base is irrelevant since it only
  rescales the absolute constant `C`.
- **`k = 0, 1`.** Handled by the hypothesis `2 ≤ k`. For `k = 1`, `Real.log 1 = 0`
  would make the RHS `0` for every `C`, which is false as a sunflower bound
  (`f(1, r) = r`); for `k = 0` the family has at most one element. Both are trivial and
  excluded rather than patched (an alternative would be `Real.log k + 1` or
  `Real.log (k + 1)` in the bound, which keeps the asymptotics but deviates from the
  literal `log k`).
- **`C` existential vs hypothesis.** Existential (`∃ C, 0 < C ∧ …`), matching "there is
  an absolute constant `C`".
- **Bound direction / coercions.** Stated as `RHS < (W.card : ℝ)` (i.e. `|W| > RHS`).
  `r : ℕ` and `k : ℕ` are coerced to `ℝ`; the exponent `^ k` is the natural-number
  power on `ℝ`.
- **Cardinality exactly `k`.** `∀ S ∈ W, S.card = k` (not `≤`); this is a `k`-uniform
  family as in the statement.

## Uncertainties

- Mathlib does contain a classical sunflower development
  (`Mathlib/Combinatorics/SetFamily/Sunflower.lean`): a predicate around the name
  `Finset.IsSunflower` and an Erdős–Rado bound around `Finset.exists_sunflower` /
  `Finset.Set.PairwiseDisjoint`-style petals. I did not rely on it — the exact current
  signature (argument order, whether the core/petal-count are explicit) is something I
  cannot verify without a compiler, and the *improved* bound is certainly not in
  Mathlib. The self-contained `IsSunflower` here is deliberately independent of it.
- `Real.log` is the standard Mathlib name for the natural logarithm; treated as known.
- `import Mathlib` (the whole library) is used for robustness; only `Real.log` and
  `Finset` basics are actually needed.
- The precise shape of the state-of-the-art bound (e.g. `log k` vs `log(rk)`, extra
  `log log` factors) varies across ALWZ / Rao / Bell–Chueluecha–Warnke; I used the
  target `(C · r · log k) ^ k` exactly as given in the task.
