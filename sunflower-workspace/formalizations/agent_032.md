# agent_032 — improved sunflower lemma, statement

## Form chosen

A single `theorem improved_sunflower_lemma := by sorry` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ (α) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α), (∀ S ∈ W, S.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
      ∃ core T, T ⊆ W ∧ T.card = r ∧ IsSunflower T core
```

plus a helper `def IsSunflower (T : Finset (Finset α)) (core : Finset α) : Prop`.

## Encoding decisions and rationale

- **Set representation**: `Finset α` for individual sets over an arbitrary ambient type `α`,
  `Finset (Finset α)` for the family `W`. This keeps everything finite and decidable without
  carrying `Set.Finite` hypotheses. `[DecidableEq α]` is assumed (needed for `Finset.inter`
  and membership/subset on `Finset (Finset α)`).
- **`α` quantified inside, after `C`**: so that `C` is a true absolute constant not allowed
  to depend on the ambient type. `k`, `r`, `W` are likewise all under the same `∃ C`.
- **Sunflower predicate**: defined locally as
  `(T : Set (Finset α)).Pairwise (fun S₁ S₂ => S₁ ∩ S₂ = core)`.
  This is the "all pairwise intersections coincide (with the core)" formulation.
  `Set.Pairwise` constrains only distinct pairs, which is exactly right.
- **Number of petals / distinctness**: petals are members of the `Finset` `T`, so they are
  automatically distinct; the petal count is `T.card`, and "sunflower with `r` petals" is
  `T.card = r` together with `T ⊆ W`. I used `= r` (exact), matching the sunflower function
  `f(k, r)`; `≥ r` would also be defensible.
- **Petals nonempty**: not separately required. With `S.card = k` for all `S ∈ W` and
  `k ≥ 2`, any genuine sunflower has `core.card < k`, so petals `S \ core` are nonempty.
- **Cardinality**: `Finset.card` throughout.
- **Logarithm**: `Real.log` (natural log). The choice of base only rescales the absolute
  constant `C`, so any fixed base is equivalent; `Real.log` is the most standard Mathlib
  identifier.
- **Threshold comparison**: the RHS `(C r log k)^k` lives in `ℝ`; compared with `|W|` via
  `(W.card : ℝ)`. Strict `<` matches "`|W| > (C r log k)^k`".
- **`k = 0, 1` handling**: excluded via `2 ≤ k`. For `k ≤ 1`, `Real.log k ≤ 0` makes the
  threshold `0` or degenerate, and the informal claim ("`|W| > threshold` forces an
  `r`-petal sunflower") is simply false for `k = 1` (e.g. `1 ≤ |W| < r` distinct singletons).
  The literature states the bound for `k ≥ 2`. An alternative that keeps `k ≥ 1` is to
  replace `Real.log k` by `max 1 (Real.log k)`; I preferred the cleaner literal `Real.log`.
- **`r`**: `1 ≤ r` assumed ("positive integers `k` and `r`"). `r = 1` is trivially true.
- **`C` existential vs named/hypothesis**: existentially quantified inside the theorem
  (`∃ C : ℝ, 0 < C ∧ …`), so the statement is a closed proposition with no free parameters.

## Uncertainties

- Mathlib already contains a classical sunflower development in
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean` with a predicate I believe is named
  `Finset.IsSunflower` (signature something like `IsSunflower (r : ℕ) (t : Finset α)
  (𝒮 : Finset (Finset α))`, possibly bundling `𝒮.card = r`) and an Erdős–Rado lemma
  (name possibly `Finset.exists_isSunflower` / `Finset.Set.exists_sunflower`). I did **not**
  rely on those exact identifiers: I deliberately define my own `IsSunflower` inside
  `namespace ImprovedSunflower` to stay self-contained and avoid a signature clash. If the
  Mathlib predicate is `Finset.IsSunflower` with a compatible meaning, this local `def`
  could be replaced by it.
- The *improved* bound `(C r log k)^k` itself is **not** in Mathlib (only the classical
  `(r-1)^k · k!`-type bound is), so the main theorem is stated from scratch.
- `Real.log` applied to a `Nat`: I wrote `Real.log (k : ℝ)` with an explicit cast; the exact
  need for the annotation vs. automatic coercion is a minor syntactic point.
- Whether `∀ (α : Type*) [DecidableEq α] …` nested under `∃ C : ℝ` elaborates without a
  universe-metavariable hiccup is not compiler-checked here; if it complains, hoisting `α`
  to an outer `variable` and accepting `∀ α, ∃ C` (C after α) is the fallback, at the cost
  of "absolute constant" strength.
