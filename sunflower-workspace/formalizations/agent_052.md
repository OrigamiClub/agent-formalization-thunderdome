# agent_052 — improved sunflower lemma, statement note

## Form chosen

A single theorem `ImprovedSunflower.improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧
  ∀ {α : Type*} (k r : ℕ), 0 < k → 0 < r →
    ∀ W : Finset (Finset α),
      (∀ S ∈ W, S.card = k) →
      (C * r * (Real.log k + 1)) ^ k < (W.card : ℝ) →
      ∃ Y 𝒮, 𝒮 ⊆ W ∧ IsSunflower r Y 𝒮
```

plus an auxiliary `structure IsSunflower`.

## Encoding decisions

- **Set representation.** `Finset α` over an ambient type `α`, with the family a
  `Finset (Finset α)`. This gives distinctness of members and finiteness of the family for
  free, and `Finset.card` for all cardinalities. No separate distinctness hypothesis is
  needed.
- **Sunflower predicate.** Defined locally as `IsSunflower r Y 𝒮` with two fields:
  `𝒮.card = r` (exactly `r` petals) and `∀ S T ∈ 𝒮, S ≠ T → S ∩ T = Y` (all pairwise
  intersections equal a common core `Y`). The "every element in ≥ 2 sets is in all" and
  "petals `S \ Y` pairwise disjoint" properties are logical consequences and are not
  restated. The core `Y` is carried explicitly and quantified existentially in the theorem;
  for `r ≥ 2` it is uniquely determined anyway.
- **Petals not required nonempty.** The problem statement does not require it, and the
  classical lemma does not either.
- **Sub-family.** The conclusion produces `𝒮 ⊆ W`; membership in a `Finset (Finset α)`
  already encodes "distinct sets `S_1, …, S_r`".
- **Constant `C`.** Existentially quantified and required positive. `α` is bound *inside*
  the `∃ C`, so `C` cannot depend on the ambient type — it is a genuine absolute constant.
- **Logarithm.** `Real.log` (natural log). Choice of base only rescales `C`, so it is
  immaterial to the statement.
- **`k = 1` / small `k`.** `Real.log 1 = 0`, so a literal `(C r log k)^k` bound would read
  `|W| > 0` at `k = 1` and be false (take `W` = many distinct singletons with `r ≥ 2`… in
  fact that *is* a sunflower, but e.g. `|W| = 1 < r`). To keep the statement true and
  faithful for every positive `k` I use `Real.log k + 1` as the base factor. For `k ≥ 2`
  this is `Θ(log k)`, so the asymptotic content (`f(k,r) ≤ (C r log k)^k`) is unchanged; for
  `k = 1` it becomes `|W| > C r`, which correctly forces `r` distinct singletons (a
  sunflower with core `∅`). `k = 0` is excluded by `0 < k` (a family of `0`-sets has at most
  one member).
- **Inequality.** Stated as `bound < (W.card : ℝ)`, i.e. `|W| >` bound, matching
  "`|W| > (C r log k)^k`". Cardinality cast to `ℝ`.

## Uncertainties

- **Possible existing Mathlib predicate.** Mathlib may contain a sunflower lemma / a
  `Finset.IsSunflower` (or `Sunflower`) definition (Erdős–Rado bound). I could not verify its
  exact name or field signature from memory, so I deliberately defined a local
  `ImprovedSunflower.IsSunflower` to keep the file self-contained and unambiguous. If a
  canonical predicate exists, this local one should be defeq-compatible up to how the core is
  presented (explicit `Y` vs. bundled/derived).
- **Identifier `Real.log`** is standard Mathlib; the coercion `((k : ℕ) : ℝ)` inside it and
  `(r : ℝ)`, `(W.card : ℝ)` rely on the usual `Nat.cast`. Written explicitly to avoid
  elaboration ambiguity, but not compiler-checked.
- **`import Mathlib`** used for brevity; the statement only needs `Finset` and
  `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
- Universe-polymorphic binder `∀ {α : Type*}` placed under `∃ C : ℝ` is intended and, to my
  knowledge, well-formed, but not verified with a compiler.
