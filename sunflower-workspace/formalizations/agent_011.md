# agent_011 — improved sunflower lemma (statement only)

## Form chosen

A single existential statement:

```
∃ C : ℝ, 0 < C ∧
  ∀ {α} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
    2 ≤ k → 1 ≤ r →
    (∀ A ∈ W, A.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ 𝒮 ⊆ W, IsSunflower 𝒮 r
```

with a local `IsSunflower` predicate.

## Encoding decisions and why

- **Set representation:** `Finset α` over an ambient type `α` with `[DecidableEq α]`; the family
  `W` is `Finset (Finset α)`. This makes "finite family" free, makes distinctness of the members
  of `W` automatic, and makes `|W|` just `W.card : ℕ`. `α` is quantified inside the statement
  (implicit) so the constant `C` is genuinely universal over all ground types.
- **Sunflower definition:** explicit core. `IsSunflower 𝒮 r := 𝒮.card = r ∧ ∃ Y, ∀ A ∈ 𝒮, ∀ B ∈ 𝒮,
  A ≠ B → A ∩ B = Y`. The `𝒮.card = r` conjunct pins the petal count and (via `Finset`) gives
  `r` distinct sets, so no separate distinctness hypothesis is needed. The "every element in ≥ 2
  sets is in all of them" / "petals pairwise disjoint" phrasing is a consequence of this
  condition, so it is not part of the definition.
- **Petals nonempty:** *not* required. The standard statement of the improved sunflower lemma does
  not need it; for `r ≥ 2` the condition already forces at most one empty petal. Adding
  `∀ A ∈ 𝒮, Y ⊂ A` would give the "proper"/"loose" sunflower variant.
- **Conclusion as subfamily:** `∃ 𝒮 ⊆ W, IsSunflower 𝒮 r` (i.e. `∃ 𝒮, 𝒮 ⊆ W ∧ IsSunflower 𝒮 r`).
- **Constant `C`:** existentially quantified inside the theorem, matching "there is an absolute
  constant `C`". Stated with `0 < C`.
- **Logarithm:** `Real.log` applied to `(k : ℝ)`. The base does not matter — a change of base
  multiplies the bound by a constant, absorbed into `C`. `Real.logb 2` or `Nat.log 2` would be
  equally faithful.
- **Degenerate `k`:** the hypothesis `2 ≤ k` is imposed. At `k = 1`, `Real.log 1 = 0` makes the
  RHS `0`, and `|W| > 0` does **not** imply an `r`-petal sunflower (`r ≥ 2`), so the displayed
  bound genuinely requires `k ≥ 2` (as in Rao's and BCW's statements). `k = 0` is likewise
  excluded. Alternatives considered: keep `1 ≤ k` and write `Real.log (k + 1)` or
  `max (Real.log k) 1`; I preferred staying literally close to `(C r log k)^k` with the `k ≥ 2`
  side condition.
- **`r`:** `1 ≤ r` (positive integer, as stated). `r = 1` makes the conclusion trivial but the
  statement remains true and consistent with the definition.
- **Cardinality:** `Finset.card` throughout; comparison `(C * r * Real.log k) ^ k < (W.card : ℝ)`
  is in `ℝ` with `W.card` coerced. Coercions `(r : ℝ)`, `(k : ℝ)` written explicitly.
- **`f(k,r) ≤ (C r log k)^k` form:** not used, because defining the sunflower function `f` in Lean
  first requires proving it is well-defined (finiteness of sunflower-free families). The family
  form above is equivalent and self-contained.

## Uncertainties

- **No Mathlib `Sunflower` predicate.** I searched the local Mathlib checkout
  (`grep -ri sunflower`, `find -iname '*sunflower*'`) and found nothing, so `IsSunflower` is
  defined here. If a future Mathlib adds `Finset.IsSunflower` / `SetFamily.Sunflower`, this should
  be aligned with it.
- `Real.log` is the confirmed name (`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`);
  `Real.logb` exists in `.../Log/Base.lean`.
- `∃ 𝒮 ⊆ W, P 𝒮` binder-predicate notation and the mixed ℝ/ℕ arithmetic (`binop%` coercion
  insertion) are standard in current Mathlib; not machine-checked here (no compiler available).
- Placement of the instance binder `[DecidableEq α]` inside the inner `∀` after `{α : Type*}` is
  the intended order; not compiler-verified.
- Whether the "canonical" statement uses `log k`, `log(rk)`, or `log(k r)` varies by source
  (ALWZ vs Rao vs BCW). I followed the task's `log k`.
