# agent_021 — improved sunflower lemma, statement only

## Form chosen

A single theorem `ImprovedSunflower.improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
  2 ≤ k → 1 ≤ r → (∀ s ∈ W, s.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  ContainsSunflower W r
```

with two auxiliary definitions, `IsSunflower` (a subfamily + core) and `ContainsSunflower`
(`W` has an `r`-petal sunflower subfamily).

## Encoding decisions and rationale

- **Set representation:** `Finset α` for individual sets, `W : Finset (Finset α)` for the
  family, over an arbitrary ambient `α` with `[DecidableEq α]`. This makes "finite family"
  and "finite sets" automatic and gives `Finset.card` directly. `DecidableEq` is needed for
  `s ∩ t`.
- **Sunflower predicate:** defined explicitly with an existential core `Y : Finset α`.
  `IsSunflower P Y` says `Y ⊆ s` for all `s ∈ P` *and* `s ∩ t = Y` for all distinct
  `s t ∈ P`. The pairwise-intersection clause is the mathematical content; the `Y ⊆ s`
  clause is redundant once `#P ≥ 2` but disambiguates degenerate small cases. Pairwise petal
  disjointness (`(s \ Y) ∩ (t \ Y) = ∅`) follows and is not stated separately.
- **Petals = subfamily of size `r`:** `ContainsSunflower W r` asks for `P ⊆ W` with
  `P.card = r` and `IsSunflower P Y`. Because `P` is a `Finset`, `P.card = r` encodes `r`
  *distinct* petals, so distinctness is not stated as a side condition.
- **Petals nonempty:** not required. For `r ≥ 2` distinct members with common pairwise
  intersection `Y` automatically satisfy `Y ⊊ s`, so petals are nonempty anyway.
- **Logarithm:** `Real.log` (natural log). The base only changes the absolute constant `C`.
- **`k = 0, 1`:** excluded via `2 ≤ k`. For `k ≤ 1`, `Real.log k ≤ 0` makes the RHS `≤ 0`
  and the implication false for `r ≥ 2` regardless of `C`; the literature also states the
  improved bound for `k ≥ 2`. `r` is kept general with `1 ≤ r`.
- **The constant `C`:** existentially quantified, and placed *outside* all other quantifiers
  so it is genuinely one absolute constant. `0 < C` is included.
- **Comparison in `ℝ`:** `W.card`, `r`, `k` are coerced to `ℝ`; the bound is strict (`<`),
  matching "`|W| > (C r log k)^k`".

## Uncertainties

- Mathlib may already provide a sunflower predicate (I believe there is
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean` with something like `Finset.IsSunflower`
  / `IsSunflower 𝒮 t := ∀ ⦃s₁⦄ ∈ 𝒮, ∀ ⦃s₂⦄ ∈ 𝒮, s₁ ≠ s₂ → s₁ ∩ s₂ = t`, plus the classical
  bound `f(k,r) ≤ k! (r-1)^k`). I did not rely on it: identifier/namespace/argument order
  are uncertain, and the classical file does not contain the improved bound. My `IsSunflower`
  is essentially that predicate plus the explicit `Y ⊆ s` clause.
- `import Mathlib` is used for simplicity; only `Real.log` and `Finset` machinery are actually
  needed.
- Binder syntax `∀ {α : Type*} [DecidableEq α] (k r : ℕ) ...` inside the existential is, to my
  knowledge, accepted in Lean 4 / Mathlib; I have no compiler to confirm.
