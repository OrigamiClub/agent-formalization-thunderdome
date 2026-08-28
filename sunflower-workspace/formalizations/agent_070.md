# Agent 070 — note on the formalization

## Form chosen

A single `theorem improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
  0 < k → 0 < r → (∀ S ∈ W, S.card = k) →
  (C * r * Real.log (k + 1)) ^ k < (W.card : ℝ) →
  ∃ Y P, P ⊆ W ∧ IsSunflower r Y P
```

with an auxiliary `def IsSunflower r Y P := P.card = r ∧ ∀ S ∈ P, ∀ T ∈ P, S ≠ T → S ∩ T = Y`.

## Encoding decisions and rationale

- **Set representation:** `Finset (Finset α)` over an arbitrary ambient type `α`
  with `[DecidableEq α]`. This gives finiteness of the family and distinctness of
  its members for free, and `S ∩ T` / `Finset.card` are directly available.
- **Sunflower predicate:** defined explicitly via "all pairwise intersections equal
  the core `Y`", plus `P.card = r` to pin the number of petals. This is the same
  formulation Mathlib uses for its classical `Finset.IsSunflower` (which I did not
  depend on, to keep the file self-contained and avoid a possibly-misremembered
  signature). Pairwise disjointness of petals, the "in two ⇒ in all" property, and
  `Y ⊆ S` (for `r ≥ 2`) are consequences, so they are not stated.
- **Petals nonempty / core nontrivial:** not required (matches the standard
  definition; the lemma is about the combinatorial structure, not size of petals).
- **The constant `C`:** existentially quantified with `0 < C`, matching "there is an
  absolute constant `C`". It is bound outside the quantifier over `α, k, r, W`, so it
  is genuinely uniform.
- **Logarithm:** `Real.log` (natural log). Applied to `k + 1` rather than `k`.
  Reason: at `k = 1`, `Real.log 1 = 0` makes `(C r log k)^k = 0`, which would falsely
  claim that any family with `|W| ≥ 1` contains an `r`-petal sunflower. Using
  `log (k + 1)` fixes the `k = 1` boundary while only inflating the implied
  (existential) constant; for `k ≥ 2` the two forms differ by a bounded factor. The
  base of the log is irrelevant here since it is absorbed into `C`; `Real.log` is the
  most convenient Mathlib choice.
- **`k = 0`:** excluded by `0 < k` (and would be vacuous anyway: only `S = ∅`).
- **Comparison in `ℝ`:** `W.card` and `r` are cast to `ℝ`; the power `_ ^ k` is the
  monoid power `ℝ → ℕ → ℝ`.
- **"Contains a sunflower":** the witnessing sub-family `P` is required to satisfy
  `P ⊆ W`.

## Uncertainties

- I did not rely on Mathlib's `Finset.IsSunflower` / the classical Erdős–Rado
  sunflower lemma name (`Finset.exists_isSunflower` or similar) because I could not
  verify the exact identifier/signature without a compiler. My `IsSunflower` is a
  local definition in `namespace ImprovedSunflower`, so there is no clash.
- `∀ {α : Type*} [DecidableEq α], …` appearing inside the body of an `∃` should
  elaborate with the universe autobound as a parameter of the theorem (so `C` is
  independent of `α` and its universe); I believe this is accepted but could not
  check.
- The improved sunflower lemma itself is (to my knowledge) not in Mathlib, so this
  is a fresh statement rather than a re-statement of an existing lemma.
- Choice of `log (k + 1)` vs. alternatives (`1 + Real.log k`, `max 1 (Real.log k)`,
  or a hypothesis `2 ≤ k`) is a judgement call; all are faithful up to the
  existential constant.
