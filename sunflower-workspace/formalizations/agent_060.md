# agent_060 — improved sunflower lemma (statement only)

## Form chosen

A single `theorem improved_sunflower_lemma := by sorry` of the shape

```
∃ C : ℝ, 0 < C ∧
  ∀ {α} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
    2 ≤ k → 1 ≤ r →
    (∀ s ∈ W, s.card = k) →
    (C * (r : ℝ) * Real.log k) ^ k < (W.card : ℝ) →
    ∃ S ⊆ W, ∃ Y, S.card = r ∧ IsSunflower S Y
```

plus a local `def IsSunflower`.

## Encoding decisions and rationale

- **Set representation.** Ambient type `α` with `[DecidableEq α]`; a family is
  `W : Finset (Finset α)`, each member a `Finset α`. `Finset (Finset α)` is the
  most direct reading of "finite family of sets" and gives distinctness of
  members for free. `DecidableEq` is needed for `s ∩ t`.
- **Cardinality.** `Finset.card` throughout: `s.card = k` for member size,
  `W.card` for family size, `S.card = r` for the number of petals. No
  `Set.ncard`/`Nat.card` since everything is already a `Finset`.
- **Sunflower predicate.** Defined locally as
  `IsSunflower S Y := ∀ s ∈ S, ∀ t ∈ S, s ≠ t → s ∩ t = Y`
  (the "all pairwise intersections coincide" formulation used in the
  ALWZ / Rao / BCW papers). The core `Y` is existentially quantified in the
  theorem. Petal disjointness and the "in two ⇒ in all" property are
  consequences for `r ≥ 3` and are not restated.
- **Number of petals.** Encoded as a subfamily `S ⊆ W` with `S.card = r`;
  distinctness of the `r` sets is automatic.
- **Petals nonempty / core strictly smaller.** Not required. This only weakens
  the conclusion, so the stated theorem is (if anything) safer/weaker than the
  "proper sunflower" version delivered by the proofs.
- **Logarithm.** `Real.log` (natural log). The base is irrelevant because it is
  absorbed into the absolute constant `C`.
- **`k = 0, 1` handling.** Hypothesis `2 ≤ k`. For `k = 1`, `Real.log 1 = 0`
  makes the RHS `0`, but `f(1, r) = r`, so no `(… log k)^k` bound can hold;
  `k = 0` is likewise degenerate. Restricting to `k ≥ 2` keeps the formula
  literally `(C * r * log k) ^ k` as in the source statement. `r` kept at
  `1 ≤ r` (the cases `r = 1, 2` are trivially true).
- **Constant `C`.** Existentially quantified at the front with `0 < C`, and
  placed outside the `∀ α` so that it is genuinely absolute (independent of the
  ambient type).
- **ℕ vs ℝ comparison.** `W.card` is coerced to `ℝ`; `k, r` coerced inside the
  bound. Exponent `^ k` is `Monoid.npow` (natural exponent).

## Uncertainties / guesses

- I believe Mathlib (as of early 2026) has **no** sunflower definition or
  sunflower lemma, so `IsSunflower` is defined here. If one has since been
  added, the likely name is `Finset.IsSunflower` (or `Set.IsSunflower`); the
  intended meaning matches this file's `def`.
- Not compiler-checked: that `∀ {α : Type*} [DecidableEq α] …` nested inside
  `∃ C, _ ∧ _` elaborates cleanly. It should (Mathlib routinely quantifies over
  `∀ {α} [inst] …`); if it does not, move `α` and the instance to theorem
  parameters, yielding the slightly weaker `∀ α, ∃ C, …` ordering.
- The refined constant is written as `C * r * log k` per the task statement;
  variant literatures use `C * r * log(r k)` or `(A log k)^k · r^k`. These
  differ only by absorbing factors into `C`, but the `k = 1` issue is the
  reason for the explicit `2 ≤ k`.
- `Real.log k` relies on the `ℕ → ℝ` coercion (`Real.log (↑k)`); standard.
