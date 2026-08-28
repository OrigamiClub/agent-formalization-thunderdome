# agent_063 — improved sunflower lemma (statement)

## Form chosen

Single theorem `improved_sunflower_lemma`:

```
∃ C : ℝ, 0 < C ∧
  ∀ {α} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
    ∀ W : Finset (Finset α),
      (∀ s ∈ W, s.card = k) →
      (C * (r:ℝ) * Real.log (k:ℝ)) ^ k < (W.card : ℝ) →
      ContainsSunflower W r
```

with two auxiliary definitions:

- `IsSunflowerWith S Y` : `∀ s ∈ S, ∀ t ∈ S, s ≠ t → s ∩ t = Y` (explicit core).
- `ContainsSunflower W r` : `∃ S ⊆ W, S.card = r ∧ ∃ Y, IsSunflowerWith S Y`.

## Encoding decisions and why

- **Set representation**: `Finset (Finset α)` over an arbitrary ambient type `α` with
  `[DecidableEq α]`. This is the lightest representation that gives a genuinely finite family
  and lets `∩` and `card` be plain `Finset` operations. `α` is universe-polymorphic and bound
  *inside* the statement so that the constant `C` is truly absolute (independent of `α`).
- **Sunflower predicate**: defined locally via an explicit core `Y` and pairwise intersections.
  I did not depend on a Mathlib identifier. Mathlib very likely has
  `Finset.IsSunflower (𝒮 : Finset (Finset α)) (t : Finset α)` in
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean` with the same meaning; I kept a local copy to
  stay self-contained and avoid a wrong-name break. Petal count is `S.card`.
- **Petals**: not required to be nonempty. With `k ≥ 2` and members of size `k`, petals `s \ Y`
  can only all be empty if every member equals `Y`, i.e. `S.card ≤ 1`; for `r ≥ 2` nonemptiness
  is therefore automatic, so adding it would be redundant.
- **Distinctness of the `r` chosen sets**: automatic — `S : Finset (Finset α)` with `S.card = r`.
- **Cardinality**: `Finset.card` throughout; comparison with the real bound via `(W.card : ℝ)`.
- **Logarithm**: `Real.log` (natural log). Base choice is absorbed into `C`, so this matches
  ALWZ/Rao/BCW up to the constant.
- **`k = 0, 1` handling**: hypothesis `2 ≤ k`. At `k = 1`, `Real.log 1 = 0` collapses the RHS to
  `0`, and the literal claim ("`|W| > 0` ⇒ `r` petals") is false; Rao and Bell–Chueluecha–Warnke
  also state the bound for `k ≥ 2`. This is a deliberate, documented deviation from the prompt's
  "all positive integers `k`" for correctness. An alternative keeping all `k ≥ 1` would replace
  `Real.log k` by `max 1 (Real.log k)`.
- **`r`**: `1 ≤ r` (positive, per prompt); `r = 1` is degenerate but harmless.
- **`C`**: existentially quantified inside the theorem, with `0 < C`.

## Uncertainties

- Whether `Finset.IsSunflower` (or `Set.IsSunflower`) exists in current Mathlib and its exact
  signature — avoided by using a local definition.
- Automatic `ℕ → ℝ` coercions inside `(C * (r:ℝ) * Real.log (k:ℝ)) ^ k`; written with explicit
  casts to reduce risk. The outer `^ k` is `Monoid.npow` with `k : ℕ`.
- `import Mathlib` (blanket import) assumed available.
