# Agent 079 — improved sunflower lemma, statement formalization

## Form chosen

A single `theorem improved_sunflower_lemma : ... := by sorry`, of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
  2 ≤ k → 1 ≤ r →
  (∀ s ∈ W, s.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  ∃ Y T, T ⊆ W ∧ IsSunflower r Y T
```

with a locally defined predicate `IsSunflower`.

## Encoding decisions and rationale

- **Set representation.** Ambient type `α` with `[DecidableEq α]`; a set is a
  `Finset α`; the family `W` is a `Finset (Finset α)`. This gives finiteness of
  `W` for free, makes `|W|` just `W.card`, and makes members automatically
  distinct. `DecidableEq` is needed for `Finset` intersection `s ∩ t`.

- **"Sunflower with `r` petals".** Defined explicitly with a core `Y : Finset α`:
  `IsSunflower r Y T` iff `T.card = r`, every `s ∈ T` contains `Y`, and
  `s ∩ t = Y` for all distinct `s, t ∈ T`. The witnessed sunflower is a
  subfamily `T ⊆ W`.
  - Distinctness of the `r` sets is automatic: `T` is a `Finset` of cardinality
    `r`.
  - Pairwise-disjoint petals and "any element in ≥ 2 members is in all of them"
    are *consequences* of the pairwise-intersection condition (see the doc
    comment), so they are not restated.
  - The clause `Y ⊆ s` is redundant for `r ≥ 2` (`Y = s ∩ t ⊆ s`); kept only to
    keep the predicate meaningful for `r ≤ 1`.
  - Petals are **not** required nonempty (standard; the empty-core / small
    cases are still covered).

- **The constant `C`.** Existentially quantified at the very front, *before* the
  quantifiers over `α, k, r, W`, so it is a genuine absolute constant. Required
  `0 < C`.

- **Logarithm.** `Real.log` (natural logarithm). Any other base is absorbed into
  `C`, so the choice is immaterial to the statement's content. The bound term
  `(C * r * Real.log k) ^ k` is real-valued and compared with the natural
  `W.card` cast to `ℝ`; the inequality is strict (`>` in the informal
  statement).

- **Small `k`.** Assumed `2 ≤ k`. For `k = 1`, `Real.log 1 = 0` makes the
  displayed bound `0`, which is false as a threshold (`r` distinct singletons
  are needed); for `k = 0`, `Real.log 0 = 0` in Mathlib's junk convention.
  Restricting to `k ≥ 2` is the cleanest way to state exactly the intended
  content. `r ≥ 1` encodes "positive integers `r`".

- **Cardinality.** `Finset.card` throughout (`s.card = k`, `W.card`).

## Uncertainties / guessed identifiers

- `Real.log` is the correct Mathlib name (natural log on `ℝ`); `Real.log 0 = 0`
  and `Real.log` of negatives is the standard junk value. High confidence.
- Mathlib **does** contain a sunflower development in
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean` with a predicate along the
  lines of `Finset.IsSunflower` / `Finset.EqUnion` and the classical bound
  (`(r-1)^k * k! < card`). I deliberately did **not** rely on its exact name or
  argument order (which I am not certain of) and defined `IsSunflower` locally
  instead, to keep the file self-contained and unambiguous. If aligning with
  Mathlib, that file is the place to look, and the improved bound proved here
  would be a strengthening of what Mathlib currently has.
- `∀ {α : Type*} [inst : DecidableEq α] ...` as binders inside a `∀`-term is
  valid Lean 4 syntax; used so that `C` precedes `α`.
- Not machine-checked: no Lean compiler was available. Intent is that only
  `sorry` is missing.
