# agent_090 — improved sunflower lemma (statement only)

## Form chosen

Single `theorem improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ {α} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
  2 ≤ k → 1 ≤ r → (∀ s ∈ W, s.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  ∃ Y S, S ⊆ W ∧ IsSunflower r Y S
```

plus a local `def IsSunflower r Y S := S.card = r ∧ (S : Set _).Pairwise (· ∩ · = Y)`.

## Encoding decisions and why

- **Sets**: `Finset α` over an arbitrary `α` with `[DecidableEq α]`; the family `W` is
  `Finset (Finset α)`. This matches Mathlib's existing `Combinatorics/SetFamily` conventions and
  gives finiteness for free. The found sunflower `S` is a `Finset (Finset α)` with `S ⊆ W`.
- **"Sunflower with r petals"**: defined explicitly with an explicit core `Y` and
  `Set.Pairwise (fun s₁ s₂ => s₁ ∩ s₂ = Y)`. `Set.Pairwise` constrains only distinct pairs, i.e.
  exactly "for every i ≠ j". Cardinality of the sunflower is bundled as `S.card = r`.
- **Distinctness** of the `r` members: automatic because `S` is a `Finset`; `S.card = r` then
  gives exactly `r` distinct sets.
- **Petals nonempty**: not stated; it is automatic here (equal-cardinality members, `r ≥ 2`), and
  the classical statement does not require it.
- **Cardinality**: `Finset.card` throughout (`s.card = k`, `W.card`, `S.card`).
- **Logarithm**: `Real.log` (natural log). The constant `C` absorbs any change of log base.
- **k = 0 / k = 1**: excluded via `2 ≤ k`. For `k = 1`, `Real.log 1 = 0` makes
  `(C·r·log k)^k = 0`, but `f(1, r) = r − 1 > 0`, so the displayed bound is literally false at
  `k = 1`; standard statements restrict to `k ≥ 2` (or replace `log k` by `log(rk)` / `max 1 (log k)`).
  I kept the task's exact expression `(C·r·log k)^k` and restricted `k`.
- **r**: `1 ≤ r` ("positive integers r"). `r = 1` is trivially true.
- **C**: existentially quantified *outside* the quantifier over `α`, so it is absolute — one `C`
  works for every ambient type, every `k`, every `r`. `0 < C` included.
- **Comparison across ℕ/ℝ**: bound compared as reals, `... < (W.card : ℝ)`.

## Uncertainties

- **Mathlib may already have a sunflower predicate.** I believe
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean` defines something like `Finset.IsSunflower`
  (core + pairwise-intersection condition) and proves the classical Erdős–Rado bound (name
  possibly `Finset.exists_isSunflower` or similar). I could not verify identifiers, so I defined
  a local `ImprovedSunflower.IsSunflower` to keep the file self-contained. If the Mathlib
  predicate exists, this def should be defeq / trivially interchangeable.
- `(W : Set (Finset α)).Sized k` (from Mathlib) is an idiomatic alternative to
  `∀ s ∈ W, s.card = k`; I used the explicit form to avoid a guessed identifier in the statement.
- Putting `∀ {α : Type*} [DecidableEq α] ...` inside an `∃` is legal Lean 4 but slightly unusual;
  an alternative is to make `α` a section `variable` (at the cost of `C` formally being allowed to
  depend on `α`). I preferred faithfully expressing "absolute constant".
- `import Mathlib` used for brevity; the minimal imports would be the `Finset`, `Set.Pairwise`,
  and `Real.log` files.
