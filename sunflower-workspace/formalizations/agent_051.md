# Agent 051 — improved sunflower lemma, statement formalization

## Form chosen

One theorem, `ImprovedSunflower.improved_sunflower_lemma`, of shape

```
∃ C : ℝ, 0 < C ∧ ∀ (α) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
  2 ≤ k → 1 ≤ r → (∀ s ∈ W, s.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  ∃ core P, P ⊆ W ∧ IsSunflower r core P
```

plus an auxiliary `def IsSunflower`.

## Encoding decisions and why

- **Set representation.** Ambient type `α` with `[DecidableEq α]`; individual sets are
  `Finset α`; the family `W` is `Finset (Finset α)`. This makes "finite family" automatic
  and lets `Finset.card` do all the counting. "Each of cardinality exactly `k`" is
  `∀ s ∈ W, s.card = k`.

- **Sunflower predicate.** Defined explicitly with an explicit core:
  `P.card = r ∧ ∀ s ∈ P, ∀ t ∈ P, s ≠ t → s ∩ t = core`.
  - Chosen the "all pairwise intersections coincide with a named core `Y`" formulation
    (equivalent to the kernel/petal description; petal disjointness and the
    "in ≥ 2 ⇒ in all" property follow).
  - The `r` petals are distinct for free (elements of a `Finset`); `P.card = r` pins the
    count, so distinctness needs no separate hypothesis.
  - Petals `s \ core` are **not** required to be nonempty (matches the usual definition;
    at most one petal can be empty once `r ≥ 2`).
  - Conclusion gives `P ⊆ W` so the sunflower is genuinely found inside `W`.

- **Logarithm.** `Real.log` (natural log). Any fixed base only rescales the absolute
  constant `C`, so the base is immaterial to the statement; `Real.log` is the most
  standard Mathlib choice. `Real.log (k : ℝ)` is total (`= 0` at `k = 0, 1`).

- **k = 1 / k = 0 handling.** Added hypothesis `2 ≤ k`. At `k = 1`, `Real.log 1 = 0`
  makes the bound `(C·r·0)^1 = 0`, so the hypothesis would read `|W| > 0` and the
  conclusion (an `r`-petal sunflower, `r ≥ 2`) can fail — e.g. `W = {{a}}`. Restricting
  to `k ≥ 2` is the form in which the improved bound is normally stated and is true.
  A genuinely all-positive-`k` variant would write `max 1 (Real.log k)` in place of
  `Real.log k`; noted in the source docstring.

- **The constant `C`.** Existentially quantified *inside* the theorem but *outside* the
  quantifiers over `α, k, r, W` — i.e. a single absolute constant, as in the informal
  statement. Taken in `ℝ` with `0 < C` (a `ℕ` constant would work equally well).

- **Inequality direction.** Written `threshold < (W.card : ℝ)`, i.e. `|W| > threshold`,
  with `W.card` cast to `ℝ`. Exponent `^ k` is the natural-number power.

- **`r`.** Required `1 ≤ r`. `r = 1` is vacuously fine (a single set); `r = 0` is
  excluded only to avoid a trivial/degenerate case, not for correctness.

## Uncertainties

- Mathlib may already provide `Finset.IsSunflower` and an Erdős–Rado
  `Finset.exists_isSunflower` in `Mathlib.Combinatorics.SetFamily.Sunflower` (argument
  order and exact names not verified from memory). I deliberately defined a local
  `IsSunflower` to keep the file self-contained and avoid a name/shape mismatch; if the
  Mathlib predicate exists it is expected to be definitionally the same
  (`card = r` ∧ pairwise-intersection-equals-core, the latter possibly phrased with
  `Set.Pairwise`).
- `Real.log` applied to a `ℕ` argument relies on the standard `Nat.cast` coercion being
  inserted; I wrote `Real.log (k : ℝ)` explicitly to be safe. Likewise `(r : ℝ)` and
  `(W.card : ℝ)` are written with explicit casts.
- `∀ (α : Type*) [DecidableEq α], …` nested under `∃ C : ℝ` pushes the statement into a
  higher universe; this is legal for a `Prop` and used elsewhere in Mathlib, but I could
  not machine-check it here (no compiler available).
- No claim that the bound is tight or that the constant is small; only the upper bound
  (existence of the sunflower) is stated.
