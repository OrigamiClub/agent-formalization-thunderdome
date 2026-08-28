# Agent 065 — improved sunflower lemma (statement only)

## Form chosen

A single theorem `improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ {α} [DecidableEq α] (W : Finset (Finset α)),
    (∀ s ∈ W, s.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ P ⊆ W, ∃ Y : Finset α, IsSunflower r Y P
```

closed with `:= by sorry`. One auxiliary `def IsSunflower`.

## Encoding decisions

- **Set representation.** Ambient type `α` with `[DecidableEq α]`; a family is
  `W : Finset (Finset α)`. This keeps everything finite and decidable with no
  side finiteness hypotheses, and makes "distinct members" automatic (elements of
  a `Finset`). The subfamily forming the sunflower is `P : Finset (Finset α)`
  with `P ⊆ W`.

- **Absolute constant `C`.** Existentially quantified at the very outside with
  `0 < C`. Crucially `α`, `k`, `r`, `W` are all bound *inside* the `∃ C`, so `C`
  cannot depend on them — this is what "absolute constant" means. Lean
  auto-generalizes the universe of `α`, so `C` is also universe-independent.

- **"Sunflower with `r` petals".** Custom predicate
  `IsSunflower r Y P := P.card = r ∧ (∀ s₁ ∈ P, ∀ s₂ ∈ P, s₁ ≠ s₂ → s₁ ∩ s₂ = Y)`.
  Explicit core `Y`, pairwise-intersection form. `P.card = r` supplies both the
  petal count and (via `Finset`) distinctness. Requiring exactly `r` rather than
  `≥ r` loses no generality (pass to a subfamily). The "every element in ≥ 2 sets
  is in all" / "petals pairwise disjoint" phrasings are equivalent consequences
  and are noted in the docstring, not separately asserted.

- **Petals nonempty / `Y ⊊ s`.** Not required, matching the standard definition.
  For `r ≥ 2` the pairwise condition already pins down `Y` and forces `Y ⊆ s` for
  every `s ∈ P`; for `r ≤ 1` the statement is trivially satisfiable, which is
  harmless.

- **Cardinality.** `Finset.card` throughout (`s.card = k`, `P.card = r`,
  `W.card`).

- **The bound.** `(C * (r:ℝ) * Real.log (k:ℝ)) ^ k < (W.card : ℝ)`, a strict
  inequality rendering `|W| > (C r log k)^k`. `W.card` is cast to `ℝ`; the
  exponent `k` stays `ℕ` (monoid power).

- **Logarithm.** `Real.log` (natural log). The base is irrelevant: changing base
  multiplies the log by a constant, which is absorbed into `C`. Chose the natural
  log as the cleanest Mathlib default over `Real.logb 2` / `Nat.log 2`.

- **`k = 0, 1` handling.** Hypothesis `2 ≤ k`. At `k = 1`, `Real.log 1 = 0`, so
  the right-hand side is `0` and the hypothesis degenerates to `W` nonempty,
  under which an `r`-petal sunflower need not exist (`r ≥ 2`, `|W| = 1`) — i.e.
  the literal `Real.log k` statement is *false* at `k = 1`. `k = 0` gives only
  the empty set as a `0`-set and is uninteresting. Requiring `k ≥ 2` yields a
  true statement while staying faithful to the "`(C r log k)^k`" form. A common
  alternative that admits `k = 1` is to write `Real.log (k + 1)` (or
  `1 + Real.log k`); not used here to keep the displayed bound literal.

- **`r` positivity.** `1 ≤ r`, matching "for all positive integers r".

- **Distinctness of members.** Not stated explicitly; free from the `Finset`
  representation of both `W` and `P`.

## Uncertainties

- **Mathlib overlap.** `Mathlib/Combinatorics/SetFamily/Sunflower.lean` exists and
  contains the *classical* Erdős–Rado sunflower lemma and some sunflower
  predicate (I believe named `Finset.IsSunflower` or similar, possibly a
  structure with fields `card` and a pairwise-intersection condition; the
  classical lemma name I am unsure of — perhaps `Finset.exists_isSunflower` or
  `Finset.Set.exists_sunflower`). To stay self-contained and avoid a wrong
  identifier I defined my own `IsSunflower`. The *improved* (ALWZ / Rao /
  Bell–Chueluecha–Warnke) bound is, to my knowledge, **not** in Mathlib.

- **Identifiers assumed present:** `Real.log`, `Finset.card`, `Finset.inter`
  (needs `[DecidableEq α]`), the `∃ P ⊆ W, _` binder-predicate notation. These
  are stable in current Mathlib.

- `import Mathlib` (whole library) is used for safety since no compiler is
  available to verify a minimal import list.
