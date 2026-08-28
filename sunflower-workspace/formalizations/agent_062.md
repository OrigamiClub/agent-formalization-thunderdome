# Agent 062 — improved sunflower lemma (statement only)

## Form chosen

Primary theorem `Agent062.improved_sunflower_lemma`:

```
∃ C : ℝ, 0 < C ∧
  ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
    ∀ (W : Finset (Finset α)),
      (∀ s ∈ W, s.card = k) →
      (C * r * Real.log k) ^ k < (W.card : ℝ) →
      ContainsSunflower r W
```

A second, equivalent packaging `improved_sunflower_lemma_function` phrases the bound for
a sunflower/threshold function `f k r` (supplied together with its forcing property as
hypotheses): `f k r ≤ (C * r * Real.log k) ^ k`.

## Auxiliary definitions

* `IsSunflower (r : ℕ) (core : Finset α) (petals : Finset (Finset α)) : Prop`
  := `petals.card = r ∧ ∀ s ∈ petals, ∀ t ∈ petals, s ≠ t → s ∩ t = core`.
  The "pairwise intersections all coincide (with a named core)" formulation.
* `ContainsSunflower (r : ℕ) (W : Finset (Finset α)) : Prop`
  := `∃ core, ∃ petals ⊆ W, IsSunflower r core petals`.

## Encoding decisions and rationale

* **Set representation.** `Finset α` over an ambient type `α` with `[DecidableEq α]`
  (needed for `Finset` intersection). The family is `W : Finset (Finset α)`. This makes
  finiteness of `W` and distinctness of its members automatic, so no separate
  `W.Finite` / pairwise-`≠` hypotheses are required. `α` is quantified *inside* the
  statement, after `∃ C`, so that the constant `C` is genuinely universal (independent
  of the ground type).

* **Sunflower predicate.** Defined locally (namespace `Agent062`) rather than relying on
  a Mathlib identifier, to keep the file self-contained and avoid a wrong name. Mathlib
  does have a sunflower development (I believe `Finset.IsSunflower 𝒜 t`, the
  pairwise-intersection version without a petal count, plus an Erdős–Rado bound lemma
  whose exact name I am unsure of — possibly `Finset.exists_isSunflower` /
  `Finset.exists_sunflower_...`). My `IsSunflower` bundles the petal count `petals.card = r`
  into the predicate; with Mathlib's one would instead write
  `∃ P ⊆ W, P.card = r ∧ Finset.IsSunflower P core`.

* **Petals / core.** Petals are not required to be nonempty (at most one petal, namely a
  set equal to the core, can be empty; irrelevant for `r ≥ 2`). The clause
  `core ⊆ s for all petals s` is omitted: it is forced for `r ≥ 2` and matches the
  standard pairwise-intersection convention. Distinctness of the `r` sets is free from
  `Finset` + `card = r`.

* **Cardinality.** `Finset.card`; "each of cardinality exactly `k`" is
  `∀ s ∈ W, s.card = k`.

* **Logarithm.** `Real.log` (natural log). The base is immaterial — any fixed base
  changes `log` by a constant factor absorbed into `C`. `Real.logb 2` or `Nat.log 2`
  would be equally faithful.

* **Constant `C`.** Existentially quantified inside the theorem ("there is an absolute
  constant `C`"), with `0 < C`.

* **The bound.** Compared with a strict `<` against `(W.card : ℝ)`, matching
  `|W| > (C r log k)^k`. The whole right-hand side lives in `ℝ` with `k`, `r` cast from
  `ℕ`; the exponent `^ k` is natural-number power.

* **`k`, `r` range.** `0 < k` and `0 < r`, i.e. "all positive integers", as stated.

## Uncertainties

* **`k = 1` degeneracy.** `Real.log 1 = 0`, so for `k = 1` the hypothesis becomes
  `0 < (W.card : ℝ)` while the conclusion needs `|W| ≥ r`; the statement is therefore
  *false* at `k = 1` for `0 < |W| < r`. This mirrors how the source statements are
  written (they are really about `k ≥ 2` / the asymptotic regime). An unconditionally
  true variant replaces `Real.log k` by `Real.log (k + 1)` or `max 1 (Real.log k)`, or
  adds the hypothesis `2 ≤ k`; for `k ≥ 2` all of these agree up to the choice of `C`.
  I kept the literal `Real.log k` form for fidelity and documented the caveat in the
  Lean file.

* **Mathlib identifiers.** `Real.log` is certain. The existence and exact name of a
  Mathlib sunflower predicate (`Finset.IsSunflower`) and of the classical Erdős–Rado
  bound lemma are guessed; the file does not depend on them (own definitions used).

* **`import Mathlib`.** Used wholesale for convenience; the real dependencies are just
  `Finset` and `Real.log`.

* No proofs attempted: both theorems end in `:= by sorry`.
