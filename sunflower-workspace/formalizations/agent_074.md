# agent_074 — improved sunflower lemma (statement only)

## Form chosen

A single `theorem improved_sunflower_lemma` of the shape

```
∃ C : ℝ, 0 < C ∧ ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
  ∀ W : Finset (Finset α),
    (∀ S ∈ W, S.card = k) →
    (C * r * Real.log k) ^ k < (W.card : ℝ) →
    ∃ (P : Finset (Finset α)) (Y : Finset α), P ⊆ W ∧ IsSunflower r Y P
```

plus a local `def IsSunflower`.

## Encoding decisions

- **Set representation.** `Finset α` for individual sets over an arbitrary type
  `α`, and `W : Finset (Finset α)` for the family. This makes "finite family",
  "each set finite", and "the members are distinct" all automatic, and
  `Finset.card` is the single notion of cardinality used.
- **`IsSunflower r core petals`.** Defined explicitly with a named core:
  `petals.card = r`, `core ⊆ s` for every `s ∈ petals`, and `s ∩ t = core` for
  every pair of distinct members. The `core ⊆ s` clause is redundant for `r ≥ 2`
  (it follows from the pairwise-intersection clause) but makes the predicate
  sensible for `r ≤ 1` and faithful to "core `Y` with petals `S_i \ Y`".
  Distinctness of the `r` sets is free because `petals` is a `Finset`. Petals are
  not required to be nonempty as a separate hypothesis; each member has
  cardinality `k ≥ 2` so is nonempty anyway.
- **Conclusion.** `∃ P ⊆ W, ∃ Y, IsSunflower r Y P` — `W` "contains" a sunflower
  as a sub-family, with the core existentially quantified.
- **Logarithm.** `Real.log` (natural log). The base only changes `C`, which is
  existential. The bound is compared in `ℝ`: `(C * r * Real.log k) ^ k` with the
  `ℕ` exponent `k` (monoid power), against `(W.card : ℝ)`.
- **`k = 0, 1`.** Excluded via `2 ≤ k`. For `k ≤ 1`, `Real.log k = 0`, so the
  right-hand side is `0` and the statement "`|W| > 0 ⟹ r-sunflower`" is false for
  `r ≥ 2`. The literature's `(C r log k)^k` bound is understood for `k ≥ 2`
  (small `k` folded into the constant), so this is a faithful reading. An
  alternative would be `Real.log (k + 1)` with only `1 ≤ k`.
- **`r`.** Required `1 ≤ r`. `r = 1` is trivially satisfiable, so no falsity is
  introduced; `r = 0` is excluded for tidiness.
- **Constant `C`.** Existentially quantified with `0 < C`, and placed outside the
  `∀ α` binder so it cannot depend on the ambient type — a genuinely absolute
  constant. Alternative encodings (named `noncomputable def C`, or `C` supplied as
  a hypothesis `1 ≤ C`) were rejected as less self-contained.

## Uncertainties

- **Mathlib may already have a sunflower predicate.** I could not verify its
  presence or name. Candidates I would check: `Finset.IsSunflower`,
  `Finset.Sunflower`, a `Sunflower` structure in
  `Mathlib/Combinatorics/SetFamily/Sunflower.lean`, possibly with signature
  `(petals) (core)` or bundling the core. To stay self-contained I defined my own
  `IsSunflower`; if the Mathlib one exists it may differ in argument order, in
  whether the core is bundled/existential, and in whether it demands `2 ≤ r` or
  petal-disjointness directly.
- Whether Mathlib states the classical Erdős–Rado sunflower lemma (e.g.
  `Finset.exists_sunflower` / `exists_isSunflower`) is likewise unverified; the
  improved bound is very likely not in Mathlib.
- `import Mathlib` is used for convenience; a minimal import would be roughly
  `Mathlib.Analysis.SpecialFunctions.Log.Basic` plus
  `Mathlib.Combinatorics.SetFamily.Basic` (names approximate).
- Coercions in `C * r * Real.log k`: relies on the `binop%` elaborator inserting
  `ℕ → ℝ` casts for `r` and `k`. Believed correct but not compiler-checked.
